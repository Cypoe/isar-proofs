---
type: frag
id: 0025
provenance: devin-cli
ts: 2026-10-06
tags: [phi2, gc, sweep, eval-menv, cogen, fasmg, x86, raw-bytes]
---

# 0025 — native eval\<menv> under gc=sweep emits a real x86 byte; fasmg raw oracle; pass1 is the nibble-chain wall

## What landed

`np_gates_rel.gate_rel_native_menv_enc2` — the first committed
phi2-native witness: the unrolled corpus evaluator
(`machine_term`) interprets the **generated**
`assemble_x86_win64` map environment under
`Realization(reclaim="redirect", gc="sweep", io=("stdin",
"stdout"), fuel=2e9, ir_arena=2GiB)` and computes
`enc2<'op('ret)> = [0xC3]` — byte-identical to fasmg's
flat-`format binary` output for `ret`.

This is the collapsed cogen leg the frag-0016 line needed:
real bytes out of corpus evaluation, GC reclamation active,
no PE container, no Python assembling — Python only packs the
term and reifies the subst spine.

## Measurements (native, gc=sweep, 2GiB arena)

```
probe                          steps          wall    result
eval<menv> cons<atom5,atom6>   203K            ~1s     sol: pair(5,6)
eval<menv> enc2<'ret'>         296,038,631     7.8s    c3 == fasmg c3
eval<menv> enc2_len<'ret'>     —               >4min   nibble-length chain
eval<menv> pass1<[ret]>        —               OOM     rc=4: arena exhausted,
                                                       sweep frees nothing
eval<menv> assemble<[*]>       —               —       pass1-bound (assemble2
                                                       calls enc2_len per op)
```

GC telemetry on enc2: `alloc=444,304,321 gc=41
free=435,386,698` — 444M cells allocated, 98% reclaimed into a
~260MB working set.  Pre-GC this class of run committed >100GB.

## What is proven

- The corpus evaluator computes a real x86 encoding **under
  sweep GC** on the packed-IR kernel — the GC'd realization is
  exercised end-to-end, not just registered.
- The byte tree is decode-boundary honest: subst reification
  (var0 → 'pair spine → 'atom(8,v) leaves) yields `c3`, and the
  witness is fasmg's own flat output — the same oracle every
  ISA row was mined against, not the map's own tables.
- eval\<menv> at one interpretation level (the compiled corpus
  eval over the map env) is the minimal honest collapse —
  `cons` (203K steps) and `enc2` (296M) both decode real sols.

## What is NOT proven — the walls, named

- **`enc2_len`/`pass1` are the corpus's own wall.**  Byte
  *emission* is feasible (296M steps/op); *length* arithmetic is
  not: `nl_add`/`nibble_succ` chains on 8-nibble words plus
  absence-probe guards (`i32f`, `v7 != ...` rows — each a nested
  RUN) materialize a live working set that OOMs the 2GiB arena
  even under collection.  GC cannot reclaim what is still
  reachable — this is a corpus-shape problem, not a memory bug.
  This is now **measured** motivation for decision 065's
  `byte_add`: the nibble-chain path is the wall at level 1, not
  just at interpreter².
- **interpreter² `eval<menv>`** (corpus eval interpreting corpus
  eval interpreting the map — the full `apply`/`rfold` dispatch
  chain) was not reached here: the gate exercises the level-1
  leg.  At mfuel=160 interp² probes return `[]` within ~31M
  steps (fuel-cut or empty — the frag-0016 ambiguity); the L1
  collapse is the deliberate simplification.
- Observational equivalence of *running programs* remains the
  open hard part — this frag covers raw-byte/encoding equality
  only.

## Honest edges

- The gate's decode path is Python-side reification — data
  crosses the boundary, never logic (the corpus produces the
  byte tree; Python only walks the subst spine).
- fasmg absence raises `FileNotFoundError` naming the oracle —
  a loud refusal, not a silent pass.
- `_ncogen.py` (repo-root scratch) is the probe driver the gate
  was distilled from; the gate is the committed replayable form.
