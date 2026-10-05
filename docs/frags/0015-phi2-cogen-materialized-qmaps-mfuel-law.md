---
type: frag
id: 0015
provenance: devin-cli
ts: 2026-02-19
tags: [phi2, cogen, realize, apply, assemble, qmaps, mfuel, l2-wall]
---

# 0015 — cogen emits real bytes (corpus); native 'call-dispatch congruent to the eval<menv> wall; mfuel law measured

## What landed

- **`qmaps` materialized from the toolchain catalog** (host-side
  loader, `_cogen_probe.py`): catalog rows walked via
  `run_value(dg,"toolchain")`; the x86 map becomes
  `'map(menv, 'assemble)` where `menv = enc_env` of the map's
  call-closure `{assemble, enc, reg_code, append, cons}`.
  **`cons` is load-bearing**: `append` destructures via
  `cons<h,t> = xs`, so a map env missing `cons` refuses every
  `append` — that was a real refusal, not a bug.
- **Corpus `cogen<spec>` → 1 solution**, decode → emitted
  byte-spine `55 C3` for `[push rbp, ret]` (and the `mov_ri`
  program's expected `55 48 B8 42 00*7 5D C3`). The chain
  `cogen → realize → rfold → apply → eval<menv> → assemble`
  carries a real spec to real bytes.
- **Native 'call-dispatch: congruent, no machine bug.** Every
  anomaly from the previous session resolved:

  | probe | mfuel | result |
  |---|---|---|
  | `'call('realize)` spec `maps=[]` | 512 | 1 sol, src passthrough (2.55M steps) |
  | `'call('rfold)` `NILe³` | 512 | 1 sol, acc passthrough (1.06M) |
  | `'call('unify_args)` | 512 | 1 sol (1.01M) |
  | `'call('append/assoc/eq_t/nonvar/walk/subst_lookup/member/next_id)` | 160 | sols |
  | `env_find` on `'pair`-noded env | 160 | 1 sol |

## The mfuel law (previously misread as divergence)

`'call`-dispatched defs that internally `RUN`-probe or nest
`'call`s consume ~3–5 machine unrolls **per nested dispatch**
(inst → RUN(ren_find) → eval → 'call → env_find → eval_call →
inst_list → unify_args → eval_body → eval → unify_enc → walk →
nonvar → RUN(var_probe) → …). Deep clauses need `mfuel ≥ ~256`;
`realize`-class chains need `≥512`.

At `mfuel=160` the failure signature is **~6.66M steps → empty
stream** — every path bottomed at the unroll cap. Earlier reads
of this as "semantic miss" were wrong; the corpus oracle and
the machine agree at sufficient mfuel on every completed probe.

## The wall, precisely located

`eval<menv>` — `'call('eval)` dispatching the enc'd-once
eval-def to interpret enc'd-once map defs — is interpreter²:
every inner `'call`/`unify`/probe re-enters the full dispatch
tower with inst-allocation retained. `rc=4` at 16 GB arena even
for `'unify(a8,a8)` and dummy-`'call` goals — the inst'd
eval-def's own clause machinery is the cost, before the map
runs. Same documented class as the L2 `'call('eval)` wall
(frag 0014): finite derivation, bump-arena retains the whole
lazy search tree. The fix axis is the queued
**GC'd/reclaiming realization for single search trees** —
unblocked work item, not a workaround.

## Congruence summary

| path | corpus | native (mfuel≥512) |
|---|---|---|
| `cogen<spec>` → bytes | 1 sol, `55 C3` | OOM at `eval<menv>` |
| `realize` maps=`[]` | 1 sol | 1 sol |
| `rfold/apply` dispatch | works | works to `eval<menv>` |
| inner `eval<menv>` | 1 sol, bytes | rc=4 (retention wall) |

Native cogen is therefore honest-blocked at exactly one link —
the inner evaluator — not at dispatch, env materialization, or
spec encoding.
