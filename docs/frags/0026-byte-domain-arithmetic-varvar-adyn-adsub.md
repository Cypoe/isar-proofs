---
type: frag
id: 0026
provenance: devin-cli
ts: 2026-10-11
tags: [phi2, byte-add, adyn, adsub, natsub, eval-menv, gc-sweep,
       decision-065, x86, pass1, wall]
---

# 0026 — corpus-level byte_add landed (var-var `adyn`/`adsub`); decode-verified telemetry: nibble wall reproduced as OOM, byte-domain clears enc2_len/pass1; residual wall = quadratic assoc-subst scan

## What landed

Decision 065's `byte_add`, as the `succ`-precedent mechanism —
a `clauses:null` declared computed rel whose `out` is an
`atom_dyn` term — extended to **var-var** operands:

- `atom_dyn` gains `var_add` (`ATOM(8, a+b)` → `'adyn('nvar a,
  'nvar b)`) and `var_sub` (`ATOM(8, a-b)` → `'adsub('nvar a,
  'nvar b)`).  `adyn_res` already *walked* the delta operand;
  the var-var form needed only parser (`_aexpr`), enc, lazy
  (`rel_eval`/`seed`), and machine tags (`is_adsub`, `natsub` —
  Scott-peel, floors at 0).
- Negative `var_delta` (`ATOM(8, x-1)`) now encodes `'adsub`
  instead of hitting `_nat_lc(-1)` → `z` — a latent machine-path
  bug (negative deltas silently computed `x+0`) closed as a
  side effect.
- Semantics: **peano floor at 0** everywhere (machine `natsub`,
  `rel_eval`, `seed` agree).  Two's-complement wrap lives in the
  *byte-list* domain where it belongs, not in scalar nat-sub.
- Std corpus gains `sub` (`arith_peano_succ`); generated map
  rewritten to byte domain: pc/labels/symtab/rel32 as 4-byte LE
  lists, `bs4_add`/`bs4_sub` ripple carry/borrow over
  `byte_add`/`byte_sub` + `eq`/`neq` (carry detection via
  `s-255 ≠ 0`, borrow via `a-b==0 ∧ a≠b` — no `blt` needed).
  `nl_add`/`len_nl`/`nibble_sub`/`nadd_*` dropped; nibble
  machinery kept only where operands are nibble-shaped
  (`im32`, `se8f`, `nibs2bytes`).

## Measurements — the before/after pair, decode-verified

Committed data (sha256-manifest regime):
`telemetry/phi2_repr_cost/` — `rows.jsonl` + `README.md` +
`nibble_map_9bb305a.plex` (byte-for-byte pin of the nibble map).
Both maps measured under the **same reordered evaluator**
(post-`eval_clause` reorder), `take 1`, `gc=sweep`, fuel 2e9,
arena 2GiB.  `sols` = decoded sol count of the take-1 stream;
`sols=0` = empty-stream semantic failure, **not** a cost wall.

```
probe                nibble map (9bb305a)          byte map (cfbfcca)
byte_add<200,55>     —                            627K  sols=1
enc2 ret             296M  sols=1  (gate-verified 285M  sols=1
                     fasmg bytes)
enc2 push            405M  sols=1                 394M  sols=1
enc2_len ret         rc=4 OOM 922s                397M  sols=1
enc2_len push        rc=4 OOM 1506s               648M  sols=1
pass1 [ret]          rc=4 OOM 1253s               549M  sols=1
pass1 [ret,ret]      rc=4 OOM 1124s               rc=2  fuel-cap 305s
pass1 [push,ret]     rc=4 OOM 565s                rc=2  fuel-cap 1381s
assemble2 [push,ret] rc=2 fuel-cap 184s           rc=2  fuel-cap 210s
assemble [push,ret]  rc=4 OOM 851s                rc=2  fuel-cap 1516s
```

(`assemble2` on nibble fuel-caps instead of OOMing because the
`[push,ret]` program has no labels — the relfix/nibble-sub path
never runs, so no chain live-set accumulates; it just scans.)

**Interpretation (three corrections were needed to get here).**
An earlier telemetry pass read nibble-map `enc2_len`/`pass1`/
`assemble` as *empty-stream semantic failures* — that was a
probe artifact: the harness loaded only 5 std bundles and
`nibble_succ`/`nibble_add` live in `arith_nibble_carry`, so
`nadd_b` failed `env_find` and ∅ propagated up.  With the full
std env the nibble-map wall reproduces exactly as frag 0025
recorded it — `enc2_len<'ret'>` OOMs the 2GiB arena (rc=4)
at ~920 s under the *reordered* evaluator too.  So: the
nibble wall is **real** (live-set blowup on 8-nibble
succ-chains), the byte map genuinely clears it (`enc2_len` and
`pass1` produce the first machine-verified sols those rels have
ever yielded), and both earlier misreadings are recorded so
the dataset carries the caveat.

**Residual wall — mechanism now measured, not hypothesized.**
`eval.phi` threads ONE assoc-list subst `s` through all nested
`'call` goals (`eval_body` line: `eval<env,g,s,n>`), and
`subst_lookup` scans it linearly.  Host-level instrumentation
of the same relations: `pass1` over k ops costs a constant
~2,372 walks/op while the shared subst grows +164 bindings/op —
linear × linear ⇒ **quadratic in op count** at machine level.
Corroborated natively: `pass1<[ret]>` at pc=0 vs pc=1 differ by
3,427 steps (548.55M both) — the op-2-position work is
intrinsically identical, so the >1.45G op-2 marginal inside
`pass1<[ret,ret]>` is pure accumulated subst depth.  769 ops →
~10¹⁴ reducer steps: unreachable, and no corpus-data change to
the map can fix it — the fix is an `eval.phi`-level subst
structure (tree/indexed subst or scoping), a declared-strategy
change, not new substrate.

Two measurement traps recorded for future bisects:

1. `rc=0` proves only that the reducer finished; an absent-rel
   env (closure-pruned or under-provisioned) returns an ~1.2M-
   step empty stream that reads as "fast success."  Always
   decode sols AND check env completeness against `uses:`.
2. `take 2` on a single-sol stream forces proof of no second
   sol across all backtracking — far pricier than `take 1`.
   All rows are take-1.

The `eval_clause` reorder (unify before goals-inst) itself is
semantics-preserving, landed in `eval.phi` + machine lts, and
kept as a strict-improvement reorder; it changed neither the
nibble wall (still OOM) nor the byte-map sols.

Host-level verification of the same map: `assemble<[push rbp;
ret]>` → `[0x55,0xC3]`; `bs4_sub [5,0,0,0] [200,0,0,0]` →
`[61,255,255,255]` = `0xFFFFFF3D` (exact two's-complement
borrow); rel32 backward `e8 fb ff ff ff c3` and forward
`e8 01 00 00 00 c3`, both fasmg-exact.  The committed enc2
gate still passes (35/35), battery fast 31/31.

## What is proven

- **Byte-domain corpus arithmetic works natively end to end and
  clears the nibble wall.**  `byte_add` = 627K steps; `enc2_len`
  and `pass1[ret]` produce decoded sols — the first
  machine-verified results those rels have ever yielded.  On
  the nibble map (complete env, same evaluator) the same probes
  OOM the arena — frag-0025's wall reproduced, then removed.
- The `clauses:null` + `atom_dyn` computed-rel mechanism scales
  to var-var operands with engine-side support in all three
  evaluators (host `rel_eval`, phi2 `seed`, machine `lts`).

## What is NOT proven — the residual wall, named

- **Multi-op `pass1`/`assemble2`/`assemble` exceed the 2e9-step
  fuel cap on the byte map** (fuel is an i32 immediate; 2e9 is
  the ceiling).  Mechanism is now *measured*, not hypothesized:
  `eval.phi` threads one assoc-list subst through every nested
  `'call`; `subst_lookup` scans it linearly.  Host
  instrumentation of the same relations: +2,372 walks/op ×
  +164 bindings/op ⇒ quadratic.  Native discriminating probe:
  `pass1<[ret]>` at pc=1 standalone = 548,555,085 steps vs
  pc=0 = 548,551,658 (Δ=3,427) — the op-2-position work is
  intrinsically identical, so the >1.45G op-2 marginal inside
  `pass1<[ret,ret]>` is accumulated subst depth, nothing else.
  At ~500M + k·~1G steps/op the 769-op full-src is unreachable
  (~10¹⁴ steps) under this strategy — an **evaluator-strategy**
  cost.  The fix lives in `eval.phi`'s subst structure
  (tree/indexed subst or scoping) — declared corpus data, not
  new substrate.
- MEGAPLAN §7 criterion (native `assemble` full-src under
  gc=sweep) is therefore **still open**; the blocker is the
  assoc-subst scan in the corpus evaluator, which no
  corpus-data change to the map fixes.
- Interpreter² `[]` ambiguity (frag 0016) remains deliberately
  open — unchanged, out of criterion scope.

## Honest edges

- `var_sub` floors at 0 by design (peano nats); the map only
  calls it where the guard establishes `a≥b`, and fixed-width
  wrap is re-established by the borrow chain, not by signed
  scalars.
- `sub` lives in std (`arith_peano_succ`), not duplicated in
  the generated map — the map merges std, so no repetition.
- The decode-side fuel-bottom tail (`sym` sentinel on truncated
  streams) is a known scratch-decoder artifact, handled
  leniently in probes; it does not affect step/gc telemetry.
- The fuel ceiling is structural: `cmp_r64_imm` sign-extends an
  i32.  No probe can exceed ~2.1e9 steps under this emitter —
  recorded so future walls are classified correctly (fuel-cap
  rc=2 vs OOM rc=4 are different failures).
