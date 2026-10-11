---
type: frag
id: 0026
provenance: devin-cli
ts: 2026-10-11
tags: [phi2, byte-add, adyn, adsub, natsub, eval-menv, gc-sweep,
       decision-065, x86, pass1, wall]
---

# 0026 — corpus-level byte_add landed (var-var `adyn`/`adsub`); decode-verified telemetry shows the nibble "wall" was a semantic ∅, and byte-domain fixed it; residual is evaluator-strategy cost

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
enc2_len ret         508M  sols=0  EMPTY          397M  sols=1
enc2_len push        615M  sols=0  EMPTY          648M  sols=1
pass1 [ret]          521M  sols=0  EMPTY          549M  sols=1
pass1 [ret,ret]      521M  sols=0  EMPTY          rc=2  fuel-cap 305s
pass1 [push,ret]     651M  sols=0  EMPTY          rc=2  fuel-cap 1381s
assemble2 [push,ret] (subsumed by assemble)       rc=2  fuel-cap 210s
assemble [push,ret]  787M  sols=0  EMPTY          rc=2  fuel-cap 1516s
```

**This table invalidates the frag-0025 narrative.**  On the
nibble map, `enc2_len` and everything above it (`pass1`,
`assemble`) do not "hit a wall" under the reordered evaluator —
they return **empty streams**: a machine-eval semantic
divergence in the nibble-chain length machinery that was
masked as OOM/>4min on the pre-reorder evaluator (eager
`inst_list<goals>` made the failing search expensive enough to
kill the arena before it could finish returning ∅).  The
byte-domain rewrite therefore delivered a **correctness** fix —
`enc2_len`/`pass1` produce real machine-verified sols for the
first time — not merely a speedup.  Step-count deltas where
both maps solve: `enc2 ret` −4%, `enc2 push` −3%.

Two measurement traps recorded for future bisects:

1. `rc=0` proves only that the reducer finished; an absent-rel
   env prunes to an ~1.2M-step empty stream that reads as "fast
   success."  Always decode sols.
2. `take 2` on a single-sol stream forces the evaluator to
   prove no second sol exists across all backtracking branches —
   far more expensive than `take 1`.  All rows here are take-1.

The `eval_clause` reorder (unify before goals-inst) itself is
semantics-preserving and landed in `eval.phi` + machine lts;
it converted the nibble-map failure mode from OOM to fast-∅,
and is kept as a strict-improvement reorder.

Host-level verification of the same map: `assemble<[push rbp;
ret]>` → `[0x55,0xC3]`; `bs4_sub [5,0,0,0] [200,0,0,0]` →
`[61,255,255,255]` = `0xFFFFFF3D` (exact two's-complement
borrow); rel32 backward `e8 fb ff ff ff c3` and forward
`e8 01 00 00 00 c3`, both fasmg-exact.  The committed enc2
gate still passes (35/35), battery fast 31/31.

## What is proven

- **Byte-domain corpus arithmetic works natively end to end and
  restores machine-eval semantics above `enc2`.**  `byte_add` =
  627K steps; `enc2_len` and `pass1[ret]` produce decoded sols —
  the first machine-verified results those rels have ever
  produced.  On the nibble map the same probes return empty
  streams (see table): the frag-0025 "representation wall" was
  in fact a semantic divergence, and the byte map fixes it.
- The `clauses:null` + `atom_dyn` computed-rel mechanism scales
  to var-var operands with engine-side support in all three
  evaluators (host `rel_eval`, phi2 `seed`, machine `lts`).

## What is NOT proven — the residual wall, named

- **Multi-op `pass1`/`assemble2`/`assemble` exceed the 2e9-step
  fuel cap on the byte map** (fuel is an i32 immediate; 2e9 is
  the ceiling).  `pass1[ret]` = 549M; the second op pushes past
  2e9 — superlinear per-op growth inside a *correct* search
  (byte `pass1` does produce sols, it just can't afford op 2).
  Mechanism candidates (not yet isolated): linear
  `subst_lookup` over an assoc list growing per pass1 level,
  corpus-peano `add`/`sub` inside `adyn_res` on each pc advance,
  `eval_clauses` disjunction under nested `bind`/`append`
  streams.  The cheap-fail reorder (unify before goals-inst)
  did NOT move this number — the wall is deeper than
  failed-clause cost.  At ≥500M–1.5G steps/op marginal, the
  769-op full-src program is unreachable under this evaluation
  strategy — an **evaluator-strategy** cost, not an
  arithmetic-representation cost.
- MEGAPLAN §7 criterion (native `assemble` full-src under
  gc=sweep) is therefore **still open**; the remaining blocker
  is clause-scan/subst-scan overhead in the corpus evaluator —
  a property of `eval.phi`'s declared strategy (or the
  machine's interpretation of it), which no corpus-data change
  to the map fixes.
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
