---
type: frag
id: 0026
provenance: devin-cli
ts: 2026-10-11
tags: [phi2, byte-add, adyn, adsub, natsub, eval-menv, gc-sweep,
       decision-065, x86, pass1, wall]
---

# 0026 — corpus-level byte_add landed (var-var `adyn`/`adsub`); the representation wall broke; the residual wall is clause/subst scan, not arithmetic

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

## Measurements — the before/after pair, same corpus evaluator

Native `eval<menv>` (compiled corpus eval over the generated
map env), `reclaim=redirect, gc=sweep, fuel=2e9, arena=2GiB`:

```
probe                    nibble map (frag 0025)   byte map (this frag)
byte_add<200,55>         — (didn't exist)          627K steps, 0.5s, rc=0
enc2_len<'ret'>          >4min (wall)              397M steps, 10.0s, gc=58
enc2_len<'push r64 rbp'> —                         647M steps, 36.5s, rc=0
pass1<[ret]>             OOM rc=4                  548M steps, 22.8s, rc=0
pass1<[ret,ret]>         —                         rc=2 fuel-cap (>2e9),
                                                   357s pre- / 283s
                                                   post-reorder
assemble2<[push,ret]>    —                         rc=2 fuel-cap, 252s
assemble batch (4 probes)—                         OOM rc=4, 729s
```

A second corpus-strategy change also landed: `eval_clause` in
`eval.phi` + the machine lts now gates on `unify_args` /
`unify_enc` **before** `inst_list<goals>` — failed clauses no
longer instantiate the whole goal body.  Semantics-preserving
conjunction reorder (same sol set; goals-inst shifts per-sol
for multi-sol unifications, which our probes don't exercise).
Measured effect on the bisect probes: none (enc2_len 397M
pre/post, pass1-1op 548M pre/post) — the matched clause's body
evaluation dominates, not failed-clause inst.  Kept anyway as
a strict-improvement reorder with zero measured cost.

Probe-hygiene note for future bisects: an `eval` call whose rel
is *absent from the pruned env* returns an empty stream in
~1.2M steps — a mirage that twice read as "fast success."
Always confirm a decoded sol, not just rc=0.

Host-level verification of the same map: `assemble<[push rbp;
ret]>` → `[0x55,0xC3]`; `bs4_sub [5,0,0,0] [200,0,0,0]` →
`[61,255,255,255]` = `0xFFFFFF3D` (exact two's-complement
borrow); rel32 backward `e8 fb ff ff ff c3` and forward
`e8 01 00 00 00 c3`, both fasmg-exact.  The committed enc2
gate still passes (35/35), battery fast 31/31.

## What is proven

- **Byte-domain corpus arithmetic works natively end to end.**
  `byte_add` at 627K steps vs the nibble `nl_add` chains that
  put `enc2_len` over 4 minutes — the representation cost is
  now measured, not hypothesized.
- **`enc2_len` and single-op `pass1` complete under gc=sweep**
  where the nibble map OOM'd the arena.  The frag-0025 wall
  was real and is now behind us.
- The `clauses:null` + `atom_dyn` computed-rel mechanism scales
  to var-var operands with engine-side support in all three
  evaluators (host `rel_eval`, phi2 `seed`, machine `lts`).

## What is NOT proven — the residual wall, named

- **Multi-op `pass1`/`assemble2` exceed the 2e9-step fuel cap**
  (fuel is an i32 immediate; 2e9 is the ceiling).  Op-1 ≈ 548M
  steps; op-2 marginal > 1.45G — **superlinear growth per op**.
  Mechanism candidates (not yet isolated): linear
  `subst_lookup` over an assoc list growing ~5–10 bindings per
  pass1 level, `eval_clauses` disjunction cost inside nested
  `bind`/`append` streams, or `inst` of deepened patterns.  The
  cheap-fail reorder (unify before goals-inst) did NOT move the
  number — the wall is deeper than failed-clause cost.  At
  ≥500M–1.5G steps/op marginal, the 769-op full-src program is
  unreachable under this evaluation strategy — an
  **evaluator-strategy** cost (dispatch/enumeration), not an
  arithmetic-representation cost.
- MEGAPLAN §7 criterion (native `assemble` full-src under
  gc=sweep) is therefore **still open** as of this frag; the
  remaining blocker is clause-scan/subst-scan overhead in the
  corpus evaluator, which no corpus-data change to the map
  fixes — it is a property of `eval.phi`'s declared strategy
  (or of the machine's interpretation of it).
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
