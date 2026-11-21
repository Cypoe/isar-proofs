# 065 — corpus batch primitives: declared byte-add, congruence-gated, deferred to measurement

## Context

The phi2/rel.rs evaluator sits within ~2–3x of its per-operation
floor (decision 062/frag 0020: HAMT subst, clause-template compile,
head-literal dispatch index all landed — what remains is the cost
of the relations themselves, not evaluation machinery).  The
dominant relation-level cost is nibble-domain arithmetic: every
address/offset in `assemble_x86_win64` is an 8-nibble LE list, and
`nibble_add`/`nibble_pred` unfold as ~8 unifications plus a carry
chain *per add* — tens of engine steps for what a host computes in
one instruction.  Interpreter-squared probes compound this: the
inner evaluator pays nibble-chain cost for the *outer* machine's
arithmetic too.

The candidate change is a corpus-level batch primitive: a declared
`byte_add`/`byte_sub` (or packed-limb add) relation that replaces
the nibble chains at assembly-map hot points.

## Numbers in hand

- rel.rs and seed.py agree term-for-term at ~2–3x of the Python
  per-op floor — dispatch is no longer the bottleneck; relation
  unfolding is.
- `assemble` of a ~60-item program: 7.35M `_tset` / 2.14M `_tget`
  calls (frag 0020) — the bulk driven by pc-threading arithmetic
  through `nibble_add` chains.
- interpreter-squared rt probes committed >100GB before being
  killed (rel.rs without GC; frag 0016's sweep exists only
  natively on win64).
- A byte-level add collapses each add's ~8-clause-digit unfold to
  one row lookup: measured-vs-declared trade, not free.
- **2026-10-06, native eval\<menv> under gc=sweep (frag 0025):**
  `enc2<'ret'>` completes in 296M steps / ~8s (alloc=444M, gc=41,
  free=435M — 98% reclaimed) and matches fasmg byte-for-byte;
  `enc2_len<'ret'>`/`pass1`/`assemble2` OOM the 2GiB arena (rc=4 —
  collection frees nothing, the live set is the nibble chains).
  The wall is already visible at the level-1 leg, not only at
  interpreter² — GC cannot fix a live working set; the corpus
  itself must stop spelling byte arithmetic in nibble chains.

## Decision

Adopt batch arithmetic **as declared corpus relations, not engine
tuning** — but only behind a congruence obligation:

1. `byte_add`/`byte_sub` enter the corpus as *declared* rels.  The
   nibble chains stay the definitional spec; the batch forms must
   carry a Lean-checked congruence (`byte_add a b c` iff the
   nibble-chain equivalent) — the same witness discipline as every
   corpus relation.  Without that proof obligation the primitive
   is smuggled semantics.
2. No engine special-casing of `nibble_add` patterns: an engine
   recognizing and accelerating a *named* relation is a hidden
   shortcut — the same bypass we refused elsewhere.  The speedup
   must live in the declared corpus, where the toolchain catalog
   and gates can see it.
3. Ordering: the GC port to rel.rs (decision 059's engine) lands
   first — interpreter-squared probes are the only place this
   matters at full scale, and they cannot run to completion until
   the Rust engine reclaims memory.  Batch primitives are
   premature until that substrate can measure them end-to-end.

## Alternatives rejected

- *Silent engine recognition of nibble_add*: smuggles semantics —
  a performance path the corpus doesn't declare and the proofs
  don't see.
- *Batch primitives now, proof later*: inverts the discipline —
  the declared relation IS the spec; it cannot precede its own
  congruence.
- *Status quo permanently*: leaves cogen gated by nibble-chain
  cost forever; the 2–3x floor gap is real and this is the only
  corpus-level lever for it.

## Outcome triggers

Land when: (a) an honest before/after wall exists — **met on the
native kernel** (frag 0025: enc2 emits bytes under gc=sweep;
enc2_len/pass1 OOM on nibble chains — the wall is corpus shape,
measured at L1 eval\<menv>); (b) a `byte_add` congruence
obligation exists on the Lean side or is explicitly scoped.
Trigger (a) no longer waits on the rel.rs GC port — the win64
sweep collector already carries the measurement.  What remains
open: full `assemble` (label pass over nibble arithmetic) and the
interpreter² leg still cannot complete — both are the same wall.

## Outcome — landed 2026-10-11 (frag 0026)

The primitive mechanism turned out narrower than sketched: no new
`byte_add`-as-builtin was needed.  `atom_dyn` already *walked*
its delta operand (`adyn_res` resolves `'adyn(base, delta)` by
walking both), so var-var arithmetic is `atom_dyn` gaining
`var_add`/`var_sub` payloads → `'adyn`/`'adsub` tags →
`natadd`/`natsub` (peano floor).  `byte_add`/`byte_sub` are
`clauses:null` declared rels — the `succ`/`pred` precedent —
not engine special-casing, satisfying decision point 2 by
construction.  The nibble chains stay the definitional spec
(they remain in the map where operands are genuinely
nibble-shaped); the Lean congruence obligation (decision point
1) is still open debt — the batch form is admitted, the proof
is not yet discharged.

Generated map rewritten to byte domain: pc/labels/symtab/rel32
as 4-byte LE lists via `bs4_add`/`bs4_sub` ripple over
`byte_add`/`byte_sub` + `eq`/`neq` only.  Measured, same corpus
evaluator both sides, **decode-verified** (committed data:
`telemetry/phi2_repr_cost/`, nibble map pinned byte-for-byte):

```
probe            nibble (9bb305a)          byte (cfbfcca)
enc2 ret         296M sols=1 (fasmg)      285M sols=1
enc2 push        405M sols=1              394M sols=1
enc2_len ret     rc=4 OOM 922s            397M sols=1
enc2_len push    rc=4 OOM 1506s           648M sols=1
pass1 [ret]      rc=4 OOM 1253s           549M sols=1
pass1 [ret,ret]  rc=4 OOM 1124s           rc=2 fuel-cap 305s
pass1 [push,ret] rc=4 OOM 565s            rc=2 fuel-cap 1381s
assemble2 2op    rc=2 fuel-cap 184s       rc=2 fuel-cap 210s
assemble 2op     rc=4 OOM 851s            rc=2 fuel-cap 1516s
```

**Confirmed finding:** the frag-0025 nibble wall is real —
reproduced as rc=4 arena-OOM under the reordered evaluator with
the complete std env.  (An intermediate telemetry pass read
those probes as empty-stream failures; that was a harness
artifact — `nibble_succ`/`nibble_add` live in
`arith_nibble_carry`, which the harness had omitted, so
`env_find` failed and ∅ propagated.  Recorded as a trap in
telemetry/phi2_repr_cost/README.md.)  The byte map genuinely
clears it: first machine-verified `enc2_len`/`pass1` sols.

**Residual wall — mechanism measured:** multi-op
`pass1`/`assemble2`/`assemble` on the byte map exceed the 2e9
fuel cap inside a correct search.  Cause: `eval.phi` threads
one assoc-list subst through every nested `'call`;
`subst_lookup` scans it linearly.  Host instrumentation:
+2,372 walks/op × +164 bindings/op ⇒ quadratic.  Native
discriminator: `pass1[ret]@pc=1` = 548,555,085 vs @pc=0 =
548,551,658 steps (Δ=3,427) — op-2 intrinsic work identical;
the >1.45G marginal is subst depth.  769 ops ⇒ ~10^14 steps ⇒
unreachable under this strategy.  Fix surface: `eval.phi`
subst structure (tree/indexed or scoped) — declared corpus
data, not new substrate.  Ordering point 3 superseded: batch
primitives landed natively without the rel.rs GC port; the
win64 kernel carried the measurement.
