# 022 — G9b: specialization cell on the real catalog (P1 shape)

**Status:** implemented (isar-proofs `host/spec_term.py`, gate `G9b`)

## What landed

`spec_term.py` now runs a second pass after the direct queries: the
Futamura P1 shape with the spec itself as the static input.

    prog     = QUERY v0 v1        (v0 = static spec, v1 = dynamic name)
    residual = nf_lo(specialize(prog, {0: SPEC}))
    check    = residual[1 := str_term(name)] ~O query(name)

for every name in the catalog plus the negative, on graph.lo /
native exe / graph.cd, agreeing with the direct dict walk. The
residual must keep `v1` free — a residual with no dynamic input left
would mean the specializer evaluated instead of specializing (that
degeneracy is gated, not assumed away).

This is the first specialization step on the real spec object — the
shape that "specialize → regenerate emit(R)" needs, demonstrated on
the catalog's own interpreter before any emit machinery exists at
term level.

## Honest measurements (the interesting part)

- Residual TREE: ~460k nodes — bigger than the spec's ~24k dag.
  `MixStrategy` is subst-only; the NF unrolls every static
  Church-numeral fold over dynamic `v_name` (per-entry `eqStr`,
  n-iterated step bodies all inlined). This is the documented limit:
  without real BTA / loop residualization (the Futamura.lean
  1993-mix open item), specialization *unrolls* rather than
  residualizes.
- Residual-instance DAG after hash-consing: ~6.7k unique nodes
  (~spec size — the toolchains array dominates the catalog).
- Residual instances are consistently ~35–45% cheaper than direct on
  every witness (measured over all 14 queries): lo ~36k vs ~57k steps,
  native ~170k vs ~330k steps, cd ~8.4k vs ~12k rounds. The win is
  real: the top-level `specGet` and entry-dispatch machinery fired at
  specialize time; the payload array remains — as expected, since the
  lookup key is dynamic.

## Residual producer caveat

The residual is produced by graph.lo, not the tree mirror —
`reduce.py`'s step rebuilds spines per step and the shared-dag-as-tree
walk is infeasible at this size. Independence is kept downstream: a
graph-produced wrong residual disagrees under the native exe and the
dict walk (same argument the suite already uses for direct queries).

## Open / deferred

- G9 proper (term-level emit machinery → regenerate emit(R)) stays
  open; this wave proved the specialization cell on the real spec
  object, which was its precondition.
- `HDev_total` termination measure: documented in 021 — live-cone
  cardinality is the right shape; deferred per user direction (may be
  subsumed by a later interaction-net formulation rather than proved
  as-is).
- Lamping optimality: out of scope; if a net formulation lands it
  likely *replaces* the HDev_total problem with a cleaner per-round
  draining argument rather than solving the heap version.
