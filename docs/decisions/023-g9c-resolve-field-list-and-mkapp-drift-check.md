# 023 — G9c resolveOf as a field list; mk_app interned-hit drift check

Status: implemented (pending suite green).

## What landed

**`host/spec_term.py`** — `resolveOf` (emit stage 1, `toolchain.resolve`)
as a basis term:

```
\spec. \name. (specGet spec "toolchains" …) I (\arr.
  (NARR _STEP_R pack0) sel I I)
```

`_STEP_R` folds the toolchains array with eqStr on `"name"`; on match it
evaluates `_resstr` — eight continuation-passing field lookups
(`entry[fk] → cn`, `spec[sk] → sect`, `sect[cn] → rec`, `rec[rk] → v`),
each yielding `v` or `"!"` (the NotRealized shadow), consed into a Scott
list `[d_mod, d_rec, i_mod, i_rec, r_mod, r_rec, t_mod, t_rec]`.

Observable is the **raw field list** — `decode_resolve` destructures the
NF by probes (`cell I K → head`, `cell I (K I) → tail`; nibble selector
applied to 16 VAR markers → `v_k`) via a minimal L0 tree stepper used
only for decoding.

**`host/graph_runtime.py`** — the latent cycle-fabrication bug found
while chasing this: `mk_app` interned hits returned nodes whose raw
children had redirected since interning, so the hit's *effective* term
was not the requested `app(l,r)` and could reach a live spine node —
`redirect` then linked the redex into a term containing it (HeapDev's
`Acyc` violated in the host).  Fix is O(1): a hit is honoured only if
`repr(left[got]) == left and repr(right[got]) == right` and `got` is not
pending; otherwise a fresh node is allocated (and the stale intern entry
updated).  `redirect` keeps a `_freeze` fallback for a directly-pending
dst.  Soundness argument: pending nodes are strictly ancestors of the
focus; every `mk_app` argument is a descendant or a prior result, so
results are pending-free by induction and the verified hit is the only
channel that needed a guard.

## What was rejected along the way

- **Flat-string resolve via `APPEND`/`REVONTO`** (bounded Church-fold
  string concatenation): the L0-lowered term diverges whenever the fold
  bound exceeds the list length by ~5+ — the nil-case pack fixpoint is
  only benign when the list argument is already a value, and nested lazy
  applications make the excess iterations feed a self-rebuilding
  residual (faithful L0 tree evaluator confirms it is the term, not the
  dag).  The field list is the honest observable anyway; the host
  flattens at the boundary.
- **`_cov` closure tracking** (refcounted ancestor-closure of pending
  nodes over raw-parents + reverse-repr maps): correct but O(arena) —
  the closure flooded to ~5.3M marks on a 52k-node term and
  `_unshare_pending` was called ~10k×/step.  Replaced by the drift
  check, which prevents pending from entering results at all.
- **Non-interning during pending regimes**: kills intra-step sharing —
  the dag explodes (~1M allocs in 5k steps).  Interning is
  load-bearing.

## Measurement

mini-catalog resolve: ~277k lo steps, exact match.  Full catalog:
~720k steps / ~24M allocs / ~90s per query on graph.lo; negative
(miss) ~200k steps → `None`.  Field strings decode identically on
graph.lo and (via the probe decoder) on native/cd exports.
