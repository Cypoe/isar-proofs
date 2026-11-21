# 020 — HeapDev: the non-linear shared-dag path is proved sound (2026-10)

Belief change: the shared-graph evaluator is no longer the unproven layer.
`GraphDev` modelled `Graph.cd` on an append-only node table — hash-consing
and `fwd` redirects were quotiented away by `dagUnfold`. `HeapDev.lean`
models them: heaps carry `{ns, fw}`, children are resolved through `repr`,
`dup` returns a *shared* node index, and parents observe results through
redirects. `HDev_sound` proves the output readback joins `cdBasis` of the
input readback — the non-linear path is observational-equivalence-sound, for
the live runtime and for compile-time evaluation (cogen runs the same `cd`).

## Host findings that shaped the model

- **Seal gap in `_cd_memo`**: the memo is keyed on the rep, but the *result*
  node gets no memo entry. A second parent reaching a shared node mid-round
  re-develops it — observed `((D K) K) K` where `cdIter` would leave a
  residual redex. Sound (still joins `cdBasis`) but not exactly `cdIter n`;
  the round counter is a bound, not an equality. One-line host fix:
  `mo[out] = out` (seal the result). Under sealing the memo is transparent,
  so `HDev` needs no memo semantics — `D` is just the set of sealed reps,
  threaded so later siblings see earlier results.
- **Interning hazard**: `mk_app` resolves children and interns on resolved
  shape, so it can return an *ancestor* — resolved-dag cycles are a real
  possibility. `HeapWf.acyc` (TransGen `RSub` irreflexivity) is a genuine
  invariant, and `RedirectOk` carries the splice guard `¬ RSub src dst`:
  redirecting `src ↦ dst` is only sound when `dst` is not already below
  `src` in the resolved dag.
- **`_fun_arg` resolves children** at every level, and `mk_app` returns
  `repr(got)` — always a rep. `isRedexNodeR` (the Bool-level check) and
  `isRedexNodeR_eq` (its correspondence with `isRedexHead` of the readback)
  record that the host's fall-through branch is the semantic generic case.

## What landed (commit afc91ae + predecessors)

`src/ISAR/HeapDev.lean` (~2500 lines, builds in ~7s):

- `resolveS` — representative resolution with `Finset`-seen termination
  (no fuel bookkeeping), `resolveS_spec`/`resolveS_set` (redirect retargets
  chains ending at `src` to `dst`), `resolveS_extend` (allocation-stable).
- `RChild`/`RSub`/`Acyc`/`RSubSet` — the resolved-dag child relation and
  strict-descendant measure.
- `heapUnfold` — readback through forwards by well-founded recursion on
  the descendant-set cardinality (fold-based `dagUnfold` cannot read
  through `fwd`, which points forward in allocation order).
- `heapUnfold_redirect` — a redirect's readback effect is exactly the
  term-level `Splice` of `unfold dst` over `unfold src` subtrees.
- `heapUnfold_redirect_below` — below-`dst` readback is untouched; needs
  the `Occ`/`SOcc`/`tsize` argument (a descendant resolving to `dst` would
  make `unfold dst` a strict subterm of itself).
- `Join` — common-reduct observational equivalence + algebra (refl/symm/
  trans, app congruence, `cdJoin`, `Splice_join`).
- `HLe` — heap-extension order (push/redirect preserve it via
  `Splice_join`).
- `MkApp` — allocate-or-intern disjunction; `MkApp_join`/`MkApp_out`/
  `MkApp_wf`/`MkApp_hle`.
- `HDev` — one constructor per host `cd` clause, memo `D` threaded.
  `app_dev`'s guard is the semantic `isRedexHead` on the resolved left
  child's readback.
- `HDev_wf` (heaps grow, output in range), `HDev_sound`:
  `Join (heapUnfold h' o) (cdBasis (heapUnfold h i))` with the `HLe`
  extension recorded.

## What this does NOT claim

- **Totality**: `HDev_sound` is relational soundness — every derivation is
  right, but existence of a derivation for every in-range node is not yet
  proved (needs a termination measure on the development — same shape as
  `DevRel_total`'s index recursion, plus the memo invariant).
- **Round parity**: `HDevChain` (n rounds ↔ `cdIter n`) is not built;
  per the seal finding it also pins down which host semantics it would
  prove (sealed-memo = exact `cdIter`; unsealed = bounded over-development).
- **Lamping optimality**: shared-work bookkeeping/oracle minimality remain
  out of scope (decision 005/019 boundary).
- `D` is not constrained to *actually* contain sealed results — the model
  permits `hit` on any rep in `D`; soundness doesn't depend on it, totality
  will.

## Tactic-level gotchas worth keeping

- `·` is both the case-bullet and `ITerm.app` infix in this codebase —
  any term-ending tactic (`refine`/`exact`/`by_cases`/`change`) followed
  by a `·` bullet parses as `term · tac`. Use `next`/`case` after
  term-tactics.
- `rw`'s trailing auto-`rfl` is reducible-only — `cdBasis` on redex shapes
  needs an explicit `rfl` (or `show`) after the rewrite.
- `cases h : e` abstracts `e` but nested match scrutinees bound by *arm
  patterns* are not the same `e` — iota the parent match (`simp only []`
  or `split`) before casing the inner scrutinee.
- `rename_i` works for implicit ctor args after `induction` (with-pattern
  binds explicit args only).
