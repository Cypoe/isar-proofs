# 019 — Dag executor formalized: basis-level cd + DevRel/DevChain (2026-09-2x)

Belief change: the fastest evaluator stopped being the least-proven.

## What was true before

- `Kernel.lean`'s complete-development machinery (`ParStep`, `cd`, diamond,
  `ParN`, `cd_loop`, `nf_of_term`) was **surface-level**: `IStep` has
  `konst_macro` + `sβ`; `dup`/`swap` are inert there.
- The hosts (graph.lo/cd, all three native routine modules, both ABIs) execute
  **basis** semantics: `IStepCore ∪ IStepKMacro` — norm/konst/comp/dup/swap,
  `sₛ` expanded away at import.
- So every `rounds=` counter the executors report had *no formal counterpart* —
  agreement was observational only.

## What landed (commit 0967be6)

`src/ISAR/BasisDev.lean` — `ParStepBasis` (parallel step over the basis rules),
`cdBasis` (complete development mirroring the host's clauses), both embeddings
(`IStepBasis ↔ ParStepBasis`, `ParStepBasis → IRedBasis`), `cdBasis_ired`,
Takahashi triangle, diamond, **`IRedBasis_confluence`**.

`src/ISAR/GraphDev.lean` — relational spec of the host `Graph.cd` pass:

- `DagWf` (children-before-parents) + fold-based `dagTerms`/`dagUnfold`
  readback over raw `List GNode` with `getD` lookup — deliberately no `Fin`
  proofs embedded (early `▸` rewrite-motive failures made that the right call).
- `DevRel`: one constructor per host clause (atom/var/norm/konst/dup/comp/
  swap/app_dev). `DevRel_extends` (append-only), `DevRel_sound` (developments
  unfold to `cdBasis` of the input — determinism is a corollary),
  `DevRel_total` (strong recursion on node index; the dag is universal in the
  motive because the host re-develops children in the *grown* table).
- `isRedexNode`/`isRedexHead` Bool transfer keeps the structural `app_dev`
  case honest (a node the host doesn't recognize as a redex unfolds to a term
  whose head isn't a basis redex → `cdBasis`'s generic clause).
- `DevChain`/`DevChain_unfold`/`DevChain_ired`: n host cd rounds unfold to
  `cdIter n` and stay inside `IRedBasis` — round-iteration parity for the
  executor counter.

## What this does NOT claim

- `fwd` redirects / hash-consing are representational in the model — the
  readback quotients them. A mutable-dag correctness proof would need a
  heap-level refinement layer.
- No interaction-net optimality claims (no Lévy/Lamping bookkeeping) and no
  Lafont δ/ε/γ net rules — decision 005 already drew that boundary: the
  IN-like runtime is congruent *use* of IStep/ParStep/cd, not the kernel.

  Correction (2026-10): an earlier draft of this note called a real i-net
  formalization "research-scale" — too broad. Substantial groundwork exists:
  `LinearIKTerm`/`dupCount`/`cd_size_le_LinearIK`/`cd_size_lt_LinearIK`/
  `LinearIKTerm_cd` (InvariantLayer.lean:386-630) formalize the linear
  fragment where sharing degenerates; `sufficient_fuel t := term_size t`
  (InvariantLayer.lean:825) is a *proved* termination bound on it and
  `ComputableISAR_Kernel_Optimal` (KernelCategory.lean:63) packages it —
  the optimality result for the fragment where no dupβ fires. The Turner
  dialect (decision 004) emits dup/swap atoms via W/C bracket abstraction,
  so the net-primitive vocabulary is already an encoding target. What is
  genuinely unformalized is the *non-linear* fragment: heap-level sharing
  invariance once dupβ copies node references — a bounded extension of this
  file's DevRel (model fwd/memo as a quotient), not a fresh research program,
  as long as Lamping-optimality stays out of scope.

## Consequence for G9

The blocker on full-spec cd was always executor cost (per-round memo cleared,
superlinear). The dag semantics is now proved, so a persistent-memo or
shared-graph cd variant is a *verifiable strategy change* — any change to the
round loop can be re-proved against `DevRel`/`DevChain`, not just re-observed.
