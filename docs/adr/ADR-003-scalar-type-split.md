# ADR-003: Scalar Type Split — ℝ for Algebra, `axiom` for Analysis

**Status**: Accepted
**Date**: 2026-06-19
**File**: `src/ISAR/ISARApproximation.lean`

---

## Context

`ISARApproximation.lean` must prove two things:

1. **Algebraic**: The ISAR update matrix family inherits nilpotency from `ISARMatrices.lean`.
2. **Topological / Statistical**: The continuous limit of the state space has universal representation (every continuous function is represented by a unique address in the continuous morphism space).

The algebraic claim is constructive and finite. The topological representation claim requires continuous analysis and category-theoretic limits (ℝ, infinite parameter sequences, topological terminality) declared as `axiom` to cite the mathematical correspondence.

---

## Decision

### Scalar type for the matrix algebra: `Real` (ℝ) via Mathlib

```lean
abbrev RMat := Matrix (Fin 4) (Fin 4) ℝ
```

**`Float` rejected**: opaque to Lean's kernel; all Float arithmetic requires `sorry` or
`native_decide` (oracle). Rejected on correctness grounds.

**`Bool` rejected**: Boolean scalars give 𝔽₂ (characteristic 2). Nilpotency over 𝔽₂ is
vacuous. The UAT requires characteristic 0. Rejected on mathematical-content grounds.

**`Rat` (ℚ) bypassed**: Originally proposed to avoid Mathlib dependency in `ISARApproximation.lean`. However, because ℚ is totally disconnected, this created a ℚ→ℝ density gap for the representation/approximation theorems.

**`Real` (ℝ) accepted**: By using Mathlib's `Matrix (Fin 4) (Fin 4) ℝ`, we fully type the algebraic maps and the representation space over ℝ, closing the density gap. The algebraic proofs (e.g. `toRMat_mul`, `K1R_nilpotent`) remain entirely `sorry`-free, closed via `fin_cases`, `push_cast`, and `ring`.

### Representation content: `axiom`

The universal representation theorem is the topological counterpart to the discrete `morphism_uniqueness` terminality theorem. Rather than approximating a target function $f$ up to $\varepsilon$ using external grid scaffolding, $f$ is represented exactly as a trajectory (address) in the continuous morphism space. These components are declared as `axiom`.

---

## Resolution of the ℚ vs ℝ Gap

By transitioning fully to `ℝ`, the parameters of `ISARUpdateR` are real numbers `α ∈ ℝ⁴`. This allows the algebraic space to directly sit in the topological field over which the continuous representation space is defined.

---

## Axiom Inventory

By formalizing the quotient structure and continuous activations, the axiom inventory has been minimized to only two analytical axioms:

| Axiom / Definition | Role | Why axiomatic / defined |
|---|---|---|
| `Activation` | Nonlinear activation σ | **Definitional**: Concrete type `C(ℝ, ℝ)`. |
| `Activation.nonPolynomial` | σ is non-polynomial | **Definitional**: Concrete predicate defined using Horner's method. |
| `RawAddress` | Configuration space | **Definitional**: Concrete type representing $(N, T, \theta, encode, readout)$ configurations. |
| `KernelAddress` | Address space | **Definitional**: Concrete quotient of `RawAddress` modulo functional equivalence. |
| `continuousRealization` | Address realization map | **Definitional**: Lifted composition map on the quotient. |
| `activatedUpdate` | T-step update map | **Axiomatic**: Requires the continuous-limit block dynamics. |
| `ISAR_UAT` | Universal approximation | **Axiomatic**: Standard Cybenko/Hornik approximation theorem on compact domains. |

**No algebraic theorems use `sorry` or `axiom`.**

---

## Consequences

- The algebraic representation is fully unified with the topological representation space over `ℝ`.
- The UAT is replaced by an exact representation theorem (`ISAR_representation`), mirroring the category-theoretic terminality (`morphism_uniqueness`) in the continuous limit.
- The axiom inventory is significantly simplified, removing all grid-scaffolding axioms (`GridState`, `ISARGridUpdate`, `gridEncode`, `gridReadout`, etc.).
- `Mathlib.Tactic` is imported for `fin_cases`, `push_cast`, `ring`. It does NOT
  introduce `sorry` or other non-constructive axioms into the algebraic proofs.
