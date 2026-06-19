# ADR-003: Scalar Type Split — ℝ for Algebra, `axiom` for Analysis

**Status**: Accepted
**Date**: 2026-06-19
**File**: `src/ISAR/ISARApproximation.lean`

---

## Context

`ISARApproximation.lean` must prove two things:

1. **Algebraic**: The ISAR update matrix family inherits nilpotency from `ISARMatrices.lean`.
2. **Statistical**: The iterated ISAR update can approximate any continuous function on a
   compact domain (Universal Approximation Theorem, UAT).

The algebraic claim is constructive and finite. The statistical claim requires real analysis
(ℝ, compactness, Weierstrass density) unavailable without Mathlib's analysis library.

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

**`Rat` (ℚ) bypassed**: Originally proposed to avoid Mathlib dependency in `ISARApproximation.lean`. However, because ℚ is totally disconnected, this created a ℚ→ℝ density gap for the UAT (which requires differentiability and continuity on ℝ).

**`Real` (ℝ) accepted**: By using Mathlib's `Matrix (Fin 4) (Fin 4) ℝ`, we fully type the algebraic maps and the UAT over ℝ, closing the density gap. The algebraic proofs (e.g. `toRMat_mul`, `K1R_nilpotent`) remain entirely `sorry`-free, closed via `fin_cases`, `push_cast`, and `ring`.

### Analytic content: `axiom`

The UAT conclusion requires topology, norms, Weierstrass density, and Cybenko/Hornik.
These are declared as `axiom` — the Lean equivalent of citing Cybenko 1989.

---

## Resolution of the ℚ vs ℝ Gap

By transitioning fully to `ℝ`, the parameters of `ISARUpdateR` are real numbers `α ∈ ℝ⁴`.
This allows the state space and update parameters to reside in the same topological field, satisfying the continuity conditions of the UAT without a density bridge.

---

## Axiom Inventory

All axioms are intentional analytic declarations (see proof sketch in section 7):

| Axiom / Definition | Role | Why axiomatic / defined |
|---|---|---|
| `GridState N` | State space ℝ^{4N} | **Definitional**: Concrete Mathlib type `EuclideanSpace ℝ (Fin (4 * N))` (not an axiom). |
| Norm on `GridState N` | Approximation error norm | **Definitional**: Comes free from `NormedAddCommGroup` (not an axiom). |
| `Activation` | Nonlinear activation σ | Continuous function type over ℝ |
| `Activation.applyGrid` | σ elementwise | Requires continuity infrastructure |
| `Activation.nonPolynomial` | σ is non-polynomial | Real-analysis predicate |
| `ISARGridUpdate` | ISAR update (ℝ params) | Real-valued linear map |
| `gridEncode` | ℝᵈ → state embedding | Continuous injection |
| `gridReadout` | state → ℝᵏ projection | Continuous surjection |
| `ISAR_UAT` | Universal approximation | Cybenko/Hornik |

**No algebraic theorems use `sorry` or `axiom`.**

---

## Consequences

- The algebraic representation is fully unified with the analytic representation over `ℝ`.
- `GridState` and the norm on it are fully concrete Mathlib objects.
- `Mathlib.Tactic` is imported for `fin_cases`, `push_cast`, `ring`. It does NOT
  introduce `sorry` or other non-constructive axioms into the algebraic proofs.
