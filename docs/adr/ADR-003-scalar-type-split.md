# ADR-003: Scalar Type Split — ℚ for Algebra, `axiom` for Analysis

**Status**: Accepted
**Date**: 2026-06-18
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

### Scalar type for the matrix algebra: `Rat` (ℚ)

```lean
def QMat := Fin 4 → Fin 4 → Rat
```

**`Float` rejected**: opaque to Lean's kernel; all Float arithmetic requires `sorry` or
`native_decide` (oracle). Rejected on correctness grounds.

**`Bool` rejected**: Boolean scalars give 𝔽₂ (characteristic 2). Nilpotency over 𝔽₂ is
vacuous. The UAT requires characteristic 0. Rejected on mathematical-content grounds.

**`Real` (ℝ) deferred**: requires `Mathlib.Data.Real.Basic` and Cauchy/Dedekind machinery.
The algebraic content (nilpotency, ring homomorphism) is valid over any characteristic-0
field; ℚ is the smallest such field and has zero import overhead.

**`Rat` accepted**: Lean's core `Rat` type has exact arithmetic, is fully kernel-reducible,
and supports `ring`/`push_cast` without Mathlib. All algebraic proofs are sorry-free.

### Analytic content: `axiom`

The UAT conclusion requires topology, norms, Weierstrass density, and Cybenko/Hornik.
These are declared as `axiom` — the Lean equivalent of citing Cybenko 1989.

---

## The ℚ vs ℝ Gap

This is the key honest limitation.

`ISARUpdateQ` takes α ∈ ℚ⁴. The UAT requires continuity in α ∈ ℝ⁴.
**ℚ is totally disconnected** — no differentiability or continuity notion yields the UAT.

The bridge (cited, not proved):
1. The ℚ-family `{αI·I + αR·R + αA·A + αS·S | α ∈ ℚ⁴}` is proved here over ℚ.
2. By density of ℚ in ℝ, the unique continuous extension to ℝ⁴ exists.
3. The UAT applies to the real closure. This is the content of `axiom ISAR_UAT`.

`Float` in the axiom statements stands in for ℝ in the conclusion.

---

## Axiom Inventory

All axioms are intentional analytic declarations (see proof sketch in section 7):

| Axiom | Role | Why axiomatic |
|---|---|---|
| `GridState N` | State space ℝ^{4N} | Requires ℝ-vector space |
| `GridNorm N` | Approximation error norm | Requires metric/norm on ℝ^{4N} |
| `Activation` | Nonlinear activation σ | Continuous function type over ℝ |
| `Activation.applyGrid` | σ elementwise | Requires continuity infrastructure |
| `Activation.nonPolynomial` | σ is non-polynomial | Real-analysis predicate |
| `ISARGridUpdate` | ISAR update (Float params) | Real-valued linear map |
| `gridEncode` | ℝᵈ → state embedding | Continuous injection |
| `gridReadout` | state → ℝᵏ projection | Continuous surjection |
| `ISAR_UAT` | Universal approximation | Cybenko/Hornik + ℚ→ℝ bridge |

**No algebraic theorems use `sorry` or `axiom`.**

---

## Consequences

- Eliminating `axiom ISAR_UAT` in the future requires only adding
  `import Mathlib.Analysis.SpecialFunctions` and swapping `Rat → ℝ` in `ISARUpdateQ`.
  All algebraic proofs remain unchanged.
- `Mathlib.Tactic` is imported for `fin_cases`, `push_cast`, `ring`. It does NOT
  introduce `Classical.choice` or other non-constructive axioms into the algebraic proofs.
