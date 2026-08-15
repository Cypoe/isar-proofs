# ADR-003: Scalar Type Split — ℝ for Algebra, `axiom` for Analysis

**Status**: Accepted
**Date**: 2026-06-19
**File**: `src/ISAR/ISARApproximation.lean`

---

## Context

`ISARApproximation.lean` splits two kinds of claim:

1. **Algebraic**: The ISAR update matrix family inherits nilpotency from `ISARMatrices.lean`.
2. **Topological / Statistical**: Approximation and unique addresses in a completion of `KernelAddress` are **named axioms** (`ISAR_UAT`, `KernelAddressLimit`, …), not theorems. `KernelAddress` has no metric.

The algebraic claim is constructive and finite. The analytic/completion claims stay `axiom`.

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

`ISAR_UAT` is a named Leshno-style approximation axiom (compact `K`, ε-close, **not proved**). Unique exact addresses live on the named type `KernelAddressLimit` via `topological_extension_bijection` — also not constructed. These do **not** replace approximation by an exact theorem; both layers stay axiomatic. `ISAR_representation` is a theorem only relative to those axioms.

---

## Resolution of the ℚ vs ℝ Gap

By transitioning fully to `ℝ`, the parameters of `ISARUpdateR` are real numbers `α ∈ ℝ⁴`. This allows the algebraic space to directly sit in the topological field over which the continuous representation space is defined.

---

## Axiom Inventory

Six named analytic/completion axioms remain (not three). Definitions in the table are constructed; the last rows are axioms:

| Axiom / Definition | Role | Why axiomatic / defined |
|---|---|---|
| `Activation` | Nonlinear activation σ | **Definitional**: Concrete type `C(ℝ, ℝ)`. |
| `Activation.nonPolynomial` | σ is non-polynomial | **Definitional**: Concrete predicate defined using Horner's method. |
| `RawAddress` | Configuration space | **Definitional**: Concrete type representing $(N, T, \theta, encode, readout)$ configurations. |
| `KernelAddress` | Address space | **Definitional**: Concrete quotient of `RawAddress` modulo functional equivalence. |
| `continuousRealization` | Address realization map | **Definitional**: Lifted composition map on the quotient. |
| `activatedUpdate` | T-step update map | **Definitional**: Concrete recursive composition map. |
| `ISAR_UAT` | Universal approximation | **Axiomatic**: Named Leshno-style (non-polynomial σ) density on compact domains. **Not a theorem.** Cybenko/Hornik boundedness is not the statement. |
| `KernelAddressLimit` | Named completion type | **Axiomatic**: `KernelAddress` has no metric; this is **not** `Metric.Completion`. |
| `continuousRealizationLimit` | Named realization on the limit | **Axiomatic**: not a Mathlib extension. |
| `kernelAddressEmbedding` | Named embedding into the limit | **Axiomatic**: not a completion inclusion. |
| `continuousRealizationLimit_coe` | Named commuting law | **Axiomatic**. |
| `topological_extension_bijection` | Named extension axiom | **Axiomatic**: would follow from a metric + density; neither is constructed. |

**No algebraic theorems use `sorry` or `axiom`.**

---

## Consequences

- The algebraic representation is fully unified with the topological representation space over `ℝ`.
- `ISAR_representation` is a theorem **relative to** named axioms `ISAR_UAT` and `topological_extension_bijection`. It does not prove UAT or construct a metric completion.
- The axiom inventory is significantly simplified, removing all grid-scaffolding axioms (`GridState`, `ISARGridUpdate`, `gridEncode`, `gridReadout`, etc.).
- **Topological Completion Roadmap (frozen 2026-08-14):** the blocker is the missing metric/uniform structure on `KernelAddress` (`C(ℝᵈ, ℝᵏ)` is compact-open, not a global supremum metric), not Mathlib API stability. Next wiring is `Metric.Completion` / `UniformSpace.Completion` only, after a metric exists. `ISAR_UAT` stays named.
- `Mathlib.Tactic` is imported for `fin_cases`, `push_cast`, `ring`. It does NOT
  introduce `sorry` or other non-constructive axioms into the algebraic proofs.
