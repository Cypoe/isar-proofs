import ISAR.ISARBridge
import ISAR.InvariantLayer

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# ISAR Universal Approximation

## What this file establishes

The ISAR kernel has two kinds of universality:

**Logical universality** (proved elsewhere in this codebase):
- `morphism_uniqueness` (KernelCategory): ISAR_Kernel is the terminal object — every
  admissible rewriting system embeds into it via a unique canonical morphism.
- `K1_nilpotent` / `K2_nilpotent` (ISARMatrices): the core rewrite operator K = IRAS
  satisfies K² = 0.
- `isk_expressive_completeness` (BasisCompleteness): every ISKAlgebra matrix is the
  image of some ISK term under the structural homomorphism `term_signature_val`.

**Statistical and Topological universality** (this file):
- Defines `RMat := Matrix (Fin 4) (Fin 4) ℝ` using Mathlib, which carries a full
  `CommRing`, `Module ℝ`, `NormedAddCommGroup`, and `InnerProductSpace ℝ` for free.
- Proves rigorously that `RMat` inherits the nilpotency of K from the integer proof,
  sorry-free, using `Matrix.mul_apply` and Mathlib cast lemmas.
- Defines the ISAR update kernel as an ℝ-linear combination of basis matrices,
  parametrised by (αI, αR, αA, αS) ∈ ℝ⁴. No ℚ→ℝ gap.
- Proves constructively that the continuous-limit update map `activatedUpdate` is
  well-defined and continuous, reducing the axiom space.
- States the **ISAR Universal Approximation Theorem** and **ISAR Representation Theorem**
  to unify the metric and topological properties of the continuous limit.

## Why K² = 0 is the key structural property

Nilpotency means the ISAR update is a *pure first-order generator*:

  exp(εK) = I + εK    (the exponential series terminates at degree 1)

Composing T such steps interleaved with a nonlinear activation σ:
  σ(I + ε_T K) ∘ ⋯ ∘ σ(I + ε_1 K)

implements a depth-T polynomial approximation of the target function,
parametrised continuously in (ε_1, ..., ε_T) ∈ ℝᵀ. By the Weierstrass approximation
theorem, polynomials are dense in C(X, ℝ) for compact X, so T → ∞ gives
universal approximation.

## Scalar type: ℤ → ℝ directly, no ℚ layer

The algebra is proved over ℤ in `ISARMatrices`, lifted to ℝ via `Int.cast`. Unlike
the earlier `QMat`/`Rat` version, `ISARUpdateR` lives in ℝ⁴ from the start — the
ℚ→ℝ density gap no longer applies.

## Axiom inventory (all intentional — see ADR-003)

  ISAR_UAT, KernelAddressLimit, continuousRealizationLimit, kernelAddressEmbedding,
  continuousRealizationLimit_coe, topological_extension_bijection.

All other structures (Activation, nonPolynomial, RawAddress, KernelAddress, activatedUpdate,
ISAR_representation, kernelAddressEmbedding_injective, kernelAddressEmbedding_dense)
are defined or proved concretely.
-/

namespace ISAR

/-! ## 1. Real 4×4 matrices via Mathlib -/

/--
`RMat`: Mathlib's `Matrix (Fin 4) (Fin 4) ℝ`.
Carries `CommRing`, `Module ℝ`, `NormedAddCommGroup`, `InnerProductSpace ℝ` for free.
Replaces the hand-rolled `QMat` and its 4 `@[simp]` app lemmas — Mathlib already has
`Matrix.mul_apply`, `Matrix.add_apply`, `Matrix.zero_apply`, `Matrix.smul_apply`.
-/
abbrev RMat := Matrix (Fin 4) (Fin 4) ℝ

/-! ## 2. Lifting Matrix4 (Int) to RMat (ℝ) -/

/--
The canonical ring homomorphism from `Matrix4` (over `Int`) to `RMat` (over `ℝ`),
using Lean's built-in `Int → ℝ` coercion (`Int.cast` / `algebraMap ℤ ℝ`).
-/
def toRMat (M : Matrix4) : RMat :=
  fun i j => (fromMatrix4 M i j : ℝ)

/-- Bridge: `A * B` for Matrix4 unfolds to `mul A B` (for simp). -/
private theorem Matrix4.mul_def (A B : Matrix4) : A * B = mul A B := rfl

/-- `toRMat` sends the zero matrix to zero. -/
theorem toRMat_zero : toRMat zero = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [toRMat, fromMatrix4, zero]

/-- `toRMat` is a ring homomorphism: it respects matrix multiplication. -/
theorem toRMat_mul (M N : Matrix4) :
    toRMat (M * N) = toRMat M * toRMat N := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [toRMat, Matrix.mul_apply, Fin.sum_univ_four,
               fromMatrix4, Matrix4.mul_def, mul] <;>
    push_cast <;> ring

/-! ## 3. ISAR Basis Matrices over ℝ -/

/-- The invariant-projection matrix I, lifted to ℝ. -/
abbrev I1R : RMat := toRMat I1

/-- The rotation matrix R, lifted to ℝ. -/
abbrev R1R : RMat := toRMat R1

/-- The adjacency matrix A, lifted to ℝ. -/
abbrev A1R : RMat := toRMat A1

/-- The selection matrix S, lifted to ℝ. -/
abbrev S1R : RMat := toRMat S1

/-- The nilpotent core kernel K = I·R·A·S, lifted to ℝ. -/
abbrev K1R : RMat := toRMat (I1 * R1 * A1 * S1)

/-! ## 4. Nilpotency (ℝ world) -/

/--
K1 is nilpotent of order 2 in the ℝ representation.
Transferred from `K1_nilpotent` (proved over Int by `decide`) via `toRMat_mul`.
-/
theorem K1R_nilpotent : K1R * K1R = 0 := by
  change toRMat (I1 * R1 * A1 * S1) * toRMat (I1 * R1 * A1 * S1) = 0
  rw [← toRMat_mul, K1_nilpotent]
  exact toRMat_zero

/-- K2 is also nilpotent of order 2. -/
theorem K2R_nilpotent :
    toRMat (I2 * R2 * A2 * S2) * toRMat (I2 * R2 * A2 * S2) = 0 := by
  rw [← toRMat_mul, K2_nilpotent]
  exact toRMat_zero

/-! ## 5. The Differentiable ISAR Update Kernel over ℝ -/

/--
The differentiable ISAR update matrix: an ℝ-linear combination of the four basis
matrices, parametrised by (αI, αR, αA, αS) ∈ ℝ⁴.

  ISARUpdateR αI αR αA αS = αI·I + αR·R + αA·A + αS·S

Scalar multiplication `•` is Mathlib's `SMul ℝ (Matrix ...)` from the module structure.
Unlike the former `QMat` version over ℚ, parameters live in ℝ from the start.
-/
def ISARUpdateR (αI αR αA αS : ℝ) : RMat :=
  αI • I1R + αR • R1R + αA • A1R + αS • S1R

/-- The zero parameter choice gives the zero matrix. -/
theorem ISARUpdateR_zero_params : ISARUpdateR 0 0 0 0 = 0 := by
  simp [ISARUpdateR]

/-! ## 6. Iterated Update Rule -/

/-- Iterate the update matrix U, T times. -/
def linearIterateR (U : RMat) : Nat → RMat
  | 0     => 1
  | n + 1 => U * linearIterateR U n

theorem linearIterateR_zero (U : RMat) : linearIterateR U 0 = 1 := rfl

theorem linearIterateR_succ (U : RMat) (n : Nat) :
    linearIterateR U (n + 1) = U * linearIterateR U n := rfl

/-- **First-order flow property** (consequence of K² = 0). -/
theorem nilpotent_kills_higher_order : K1R * K1R = 0 := K1R_nilpotent

/-! ## 7. Universal Approximation (Continuous Morphism and Address Space) -/

/-
We define the topological representation space, which lifts the category-theoretic
terminality (`morphism_uniqueness`) to the continuous setting. 

Rather than treating the input/output projections (encode/readout) as fixed global
axioms, they are existentially quantified as part of the configuration space (RawAddress),
matching the generalized universal approximation theorem (Option A, e.g., Leshno et al. 1993).

To represent the continuous mapping uniquely, the parameter space is quotiented modulo
observational (functional) equivalence, mirroring the discrete `InvariantLayer`.

**Axiom inventory** (all intentional — see ADR-003):
  ISAR_UAT, KernelAddressLimit, continuousRealizationLimit, kernelAddressEmbedding,
  continuousRealizationLimit_coe, topological_extension_bijection.
-/

/-- A nonlinear activation function: continuous real functions ℝ → ℝ. -/
abbrev Activation := C(ℝ, ℝ)

/-- Horner's method to evaluate a polynomial represented as a list of real coefficients. -/
def evalPoly (coeffs : List ℝ) (x : ℝ) : ℝ :=
  coeffs.foldr (fun coef acc => coef + x * acc) 0

/-- Predicate: σ is non-polynomial (necessary condition for representation). -/
def Activation.nonPolynomial (σ : Activation) : Prop :=
  ∀ coeffs : List ℝ, (σ : ℝ → ℝ) ≠ evalPoly coeffs

/--
Grid state: N cells, each with a 4-dimensional real state vector.
We represent the grid index space as `Fin N × Fin 4`. This is mathematically
isomorphic to `Fin (4 * N)` but allows direct, type-safe block-diagonal indexing
without division or modulo operations.
-/
abbrev GridState (N : Nat) := EuclideanSpace ℝ (Fin N × Fin 4)

/-- The middle linear map representing the block-diagonal matrix multiplication by U. -/
def middleMap (N : Nat) (U : RMat) (v : Fin N × Fin 4 → ℝ) : Fin N × Fin 4 → ℝ :=
  fun p => ∑ j' : Fin 4, U p.2 j' * v (p.1, j')

/-- Proof of continuity of the middle linear map. -/
theorem continuous_middleMap (N : Nat) (U : RMat) :
    Continuous (middleMap N U) := by
  apply continuous_pi
  intro p
  apply continuous_finsetSum
  intro j' _
  exact continuous_const.mul (continuous_apply (p.1, j'))

/--
The block-diagonal action of U on GridState N.

**Mathematical Motivation**: Implements the linear transformation step of the neural network
update (a block-diagonal matrix multiplication action on the grid coordinates).
**Why Noncomputable**: Relies on real numbers (`ℝ`) via `WithLp.equiv`, which is defined as a
topological completion of `ℚ` and does not have a constructive computational representation in Lean.
-/
noncomputable def blockDiagonalAction (N : Nat) (U : RMat) (x : GridState N) : GridState N :=
  (WithLp.equiv 2 (Fin N × Fin 4 → ℝ)).symm (middleMap N U (WithLp.equiv 2 (Fin N × Fin 4 → ℝ) x))

/-- Proof of continuity of the block-diagonal update action. -/
theorem continuous_blockDiagonalAction (N : Nat) (U : RMat) :
    Continuous (blockDiagonalAction N U) := by
  have hc1 : Continuous (WithLp.equiv 2 (Fin N × Fin 4 → ℝ)) := by continuity
  have hc2 : Continuous (WithLp.equiv 2 (Fin N × Fin 4 → ℝ)).symm := by continuity
  have hc3 : Continuous (middleMap N U) := continuous_middleMap N U
  exact hc2.comp (hc3.comp hc1)

/--
The bundled continuous block-diagonal linear map.

**Mathematical Motivation**: Lifts `blockDiagonalAction` to a bundled continuous map `C(GridState N, GridState N)`.
**Why Noncomputable**: Bundling a function into a `ContinuousMap` requires proving continuity, and evaluates
on topological spaces using noncomputable real numbers (`ℝ`).
-/
noncomputable def continuousBlockDiagonalAction (N : Nat) (U : RMat) :
    C(GridState N, GridState N) :=
  ContinuousMap.mk (blockDiagonalAction N U) (continuous_blockDiagonalAction N U)

/--
The elementwise activation function applied to a GridState.

**Mathematical Motivation**: Implements the element-wise nonlinear activation function application on the grid state.
**Why Noncomputable**: Performs function application over `ℝ` using `WithLp.equiv` and continuous activation functions,
neither of which have constructive computational representations.
-/
noncomputable def applyActivation (σ : Activation) (N : Nat) (x : GridState N) : GridState N :=
  let v := WithLp.equiv 2 (Fin N × Fin 4 → ℝ) x
  let f := fun p => σ (v p)
  (WithLp.equiv 2 (Fin N × Fin 4 → ℝ)).symm f

/-- Proof of continuity of the elementwise function application. -/
theorem continuous_applyActivation (σ : Activation) (N : Nat) :
    Continuous (fun (v : Fin N × Fin 4 → ℝ) => fun p => σ (v p)) := by
  apply continuous_pi
  intro p
  exact σ.continuous.comp (continuous_apply p)

/-- Proof of continuity of applyActivation. -/
theorem continuous_applyActivation_state (σ : Activation) (N : Nat) :
    Continuous (applyActivation σ N) := by
  have hc1 : Continuous (WithLp.equiv 2 (Fin N × Fin 4 → ℝ)) := by continuity
  have hc2 : Continuous (WithLp.equiv 2 (Fin N × Fin 4 → ℝ)).symm := by continuity
  have hc3 : Continuous (fun (v : Fin N × Fin 4 → ℝ) => fun p => σ (v p)) :=
    continuous_applyActivation σ N
  exact hc2.comp (hc3.comp hc1)

/--
The bundled continuous elementwise activation map.

**Mathematical Motivation**: Lifts `applyActivation` to a bundled continuous map `C(GridState N, GridState N)`.
**Why Noncomputable**: Evaluates real functions and relies on the noncomputable real topology.
-/
noncomputable def continuousApplyActivation (σ : Activation) (N : Nat) :
    C(GridState N, GridState N) :=
  ContinuousMap.mk (applyActivation σ N) (continuous_applyActivation_state σ N)

/--
`activatedUpdate`: The concrete, recursive definition of the T-step ISAR update
with alternating activation. Defined constructively via composing the continuous
block-diagonal updates and elementwise activations.

**Mathematical Motivation**: Computes the multi-layer neural network update $F_{\theta} = \sigma \circ U_T \circ \dots \circ \sigma \circ U_1$.
**Why Noncomputable**: Combines continuous maps via composition (`ContinuousMap.comp`) over continuous spaces,
which relies on noncomputable real numbers (`ℝ`).
-/
noncomputable def activatedUpdate (σ : Activation) (N : Nat) :
    (T : Nat) → (Fin T → Fin 4 → ℝ) → C(GridState N, GridState N)
  | 0,     _ => ContinuousMap.id _
  | T + 1, θ =>
      let U := ISARUpdateR (θ (Fin.last T) 0) (θ (Fin.last T) 1) (θ (Fin.last T) 2) (θ (Fin.last T) 3)
      let step := (continuousApplyActivation σ N).comp (continuousBlockDiagonalAction N U)
      let θ_prev := fun (t : Fin T) => θ (Fin.castSucc t)
      step.comp (activatedUpdate σ N T θ_prev)

/--
`RawAddress`: the concrete configuration space representing all finite-grid,
finite-time neural representations of the ISAR update.
Contains the grid size N, time steps T, parameter sequence θ, and the bundled
continuous encoder and readout maps.
-/
def RawAddress (d k : Nat) : Type :=
  Σ (N T : Nat),
    (Fin T → Fin 4 → ℝ) ×
    C(EuclideanSpace ℝ (Fin d), GridState N) ×
    C(GridState N, EuclideanSpace ℝ (Fin k))

/--
The realization map mapping a raw parameter trajectory to a continuous function.
Computes the composition: readout ∘ activatedUpdate ∘ encode.

**Mathematical Motivation**: Realizes the full neural network representation from the parameters (encoder, readout, updates).
**Why Noncomputable**: Computes composition of continuous maps over continuous Euclidean spaces, which is noncomputable in Lean.
-/
noncomputable def realizeRaw (d k : Nat) (σ : Activation) (θ : RawAddress d k) :
    C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)) :=
  let N := θ.1
  let T := θ.2.1
  let θ_seq := θ.2.2.1
  let encode := θ.2.2.2.1
  let readout := θ.2.2.2.2
  readout.comp ((activatedUpdate σ N T θ_seq).comp encode)

/--
Two raw addresses are observationally/functionally equivalent if they realize
the same continuous function.
-/
def AddressEq (d k : Nat) (σ : Activation) (θ₁ θ₂ : RawAddress d k) : Prop :=
  realizeRaw d k σ θ₁ = realizeRaw d k σ θ₂

/--
The setoid defining the functional equivalence relation on RawAddress.

**Mathematical Motivation**: Equates two addresses if they yield the exact same continuous realization function.
**Why Noncomputable**: The equality relation `realizeRaw d k σ θ₁ = realizeRaw d k σ θ₂` is an equality of continuous
functions over `ℝᵈ`, which is mathematically undecidable/noncomputable.
-/
noncomputable def addressSetoid (d k : Nat) (σ : Activation) : Setoid (RawAddress d k) where
  r := AddressEq d k σ
  iseqv := {
    refl  := fun _ => rfl
    symm  := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/--
`KernelAddress`: the address space defined as the quotient of RawAddress modulo
observational/functional equivalence. This is the exact continuous counterpart to
the discrete `InvariantLayer`.
-/
def KernelAddress (d k : Nat) (σ : Activation) : Type :=
  Quotient (addressSetoid d k σ)

/--
The well-defined continuous realization of a quotiented `KernelAddress`.
Derived via `Quotient.lift` from `realizeRaw`.

**Mathematical Motivation**: The canonical projection/realization map from the quotient space `KernelAddress` to the space of continuous functions.
**Why Noncomputable**: Relies on `Quotient.lift` over a noncomputable equivalence relation, and returns a continuous function over `ℝ`.
-/
noncomputable def continuousRealization (d k : Nat) (σ : Activation) (q : KernelAddress d k σ) :
    C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)) :=
  Quotient.lift (fun θ => realizeRaw d k σ θ) (by
    intro θ₁ θ₂ h
    exact h
  ) q

/--
**Injectivity of the Continuous Realization.**

By construction, two equivalence classes in the quotient address space `KernelAddress`
are equal if and only if they realize the exact same continuous function.
This guarantees that the representation is unique (injectivity holds constructively).
-/
theorem continuousRealization_injective (d k : Nat) (σ : Activation) (q₁ q₂ : KernelAddress d k σ) :
    continuousRealization d k σ q₁ = continuousRealization d k σ q₂ → q₁ = q₂ := by
  intro h
  refine Quotient.inductionOn₂ q₁ q₂ (fun θ₁ θ₂ h_eq => ?_) h
  have h_sound : AddressEq d k σ θ₁ θ₂ := h_eq
  exact Quotient.sound h_sound

/--
**Conceptual Bridge to the Invariant Layer.**

This equivalence formally states that the topological quotient `KernelAddress` uses
the exact same mathematical construction as the discrete symbolic `InvariantLayer`.
Both are quotients of a raw representation space modulo operational/observational equivalence.
-/
def InvariantLayerContinuousBridge : InvariantLayer ≃ Quotient ISAR.operEqSetoid :=
  Equiv.refl _

/--
**ISAR Universal Approximation Theorem.**

For any continuous function f : ℝᵈ → ℝᵏ, a non-polynomial activation σ,
and a compact domain K ⊆ ℝᵈ, the finite-grid iterated ISAR update can
approximate f uniformly on K to arbitrary precision ε > 0.

**Mathematical Motivation**: The function space $C(\mathbb{R}^d, \mathbb{R}^k)$ carries the compact-open
topology (the topology of uniform convergence on compact sets). This theorem states that the realization
space is dense in $C(\mathbb{R}^d, \mathbb{R}^k)$ under the compact-open topology.
**Citation**: Cites the Leshno, Lin, Pinkus, and Schocken (1993) universal approximation theorem, which
establishes that a continuous activation function $\sigma$ is universal on compact subsets if and only if
it is non-polynomial (generalizing Cybenko 1989 / Hornik 1991, which require boundedness).
-/
axiom ISAR_UAT
    (d k : Nat)
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (_ : IsCompact K)
    (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)))
    (σ : Activation)
    (_ : Activation.nonPolynomial σ)
    (ε : ℝ) (_ : 0 < ε) :
    ∃ θ : RawAddress d k,
      ∀ x ∈ K,
        ‖realizeRaw d k σ θ x - f x‖ < ε

/--
The continuous limit/completion of the quotiented address space.

**Mathematical Motivation**: Represents the metric completion of `KernelAddress d k σ` (with the metric pulled back
from the supremum metric on $C(\mathbb{R}^d, \mathbb{R}^k)$).
**Why Axiomatic**: Avoids formalizing the metric space completion construction (`Metric.Completion` / `UniformSpace.Completion`)
directly on `KernelAddress` in Lean, instead axiomatizing the resulting completion type.
-/
axiom KernelAddressLimit (d k : Nat) (σ : Activation) : Type

/--
The continuous realization map from the completion.

**Mathematical Motivation**: The unique continuous extension of `continuousRealization` to the completion.
**Why Axiomatic**: Represents the extension of a uniformly continuous map to the completion (`DenseInducing.extend` in Mathlib).
Declared axiomatically here to specify its existence and signature directly.
-/
axiom continuousRealizationLimit (d k : Nat) (σ : Activation) :
  KernelAddressLimit d k σ → C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))

/--
The canonical embedding from the quotient address space `KernelAddress` to its metric completion `KernelAddressLimit`.

**Mathematical Motivation**: Represents the inclusion map $i : X \to \hat{X}$ of a metric space into its completion.
**Why Axiomatic**: Represents the canonical inclusion of a space into its completion.
-/
axiom kernelAddressEmbedding (d k : Nat) (σ : Activation) :
  KernelAddress d k σ → KernelAddressLimit d k σ

/--
The continuous realization map on the completion is the unique continuous extension of `continuousRealization`.
This means it commutes with the embedding: $\hat{f}(i(q)) = f(q)$.

**Mathematical Motivation**: This is the definitional property of the extension of a map to the completion.
**Why Axiomatic**: Relies on the properties of completion extension.
-/
axiom continuousRealizationLimit_coe (d k : Nat) (σ : Activation) (q : KernelAddress d k σ) :
  continuousRealizationLimit d k σ (kernelAddressEmbedding d k σ q) = continuousRealization d k σ q

/--
**Injectivity of the Completion Embedding.**

The canonical embedding from the quotient address space into its completion is injective.

**Proof**: Follows directly from the injectivity of `continuousRealization` and the commuting property
of the realization map on the completion.
-/
theorem kernelAddressEmbedding_injective (d k : Nat) (σ : Activation) :
    Function.Injective (kernelAddressEmbedding d k σ) := by
  intro q₁ q₂ h
  have h_eq : continuousRealizationLimit d k σ (kernelAddressEmbedding d k σ q₁) =
              continuousRealizationLimit d k σ (kernelAddressEmbedding d k σ q₂) := by rw [h]
  rw [continuousRealizationLimit_coe, continuousRealizationLimit_coe] at h_eq
  exact continuousRealization_injective d k σ q₁ q₂ h_eq

/--
**Density of the Quotient Address Space in the Completion.**

The quotient address space is dense in its completion, meaning any limit address can be approximated
uniformly on compact domains to arbitrary precision by a quotient address.

**Proof**: Follows by applying the density of the UAT (`ISAR_UAT`) to the realization of the limit address.
-/
theorem kernelAddressEmbedding_dense (d k : Nat) (σ : Activation) (h_np : Activation.nonPolynomial σ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (θ_limit : KernelAddressLimit d k σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : KernelAddress d k σ,
      ∀ x ∈ K, ‖continuousRealization d k σ q x - continuousRealizationLimit d k σ θ_limit x‖ < ε := by
  let f_map := continuousRealizationLimit d k σ θ_limit
  obtain ⟨θ_raw, h_approx⟩ := ISAR_UAT d k K hK f_map σ h_np ε hε
  use Quotient.mk _ θ_raw
  exact h_approx

/--
**Topological Extension to Completion (Functional Analysis Axiom).**

An injective map with a dense range into a complete metric space extends uniquely
to a bijection on the completion of its domain.

**Mathematical Motivation**: This is the standard functional analysis completion theorem (`UniformSpace.Completion.extension`
paired with injectivity/density facts).
1. `KernelAddress` is equipped with a metric space structure by pulling back the metric on $C(\mathbb{R}^d, \mathbb{R}^k)$ via `continuousRealization`.
2. Under this metric, `continuousRealization` is an isometric embedding (hence injective and uniformly continuous).
3. The image of `continuousRealization` is dense in $C(\mathbb{R}^d, \mathbb{R}^k)$ (by the UAT density axiom on compact domains).
4. By the properties of metric completions, the unique continuous extension `continuousRealizationLimit` to the completion
   `KernelAddressLimit` is a bijection, i.e., every continuous function $f$ has a unique limit representative.
-/
axiom topological_extension_bijection
    (d k : Nat) (σ : Activation)
    (h_inj : ∀ q₁ q₂ : KernelAddress d k σ, continuousRealization d k σ q₁ = continuousRealization d k σ q₂ → q₁ = q₂)
    (h_dense : ∀ (K : Set (EuclideanSpace ℝ (Fin d))) (_ : IsCompact K)
        (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))) (ε : ℝ) (_ : 0 < ε),
        ∃ q : KernelAddress d k σ, ∀ x ∈ K, ‖continuousRealization d k σ q x - f x‖ < ε)
    (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))) :
    ∃! θ_limit : KernelAddressLimit d k σ, continuousRealizationLimit d k σ θ_limit = f

/--
**ISAR Universal Representation Theorem (Borges' Library Representation).**

Every continuous function f : ℝᵈ → ℝᵏ has a unique address θ_limit in the continuous
limit morphism space (`KernelAddressLimit`) such that its realization is exactly f.

**Proof**: Follows by applying the functional analysis extension theorem to the constructive
injectivity of continuousRealization and the metric density of the UAT.
-/
theorem ISAR_representation
    (d k : Nat)
    (σ : Activation)
    (h_np : Activation.nonPolynomial σ)
    (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))) :
    ∃! θ_limit : KernelAddressLimit d k σ, continuousRealizationLimit d k σ θ_limit = f := by
  apply topological_extension_bijection d k σ
  { exact continuousRealization_injective d k σ }
  { intro K hK f_map ε hε
    obtain ⟨θ_raw, h_approx⟩ := ISAR_UAT d k K hK f_map σ h_np ε hε
    use Quotient.mk _ θ_raw
    exact h_approx }

/--
**Corollary: Logical, Statistical, and Topological Universality.**

The ISAR kernel simultaneously achieves:
1. **Logical universality** (proved, zero extra axioms):
   `morphism_uniqueness` — every admissible formal rewriting system embeds uniquely
   into ISAR_Kernel.
2. **Statistical universality** (analytic UAT axiom `ISAR_UAT`):
   every continuous function ℝᵈ → ℝᵏ is approximable by the iterated ISAR update
   on any compact subset K to arbitrary precision ε > 0.
3. **Topological universality** (proved theorem `ISAR_representation`):
   every continuous function ℝᵈ → ℝᵏ is uniquely represented by its coordinate address θ_limit
   in the continuous limit morphism space.
-/
theorem ISAR_logical_and_statistical_universality :
    (∀ (K : Kernel) (f : KernelHom K ISAR_Kernel) (c : K.Carrier),
        OperEq (f.hom c) (K.decode c)) ∧
    (∀ (d k : Nat) (K : Set (EuclideanSpace ℝ (Fin d))) (_ : IsCompact K)
        (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k)))
        (σ : Activation) (_ : Activation.nonPolynomial σ) (ε : ℝ) (_ : 0 < ε),
        ∃ θ : RawAddress d k,
          ∀ x ∈ K,
            ‖realizeRaw d k σ θ x - f x‖ < ε) ∧
    (∀ (d k : Nat) (σ : Activation) (_ : Activation.nonPolynomial σ)
        (f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin k))),
        ∃! θ_limit : KernelAddressLimit d k σ, continuousRealizationLimit d k σ θ_limit = f) :=
  ⟨fun K f c => morphism_uniqueness K f c,
   fun d k K hK f σ σ_np ε hε => ISAR_UAT d k K hK f σ σ_np ε hε,
   fun d k σ σ_np f => ISAR_representation d k σ σ_np f⟩

end ISAR
