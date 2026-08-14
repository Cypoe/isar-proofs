import ISAR.Holonomic
import ISAR.HolonomicInstances
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Composition refusal (Python `registry.compose`)

General composition of holonomic generators is **not** a closure operation.
The counterexample is `exp ∘ exp`: both factors are order-1 holonomic
(`f' - f = 0`), yet `exp(exp x)` is not D-finite.

## Axiom boundary

Mathlib v4.31 has no Stanley root-growth theorem linking Bell numbers to the
Taylor series of `exp ∘ exp`. The single named axiom below records that
analytic fact; theorems cite it explicitly. There is no silent `sorry`.

All Python self-test residual certificates (including sum and mixed product)
are proved in `HolonomicInstances`.
-/

noncomputable section

open Polynomial Classical

namespace ISAR

/-- Outcome of a requested composition, mirroring Python `registry.compose`. -/
inductive ComposeOutcome where
  | impossible (proof : String)
  deriving Repr

/-- Structured refusal returned by the composition interface. -/
def composeRefuse : ComposeOutcome :=
  .impossible
    "Composition of holonomic generators is not closed in general \
(counterexample: exp ∘ exp; Bell/Stanley obstruction)."

/-- The registry composition operation always refuses in the general case. -/
def compose (_outer _inner : HolonomicCertificate) : ComposeOutcome :=
  composeRefuse

theorem compose_refuses_in_general (c₁ c₂ : HolonomicCertificate) :
    compose c₁ c₂ = composeRefuse :=
  rfl

/-! ## Sole analytic axiom for composition obstruction -/

/--
Direct non-holonomicity of `exp ∘ exp`.

**Content (classical analysis):** the Taylor coefficients of `exp(exp x)` at `0`
involve Bell numbers whose root growth diverges, so by Stanley’s criterion the
function is not D-finite / holonomic. Mathlib does not yet contain this chain;
we import the conclusion as one named axiom.
-/
axiom exp_exp_not_holonomic :
    ¬ IsHolonomic (fun x : ℝ => Real.exp (Real.exp x))

/-! ## Proved interface facts -/

/-- Both factors of the composition counterexample are holonomic. -/
theorem exp_exp_factors_holonomic :
    IsHolonomic Real.exp ∧ IsHolonomic Real.exp :=
  ⟨exp_isHolonomic, exp_isHolonomic⟩

/--
If holonomic functions were closed under composition, then `exp ∘ exp` would be
holonomic. Combined with `exp_exp_not_holonomic`, this yields the general refusal.
-/
theorem holonomic_compose_would_imply_exp_exp
    (H : ∀ f g : ℝ → ℝ, IsHolonomic f → IsHolonomic g → IsHolonomic (f ∘ g)) :
    IsHolonomic (fun x => Real.exp (Real.exp x)) := by
  change IsHolonomic (Real.exp ∘ Real.exp)
  exact H Real.exp Real.exp exp_isHolonomic exp_isHolonomic

/--
General composition closure is impossible: it would contradict
`exp_exp_not_holonomic`.
-/
theorem holonomic_not_closed_under_compose :
    ¬ (∀ f g : ℝ → ℝ, IsHolonomic f → IsHolonomic g → IsHolonomic (f ∘ g)) := by
  intro H
  exact exp_exp_not_holonomic (holonomic_compose_would_imply_exp_exp H)

/--
Python `compose_is_provably_impossible_in_general` evidence package.
-/
theorem compose_impossibility_package :
    IsHolonomic Real.exp ∧
      IsHolonomic Real.exp ∧
      ¬ IsHolonomic (fun x => Real.exp (Real.exp x)) ∧
      (∀ c₁ c₂, compose c₁ c₂ = composeRefuse) :=
  ⟨exp_isHolonomic, exp_isHolonomic, exp_exp_not_holonomic, compose_refuses_in_general⟩

end ISAR
