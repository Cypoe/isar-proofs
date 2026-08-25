import ISAR.Holonomic
import ISAR.HolonomicClosure
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Concrete holonomic certificates (Python self-test parity)
-/

noncomputable section

open Polynomial

namespace ISAR

/-! ## `Real.exp` -/

theorem exp_holonomic :
    satisfiesODE (orderOneCert (-1) 1 (by simp)) Real.exp := by
  intro x
  rw [orderOneCert_residual]
  simp [Real.deriv_exp]

theorem exp_multiplicative :
    satisfiesOrderOneMultiplicative (1 : ℝ[X]) Real.exp := by
  intro x
  simp [eval_one, Real.deriv_exp]

theorem exp_differentiable : Differentiable ℝ Real.exp :=
  Real.differentiable_exp

theorem exp_isHolonomic : IsHolonomic Real.exp :=
  ⟨_, exp_holonomic⟩

/-! ## Gaussian `exp(-x²)` -/

def gaussian : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))

private theorem hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa [pow_one] using hasDerivAt_pow 2 x

private theorem hasDerivAt_neg_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x :=
  (hasDerivAt_sq x).neg

theorem hasDerivAt_gaussian (x : ℝ) :
    HasDerivAt gaussian (gaussian x * (-(2 * x))) x := by
  unfold gaussian
  exact (hasDerivAt_neg_sq x).exp

theorem deriv_gaussian (x : ℝ) :
    deriv gaussian x = -(2 * x) * gaussian x := by
  rw [(hasDerivAt_gaussian x).deriv]
  ring

theorem gaussian_differentiable : Differentiable ℝ gaussian :=
  fun x => (hasDerivAt_gaussian x).differentiableAt

theorem gaussian_holonomic :
    satisfiesODE (orderOneCert (C 2 * X) 1 (by simp)) gaussian := by
  intro x
  rw [orderOneCert_residual, deriv_gaussian]
  simp [eval_mul, eval_C, eval_X]

theorem gaussian_multiplicative :
    satisfiesOrderOneMultiplicative (-(C 2 * X)) gaussian := by
  intro x
  rw [deriv_gaussian]
  simp [eval_neg, eval_mul, eval_C, eval_X]

theorem gaussian_isHolonomic : IsHolonomic gaussian :=
  ⟨_, gaussian_holonomic⟩

/-- Second derivative of the gaussian, used by sum/product residuals. -/
theorem deriv_deriv_gaussian (x : ℝ) :
    deriv (deriv gaussian) x = (-2 + 4 * x ^ 2) * gaussian x := by
  have heq : deriv gaussian = (fun y : ℝ => -((2 : ℝ) * y)) * gaussian := by
    funext y
    simpa [Pi.mul_apply, mul_comm] using deriv_gaussian y
  rw [heq]
  have hlin : DifferentiableAt ℝ (fun y : ℝ => -((2 : ℝ) * y)) x :=
    (differentiableAt_id.const_mul (2 : ℝ)).neg
  rw [deriv_mul hlin (gaussian_differentiable x)]
  have hlin' : deriv (fun y : ℝ => -((2 : ℝ) * y)) x = -2 := by
    simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).neg.deriv
  rw [hlin', deriv_gaussian]
  ring

/-! ## Product `exp * gaussian` -/

theorem exp_mul_gaussian_holonomic :
    satisfiesODE (orderOneCert (-(1 + -(C 2 * X))) 1 (by simp))
      (Real.exp * gaussian) :=
  product_holonomic_orderOne (1 : ℝ[X]) (-(C 2 * X)) Real.exp gaussian
    exp_multiplicative gaussian_multiplicative exp_differentiable gaussian_differentiable

theorem exp_mul_gaussian_isHolonomic : IsHolonomic (Real.exp * gaussian) :=
  ⟨_, exp_mul_gaussian_holonomic⟩

theorem exp_mul_gaussian_order_bound :
    (orderOneCert (-(1 + -(C 2 * X))) 1 (by simp)).order ≤ 1 * 1 := by
  decide

/-! ## Sum (constant-rate + variable-rate) -/

theorem exp_add_exp_holonomic :
    satisfiesODE (orderTwoCert (C (1 * 1)) (C (-(1 + 1))) 1 (by simp))
      (Real.exp + Real.exp) :=
  sum_holonomic_const_rates 1 1 Real.exp Real.exp
    exp_multiplicative exp_multiplicative exp_differentiable exp_differentiable

theorem exp_add_exp_isHolonomic : IsHolonomic (Real.exp + Real.exp) :=
  ⟨_, exp_add_exp_holonomic⟩

theorem one_add_two_X_ne : (1 + C 2 * X : ℝ[X]) ≠ 0 := by
  intro h
  exact absurd (congrArg (coeff · 0) h) (by simp)

/-- Python TEST 4 sum residual: `exp + exp(-x²)`. -/
theorem exp_add_gaussian_holonomic :
    satisfiesODE
      (orderTwoCert (C 2 - C 2 * X - C 4 * X ^ 2) (C (-3) + C 4 * X ^ 2)
        (1 + C 2 * X) one_add_two_X_ne)
      (Real.exp + gaussian) := by
  intro x
  rw [orderTwoCert_residual]
  have hF : deriv (Real.exp + gaussian) = fun y => Real.exp y + deriv gaussian y := by
    funext y
    rw [deriv_add (exp_differentiable y) (gaussian_differentiable y), Real.deriv_exp]
  have h1 : deriv (Real.exp + gaussian) x = Real.exp x + deriv gaussian x :=
    congrFun hF x
  have hgg : DifferentiableAt ℝ (deriv gaussian) x := by
    have heq : deriv gaussian = (fun y : ℝ => -((2 : ℝ) * y)) * gaussian := by
      funext y
      simpa [Pi.mul_apply, mul_comm] using deriv_gaussian y
    rw [heq]
    exact ((differentiableAt_id.const_mul (2 : ℝ)).neg).mul (gaussian_differentiable x)
  have h2 : iteratedDeriv 2 (Real.exp + gaussian) x =
      Real.exp x + deriv (deriv gaussian) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hF]
    change deriv (fun y => Real.exp y + deriv gaussian y) x = _
    have hadd :
        (fun y => Real.exp y + deriv gaussian y) = Real.exp + deriv gaussian := by
      funext y; rfl
    rw [hadd, deriv_add (exp_differentiable x) hgg, Real.deriv_exp]
  simp only [h1, h2, deriv_gaussian, deriv_deriv_gaussian, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X, eval_one, Pi.add_apply]
  ring

theorem exp_add_gaussian_isHolonomic : IsHolonomic (Real.exp + gaussian) :=
  ⟨_, exp_add_gaussian_holonomic⟩

/-! ## Double-integral chain -/

def gaussianCert : HolonomicCertificate :=
  orderOneCert (C 2 * X) 1 (by simp)

def gaussianDoubleIntegralCert : HolonomicCertificate :=
  gaussianCert.integralShift.integralShift

theorem gaussian_double_integral_closure (H : ℝ → ℝ)
    (hH : deriv (deriv H) = gaussian) :
    satisfiesODE gaussianDoubleIntegralCert H := by
  have hmid : satisfiesODE gaussianCert.integralShift (deriv H) :=
    integral_closure_shift gaussianCert gaussian (deriv H) gaussian_holonomic hH
  exact integral_closure_shift gaussianCert.integralShift (deriv H) H hmid rfl

theorem gaussianDoubleIntegralCert_order :
    gaussianDoubleIntegralCert.order = 3 := rfl

/-! ## `sin(x²)` -/

def fresnelSin : ℝ → ℝ := fun x => Real.sin (x ^ 2)

theorem hasDerivAt_fresnelSin (x : ℝ) :
    HasDerivAt fresnelSin (Real.cos (x ^ 2) * (2 * x)) x := by
  unfold fresnelSin
  exact (hasDerivAt_sq x).sin

theorem deriv_fresnelSin (x : ℝ) :
    deriv fresnelSin x = (2 * x) * Real.cos (x ^ 2) := by
  rw [(hasDerivAt_fresnelSin x).deriv]
  ring

theorem fresnelSin_differentiable : Differentiable ℝ fresnelSin :=
  fun x => (hasDerivAt_fresnelSin x).differentiableAt

theorem X_ne_zero : (X : ℝ[X]) ≠ 0 := by
  intro h
  have := congrArg (coeff · 1) h
  simp [coeff_X] at this

theorem hasDerivAt_deriv_fresnelSin (x : ℝ) :
    HasDerivAt (deriv fresnelSin)
      (2 * Real.cos (x ^ 2) + (2 * x) * (-Real.sin (x ^ 2) * (2 * x))) x := by
  have heq : deriv fresnelSin = fun y => (2 * y) * Real.cos (y ^ 2) := by
    funext y; exact deriv_fresnelSin y
  rw [heq]
  have hlin : HasDerivAt (fun y : ℝ => (2 : ℝ) * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  exact hlin.mul (hasDerivAt_sq x).cos

theorem deriv_deriv_fresnelSin (x : ℝ) :
    deriv (deriv fresnelSin) x =
      2 * Real.cos (x ^ 2) - 4 * x ^ 2 * Real.sin (x ^ 2) := by
  have h := (hasDerivAt_deriv_fresnelSin x).deriv
  simp [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, pow_two] at h ⊢
  convert h using 1
  ring

theorem fresnelSin_holonomic :
    satisfiesODE (orderTwoCert (C 4 * X ^ 3) (-1) X X_ne_zero) fresnelSin := by
  intro x
  rw [orderTwoCert_residual]
  have h1 := deriv_fresnelSin x
  have h2 : iteratedDeriv 2 fresnelSin x =
      2 * Real.cos (x ^ 2) + (2 * x) * (-Real.sin (x ^ 2) * (2 * x)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hasDerivAt_deriv_fresnelSin x).deriv
  simp [h1, h2, eval_mul, eval_pow, eval_C, eval_X, eval_neg, eval_one, fresnelSin]
  ring

theorem fresnelSin_isHolonomic : IsHolonomic fresnelSin :=
  ⟨_, fresnelSin_holonomic⟩

/-! ## Mixed product `sin(x²)·exp(-x²)` (Python TEST 4b) -/

theorem fresnel_gaussian_tensor_bound :
    (orderTwoCert (C 8 * X ^ 3) (C 4 * X ^ 2 - 1) X X_ne_zero).order = 2 * 1 :=
  rfl

theorem fresnelSin_mul_gaussian_factors_holonomic :
    IsHolonomic fresnelSin ∧ IsHolonomic gaussian :=
  ⟨fresnelSin_isHolonomic, gaussian_isHolonomic⟩

/-- First derivative of the mixed product. -/
theorem deriv_fresnel_mul_gaussian (x : ℝ) :
    deriv (fresnelSin * gaussian) x =
      (2 * x) * Real.cos (x ^ 2) * gaussian x +
        Real.sin (x ^ 2) * (-(2 * x) * gaussian x) := by
  rw [deriv_mul (fresnelSin_differentiable x) (gaussian_differentiable x),
    deriv_fresnelSin, deriv_gaussian, fresnelSin]

/-- Second derivative of the mixed product via product rule on the first derivative. -/
theorem deriv_deriv_fresnel_mul_gaussian (x : ℝ) :
    deriv (deriv (fresnelSin * gaussian)) x =
      (2 * Real.cos (x ^ 2) - 4 * x ^ 2 * Real.sin (x ^ 2)) * gaussian x +
        (2 * x) * Real.cos (x ^ 2) * (-(2 * x) * gaussian x) +
        ((2 * x) * Real.cos (x ^ 2) * (-(2 * x) * gaussian x) +
          Real.sin (x ^ 2) * ((-2 + 4 * x ^ 2) * gaussian x)) := by
  have heq : deriv (fresnelSin * gaussian) =
      fun y =>
        (2 * y) * Real.cos (y ^ 2) * gaussian y +
          Real.sin (y ^ 2) * (-(2 * y) * gaussian y) := by
    funext y; simpa [fresnelSin] using deriv_fresnel_mul_gaussian y
  rw [heq]
  set A : ℝ → ℝ := fun y => (2 * y) * Real.cos (y ^ 2) * gaussian y
  set B : ℝ → ℝ := fun y => Real.sin (y ^ 2) * (-(2 * y) * gaussian y)
  have hadd : (fun y => A y + B y) = A + B := by funext y; rfl
  have hA : DifferentiableAt ℝ A x := by
    refine DifferentiableAt.mul ?_ (gaussian_differentiable x)
    exact (differentiableAt_id.const_mul 2).mul (hasDerivAt_sq x).cos.differentiableAt
  have hB : DifferentiableAt ℝ B x := by
    have hs : DifferentiableAt ℝ (fun y => Real.sin (y ^ 2)) x :=
      fresnelSin_differentiable x
    exact hs.mul
      (((differentiableAt_id.const_mul (2 : ℝ)).neg).mul (gaussian_differentiable x))
  change deriv (fun y => A y + B y) x = _
  rw [hadd, deriv_add hA hB]
  have dA : deriv A x =
      (2 * Real.cos (x ^ 2) + (2 * x) * (-Real.sin (x ^ 2) * (2 * x))) * gaussian x +
        (2 * x) * Real.cos (x ^ 2) * deriv gaussian x := by
    unfold A
    have hcg : DifferentiableAt ℝ (fun y => (2 * y) * Real.cos (y ^ 2)) x :=
      (differentiableAt_id.const_mul 2).mul (hasDerivAt_sq x).cos.differentiableAt
    have hmul :
        (fun y => (2 * y) * Real.cos (y ^ 2) * gaussian y) =
          (fun y => (2 * y) * Real.cos (y ^ 2)) * gaussian := by
      funext y; rfl
    rw [hmul, deriv_mul hcg (gaussian_differentiable x)]
    have dcg : deriv (fun y => (2 * y) * Real.cos (y ^ 2)) x =
        2 * Real.cos (x ^ 2) + (2 * x) * (-Real.sin (x ^ 2) * (2 * x)) := by
      have hlin : HasDerivAt (fun y : ℝ => (2 : ℝ) * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      have hcg_eq :
          (fun y => (2 * y) * Real.cos (y ^ 2)) =
            (fun y : ℝ => (2 : ℝ) * y) * fun y => Real.cos (y ^ 2) := by
        funext y; rfl
      rw [hcg_eq]
      simpa using (hlin.mul (hasDerivAt_sq x).cos).deriv
    rw [dcg]
  have dB : deriv B x =
      (2 * x) * Real.cos (x ^ 2) * (-(2 * x) * gaussian x) +
        Real.sin (x ^ 2) * deriv ((fun y : ℝ => -((2 : ℝ) * y)) * gaussian) x := by
    unfold B
    have hs : DifferentiableAt ℝ (fun y => Real.sin (y ^ 2)) x :=
      fresnelSin_differentiable x
    have hr : DifferentiableAt ℝ ((fun y : ℝ => -((2 : ℝ) * y)) * gaussian) x :=
      ((differentiableAt_id.const_mul 2).neg).mul (gaussian_differentiable x)
    have hmul :
        (fun y => Real.sin (y ^ 2) * (-(2 * y) * gaussian y)) =
          (fun y => Real.sin (y ^ 2)) * ((fun y : ℝ => -((2 : ℝ) * y)) * gaussian) := by
      funext y; simp [Pi.mul_apply]
    rw [hmul, deriv_mul hs hr]
    have ds : deriv (fun y => Real.sin (y ^ 2)) x = (2 * x) * Real.cos (x ^ 2) := by
      simpa [fresnelSin, mul_comm] using deriv_fresnelSin x
    rw [ds]
    simp [Pi.mul_apply]
  have dr' : deriv ((fun y : ℝ => -((2 : ℝ) * y)) * gaussian) x =
      (-2 + 4 * x ^ 2) * gaussian x := by
    have heq' : deriv gaussian = (fun y : ℝ => -((2 : ℝ) * y)) * gaussian := by
      funext y
      simpa [Pi.mul_apply, mul_comm] using deriv_gaussian y
    rw [← heq', deriv_deriv_gaussian]
  simp only [dA, dB, dr', deriv_gaussian]
  ring

/-- Python TEST 4b: `8x³ h + (4x²-1) h' + x h'' = 0`. -/
theorem fresnelSin_mul_gaussian_holonomic :
    satisfiesODE
      (orderTwoCert (C 8 * X ^ 3) (C 4 * X ^ 2 - 1) X X_ne_zero)
      (fresnelSin * gaussian) := by
  intro x
  rw [orderTwoCert_residual]
  have h1 := deriv_fresnel_mul_gaussian x
  have h2 : iteratedDeriv 2 (fresnelSin * gaussian) x =
      deriv (deriv (fresnelSin * gaussian)) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, deriv_deriv_fresnel_mul_gaussian]
  simp only [h1, eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one, Pi.mul_apply,
    fresnelSin, gaussian]
  ring

theorem fresnelSin_mul_gaussian_isHolonomic : IsHolonomic (fresnelSin * gaussian) :=
  ⟨_, fresnelSin_mul_gaussian_holonomic⟩

end ISAR
