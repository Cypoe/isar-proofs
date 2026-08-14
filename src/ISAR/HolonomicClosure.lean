import ISAR.Holonomic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Holonomic closure theorems

Python counterparts:
* `HolonomicRegistry.integral_closure` — coefficient shift theorem
* `product_closure` — order-1 multiplicative product (tensor bound 1)
* `sum_closure` — constant-rate order-1 sum (order ≤ 2)
-/

noncomputable section

open Polynomial Classical

namespace ISAR

/-- If `deriv h = g` as functions, higher derivatives of `h` match those of `g` shifted. -/
theorem iteratedDeriv_of_deriv_eq {g h : ℝ → ℝ} (hg : deriv h = g) (n : ℕ) :
    iteratedDeriv (n + 1) h = iteratedDeriv n g := by
  rw [iteratedDeriv_succ', hg]

private theorem integralShift_residual_eq (c : HolonomicCertificate) (g h : ℝ → ℝ)
    (hd : deriv h = g) (x : ℝ) :
    c.integralShift.residual h x =
      ∑ i : Fin (c.order + 1), (c.coeffs i).eval x * iteratedDeriv i.val g x := by
  unfold HolonomicCertificate.residual HolonomicCertificate.integralShift
  rw [Fin.sum_univ_succ]
  -- Index 0 coefficient is zero.
  simp only [Fin.val_zero, ↓reduceDIte, eval_zero, zero_mul, zero_add]
  refine Fintype.sum_congr _ _ fun i => ?_
  simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_one_sub_one,
    iteratedDeriv_of_deriv_eq hd, Fin.eta]

/-- **Integral closure shift** (Python `integral_closure`). -/
theorem integral_closure_shift (c : HolonomicCertificate) (g h : ℝ → ℝ)
    (hg : satisfiesODE c g) (hd : deriv h = g) :
    satisfiesODE c.integralShift h := by
  intro x
  rw [integralShift_residual_eq c g h hd x]
  simpa [HolonomicCertificate.residual] using hg x

/-- Order-1 multiplicative form: `f' = a · f` with polynomial `a`. -/
def satisfiesOrderOneMultiplicative (a : ℝ[X]) (f : ℝ → ℝ) : Prop :=
  ∀ x, deriv f x = a.eval x * f x

theorem satisfiesOrderOneMultiplicative.to_satisfiesODE (a : ℝ[X]) (f : ℝ → ℝ)
    (hf : satisfiesOrderOneMultiplicative a f) :
    satisfiesODE (orderOneCert (-a) 1 (by simp)) f := by
  intro x
  rw [orderOneCert_residual]
  simp [hf x]

/-- Product of two order-1 multiplicative holonomic functions is again order-1 multiplicative. -/
theorem product_orderOne_multiplicative (a b : ℝ[X]) (f g : ℝ → ℝ)
    (hf : satisfiesOrderOneMultiplicative a f) (hg : satisfiesOrderOneMultiplicative b g)
    (hdf : Differentiable ℝ f) (hdg : Differentiable ℝ g) :
    satisfiesOrderOneMultiplicative (a + b) (f * g) := by
  intro x
  rw [deriv_mul (hdf x) (hdg x), hf x, hg x]
  simp [Pi.mul_apply, eval_add]
  ring

/-- Product closure for order-1 multiplicative certificates (order bound `≤ 1·1 = 1`). -/
theorem product_holonomic_orderOne (a b : ℝ[X]) (f g : ℝ → ℝ)
    (hf : satisfiesOrderOneMultiplicative a f) (hg : satisfiesOrderOneMultiplicative b g)
    (hdf : Differentiable ℝ f) (hdg : Differentiable ℝ g) :
    satisfiesODE (orderOneCert (-(a + b)) 1 (by simp)) (f * g) :=
  (product_orderOne_multiplicative a b f g hf hg hdf hdg).to_satisfiesODE

/-- Sum closure for constant-rate order-1 factors (`a, b ∈ ℝ`), order bound `≤ 2`. -/
theorem sum_holonomic_const_rates (a b : ℝ) (f g : ℝ → ℝ)
    (hf : satisfiesOrderOneMultiplicative (C a) f)
    (hg : satisfiesOrderOneMultiplicative (C b) g)
    (hdf : Differentiable ℝ f) (hdg : Differentiable ℝ g) :
    satisfiesODE (orderTwoCert (C (a * b)) (C (-(a + b))) 1 (by simp)) (f + g) := by
  intro x
  rw [orderTwoCert_residual]
  have heq : deriv (f + g) = fun y => a * f y + b * g y := by
    funext y
    rw [deriv_add (hdf y) (hdg y), hf y, hg y]
    simp
  have h1 : deriv (f + g) x = a * f x + b * g x := congrFun heq x
  have h2 : iteratedDeriv 2 (f + g) x = a * (a * f x) + b * (b * g x) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, heq]
    change deriv (fun y => a * f y + b * g y) x = _
    have ha : DifferentiableAt ℝ (fun y => a * f y) x := (hdf x).const_mul a
    have hb : DifferentiableAt ℝ (fun y => b * g y) x := (hdg x).const_mul b
    have hadd :
        (fun y => a * f y + b * g y) = (fun y => a * f y) + fun y => b * g y := by
      funext y; rfl
    rw [hadd, deriv_add ha hb, deriv_const_mul _ (hdf x), deriv_const_mul _ (hdg x),
      hf x, hg x]
    simp [eval_C]
  simp [h1, h2]
  ring

theorem product_holonomic_orderOne_exists (a b : ℝ[X]) (f g : ℝ → ℝ)
    (hf : satisfiesOrderOneMultiplicative a f) (hg : satisfiesOrderOneMultiplicative b g)
    (hdf : Differentiable ℝ f) (hdg : Differentiable ℝ g) :
    IsHolonomic (f * g) :=
  ⟨_, product_holonomic_orderOne a b f g hf hg hdf hdg⟩

theorem sum_holonomic_const_rates_exists (a b : ℝ) (f g : ℝ → ℝ)
    (hf : satisfiesOrderOneMultiplicative (C a) f)
    (hg : satisfiesOrderOneMultiplicative (C b) g)
    (hdf : Differentiable ℝ f) (hdg : Differentiable ℝ g) :
    IsHolonomic (f + g) :=
  ⟨_, sum_holonomic_const_rates a b f g hf hg hdf hdg⟩

end ISAR
