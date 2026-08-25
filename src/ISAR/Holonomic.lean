import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Holonomic (D-finite) certificates

Lean counterpart of the Python kernel in `scratch/isar_holonomic_closure_algebra.py`.
-/

noncomputable section

open Polynomial Classical

namespace ISAR

/-- Polynomial-coefficient linear ODE certificate of order `order`. -/
structure HolonomicCertificate where
  order : ℕ
  coeffs : Fin (order + 1) → ℝ[X]
  leading_ne : coeffs ⟨order, Nat.lt_succ_self order⟩ ≠ 0

/-- Pointwise residual of a certificate against a function. -/
def HolonomicCertificate.residual (c : HolonomicCertificate) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin (c.order + 1), (c.coeffs i).eval x * iteratedDeriv i.val f x

/-- `f` satisfies the holonomic ODE encoded by `c`. -/
def satisfiesODE (c : HolonomicCertificate) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, c.residual f x = 0

/-- `f` admits some holonomic certificate. -/
def IsHolonomic (f : ℝ → ℝ) : Prop :=
  ∃ c : HolonomicCertificate, satisfiesODE c f

theorem verify_certificate_iff (c : HolonomicCertificate) (f : ℝ → ℝ) :
    satisfiesODE c f ↔ ∀ x, c.residual f x = 0 :=
  Iff.rfl

theorem cert_sound (c : HolonomicCertificate) (f : ℝ → ℝ)
    (h : ∀ x, c.residual f x = 0) : satisfiesODE c f :=
  h

/-- Build an order-1 certificate `p₀ · f + p₁ · f' = 0` with `p₁ ≠ 0`. -/
def orderOneCert (p0 p1 : ℝ[X]) (hp1 : p1 ≠ 0) : HolonomicCertificate where
  order := 1
  coeffs := fun i => if i.val = 0 then p0 else p1
  leading_ne := by
    change (if (1 : ℕ) = 0 then p0 else p1) ≠ 0
    simpa using hp1

/-- Build an order-2 certificate with leading `p2 ≠ 0`. -/
def orderTwoCert (p0 p1 p2 : ℝ[X]) (hp2 : p2 ≠ 0) : HolonomicCertificate where
  order := 2
  coeffs := fun i =>
    if i.val = 0 then p0 else if i.val = 1 then p1 else p2
  leading_ne := by
    change (if (2 : ℕ) = 0 then p0 else if (2 : ℕ) = 1 then p1 else p2) ≠ 0
    simpa using hp2

theorem orderOneCert_residual (p0 p1 : ℝ[X]) (hp1 : p1 ≠ 0) (f : ℝ → ℝ) (x : ℝ) :
    (orderOneCert p0 p1 hp1).residual f x =
      p0.eval x * f x + p1.eval x * deriv f x := by
  unfold HolonomicCertificate.residual orderOneCert
  rw [Fin.sum_univ_two]
  simp [iteratedDeriv_zero, iteratedDeriv_one]

theorem orderTwoCert_residual (p0 p1 p2 : ℝ[X]) (hp2 : p2 ≠ 0) (f : ℝ → ℝ) (x : ℝ) :
    (orderTwoCert p0 p1 p2 hp2).residual f x =
      p0.eval x * f x + p1.eval x * deriv f x +
        p2.eval x * iteratedDeriv 2 f x := by
  unfold HolonomicCertificate.residual orderTwoCert
  rw [Fin.sum_univ_three]
  simp [iteratedDeriv_zero, iteratedDeriv_one]

/-- Prepend a zero coefficient (integral-closure construction). -/
def HolonomicCertificate.integralShift (c : HolonomicCertificate) : HolonomicCertificate where
  order := c.order + 1
  coeffs := fun i =>
    if h : (i : ℕ) = 0 then 0
    else c.coeffs ⟨(i : ℕ) - 1, by
      have := i.isLt
      have : 0 < (i : ℕ) := Nat.pos_of_ne_zero h
      omega⟩
  leading_ne := by
    have hne : ¬(c.order + 1 = 0) := Nat.succ_ne_zero _
    simp only [hne, ↓reduceDIte]
    convert c.leading_ne
    simp

end ISAR
