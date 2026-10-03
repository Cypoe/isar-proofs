import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# P-recursive (discrete holonomic) certificates

Sequence-side counterpart of `ISAR.Holonomic`: a certificate encodes a
linear recurrence with polynomial coefficients,

    ∑_{i ≤ order} p_i(n) · a_{n+i} = 0,

and the uniqueness theorem discharges the meta-obligation used by the
koru holonomic gate (`koru/scripts/holonomic_gate.py`): two sequences
satisfying the same certificate and agreeing on `order` initial terms —
and at every index where the leading coefficient is nonzero along the
way — agree everywhere. The gate implements this bound computationally;
this module proves it.
-/

open Polynomial

namespace ISAR

/-- Linear recurrence certificate of order `order` over `ℚ`-valued
sequences. `coeffs i` multiplies `a_{n+i}`; the leading coefficient is
required nonzero (as a polynomial). -/
structure PRecursiveCertificate where
  order : ℕ
  coeffs : Fin (order + 1) → ℚ[X]
  leading_ne : coeffs (Fin.last order) ≠ 0

/-- Pointwise residual of a certificate against a sequence at index `n`. -/
def PRecursiveCertificate.residual (c : PRecursiveCertificate)
    (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i : Fin (c.order + 1), (c.coeffs i).eval (n : ℚ) * a (n + i.val)

/-- `a` satisfies the recurrence encoded by `c` at every index. -/
def satisfiesRecurrence (c : PRecursiveCertificate) (a : ℕ → ℚ) : Prop :=
  ∀ n, c.residual a n = 0

/-- `a` admits some P-recursive certificate. -/
def IsPRecursive (a : ℕ → ℚ) : Prop :=
  ∃ c : PRecursiveCertificate, satisfiesRecurrence c a

/-- Split the residual into the lower-order sum and the leading term. -/
theorem PRecursiveCertificate.residual_eq (c : PRecursiveCertificate)
    (a : ℕ → ℚ) (n : ℕ) :
    c.residual a n =
      (∑ i : Fin c.order,
        (c.coeffs i.castSucc).eval (n : ℚ) * a (n + i.val)) +
        (c.coeffs (Fin.last c.order)).eval (n : ℚ) *
          a (n + c.order) := by
  unfold residual
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- **Uniqueness from initial conditions** (non-singular case): if two
sequences satisfy the same recurrence, the leading coefficient never
vanishes on `ℕ` (no singular points), and they agree on the first
`order` terms, they agree everywhere.

This is the theorem justifying the gate's bounded check: a certificate
carves out an `order`-dimensional solution space, and `order` agreeing
initial values pin the same point of it. Singular indices (where the
leading coefficient evaluates to zero) must be checked explicitly —
the gate extends its required set accordingly. -/
theorem eq_of_satisfiesRecurrence_of_init {c : PRecursiveCertificate}
    {a b : ℕ → ℚ}
    (ha : satisfiesRecurrence c a) (hb : satisfiesRecurrence c b)
    (hlead : ∀ n : ℕ,
      (c.coeffs (Fin.last c.order)).eval (n : ℚ) ≠ 0)
    (hinit : ∀ i : ℕ, i < c.order → a i = b i) :
    ∀ n, a n = b n := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  by_cases hn : n < c.order
  · exact hinit n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + c.order := ⟨n - c.order, by omega⟩
    set L := c.coeffs (Fin.last c.order)
    have ra := c.residual_eq a m ▸ ha m
    have rb := c.residual_eq b m ▸ hb m
    -- lower-order sums coincide: every index m + i < m + order is IH'd
    have hlow :
        (∑ i : Fin c.order,
          (c.coeffs i.castSucc).eval (m : ℚ) * a (m + i.val)) =
        (∑ i : Fin c.order,
          (c.coeffs i.castSucc).eval (m : ℚ) * b (m + i.val)) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := ih (m + i.val) (by
        have := i.isLt
        omega)
      rw [h]
    rw [hlow] at ra
    -- now ra : S + L·a = 0 and rb : S + L·b = 0, so L·a = L·b
    have hmul : L.eval (m : ℚ) * a (m + c.order) =
        L.eval (m : ℚ) * b (m + c.order) := by
      linarith
    exact mul_left_cancel₀ (hlead m) hmul

end ISAR
