import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

open Polynomial

namespace ISAR.RischDE

/-!
# RischDE — the degree/pole argument behind Koru's `linDESolve`

Mirror of the Risch `F·e^G` decision lane in `koru_std/sym.certgen.kz`.

For a polynomial `G` and rational `F`, the ansatz `∫F·e^G = R·e^G` gives
`R' + G'·R = F`.  A pole of order `m` in `R` appears at order `m+1` in `R'`
and at most `m` in `G'·R` (G' is a polynomial), so `R` is forced to be a
polynomial with `deg R = deg F − deg G'`, and the coefficients solve
top-down with constant leading coefficient `lt(G')`.

`linDESolve` generalises the same idea to `D·T' + A·T = F` with
`deg A ≥ deg D` — this is what the Rothstein denominator bound reduces
`R'+G'R=F` to via `R = T/D`, `D = gcd(d, d')`.  The theorems here prove
the load-bearing claims:

* `linDE_apply_natDegree` — `A·T` dominates `D·T'` when `deg A ≥ deg D`,
  so `deg (D·T' + A·T) = deg T + deg A` exactly.  This is what makes
  `deg T = deg F − deg A` forced and the triangular solve complete.
* `linDE_degree_forced` — any solution has its degree fixed by `F` and `A`.
* `linDE_unsolvable_of_deg_lt` — `deg F < deg A` rules a solution out:
  the solver's `null` is a proof of non-existence, not a bound failure.
* `linDE_unique` — the kernel of `L` is trivial, so a constructed `T` is
  THE solution.
-/

variable {K : Type*} [Field K] [IsAddTorsionFree K]

/-- `A·T` dominates `D·T'` whenever `deg A ≥ deg D`. -/
theorem linDE_apply_natDegree (D A T : K[X]) (hT : T ≠ 0) (hA : A ≠ 0)
    (hdom : D.natDegree ≤ A.natDegree) :
    (D * T.derivative + A * T).natDegree = T.natDegree + A.natDegree := by
  have hAT : (A * T).natDegree = T.natDegree + A.natDegree := by
    rw [natDegree_mul hA hT, add_comm]
  by_cases hDT : D * T.derivative = 0
  · rw [hDT, zero_add]
    exact hAT
  · have hlt : (D * T.derivative).natDegree < (A * T).natDegree := by
      rw [hAT]
      have hDTn : (D * T.derivative).natDegree ≤
          D.natDegree + T.derivative.natDegree := natDegree_mul_le
      have hd : T.natDegree ≠ 0 := by
        intro h
        have hz : T.derivative = 0 := derivative_eq_zero.mpr h
        exact hDT (by rw [hz, mul_zero])
      have hder : T.derivative.natDegree < T.natDegree :=
        natDegree_derivative_lt hd
      omega
    exact (natDegree_add_eq_right_of_natDegree_lt hlt).trans hAT

/-- If `D·T' + A·T = F` has a solution `T ≠ 0`, then `deg F = deg T + deg A`. -/
theorem linDE_degree_forced (D A T F : K[X]) (hT : T ≠ 0) (hA : A ≠ 0)
    (hdom : D.natDegree ≤ A.natDegree)
    (h : D * T.derivative + A * T = F) :
    F.natDegree = T.natDegree + A.natDegree := by
  rw [← h]
  exact linDE_apply_natDegree D A T hT hA hdom

/-- `deg F < deg A` proves no polynomial `T` solves `D·T' + A·T = F`:
    the degree argument the solver's `null` verdict stands on. -/
theorem linDE_unsolvable_of_deg_lt (D A F : K[X]) (hF : F ≠ 0) (hA : A ≠ 0)
    (hdom : D.natDegree ≤ A.natDegree) (hlt : F.natDegree < A.natDegree) :
    ¬∃ T : K[X], D * T.derivative + A * T = F := by
  rintro ⟨T, hT⟩
  have hTz : T ≠ 0 := by
    rintro rfl
    simp at hT
    exact hF hT.symm
  have hdeg := linDE_degree_forced D A T F hTz hA hdom hT
  omega

/-- The kernel of `L(T) = D·T' + A·T` is trivial under the dominance
    hypothesis, so a constructed solution is unique: `linDESolve` cannot
    return the wrong polynomial. -/
theorem linDE_unique (D A : K[X]) (hA : A ≠ 0)
    (hdom : D.natDegree ≤ A.natDegree) {T U : K[X]}
    (h : D * T.derivative + A * T = D * U.derivative + A * U) : T = U := by
  by_contra hne
  have hS : T - U ≠ 0 := sub_ne_zero.mpr hne
  have hz : D * (T - U).derivative + A * (T - U) = 0 := by
    rw [derivative_sub]
    linear_combination h
  have hdeg := linDE_apply_natDegree D A (T - U) hS hA hdom
  rw [hz, natDegree_zero] at hdeg
  have hT0 : (T - U).natDegree = 0 := (Nat.add_eq_zero_iff.mp hdeg.symm).1
  have hA0 : A.natDegree = 0 := (Nat.add_eq_zero_iff.mp hdeg.symm).2
  have hdz : (T - U).derivative = 0 := derivative_eq_zero.mpr hT0
  rw [hdz, mul_zero, zero_add] at hz
  rcases mul_eq_zero.mp hz with hAz | hTz
  · exact hA hAz
  · exact hS hTz

end ISAR.RischDE
