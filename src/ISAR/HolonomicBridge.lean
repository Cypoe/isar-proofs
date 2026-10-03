import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import ISAR.PRecursive

/-!
# D-finite → P-recursive bridge (generating-function direction)

Stanley EC2 Theorem 6.4.6, one direction, stated coefficientwise:
if `f(x) = ∑ aₙ xⁿ` satisfies `∑_{i≤m} qᵢ(x) f⁽ⁱ⁾(x) = 0`, then
extracting the coefficient of `x^N` on both sides gives

    ∑ᵢ ∑_{j ≤ deg qᵢ} q_{i,j} · (N+i-j)↓ᵢ · a_{N+i-j} = 0

which, reindexed by `r = i - j`, is a linear recurrence on `a` with
polynomial coefficients — a P-recursion. This module:

1. defines the coefficientwise residual of a polynomial-coefficient ODE
   on a coefficient sequence (no analytic machinery needed — satisfaction
   of the ODE on the formal power series *is* the vanishing of every
   coefficient residual);
2. constructs the translated `PRecursiveCertificate`;
3. proves the residuals agree, so D-finite satisfaction implies
   P-recursive satisfaction for all sufficiently large indices.

The converse direction (P-recursive ⇒ D-finite, via the Euler operator
`θ = x d/dx`) is the future half of the bridge — it needs initial-term
truncation (`f - Σ_{k<r} aₖxᵏ`) inside the ODE construction.
-/

noncomputable section

open Polynomial

namespace ISAR

/-- Integer-indexed coefficient lookup: zero for negative degrees. -/
def zcoeff (p : ℚ[X]) (z : ℤ) : ℚ :=
  if z < 0 then 0 else p.coeff z.toNat

/-- The coefficient of `x^N` in `∑ᵢ qᵢ(x) f⁽ⁱ⁾(x)` for `f = ∑ aₙxⁿ`,
expressed on the coefficient sequence: `x^j f⁽ⁱ⁾` contributes
`(N+i-j)↓ᵢ a_{N+i-j}` at `x^N` (zero for `j > N`, which the
`descPochhammer` factor also yields when `0 ≤ N+i-j < i`). -/
def dfiniteResidual {m : ℕ} (q : Fin (m + 1) → ℚ[X]) (a : ℕ → ℚ)
    (N : ℕ) : ℚ :=
  ∑ i : Fin (m + 1),
    ∑ j ∈ Finset.range ((q i).natDegree + 1),
      (q i).coeff j * (descPochhammer ℚ i.val).eval
        ((N + i.val - j : ℕ) : ℚ) * a (N + i.val - j)

/-- Shift bound: `S = maxᵢ deg qᵢ`. Every recurrence shift `r = i - j`
satisfies `r ≥ -S`, and for `N ≥ S` every index `N + i - j` in the
coefficient residual is nonnegative. -/
def shiftBound {m : ℕ} (q : Fin (m + 1) → ℚ[X]) : ℕ :=
  Finset.univ.sup fun i => (q i).natDegree

/-- The `k`-th coefficient of the translated recurrence
(`k` indexes the `a_{n+k}` term): with `r = k - S`,

    p'_k(X) = ∑ᵢ q_{i, i-r} · (X + k)↓ᵢ

so `p'_k(n) = ∑ᵢ q_{i,i-r}(n + k)↓ᵢ` — exactly the coefficient of
`a_{N+r}` in the reindexed ODE residual at `N = n + S`. -/
def bridgePolyCoeffs {m : ℕ} (q : Fin (m + 1) → ℚ[X]) (k : ℕ) : ℚ[X] :=
  ∑ i : Fin (m + 1),
    C (zcoeff (q i) ((i : ℤ) - (k : ℤ) + shiftBound q)) *
      (descPochhammer ℚ i.val).comp (X + C (k : ℚ))

theorem bridgePolyCoeffs_eval {m : ℕ} (q : Fin (m + 1) → ℚ[X])
    (k n : ℕ) :
    (bridgePolyCoeffs q k).eval (n : ℚ) =
      ∑ i : Fin (m + 1),
        zcoeff (q i) ((i : ℤ) - (k : ℤ) + shiftBound q) *
          (descPochhammer ℚ i.val).eval ((n + k : ℕ) : ℚ) := by
  simp only [bridgePolyCoeffs, eval_finsetSum, eval_mul, eval_C,
    eval_comp, eval_add, eval_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp

variable {m : ℕ} (q : Fin (m + 1) → ℚ[X])

/-- For fixed `i`, the translated-coefficient inner sum over `k`
collapses to `j = i + S - k` ranging over the `deg qᵢ` coefficients —
terms outside have a zero `zcoeff` factor (negative index or degree
above `natDegree`). -/
theorem bridge_inner {a : ℕ → ℚ} {N : ℕ} (hN : shiftBound q ≤ N)
    (i : Fin (m + 1)) :
    ∑ k ∈ Finset.range (m + shiftBound q + 1),
        zcoeff (q i) ((i : ℤ) - (k : ℤ) + shiftBound q) *
          (descPochhammer ℚ i.val).eval
            ((N - shiftBound q + k : ℕ) : ℚ) * a (N - shiftBound q + k) =
      ∑ j ∈ Finset.range ((q i).natDegree + 1),
        (q i).coeff j *
          (descPochhammer ℚ i.val).eval ((N + i.val - j : ℕ) : ℚ) *
            a (N + i.val - j) := by
  classical
  set S := shiftBound q with hSq
  have hi : (i : ℕ) ≤ m := Nat.le_of_lt_succ i.isLt
  have hdeg : (q i).natDegree ≤ S := by
    rw [hSq]
    show (q i).natDegree ≤ Finset.univ.sup (fun j => (q j).natDegree)
    exact Finset.le_sup
      (f := fun j : Fin (m + 1) => (q j).natDegree) (Finset.mem_univ i)
  -- step 1: drop k > i + S (zcoeff index negative → term zero)
  have step1 :
      ∑ k ∈ Finset.range (i + S + 1),
          zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) *
            (descPochhammer ℚ i.val).eval ((N - S + k : ℕ) : ℚ) *
              a (N - S + k) =
        ∑ k ∈ Finset.range (m + S + 1),
          zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) *
            (descPochhammer ℚ i.val).eval ((N - S + k : ℕ) : ℚ) *
              a (N - S + k) := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k hkR hkN
      simp only [Finset.mem_range] at hkR hkN
      have hz : zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) = 0 := by
        unfold zcoeff
        apply if_pos
        omega
      rw [hz]
      simp
  rw [← step1]
  -- step 2: drop k < i + S - deg (coefficient index above natDegree)
  have step2 :
      ∑ k ∈ Finset.Ico (i + S - (q i).natDegree) (i + S + 1),
          zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) *
            (descPochhammer ℚ i.val).eval ((N - S + k : ℕ) : ℚ) *
              a (N - S + k) =
        ∑ k ∈ Finset.range (i + S + 1),
          zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) *
            (descPochhammer ℚ i.val).eval ((N - S + k : ℕ) : ℚ) *
              a (N - S + k) := by
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Ico] at hk
      exact Finset.mem_range.mpr hk.2
    · intro k hkR hkN
      rw [Finset.mem_range] at hkR
      have hlt : k < i + S - (q i).natDegree := by
        by_contra hc
        exact hkN (Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt hc, hkR⟩)
      have hz : zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) = 0 := by
        unfold zcoeff
        rw [if_neg (by omega)]
        apply coeff_eq_zero_of_natDegree_lt
        have hcast : ((i + S - k : ℕ) : ℤ) = (i : ℤ) - (k : ℤ) + (S : ℤ) := by
          zify [show k ≤ i + S by omega]
          ring
        rw [← hcast, Int.toNat_natCast]
        omega
      rw [hz]
      simp
  rw [← step2]
  -- bijection: j = i + S - k maps Ico(i+S-deg, i+S+1) → range(deg+1)
  apply Finset.sum_bij (fun k _ => (i : ℕ) + S - k)
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k₁ hk₁ k₂ hk₂ h
    obtain ⟨_, hk1u⟩ := Finset.mem_Ico.mp hk₁
    obtain ⟨_, hk2u⟩ := Finset.mem_Ico.mp hk₂
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    refine ⟨(i : ℕ) + S - j, ?_, ?_⟩
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · omega
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have hkS : k ≤ (i : ℕ) + S := by omega
    have hz : zcoeff (q i) ((i : ℤ) - (k : ℤ) + (S : ℤ)) =
        (q i).coeff ((i : ℕ) + S - k) := by
      unfold zcoeff
      rw [if_neg (by omega)]
      have hcast : ((i : ℤ) - (k : ℤ) + (S : ℤ)) =
          (((i : ℕ) + S - k : ℕ) : ℤ) := by
        zify [hkS]
        ring
      rw [hcast, Int.toNat_natCast]
    have hnat : (i : ℕ) + S - ((i : ℕ) + S - k) = k := by omega
    have hN' : N + i.val - ((i : ℕ) + S - k) = N - S + k := by omega
    rw [hz, hN']

/-- **The bridge identity**: for `N ≥ S`, the coefficientwise ODE residual
at `x^N` equals the translated P-recursive residual at `n = N - S`. -/
theorem dfiniteResidual_eq_bridge {a : ℕ → ℚ} {N : ℕ}
    (hN : shiftBound q ≤ N) :
    dfiniteResidual q a N =
      ∑ k ∈ Finset.range (m + shiftBound q + 1),
        (bridgePolyCoeffs q k).eval ((N - shiftBound q : ℕ) : ℚ) *
          a (N - shiftBound q + k) := by
  unfold dfiniteResidual
  have hexp : ∀ k ∈ Finset.range (m + shiftBound q + 1),
      (bridgePolyCoeffs q k).eval ((N - shiftBound q : ℕ) : ℚ) *
          a (N - shiftBound q + k) =
        ∑ i : Fin (m + 1),
          zcoeff (q i) ((i : ℤ) - (k : ℤ) + shiftBound q) *
            (descPochhammer ℚ i.val).eval
              ((N - shiftBound q + k : ℕ) : ℚ) *
              a (N - shiftBound q + k) := by
    intro k _
    rw [bridgePolyCoeffs_eval, Finset.sum_mul]
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_comm (s := Finset.range (m + shiftBound q + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (bridge_inner q hN i).symm

/-- The translated certificate: order `m + S`, coefficients
`bridgePolyCoeffs`. `leading_ne` holds exactly when `q_order` has a
nonzero constant term — the residual identity itself needs no such
hypothesis; only packaging it as a `PRecursiveCertificate` does. -/
def toPRecursiveCertificate {m : ℕ} (q : Fin (m + 1) → ℚ[X])
    (h0 : (q (Fin.last m)).coeff 0 ≠ 0) : PRecursiveCertificate where
  order := m + shiftBound q
  coeffs := fun k => bridgePolyCoeffs q k.val
  leading_ne := by
    show bridgePolyCoeffs q (m + shiftBound q) ≠ 0
    unfold bridgePolyCoeffs
    have honly :
        ∑ i : Fin (m + 1),
            C (zcoeff (q i)
                ((i : ℤ) - ((m + shiftBound q : ℕ) : ℤ) + shiftBound q)) *
              (descPochhammer ℚ i.val).comp
                (X + C ((m + shiftBound q : ℕ) : ℚ)) =
          C ((q (Fin.last m)).coeff 0) *
            (descPochhammer ℚ m).comp
              (X + C ((m + shiftBound q : ℕ) : ℚ)) := by
      rw [Finset.sum_eq_single (Fin.last m)]
      · congr 2
        unfold zcoeff
        rw [show ((Fin.last m : ℕ) : ℤ) - ((m + shiftBound q : ℕ) : ℤ) +
              (shiftBound q : ℤ) = 0 by
          rw [Fin.val_last]; push_cast; ring]
        simp
      · intro i _ hi
        have him : (i : ℕ) < m := by
          have hne : (i : ℕ) ≠ m := by
            intro h
            exact hi (Fin.ext (by rw [Fin.val_last]; exact h))
          omega
        have hz : zcoeff (q i)
            ((i : ℤ) - ((m + shiftBound q : ℕ) : ℤ) +
              (shiftBound q : ℤ)) = 0 := by
          unfold zcoeff
          apply if_pos
          omega
        rw [hz, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [honly]
    apply mul_ne_zero
    · simpa using h0
    · exact ((monic_descPochhammer ℚ m).comp_X_add_C _).ne_zero

/-- **Bridge soundness**: if every coefficient residual of the ODE
vanishes for `N ≥ S` (the D-finite hypothesis on `f = ∑ aₙxⁿ`), the
coefficient sequence satisfies the translated recurrence — the
generating-function direction of `D-finite ↔ P-recursive`. -/
theorem satisfiesRecurrence_of_dfinite {a : ℕ → ℚ}
    (h0 : (q (Fin.last m)).coeff 0 ≠ 0)
    (h : ∀ N : ℕ, shiftBound q ≤ N → dfiniteResidual q a N = 0) :
    satisfiesRecurrence (toPRecursiveCertificate q h0) a := by
  intro n
  have hN : shiftBound q ≤ n + shiftBound q := Nat.le_add_left _ _
  have hid := dfiniteResidual_eq_bridge q (a := a)
    (N := n + shiftBound q) hN
  rw [show n + shiftBound q - shiftBound q = n by omega] at hid
  rw [h (n + shiftBound q) hN] at hid
  have hres : (toPRecursiveCertificate q h0).residual a n =
      ∑ k ∈ Finset.range (m + shiftBound q + 1),
        (bridgePolyCoeffs q k).eval (n : ℚ) * a (n + k) := by
    unfold PRecursiveCertificate.residual
    rw [Finset.sum_fin_eq_sum_range
      (fun i : Fin ((toPRecursiveCertificate q h0).order + 1) =>
        ((toPRecursiveCertificate q h0).coeffs i).eval (n : ℚ) *
          a (n + i.val))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [dif_pos (show k < (toPRecursiveCertificate q h0).order + 1 from
      Finset.mem_range.mp hk)]
    rfl
  rw [hres]
  exact hid.symm

end ISAR
