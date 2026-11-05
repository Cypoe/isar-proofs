import ISAR.HolonomicClosure
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.ENat.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

open scoped ContDiff RatFunc

/-!
# General holonomic closure — arbitrary orders

Mirrors the general `certClosure` path in `koru_std/sym.certcomp.kz`
(the linear-algebraic elimination over the jet space that the zig side
runs for arbitrary input orders), upgrading the order-1 special cases
in `HolonomicClosure.lean` to the general bounds:

* sum closure: order `≤ m + n`,
* product closure: order `≤ m · n`.

The proof is the classical one: powers of each leading coefficient
`L` clear every derivative `f⁽ᵒ⁺ᵏ⁾` into the finite jet
`{f⁽ⁱ⁾ | i < o}` (`lead_pow_mul_iteratedDeriv`), so the candidate
derivatives of `f + g` (resp. `f · g`, via Leibniz) all live in an
`m + n`-dimensional (resp. `m · n`-dimensional) vector space over
`FractionRing ℝ[X]`. `m + n + 1` (resp. `m·n + 1`) vectors are
dependent, and clearing denominators yields a genuine polynomial
certificate.
-/

noncomputable section

open Polynomial Classical

open scoped ContDiff

namespace ISAR

/-- The leading coefficient `p_order` of a certificate. -/
noncomputable def HolonomicCertificate.lead (c : HolonomicCertificate) : ℝ[X] :=
  c.coeffs ⟨c.order, Nat.lt_succ_self _⟩

theorem HolonomicCertificate.lead_ne (c : HolonomicCertificate) : c.lead ≠ 0 :=
  c.leading_ne

/-- The `i`-th coefficient of a certificate, extended by `0` out of range. -/
noncomputable def HolonomicCertificate.coeffAt (c : HolonomicCertificate) (i : ℕ) : ℝ[X] :=
  if h : i < c.order + 1 then c.coeffs ⟨i, h⟩ else 0

/-- The complement of a finite set of reals is dense. -/
private theorem dense_compl_finset (F : Finset ℝ) : Dense ((F : Set ℝ)ᶜ) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F _ ih =>
    rw [Finset.coe_insert, Set.insert_eq, Set.compl_union]
    exact (dense_compl_singleton a).inter_of_isOpen_right ih
      (isOpen_compl_iff.mpr F.finite_toSet.isClosed)

/-- A continuous function vanishing off a finite set vanishes everywhere. -/
private theorem eq_zero_of_continuous_eq_zero_off {r : ℝ → ℝ} (hr : Continuous r)
    {F : Finset ℝ} (h : ∀ x ∉ (F : Set ℝ), r x = 0) : ∀ x, r x = 0 := by
  have hcl : IsClosed {x : ℝ | r x = 0} := isClosed_eq hr continuous_const
  have hsub : closure ((F : Set ℝ)ᶜ) ⊆ {x : ℝ | r x = 0} :=
    hcl.closure_subset_iff.mpr h
  rw [(dense_compl_finset F).closure_eq] at hsub
  exact fun x => hsub (Set.mem_univ x)

/-- A continuous function annihilated by a nonzero polynomial is identically zero. -/
private theorem eq_zero_of_poly_mul_eq_zero {p : ℝ[X]} {f : ℝ → ℝ}
    (hp : p ≠ 0) (hf : Continuous f) (h : ∀ x, p.eval x * f x = 0) : ∀ x, f x = 0 := by
  refine eq_zero_of_continuous_eq_zero_off hf (F := p.roots.toFinset) fun x hx => ?_
  have hxp : p.eval x ≠ 0 := fun hpx => hx
    (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hpx))
  exact (mul_eq_zero.mp (h x)).resolve_left hxp

/-- The ODE at its top order: `L · f⁽ᵒ⁾ = -∑_{i<o} pᵢ · f⁽ⁱ⁾` pointwise. -/
private theorem lead_mul_iteratedDeriv_order {c : HolonomicCertificate}
    {f : ℝ → ℝ} (hf : satisfiesODE c f) (x : ℝ) :
    c.lead.eval x * iteratedDeriv c.order f x
      = -∑ i ∈ Finset.range c.order, (c.coeffAt i).eval x * iteratedDeriv i f x := by
  have hr := hf x
  unfold HolonomicCertificate.residual at hr
  rw [Fin.sum_univ_castSucc] at hr
  have h := eq_neg_of_add_eq_zero_left hr
  have h2 : c.lead.eval x * iteratedDeriv c.order f x
      = -(∑ i : Fin c.order,
          (c.coeffs i.castSucc).eval x * iteratedDeriv i.val f x) := by
    have hlast : (c.coeffs (Fin.last c.order)).eval x
          * iteratedDeriv (Fin.last c.order).val f x
        = c.lead.eval x * iteratedDeriv c.order f x := by
      rw [Fin.val_last]
      rfl
    have := congrArg Neg.neg h.symm
    rw [neg_neg] at this
    exact hlast ▸ this
  rw [h2]; congr 1
  trans (∑ i : Fin c.order,
    ((fun j : ℕ => (c.coeffAt j).eval x * iteratedDeriv j f x) i.val))
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hcoef : c.coeffs i.castSucc = c.coeffAt i.val := by
      rw [show i.castSucc = ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ from Fin.ext rfl]
      unfold HolonomicCertificate.coeffAt
      rw [dif_pos (Nat.lt_succ_of_lt i.isLt)]
    rw [hcoef]
  · exact Fin.sum_univ_eq_sum_range
      (fun j => (c.coeffAt j).eval x * iteratedDeriv j f x) c.order

/-- **Jet reduction**: powers of the leading coefficient clear every higher
derivative into the finite jet `{f⁽ⁱ⁾ | i < order}`, with polynomial
coefficients.  All-polynomial (cleared-denominator) form of reduction mod the
ODE. -/
theorem satisfiesODE.lead_pow_mul_iteratedDeriv {c : HolonomicCertificate}
    {f : ℝ → ℝ} (hdf : ContDiff ℝ ∞ f) (hf : satisfiesODE c f) (m : ℕ) :
    ∃ q : ℕ → ℝ[X], ∀ x,
      c.lead.eval x ^ (m + 1) * iteratedDeriv (c.order + m) f x
        = ∑ i ∈ Finset.range c.order, (q i).eval x * iteratedDeriv i f x := by
  rcases Nat.eq_zero_or_pos c.order with ho | ho
  · -- Order 0: `L·f = 0` with `L ≠ 0` forces `f ≡ 0`; the jet is empty.
    have hpf : ∀ x, c.lead.eval x * f x = 0 := by
      intro x
      have hr := hf x
      have hsum : c.residual f x
          = ∑ i ∈ Finset.range (c.order + 1),
              (c.coeffAt i).eval x * iteratedDeriv i f x := by
        unfold HolonomicCertificate.residual
        trans (∑ i : Fin (c.order + 1),
          ((fun j : ℕ => (c.coeffAt j).eval x * iteratedDeriv j f x) i.val))
        · refine Finset.sum_congr rfl fun i _ => ?_
          simp only [HolonomicCertificate.coeffAt, dif_pos i.isLt]
        · exact Fin.sum_univ_eq_sum_range
            (fun j => (c.coeffAt j).eval x * iteratedDeriv j f x) (c.order + 1)
      rw [hsum, show c.order + 1 = 1 from by omega, Finset.sum_range_one] at hr
      rw [iteratedDeriv_zero] at hr
      have hfin : (⟨0, Nat.zero_lt_succ _⟩ : Fin (c.order + 1))
          = ⟨c.order, Nat.lt_succ_self _⟩ := Fin.ext (by simp [ho])
      have hc0 : c.coeffAt 0 = c.lead := by
        simp only [HolonomicCertificate.coeffAt, HolonomicCertificate.lead]
        rw [dif_pos (Nat.zero_lt_succ _)]
        exact congrArg c.coeffs hfin
      rw [hc0] at hr
      exact hr
    have hzero := eq_zero_of_poly_mul_eq_zero c.lead_ne hdf.continuous hpf
    refine ⟨fun _ => 0, fun x => ?_⟩
    have h0 : f = 0 := funext hzero
    simp [ho, h0, iteratedDeriv_const_zero]
  induction m with
  | zero =>
    refine ⟨fun i => -(c.coeffAt i), fun x => ?_⟩
    have h := lead_mul_iteratedDeriv_order hf x
    calc c.lead.eval x ^ (0 + 1) * iteratedDeriv (c.order + 0) f x
        = c.lead.eval x * iteratedDeriv c.order f x := by simp
      _ = -∑ i ∈ Finset.range c.order,
          (c.coeffAt i).eval x * iteratedDeriv i f x := h
      _ = ∑ i ∈ Finset.range c.order, (-(c.coeffAt i)).eval x * iteratedDeriv i f x := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [eval_neg, neg_mul]
  | succ m ih =>
    obtain ⟨q, hq⟩ := ih
    have hmn : ∀ k : ℕ, (k : WithTop ℕ∞) < ∞ :=
      fun _ => compareOfLessAndEq_eq_lt.mp rfl
    have hdiff : deriv (fun x =>
          c.lead.eval x ^ (m + 1) * iteratedDeriv (c.order + m) f x)
        = deriv (fun x => ∑ i ∈ Finset.range c.order,
            (q i).eval x * iteratedDeriv i f x) := by
      congr 1; funext x; exact hq x
    have hL : ∀ x, deriv (fun y =>
          c.lead.eval y ^ (m + 1) * iteratedDeriv (c.order + m) f y) x
        = (↑(m + 1) : ℝ) * c.lead.eval x ^ m * c.lead.derivative.eval x
            * iteratedDeriv (c.order + m) f x
          + c.lead.eval x ^ (m + 1) * iteratedDeriv (c.order + m + 1) f x := by
      intro x
      have hf1 : DifferentiableAt ℝ (fun y => c.lead.eval y ^ (m + 1)) x :=
        (c.lead.differentiableAt).pow _
      have hf2 : DifferentiableAt ℝ (iteratedDeriv (c.order + m) f) x :=
        (hdf.differentiable_iteratedDeriv _ (hmn _)) x
      have hp : HasDerivAt (fun y => c.lead.eval y ^ (m + 1))
          (↑(m + 1) * c.lead.eval x ^ (m + 1 - 1) * c.lead.derivative.eval x) x :=
        (c.lead.hasDerivAt x).pow (m + 1)
      rw [deriv_fun_mul hf1 hf2, hp.deriv, Nat.add_sub_cancel,
        ← iteratedDeriv_succ]
    have hR : ∀ x, deriv (fun y => ∑ i ∈ Finset.range c.order,
          (q i).eval y * iteratedDeriv i f y) x
        = ∑ i ∈ Finset.range c.order,
          ((q i).derivative.eval x * iteratedDeriv i f x
            + (q i).eval x * iteratedDeriv (i + 1) f x) := by
      intro x
      rw [deriv_fun_sum fun i _ =>
        show DifferentiableAt ℝ (fun y => (q i).eval y * iteratedDeriv i f y) x
          from ((q i).differentiableAt).mul
            ((hdf.differentiable_iteratedDeriv i (hmn i)) x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [deriv_fun_mul ((q i).differentiableAt)
        ((hdf.differentiable_iteratedDeriv i (hmn i)) x),
        ((q i).hasDerivAt x).deriv, ← iteratedDeriv_succ]
    refine ⟨fun j =>
        c.lead * (q j).derivative
          + (if j = 0 then 0 else c.lead * q (j - 1))
          - q (c.order - 1) * c.coeffAt j
          - C ((m + 1 : ℕ) : ℝ) * c.lead.derivative * q j,
      fun x => ?_⟩
    have hE := congrFun hdiff x
    rw [hL x, hR x] at hE
    have hbase := lead_mul_iteratedDeriv_order hf x
    -- From hE, multiply by `L` and substitute the IH and the base relation.
    have step1 : c.lead.eval x ^ (m + 1 + 1) * iteratedDeriv (c.order + (m + 1)) f x
        = c.lead.eval x * (∑ i ∈ Finset.range c.order,
            ((q i).derivative.eval x * iteratedDeriv i f x
              + (q i).eval x * iteratedDeriv (i + 1) f x))
          - (↑(m + 1) : ℝ) * c.lead.derivative.eval x
              * ∑ i ∈ Finset.range c.order, (q i).eval x * iteratedDeriv i f x := by
      have h1 : c.lead.eval x ^ (m + 1) * iteratedDeriv (c.order + m + 1) f x
          = (∑ i ∈ Finset.range c.order,
              ((q i).derivative.eval x * iteratedDeriv i f x
                + (q i).eval x * iteratedDeriv (i + 1) f x))
            - (↑(m + 1) : ℝ) * c.lead.eval x ^ m * c.lead.derivative.eval x
                * iteratedDeriv (c.order + m) f x := by
        linear_combination hE
      calc c.lead.eval x ^ (m + 1 + 1) * iteratedDeriv (c.order + (m + 1)) f x
          = c.lead.eval x * (c.lead.eval x ^ (m + 1)
              * iteratedDeriv (c.order + m + 1) f x) := by ring
        _ = c.lead.eval x * ((∑ i ∈ Finset.range c.order,
              ((q i).derivative.eval x * iteratedDeriv i f x
                + (q i).eval x * iteratedDeriv (i + 1) f x))
            - (↑(m + 1) : ℝ) * c.lead.eval x ^ m * c.lead.derivative.eval x
                * iteratedDeriv (c.order + m) f x) := by rw [h1]
        _ = _ := by
            rw [mul_sub]
            congr 1
            have h2 := hq x
            linear_combination (↑(m + 1) : ℝ) * c.lead.derivative.eval x * h2
    -- The shifted part reindexed into the jet coordinates.
    have shifted : ∑ i ∈ Finset.range c.order,
          c.lead.eval x * ((q i).eval x * iteratedDeriv (i + 1) f x)
        = ∑ j ∈ Finset.range c.order,
            ((if j = 0 then 0 else c.lead * q (j - 1))
              - q (c.order - 1) * c.coeffAt j).eval x * iteratedDeriv j f x := by
      obtain ⟨n, hn⟩ : ∃ n, c.order = n + 1 := ⟨c.order - 1, by omega⟩
      rw [hn] at hbase ⊢
      simp only [Nat.add_sub_cancel]
      rw [Finset.sum_range_succ]
      have hlast : c.lead.eval x * ((q n).eval x * iteratedDeriv (n + 1) f x)
          = -(q n).eval x * ∑ j ∈ Finset.range (n + 1),
              (c.coeffAt j).eval x * iteratedDeriv j f x := by
        linear_combination (q n).eval x * hbase
      rw [hlast]
      -- Reindex `Σ_{i<n} L·qᵢ·f⁽ⁱ⁺¹⁾` as `Σ_{j<n+1} Sⱼ·f⁽ʲ⁾`.
      have hre : ∑ j ∈ Finset.range (n + 1),
            (if j = 0 then (0 : ℝ) else (c.lead * q (j - 1)).eval x)
              * iteratedDeriv j f x
          = ∑ i ∈ Finset.range n,
              c.lead.eval x * ((q i).eval x * iteratedDeriv (i + 1) f x) := by
        rw [Finset.sum_range_succ']
        have hg0 : (if (0 : ℕ) = 0 then (0 : ℝ) else (c.lead * q (0 - 1)).eval x)
            * iteratedDeriv 0 f x = 0 := by
          show (0 : ℝ) * iteratedDeriv 0 f x = 0
          rw [zero_mul]
        rw [hg0, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, eval_mul, mul_assoc]
      -- Factor `qₙ` out of its coefficient sum.
      have hqn : ∑ j ∈ Finset.range (n + 1),
            (q n * c.coeffAt j).eval x * iteratedDeriv j f x
          = (q n).eval x * ∑ j ∈ Finset.range (n + 1),
              (c.coeffAt j).eval x * iteratedDeriv j f x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [eval_mul, mul_assoc]
      -- Split the RHS summand so `sum_sub_distrib` can fire.
      have hsplit : ∀ j ∈ Finset.range (n + 1),
          (((if j = 0 then (0 : ℝ[X]) else c.lead * q (j - 1))
              - q n * c.coeffAt j).eval x * iteratedDeriv j f x)
          = (if j = 0 then (0 : ℝ) else (c.lead * q (j - 1)).eval x)
              * iteratedDeriv j f x
            - (q n * c.coeffAt j).eval x * iteratedDeriv j f x := by
        intro j _
        rw [eval_sub, sub_mul, apply_ite (fun p : ℝ[X] => p.eval x), eval_zero]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← hre, hqn,
        neg_mul, sub_eq_add_neg]
    -- Distribute `L` over the differentiated sum, reindex via `shifted`.
    have hdis : ∑ i ∈ Finset.range c.order,
          c.lead.eval x * ((q i).derivative.eval x * iteratedDeriv i f x
            + (q i).eval x * iteratedDeriv (i + 1) f x)
        = ∑ i ∈ Finset.range c.order,
            c.lead.eval x * ((q i).derivative.eval x * iteratedDeriv i f x)
          + ∑ i ∈ Finset.range c.order,
            c.lead.eval x * ((q i).eval x * iteratedDeriv (i + 1) f x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => mul_add _ _ _
    -- The `(m+1)·L'` coefficient sum factors out.
    have hmc : ∑ j ∈ Finset.range c.order,
          (C ((m + 1 : ℕ) : ℝ) * c.lead.derivative * q j).eval x
            * iteratedDeriv j f x
        = (↑(m + 1) : ℝ) * c.lead.derivative.eval x
            * ∑ j ∈ Finset.range c.order, (q j).eval x * iteratedDeriv j f x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [eval_mul]
      ring
    -- Convert each RHS coefficient to the real-evaluated pieces.
    have hconv : ∀ j ∈ Finset.range c.order,
        ((c.lead * (q j).derivative
            + (if j = 0 then (0 : ℝ[X]) else c.lead * q (j - 1))
            - q (c.order - 1) * c.coeffAt j
            - C ((m + 1 : ℕ) : ℝ) * c.lead.derivative * q j).eval x
              * iteratedDeriv j f x)
        = ((c.lead * (q j).derivative).eval x * iteratedDeriv j f x
            + ((if j = 0 then (0 : ℝ[X]) else c.lead * q (j - 1))
                - q (c.order - 1) * c.coeffAt j).eval x * iteratedDeriv j f x)
          - (C ((m + 1 : ℕ) : ℝ) * c.lead.derivative * q j).eval x
              * iteratedDeriv j f x := by
      intro j _
      simp only [eval_add, eval_sub, eval_mul]
      ring
    have hcong : ∑ i ∈ Finset.range c.order,
          c.lead.eval x * ((q i).derivative.eval x * iteratedDeriv i f x)
        = ∑ i ∈ Finset.range c.order,
            (c.lead * (q i).derivative).eval x * iteratedDeriv i f x :=
      Finset.sum_congr rfl fun i _ => by
        rw [eval_mul, mul_assoc]
    rw [step1, Finset.mul_sum, hdis, shifted, Finset.sum_congr rfl hconv,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hmc, hcong]

/-! ### Stage 2 — linear dependence over `ℝ(X)` and denominator clearing

The jet lemma gives, for each `k ≥ order`, a `ℝ(X)`-coordinate expression
`f⁽ᵏ⁾ = Σᵢ (qᵢ/L^r)·f⁽ⁱ⁾` valid wherever `L(x) ≠ 0`.  `m + n + 1` candidate
derivatives of `f + g` thus land in an `(m+n)`-dimensional `ℝ(X)`-space, so a
nontrivial relation exists; clearing its denominators and extending by
continuity off the (finite) bad set yields the polynomial-coefficient
certificate of order `≤ m + n`. -/

/-- Evaluation of a `p/q`-shaped element of `ℝ(X)` agrees with `p.eval/q.eval`
wherever `q` does not vanish (the normalised denominator divides `q`). -/
private theorem ratFunc_eval_div {x : ℝ} (p q : ℝ[X]) (hq : q.eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℝ) x
        (algebraMap ℝ[X] ℝ⟮X⟯ p / algebraMap ℝ[X] ℝ⟮X⟯ q) = p.eval x / q.eval x := by
  have hq0 : q ≠ 0 := fun h => hq (by rw [h]; simp)
  have haq : (algebraMap ℝ[X] ℝ⟮X⟯ q : ℝ⟮X⟯) ≠ 0 := RatFunc.algebraMap_ne_zero hq0
  have hdq : (RatFunc.denom (algebraMap ℝ[X] ℝ⟮X⟯ q)).eval₂ (RingHom.id ℝ) x ≠ 0 := by
    rw [RatFunc.denom_algebraMap]; simp
  have hdpq : (RatFunc.denom
      (algebraMap ℝ[X] ℝ⟮X⟯ p / algebraMap ℝ[X] ℝ⟮X⟯ q)).eval₂ (RingHom.id ℝ) x
      ≠ 0 :=
    fun h => hq (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℝ) x
      (RatFunc.denom_div_dvd p q) h)
  have hmul := RatFunc.eval_mul (f := RingHom.id ℝ) (a := x) hdpq hdq
  rw [div_mul_cancel₀ _ haq] at hmul
  have hap : RatFunc.eval (RingHom.id ℝ) x (algebraMap ℝ[X] ℝ⟮X⟯ p)
      = p.eval x := by
    rw [RatFunc.eval_algebraMap]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.eval₂_id]
  have haqe : RatFunc.eval (RingHom.id ℝ) x (algebraMap ℝ[X] ℝ⟮X⟯ q)
      = q.eval x := by
    rw [RatFunc.eval_algebraMap]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.eval₂_id]
  rw [hap, haqe] at hmul
  exact (eq_div_iff_mul_eq hq).mpr hmul.symm

private theorem ratFunc_denom_sum_dvd {ι : Type*} (s : Finset ι) (g : ι → ℝ⟮X⟯) :
    RatFunc.denom (∑ i ∈ s, g i) ∣ ∏ i ∈ s, RatFunc.denom (g i) := by
  refine s.induction_on (by simp [RatFunc.denom_zero]) fun a s has ih => ?_
  rw [Finset.sum_insert has, Finset.prod_insert has]
  exact (RatFunc.denom_add_dvd _ _).trans (mul_dvd_mul_left _ ih)

/-- `RatFunc.eval` distributes over a finite sum whenever every summand's
denominator is nonzero at the evaluation point. -/
private theorem ratFunc_eval_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ⟮X⟯) {x : ℝ}
    (h : ∀ i ∈ s, (RatFunc.denom (g i)).eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℝ) x (∑ i ∈ s, g i)
      = ∑ i ∈ s, RatFunc.eval (RingHom.id ℝ) x (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hsub : ∀ i ∈ s, (RatFunc.denom (g i)).eval x ≠ 0 :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hds : (RatFunc.denom (∑ i ∈ s, g i)).eval₂ (RingHom.id ℝ) x ≠ 0 := by
      intro hz
      have h0 := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℝ) x
        (ratFunc_denom_sum_dvd s g) hz
      rw [Polynomial.eval₂_id, Polynomial.eval_prod] at h0
      exact (Finset.prod_ne_zero_iff.mpr fun i hi => hsub i hi) h0
    rw [Finset.sum_insert has,
      RatFunc.eval_add (RingHom.id ℝ) x (h a (Finset.mem_insert_self a s)) hds,
      ih hsub, Finset.sum_insert has]

/-- `ℝ(X)`-coordinates of `f⁽ᵏ⁾` in the `{f⁽ⁱ⁾ | i < order}` jet basis:
the basis vector `eₖ` for `k < order`, and the `qᵢ/L^{k-order+1}` reduction
otherwise.  `q` is the family produced by `lead_pow_mul_iteratedDeriv`. -/
private def jetCoord (c : HolonomicCertificate) (q : ℕ → ℕ → ℝ[X]) (k : ℕ) :
    Fin c.order → ℝ⟮X⟯ :=
  fun i => if k < c.order then (if k = i.val then (1 : ℝ⟮X⟯) else 0)
    else algebraMap ℝ[X] ℝ⟮X⟯ (q (k - c.order) i.val) /
      algebraMap ℝ[X] ℝ⟮X⟯ (c.lead ^ (k - c.order + 1))

/-- Pointwise expansion of `f⁽ᵏ⁾` in the jet basis, valid wherever `L ≠ 0`. -/
private theorem jetCoord_apply {c : HolonomicCertificate} {f : ℝ → ℝ}
    (q : ℕ → ℕ → ℝ[X])
    (hq : ∀ r x, c.lead.eval x ^ (r + 1) * iteratedDeriv (c.order + r) f x
        = ∑ i ∈ Finset.range c.order, (q r i).eval x * iteratedDeriv i f x)
    {x : ℝ} (hx : c.lead.eval x ≠ 0) (k : ℕ) :
    iteratedDeriv k f x
      = ∑ i : Fin c.order, RatFunc.eval (RingHom.id ℝ) x (jetCoord c q k i)
          * iteratedDeriv i.val f x := by
  rcases lt_or_ge k c.order with h | h
  · -- `k < order`: `jetCoord` is the `k`-th basis vector.
    symm
    calc ∑ i : Fin c.order, RatFunc.eval (RingHom.id ℝ) x (jetCoord c q k i)
            * iteratedDeriv i.val f x
        = ∑ i : Fin c.order, (if i = (⟨k, h⟩ : Fin c.order) then (1 : ℝ) else 0)
            * iteratedDeriv i.val f x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold jetCoord
          by_cases hi : i = (⟨k, h⟩ : Fin c.order)
          · have hi' : k = i.val := (congrArg Fin.val hi).symm
            rw [if_pos h, if_pos hi', RatFunc.eval_one, one_mul, if_pos hi, one_mul]
          · have hi' : k ≠ i.val := fun hkk => hi (Fin.ext hkk.symm)
            rw [if_pos h, if_neg hi', RatFunc.eval_zero, zero_mul, if_neg hi, zero_mul]
        _ = ∑ i : Fin c.order, if i = (⟨k, h⟩ : Fin c.order)
            then iteratedDeriv i.val f x else 0 :=
          Finset.sum_congr rfl fun i _ => by by_cases hi : i = ⟨k, h⟩ <;> simp [hi]
        _ = iteratedDeriv (⟨k, h⟩ : Fin c.order).val f x := by simp
        _ = iteratedDeriv k f x := rfl
  · -- `k ≥ order`: the `q/L^r` reduction, divided through on `{L ≠ 0}`.
    have hL : c.lead.eval x ^ (k - c.order + 1) ≠ 0 := pow_ne_zero _ hx
    have hL' : (c.lead ^ (k - c.order + 1)).eval x ≠ 0 := by
      rw [Polynomial.eval_pow]; exact hL
    calc iteratedDeriv k f x
        = iteratedDeriv (c.order + (k - c.order)) f x := by rw [Nat.add_sub_cancel' h]
      _ = (c.lead.eval x ^ (k - c.order + 1))⁻¹
            * ∑ i ∈ Finset.range c.order, (q (k - c.order) i).eval x
                * iteratedDeriv i f x := by
          rw [← hq _ _, inv_mul_cancel_left₀ hL]
      _ = ∑ i ∈ Finset.range c.order,
            ((q (k - c.order) i).eval x / c.lead.eval x ^ (k - c.order + 1))
              * iteratedDeriv i f x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
      _ = ∑ i ∈ Finset.range c.order,
            RatFunc.eval (RingHom.id ℝ) x
              (algebraMap ℝ[X] ℝ⟮X⟯ (q (k - c.order) i)
                / algebraMap ℝ[X] ℝ⟮X⟯ (c.lead ^ (k - c.order + 1)))
              * iteratedDeriv i f x := by
          exact Finset.sum_congr rfl fun i _ => by
            rw [ratFunc_eval_div _ _ hL', ← Polynomial.eval_pow]
      _ = ∑ i : Fin c.order, RatFunc.eval (RingHom.id ℝ) x (jetCoord c q k i)
            * iteratedDeriv i.val f x := by
          rw [← Fin.sum_univ_eq_sum_range
            (fun j => RatFunc.eval (RingHom.id ℝ) x
              (algebraMap ℝ[X] ℝ⟮X⟯ (q (k - c.order) j)
                / algebraMap ℝ[X] ℝ⟮X⟯ (c.lead ^ (k - c.order + 1)))
              * iteratedDeriv j f x) c.order]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold jetCoord
          rw [if_neg (not_lt.mpr h)]

private theorem denom_eval_ne_zero_of_dvd {r : ℝ⟮X⟯} {q : ℝ[X]} {x : ℝ}
    (hd : RatFunc.denom r ∣ q) (hq : q.eval x ≠ 0) :
    (RatFunc.denom r).eval x ≠ 0 := fun h => hq (by
    obtain ⟨s, rfl⟩ := hd
    rw [Polynomial.eval_mul, h, zero_mul])

private theorem denom_mul_eval_ne_zero {r s : ℝ⟮X⟯} {x : ℝ}
    (hr : (RatFunc.denom r).eval x ≠ 0) (hs : (RatFunc.denom s).eval x ≠ 0) :
    (RatFunc.denom (r * s)).eval x ≠ 0 :=
  denom_eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd _ _)
    (by rw [Polynomial.eval_mul]; exact mul_ne_zero hr hs)

private theorem denom_jetCoord_ne_zero {c : HolonomicCertificate}
    {q : ℕ → ℕ → ℝ[X]} (k : ℕ) (i : Fin c.order) {x : ℝ}
    (hx : c.lead.eval x ≠ 0) :
    (RatFunc.denom (jetCoord c q k i)).eval x ≠ 0 := by
  unfold jetCoord
  by_cases hk : k < c.order
  · rw [if_pos hk]; split_ifs <;> simp [RatFunc.denom_one, RatFunc.denom_zero]
  · rw [if_neg hk]
    exact denom_eval_ne_zero_of_dvd (RatFunc.denom_div_dvd _ _)
      (by rw [Polynomial.eval_pow]; exact pow_ne_zero _ hx)

/-- **Iterated Leibniz rule** for scalar functions: `(f·g)⁽ⁿ⁾` expands as the
binomial sum `Σ C(n,i) f⁽ⁱ⁾ g⁽ⁿ⁻ⁱ⁾`.  Mathlib lacks this; proved by induction
through `iteratedDeriv_succ`, `deriv_fun_mul`, and Pascal's rule. -/
private theorem iteratedDeriv_fun_mul {f g : ℝ → ℝ} (n : ℕ)
    (hdf : ContDiff ℝ ∞ f) (hdg : ContDiff ℝ ∞ g) :
    ∀ x, iteratedDeriv n (f * g) x
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (iteratedDeriv i f x * iteratedDeriv (n - i) g x) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have hfun : iteratedDeriv n (f * g) = fun y =>
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (iteratedDeriv i f y * iteratedDeriv (n - i) g y) := funext ih
    have hd1 : ∀ i, Differentiable ℝ (iteratedDeriv i f) := fun i =>
      hdf.differentiable_iteratedDeriv i (compareOfLessAndEq_eq_lt.mp rfl)
    have hd2 : ∀ i, Differentiable ℝ (iteratedDeriv i g) := fun i =>
      hdg.differentiable_iteratedDeriv i (compareOfLessAndEq_eq_lt.mp rfl)
    have hdiff : ∀ i ∈ Finset.range (n + 1), DifferentiableAt ℝ
        (fun y => (n.choose i : ℝ)
          * (iteratedDeriv i f y * iteratedDeriv (n - i) g y)) x := fun i _ =>
      ((hd1 i).differentiableAt.mul (hd2 _).differentiableAt).const_mul _
    have hstep : deriv (fun y => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (iteratedDeriv i f y * iteratedDeriv (n - i) g y)) x
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
            * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x
              + iteratedDeriv i f x * iteratedDeriv (n + 1 - i) g x) := by
      rw [deriv_fun_sum hdiff]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [deriv_const_mul_field,
        deriv_fun_mul (hd1 i).differentiableAt (hd2 _).differentiableAt,
        ← iteratedDeriv_succ, ← iteratedDeriv_succ]
      rw [show n - i + 1 = n + 1 - i from by
        have := Nat.le_of_lt_succ (Finset.mem_range.mp hi); omega]
    rw [iteratedDeriv_succ, hfun, hstep,
      Finset.sum_congr rfl fun i _ => mul_add _ _ _, Finset.sum_add_distrib]
    -- Combinatorial bookkeeping: Pascal's rule.
    symm
    calc ∑ j ∈ Finset.range (n + 2), ((n + 1).choose j : ℝ)
            * (iteratedDeriv j f x * iteratedDeriv (n + 1 - j) g x)
        = (∑ j ∈ Finset.range (n + 1),
              ((n.choose j : ℝ) + (n.choose (j + 1) : ℝ))
                * (iteratedDeriv (j + 1) f x * iteratedDeriv (n - j) g x))
          + ((n + 1).choose 0 : ℝ) * (iteratedDeriv 0 f x
              * iteratedDeriv (n + 1 - 0) g x) := by
          rw [Finset.sum_range_succ']
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.choose_succ_succ, Nat.cast_add,
            show n + 1 - (j + 1) = n - j from by omega]
      _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
                * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x)
            + ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ)
                * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x))
          + ((n + 1).choose 0 : ℝ) * (iteratedDeriv 0 f x
              * iteratedDeriv (n + 1 - 0) g x) := by
          congr 1
          rw [Finset.sum_congr rfl fun j _ => add_mul _ _ _,
            Finset.sum_add_distrib]
          congr 1
          -- The i = n+1 summand vanishes since `C(n, n+1) = 0`.
          rw [Finset.sum_range_succ]
          simp
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
                * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x)
          + (∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ)
                * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x)
            + ((n + 1).choose 0 : ℝ) * (iteratedDeriv 0 f x
                * iteratedDeriv (n + 1 - 0) g x)) := add_assoc _ _ _
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
                * (iteratedDeriv (i + 1) f x * iteratedDeriv (n - i) g x)
          + ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
              * (iteratedDeriv i f x * iteratedDeriv (n + 1 - i) g x) := by
          congr 1
          rw [Finset.sum_range_succ']
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [show n + 1 - (i + 1) = n - i from by omega]
          · rw [Nat.choose_zero_right, Nat.choose_zero_right]

/-- **Generic clearing lemma**: a nontrivial `ℝ(X)`-linear relation among the
coordinate vectors of the first `N+1` derivatives of `h` yields a holonomic
certificate for `h` of order `≤ N`.  `G` is an auxiliary bad set (typically
the union of leading-coefficient roots); `hrel` supplies the pointwise
relation off `G` wherever all coefficient denominators are nonzero. -/
private theorem isHolonomic_of_ratFunc_relation {N : ℕ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h)
    (a : Fin (N + 1) → ℝ⟮X⟯) (k₀ : Fin (N + 1)) (ha0 : a k₀ ≠ 0)
    (G : Finset ℝ)
    (hrel : ∀ x ∉ (G : Set ℝ), (∀ k : Fin (N + 1),
        (RatFunc.denom (a k)).eval x ≠ 0)
      → ∑ k : Fin (N + 1), RatFunc.eval (RingHom.id ℝ) x (a k)
          * iteratedDeriv k.val h x = 0) :
    IsHolonomic h := by
  classical
  -- Clear denominators: `aₖ·D` is a polynomial image.
  let den : Fin (N + 1) → ℝ[X] := fun k => RatFunc.denom (a k)
  let D : ℝ[X] := ∏ k : Fin (N + 1), den k
  have hDne : D ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => RatFunc.denom_ne_zero _
  let p : Fin (N + 1) → ℝ[X] :=
    fun k => (a k).num * ∏ j ∈ Finset.univ.erase k, den j
  have hp_alg : ∀ k : Fin (N + 1),
      a k * algebraMap ℝ[X] ℝ⟮X⟯ D = algebraMap ℝ[X] ℝ⟮X⟯ (p k) := by
    intro k
    have hd : (algebraMap ℝ[X] ℝ⟮X⟯ (den k) : ℝ⟮X⟯) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)
    have hsplit : algebraMap ℝ[X] ℝ⟮X⟯ D
        = algebraMap _ _ (den k) * algebraMap _ _ (∏ j ∈ Finset.univ.erase k, den j) := by
      rw [← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    calc a k * algebraMap _ _ D
        = a k * (algebraMap _ _ (den k)
            * algebraMap _ _ (∏ j ∈ Finset.univ.erase k, den j)) := by
          rw [hsplit]
      _ = a k * algebraMap _ _ (den k)
            * algebraMap _ _ (∏ j ∈ Finset.univ.erase k, den j) := by
          rw [← mul_assoc]
      _ = algebraMap _ _ ((a k).num)
            * algebraMap _ _ (∏ j ∈ Finset.univ.erase k, den j) := by
          congr 1
          nth_rw 1 [← RatFunc.num_div_denom (a k)]
          exact div_mul_cancel₀ _ hd
      _ = algebraMap _ _ ((a k).num * ∏ j ∈ Finset.univ.erase k, den j) := by
          rw [map_mul]
      _ = algebraMap _ _ (p k) := rfl
  -- At least one cleared coefficient is nonzero.
  obtain ⟨p0, hp0⟩ : ∃ k : Fin (N + 1), p k ≠ 0 := by
    refine ⟨k₀, fun h => ?_⟩
    have := hp_alg k₀
    rw [h, map_zero] at this
    rcases mul_eq_zero.mp this with h1 | h2
    · exact ha0 h1
    · have hD0 : algebraMap ℝ[X] ℝ⟮X⟯ D = algebraMap ℝ[X] ℝ⟮X⟯ 0 := by
        rw [h2, map_zero]
      exact hDne (IsFractionRing.injective ℝ[X] ℝ⟮X⟯ hD0)
  -- Multiply the pointwise relation through by `D` to clear coefficients.
  have hclr : ∀ x ∉ (G : Set ℝ), (∀ k : Fin (N + 1), (den k).eval x ≠ 0)
      → ∑ k : Fin (N + 1), (p k).eval x * iteratedDeriv k.val h x = 0 := by
    intro x hxG hd
    have hDx : D.eval x ≠ 0 := by
      show (∏ k : Fin (N + 1), den k).eval x ≠ 0
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hd k
    have hde : ∀ k : Fin (N + 1),
        RatFunc.eval (RingHom.id ℝ) x (a k) * D.eval x = (p k).eval x := by
      intro k
      have hb := congrArg (RatFunc.eval (RingHom.id ℝ) x) (hp_alg k)
      rw [RatFunc.eval_mul (f := RingHom.id ℝ) (a := x) (hd k)
        (by rw [RatFunc.denom_algebraMap]; simp)] at hb
      rw [RatFunc.eval_algebraMap, RatFunc.eval_algebraMap, Polynomial.eval₂_id,
        Polynomial.eval₂_id] at hb
      exact hb
    have h0 := hrel x hxG hd
    have hmul : D.eval x * ∑ k : Fin (N + 1),
        RatFunc.eval (RingHom.id ℝ) x (a k) * iteratedDeriv k.val h x
          = 0 := by rw [h0]; ring
    rw [Finset.mul_sum] at hmul
    rw [Finset.sum_congr rfl fun k _ => show
        D.eval x * (RatFunc.eval (RingHom.id ℝ) x (a k)
            * iteratedDeriv k.val h x)
          = (p k).eval x * iteratedDeriv k.val h x from by
        rw [← mul_assoc, mul_comm (D.eval x), hde k]] at hmul
    exact hmul
  -- The good set is `G` union the union of denominator root sets.
  let F : Finset ℝ := G ∪
    Finset.univ.biUnion fun k : Fin (N + 1) => (den k).roots.toFinset
  have hrel' : ∀ x ∉ (F : Set ℝ),
      ∑ k : Fin (N + 1), (p k).eval x * iteratedDeriv k.val h x = 0 := by
    intro x hx
    have hxG : x ∉ (G : Set ℝ) := fun hmem => hx (Finset.mem_union_left _ hmem)
    have hx3 : ∀ k : Fin (N + 1), (den k).eval x ≠ 0 := fun k h => hx
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
        Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots (RatFunc.denom_ne_zero _)).mpr h)⟩))
    exact hclr x hxG hx3
  -- Continuity propagates the relation to all of `ℝ`.
  have hcont : Continuous fun x => ∑ k : Fin (N + 1), (p k).eval x
      * iteratedDeriv k.val h x :=
    continuous_finsetSum _ fun k _ =>
      (p k).continuous.mul
        (hh.continuous_iteratedDeriv _ (WithTop.coe_le_coe.mpr le_top))
  have hz := eq_zero_of_continuous_eq_zero_off hcont hrel'
  -- Assemble the certificate, trimming zero tail coefficients.
  let P : Finset (Fin (N + 1)) := Finset.univ.filter fun k => p k ≠ 0
  have hPne : P.Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0⟩⟩
  set o := (P.max' hPne).val with hodef
  have hoN : o < N + 1 := (P.max' hPne).isLt
  have htop : ∀ k : Fin (N + 1), o < k.val → p k = 0 := by
    intro k hk
    by_contra hn
    have hle : k.val ≤ o := Finset.le_max' _ _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hn⟩)
    exact absurd hle (not_le_of_gt hk)
  refine ⟨⟨o, fun i => p ⟨i.val, (Nat.lt_succ_iff.mp i.isLt).trans_lt hoN⟩,
    ?_⟩, fun x => ?_⟩
  · have hm := Finset.max'_mem _ hPne
    exact (Finset.mem_filter.mp hm).2
  · show (∑ i : Fin (o + 1),
        (p ⟨i.val, (Nat.lt_succ_iff.mp i.isLt).trans_lt hoN⟩).eval x
          * iteratedDeriv i.val h x) = 0
    -- Range-sum form of `hz` with zero-tail split.
    set s : ℕ → ℝ := fun j =>
      if hb : j < N + 1 then (p ⟨j, hb⟩).eval x * iteratedDeriv j h x else 0
    have hsf : ∀ i : Fin (N + 1),
        s i.val = (p i).eval x * iteratedDeriv i.val h x := fun i => by
      show (if hb : i.val < N + 1 then (p ⟨i.val, hb⟩).eval x
          * iteratedDeriv i.val h x else 0) = _
      rw [dif_pos i.isLt]
    have hN0 : ∑ i ∈ Finset.range (N + 1), s i = 0 := by
      rw [← Fin.sum_univ_eq_sum_range s (N + 1),
        Finset.sum_congr rfl fun i _ => hsf i]
      exact hz x
    have htail : ∀ i ∈ Finset.range (N - o), s (o + 1 + i) = 0 := by
      intro i hi
      have hlt : o + 1 + i < N + 1 := by
        have := Finset.mem_range.mp hi; omega
      show (if hb : o + 1 + i < N + 1 then (p ⟨o + 1 + i, hb⟩).eval x
          * iteratedDeriv (o + 1 + i) h x else 0) = 0
      rw [dif_pos hlt, htop ⟨_, hlt⟩ (by show o < o + 1 + i; omega)]
      simp
    have hsplit : ∑ i ∈ Finset.range (o + 1), s i = 0 := by
      rw [show N + 1 = (o + 1) + (N - o) from by omega, Finset.sum_range_add,
        Finset.sum_eq_zero htail, add_zero] at hN0
      exact hN0
    rw [← Fin.sum_univ_eq_sum_range s (o + 1)] at hsplit
    rw [Finset.sum_congr rfl fun i : Fin (o + 1) =>
        fun _ => show s i.val
            = (p ⟨i.val, (Nat.lt_succ_iff.mp i.isLt).trans_lt hoN⟩).eval x
              * iteratedDeriv i.val h x from by
          have hlt : i.val < N + 1 := (Nat.lt_succ_iff.mp i.isLt).trans_lt hoN
          show (if hb : i.val < N + 1 then (p ⟨i.val, hb⟩).eval x
              * iteratedDeriv i.val h x else 0) = _
          rw [dif_pos hlt]] at hsplit
    exact hsplit

/-- **Sum closure, general orders**: the sum of two holonomic functions is
holonomic, with order at most `m + n`.  This is the general `via=sum` lane of
`certClosure` in `koru_std/sym.certcomp.kz`: `m + n + 1` derivatives of
`f + g` are expressed in the `m + n`-dimensional `ℝ(X)`-space of joint jet
coordinates, so a nontrivial `ℝ(X)`-relation exists; clearing denominators
gives a polynomial relation off a finite bad set, and continuity propagates it
to all of `ℝ`. -/
theorem isHolonomic_add {c d : HolonomicCertificate} {f g : ℝ → ℝ}
    (hdf : ContDiff ℝ ∞ f) (hdg : ContDiff ℝ ∞ g)
    (hf : satisfiesODE c f) (hg : satisfiesODE d g) :
    IsHolonomic (f + g) := by
  classical
  set m := c.order
  set n := d.order
  set N := m + n with hN
  choose qf hqf using fun r => satisfiesODE.lead_pow_mul_iteratedDeriv hdf hf r
  choose qg hqg using fun r => satisfiesODE.lead_pow_mul_iteratedDeriv hdg hg r
  -- The `m+n+1` coordinate vectors `v_k` in `Fin (m+n) → ℝ(X)` are dependent.
  let v : Fin (N + 1) → Fin N → ℝ⟮X⟯ :=
    fun k => Fin.append (jetCoord c qf k.val) (jetCoord d qg k.val)
  have hfr : Module.finrank ℝ⟮X⟯ (Fin N → ℝ⟮X⟯) = N :=
    (Module.finrank_fintype_fun_eq_card (R := ℝ⟮X⟯) (η := Fin N)).trans
      (Fintype.card_fin N)
  have hli : ¬ LinearIndependent ℝ⟮X⟯ v := fun hv => by
    have hc := hv.fintype_card_le_finrank
    rw [hfr, Fintype.card_fin] at hc
    omega
  obtain ⟨f', g', hfg, k₀, hf'g'⟩ := Fintype.not_linearIndependent_iffₛ.mp hli
  let a : Fin (N + 1) → ℝ⟮X⟯ := fun k => f' k - g' k
  have hsum : (∑ k : Fin (N + 1), a k • v k) = 0 := by
    rw [Finset.sum_congr rfl fun k _ => sub_smul (f' k) (g' k) (v k),
      Finset.sum_sub_distrib, hfg, sub_self]
  have ha0 : a k₀ ≠ 0 := sub_ne_zero.mpr hf'g'
  -- Pointwise relation off the union of both leads' roots.
  refine isHolonomic_of_ratFunc_relation (hdf.add hdg) a k₀ ha0
    (c.lead.roots.toFinset ∪ d.lead.roots.toFinset) ?_
  intro x hxG hd
  have hx : c.lead.eval x ≠ 0 := fun h => hxG
    (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots c.lead_ne).mpr h)))
  have hx' : d.lead.eval x ≠ 0 := fun h => hxG
    (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots d.lead_ne).mpr h)))
  have hE : ∀ k : Fin (N + 1),
      RatFunc.eval (RingHom.id ℝ) x (a k) * iteratedDeriv k.val (f + g) x
        = ∑ i : Fin m, RatFunc.eval (RingHom.id ℝ) x (a k)
            * RatFunc.eval (RingHom.id ℝ) x (jetCoord c qf k.val i)
            * iteratedDeriv i.val f x
          + ∑ j : Fin n, RatFunc.eval (RingHom.id ℝ) x (a k)
            * RatFunc.eval (RingHom.id ℝ) x (jetCoord d qg k.val j)
            * iteratedDeriv j.val g x := by
    intro k
    rw [iteratedDeriv_add (hdf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
        (hdg.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
      jetCoord_apply qf hqf hx k.val, jetCoord_apply qg hqg hx' k.val,
      mul_add, Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
      (Finset.sum_congr rfl fun j _ => ?_) <;> rw [mul_assoc]
  calc ∑ k : Fin (N + 1), RatFunc.eval (RingHom.id ℝ) x (a k)
          * iteratedDeriv k.val (f + g) x
      = ∑ k : Fin (N + 1), (∑ i : Fin m,
            RatFunc.eval (RingHom.id ℝ) x (a k)
              * RatFunc.eval (RingHom.id ℝ) x (jetCoord c qf k.val i)
              * iteratedDeriv i.val f x
          + ∑ j : Fin n,
            RatFunc.eval (RingHom.id ℝ) x (a k)
              * RatFunc.eval (RingHom.id ℝ) x (jetCoord d qg k.val j)
              * iteratedDeriv j.val g x) :=
        Finset.sum_congr rfl fun k _ => hE k
    _ = ∑ i : Fin m, (∑ k : Fin (N + 1),
            RatFunc.eval (RingHom.id ℝ) x (a k * jetCoord c qf k.val i))
            * iteratedDeriv i.val f x
        + ∑ j : Fin n, (∑ k : Fin (N + 1),
            RatFunc.eval (RingHom.id ℝ) x (a k * jetCoord d qg k.val j))
            * iteratedDeriv j.val g x := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [RatFunc.eval_mul (RingHom.id ℝ) x (hd k)
            (denom_jetCoord_ne_zero k.val i hx)]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [RatFunc.eval_mul (RingHom.id ℝ) x (hd k)
            (denom_jetCoord_ne_zero k.val j hx')]
    _ = ∑ i : Fin m, RatFunc.eval (RingHom.id ℝ) x
            (∑ k : Fin (N + 1), a k * jetCoord c qf k.val i)
            * iteratedDeriv i.val f x
        + ∑ j : Fin n, RatFunc.eval (RingHom.id ℝ) x
            (∑ k : Fin (N + 1), a k * jetCoord d qg k.val j)
            * iteratedDeriv j.val g x := by
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          exact (ratFunc_eval_sum _ _ fun k _ =>
            denom_mul_eval_ne_zero (hd k) (denom_jetCoord_ne_zero k.val i hx)).symm
        · refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          exact (ratFunc_eval_sum _ _ fun k _ =>
            denom_mul_eval_ne_zero (hd k) (denom_jetCoord_ne_zero k.val j hx')).symm
    _ = 0 := by
        have hdf0 : ∀ i : Fin m, ∑ k : Fin (N + 1),
            a k * jetCoord c qf k.val i = 0 := by
          intro i
          have hv : ∀ k : Fin (N + 1),
              v k (Fin.castAdd n i) = jetCoord c qf k.val i :=
            fun k => Fin.append_left _ _ i
          have := congrFun hsum (Fin.castAdd n i)
          rw [Finset.sum_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [Finset.sum_congr rfl fun k _ =>
            congrArg (fun w => a k * w) (hv k)] at this
          exact this
        have hdg0 : ∀ j : Fin n, ∑ k : Fin (N + 1),
            a k * jetCoord d qg k.val j = 0 := by
          intro j
          have hv : ∀ k : Fin (N + 1),
              v k (Fin.natAdd m j) = jetCoord d qg k.val j :=
            fun k => Fin.append_right _ _ j
          have := congrFun hsum (Fin.natAdd m j)
          rw [Finset.sum_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [Finset.sum_congr rfl fun k _ =>
            congrArg (fun w => a k * w) (hv k)] at this
          exact this
        simp [hdf0, hdg0]

/-! ### Stage 3 — product closure

`(f·g)⁽ᵏ⁾` expands by Leibniz into `f⁽ⁱ⁾·g⁽ᵏ⁻ⁱ⁾`; each factor reduces to its
own jet basis, so every derivative of `f·g` lands in the `m·n`-dimensional
`ℝ(X)`-space spanned by `{f⁽ᵃ⁾·g⁽ᵇ⁾ | a < m, b < n}`.  `m·n+1` candidate
vectors are dependent; the generic clearing lemma assembles the certificate
of order `≤ m·n`. -/

/-- `ℝ(X)`-coordinates of `(f·g)⁽ᵏ⁾` in the product jet basis
`{f⁽ᵃ⁾·g⁽ᵇ⁾ | a < order c, b < order d}`: the Leibniz coefficient
`Σᵢ C(k,i)·(f⁽ⁱ⁾-coords)·(g⁽ᵏ⁻ⁱ⁾-coords)`. -/
private def prodJetCoord (c d : HolonomicCertificate) (qf qg : ℕ → ℕ → ℝ[X])
    (k : ℕ) : Fin c.order × Fin d.order → ℝ⟮X⟯ :=
  fun ab => ∑ i ∈ Finset.range (k + 1),
    algebraMap ℝ[X] ℝ⟮X⟯ (C ((k.choose i : ℕ) : ℝ))
      * jetCoord c qf i ab.1 * jetCoord d qg (k - i) ab.2

/-- `algebraMap`-embedded polynomials have trivial `RatFunc` denominator. -/
private theorem denom_algebraMap_ne_zero {p : ℝ[X]} {x : ℝ} :
    (RatFunc.denom (algebraMap ℝ[X] ℝ⟮X⟯ p)).eval x ≠ 0 := by
  rw [RatFunc.denom_algebraMap]; simp

/-- `prodJetCoord` denominators vanish only inside both leads' root sets. -/
private theorem denom_prodJetCoord_ne_zero {c d : HolonomicCertificate}
    {qf qg : ℕ → ℕ → ℝ[X]} (k : ℕ) (ab : Fin c.order × Fin d.order) {x : ℝ}
    (hx : c.lead.eval x ≠ 0) (hx' : d.lead.eval x ≠ 0) :
    (RatFunc.denom (prodJetCoord c d qf qg k ab)).eval x ≠ 0 := by
  refine denom_eval_ne_zero_of_dvd (ratFunc_denom_sum_dvd _ _) ?_
  rw [Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    denom_mul_eval_ne_zero (denom_mul_eval_ne_zero
      denom_algebraMap_ne_zero
      (denom_jetCoord_ne_zero i ab.1 hx))
      (denom_jetCoord_ne_zero (k - i) ab.2 hx')

/-- Pointwise expansion of `(f·g)⁽ᵏ⁾` in the product jet basis, valid wherever
both leads are nonzero. -/
private theorem prodJetCoord_apply {c d : HolonomicCertificate} {f g : ℝ → ℝ}
    (hdf : ContDiff ℝ ∞ f) (hdg : ContDiff ℝ ∞ g)
    (qf qg : ℕ → ℕ → ℝ[X])
    (hqf : ∀ r x, c.lead.eval x ^ (r + 1) * iteratedDeriv (c.order + r) f x
        = ∑ i ∈ Finset.range c.order, (qf r i).eval x * iteratedDeriv i f x)
    (hqg : ∀ r x, d.lead.eval x ^ (r + 1) * iteratedDeriv (d.order + r) g x
        = ∑ i ∈ Finset.range d.order, (qg r i).eval x * iteratedDeriv i g x)
    {x : ℝ} (hx : c.lead.eval x ≠ 0) (hx' : d.lead.eval x ≠ 0) (k : ℕ) :
    iteratedDeriv k (f * g) x
      = ∑ a : Fin c.order, ∑ b : Fin d.order,
          RatFunc.eval (RingHom.id ℝ) x (prodJetCoord c d qf qg k (a, b))
            * (iteratedDeriv a.val f x * iteratedDeriv b.val g x) := by
  rw [iteratedDeriv_fun_mul k hdf hdg]
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
          * (iteratedDeriv i f x * iteratedDeriv (k - i) g x)
      = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
          * ((∑ a : Fin c.order, RatFunc.eval (RingHom.id ℝ) x (jetCoord c qf i a)
                * iteratedDeriv a.val f x)
            * (∑ b : Fin d.order, RatFunc.eval (RingHom.id ℝ) x
                (jetCoord d qg (k - i) b) * iteratedDeriv b.val g x)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [jetCoord_apply qf hqf hx i, jetCoord_apply qg hqg hx' (k - i)]
    _ = ∑ i ∈ Finset.range (k + 1), ∑ a : Fin c.order, ∑ b : Fin d.order,
          (k.choose i : ℝ)
            * (RatFunc.eval (RingHom.id ℝ) x (jetCoord c qf i a)
              * RatFunc.eval (RingHom.id ℝ) x (jetCoord d qg (k - i) b))
            * (iteratedDeriv a.val f x * iteratedDeriv b.val g x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_; ring
    _ = ∑ a : Fin c.order, ∑ b : Fin d.order, ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ)
            * (RatFunc.eval (RingHom.id ℝ) x (jetCoord c qf i a)
              * RatFunc.eval (RingHom.id ℝ) x (jetCoord d qg (k - i) b))
            * (iteratedDeriv a.val f x * iteratedDeriv b.val g x) := by
        rw [Finset.sum_comm,
          Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    _ = ∑ a : Fin c.order, ∑ b : Fin d.order,
          RatFunc.eval (RingHom.id ℝ) x (prodJetCoord c d qf qg k (a, b))
            * (iteratedDeriv a.val f x * iteratedDeriv b.val g x) := by
        refine Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul]
        congr 1
        unfold prodJetCoord
        rw [ratFunc_eval_sum _ _ fun i _ =>
          denom_mul_eval_ne_zero (denom_mul_eval_ne_zero
            denom_algebraMap_ne_zero
            (denom_jetCoord_ne_zero i a hx))
            (denom_jetCoord_ne_zero (k - i) b hx')]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RatFunc.eval_mul (RingHom.id ℝ) x
          (denom_mul_eval_ne_zero denom_algebraMap_ne_zero
            (denom_jetCoord_ne_zero i a hx))
          (denom_jetCoord_ne_zero (k - i) b hx'),
          RatFunc.eval_mul (RingHom.id ℝ) x denom_algebraMap_ne_zero
            (denom_jetCoord_ne_zero i a hx),
          RatFunc.eval_algebraMap]
        simp
        rw [mul_assoc]

/-- **Product closure**: a product of holonomic functions is holonomic, of
order at most the product of the input orders. -/
theorem isHolonomic_mul {c d : HolonomicCertificate} {f g : ℝ → ℝ}
    (hdf : ContDiff ℝ ∞ f) (hdg : ContDiff ℝ ∞ g)
    (hf : satisfiesODE c f) (hg : satisfiesODE d g) :
    IsHolonomic (f * g) := by
  classical
  set m := c.order
  set n := d.order
  set N := m * n with hN
  choose qf hqf using fun r => satisfiesODE.lead_pow_mul_iteratedDeriv hdf hf r
  choose qg hqg using fun r => satisfiesODE.lead_pow_mul_iteratedDeriv hdg hg r
  -- The `m·n+1` coordinate vectors in `Fin (m·n) → ℝ(X)` are dependent.
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let v : Fin (N + 1) → Fin N → ℝ⟮X⟯ :=
    fun k t => prodJetCoord c d qf qg k.val (e.symm t)
  have hfr : Module.finrank ℝ⟮X⟯ (Fin N → ℝ⟮X⟯) = N :=
    (Module.finrank_fintype_fun_eq_card (R := ℝ⟮X⟯) (η := Fin N)).trans
      (Fintype.card_fin N)
  have hli : ¬ LinearIndependent ℝ⟮X⟯ v := fun hv => by
    have hc := hv.fintype_card_le_finrank
    rw [hfr, Fintype.card_fin] at hc
    omega
  obtain ⟨f', g', hfg, k₀, hf'g'⟩ := Fintype.not_linearIndependent_iffₛ.mp hli
  let a : Fin (N + 1) → ℝ⟮X⟯ := fun k => f' k - g' k
  have hsum : (∑ k : Fin (N + 1), a k • v k) = 0 := by
    rw [Finset.sum_congr rfl fun k _ => sub_smul (f' k) (g' k) (v k),
      Finset.sum_sub_distrib, hfg, sub_self]
  have ha0 : a k₀ ≠ 0 := sub_ne_zero.mpr hf'g'
  -- Pointwise relation off the union of both leads' roots.
  refine isHolonomic_of_ratFunc_relation (hdf.mul hdg) a k₀ ha0
    (c.lead.roots.toFinset ∪ d.lead.roots.toFinset) ?_
  intro x hxG hd
  have hx : c.lead.eval x ≠ 0 := fun h => hxG
    (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots c.lead_ne).mpr h)))
  have hx' : d.lead.eval x ≠ 0 := fun h => hxG
    (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots d.lead_ne).mpr h)))
  calc ∑ k : Fin (N + 1), RatFunc.eval (RingHom.id ℝ) x (a k)
          * iteratedDeriv k.val (f * g) x
      = ∑ k : Fin (N + 1), ∑ i : Fin m, ∑ j : Fin n,
          RatFunc.eval (RingHom.id ℝ) x (a k)
            * RatFunc.eval (RingHom.id ℝ) x (prodJetCoord c d qf qg k.val (i, j))
            * (iteratedDeriv i.val f x * iteratedDeriv j.val g x) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [prodJetCoord_apply hdf hdg qf qg hqf hqg hx hx' k.val,
          Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_; rw [mul_assoc]
    _ = ∑ i : Fin m, ∑ j : Fin n, (∑ k : Fin (N + 1),
            RatFunc.eval (RingHom.id ℝ) x (a k)
              * RatFunc.eval (RingHom.id ℝ) x
                (prodJetCoord c d qf qg k.val (i, j)))
            * (iteratedDeriv i.val f x * iteratedDeriv j.val g x) := by
        rw [Finset.sum_comm,
          Finset.sum_congr rfl fun i _ => Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, RatFunc.eval (RingHom.id ℝ) x
            (∑ k : Fin (N + 1), a k * prodJetCoord c d qf qg k.val (i, j))
            * (iteratedDeriv i.val f x * iteratedDeriv j.val g x) := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [Finset.sum_congr rfl fun k _ =>
          (RatFunc.eval_mul (RingHom.id ℝ) x (hd k)
            (denom_prodJetCoord_ne_zero k.val (i, j) hx hx')).symm]
        exact (ratFunc_eval_sum _ _ fun k _ =>
          denom_mul_eval_ne_zero (hd k)
            (denom_prodJetCoord_ne_zero k.val (i, j) hx hx')).symm
    _ = 0 := by
        have hz : ∀ i : Fin m, ∀ j : Fin n,
            ∑ k : Fin (N + 1), a k * prodJetCoord c d qf qg k.val (i, j)
              = 0 := by
          intro i j
          have hv : ∀ k : Fin (N + 1),
              v k (e (i, j)) = prodJetCoord c d qf qg k.val (i, j) :=
            fun k => congrArg (prodJetCoord c d qf qg k.val)
              (e.symm_apply_apply (i, j))
          have := congrFun hsum (e (i, j))
          rw [Finset.sum_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [Finset.sum_congr rfl fun k _ =>
            congrArg (fun w => a k * w) (hv k)] at this
          exact this
        simp [hz]

end ISAR
