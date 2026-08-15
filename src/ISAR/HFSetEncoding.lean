import ISAR.HFSet
import ISAR.CanonicalRepresentative
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ISAR

/-!
# Encodings: constructed Gödel / Ackermann, constructed quotient bijection

* `fromNat` / `toNat` is the Ackermann coding of hereditarily finite sets.
  `toNat (fromNat n) = n` is a theorem; the other direction holds as `ExtEq`
  (syntactic HF trees are not unique).
* `subToNat` / `natToSub` is a Gödel numbering of the ISK fragment.
* `layerToNat` / `natToLayer` is a **constructed** `noncomputable` bijection
  `Nat ≃ InvariantLayer`: enumerate OperEq classes in min-Gödel order
  (k-th least code of a class). Not `canonical_rep`. `natToLayer_inverse` is
  not `rfl` on raw Gödel numbers of non-minimal terms (`godelClass 3`).
-/

/-! ### ISK Gödel numbering via Mathlib pairing -/

def iskToNat : ITerm → Nat
  | .norm => 0
  | .konst => 1
  | .sₛ => 2
  | .app f x => Nat.pair (iskToNat f) (iskToNat x) + 3
  | .var _ | .dup | .swap | .comp => 0

def subToNat (t : ISKSubtype) : Nat := iskToNat t.val

def natToSub : Nat → ISKSubtype
  | 0 => ⟨.norm, .norm⟩
  | 1 => ⟨.konst, .konst⟩
  | 2 => ⟨.sₛ, .sₛ⟩
  | n + 3 =>
      let p := Nat.unpair n
      ⟨.app (natToSub p.1).val (natToSub p.2).val,
       .app (natToSub p.1).property (natToSub p.2).property⟩
termination_by n => n
decreasing_by
  · simp_wf
    have := Nat.unpair_left_le n
    omega
  · simp_wf
    have := Nat.unpair_right_le n
    omega

theorem subToNat_inverse (t : ISKSubtype) : natToSub (subToNat t) = t := by
  rcases t with ⟨t, ht⟩
  induction ht with
  | norm =>
      simp [subToNat, iskToNat, natToSub]
  | konst =>
      simp [subToNat, iskToNat, natToSub]
  | sₛ =>
      simp [subToNat, iskToNat, natToSub]
  | app hf hx ihf ihx =>
      apply Subtype.ext
      simp [subToNat, iskToNat, natToSub, Nat.unpair_pair]
      constructor
      { have h1 := congrArg Subtype.val ihf
        simpa [subToNat] using h1 }
      { have h1 := congrArg Subtype.val ihx
        simpa [subToNat] using h1 }

theorem natToSub_inverse (n : Nat) : subToNat (natToSub n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      match n with
      | 0 => simp [natToSub, subToNat, iskToNat]
      | 1 => simp [natToSub, subToNat, iskToNat]
      | 2 => simp [natToSub, subToNat, iskToNat]
      | n + 3 =>
          have hp1 : (Nat.unpair n).1 < n + 3 := by
            have := Nat.unpair_left_le n; omega
          have hp2 : (Nat.unpair n).2 < n + 3 := by
            have := Nat.unpair_right_le n; omega
          have ih1 := ih (Nat.unpair n).1 hp1
          have ih2 := ih (Nat.unpair n).2 hp2
          calc
            subToNat (natToSub (n + 3))
                = Nat.pair (subToNat (natToSub (Nat.unpair n).1))
                    (subToNat (natToSub (Nat.unpair n).2)) + 3 := by
                  simp [natToSub, subToNat, iskToNat]
            _ = Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 + 3 := by
                  rw [ih1, ih2]
            _ = n + 3 := by simp [Nat.pair_unpair]

/-! ### Ackermann coding `Nat → HF` -/

def fromNatInsert (n : Nat) (rec : ∀ m, m < n → HF) : Nat → HF
  | 0 => .empty
  | k + 1 =>
      let acc := fromNatInsert n rec k
      if h : k < n then
        if n.testBit k then HF.insert (rec k h) acc else acc
      else acc

def fromNat (n : Nat) : HF :=
  fromNatInsert n (fun m _ => fromNat m) n
termination_by n

theorem nat_lt_two_pow (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      omega

theorem fromNatInsert_testBit (n : Nat) (rec : ∀ m, m < n → HF)
    (hrec : ∀ m hm, toNat (rec m hm) = m) (k i : Nat) :
    (toNat (fromNatInsert n rec k)).testBit i =
      (decide (i < k) && n.testBit i) := by
  induction k with
  | zero =>
      simp [fromNatInsert, toNat]
  | succ k ihk =>
      unfold fromNatInsert
      split_ifs with hlt hbit
      { have htok : toNat (rec k hlt) = k := hrec k hlt
        rw [toNat, Nat.testBit_or, htok, Nat.testBit_shiftl, ihk]
        rcases Nat.lt_trichotomy i k with hlt' | heq | hgt
        { have hik : i < k + 1 := by omega
          have hne : i ≠ k := Nat.ne_of_lt hlt'
          simp [hlt', hik, hne] }
        { subst heq
          simp [hbit] }
        { have hnlt : ¬ i < k := by omega
          have hnlt1 : ¬ i < k + 1 := by omega
          have hne : i ≠ k := by omega
          simp [hnlt, hnlt1, hne] } }
      { have hkfalse : n.testBit k = false := by
          revert hbit
          cases n.testBit k
          { intro _; rfl }
          { intro hfalse; exact (hfalse rfl).elim }
        rw [ihk]
        rcases Nat.lt_trichotomy i k with hlt' | heq | hgt
        { have hik : i < k + 1 := by omega
          simp [hlt', hik] }
        { subst heq
          simp [hkfalse] }
        { have hnlt : ¬ i < k := by omega
          have hnlt1 : ¬ i < k + 1 := by omega
          simp [hnlt, hnlt1] } }
      { have hge : n ≤ k := Nat.not_lt.mp hlt
        have hfalse : n.testBit k = false :=
          Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (nat_lt_two_pow n)
            (Nat.pow_le_pow_right (by omega) hge))
        rw [ihk]
        rcases Nat.lt_trichotomy i k with hlt' | heq | hgt
        { have hik : i < k + 1 := by omega
          simp [hlt', hik] }
        { subst heq
          simp [hfalse] }
        { have hnlt : ¬ i < k := by omega
          have hnlt1 : ¬ i < k + 1 := by omega
          simp [hnlt, hnlt1] } }

theorem toNat_fromNat (n : Nat) : toNat (fromNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      apply Nat.eq_of_testBit_eq
      intro i
      have hrec : ∀ m hm, toNat (fromNat m) = m := fun m hm => ih m hm
      unfold fromNat
      rw [fromNatInsert_testBit n (fun m _ => fromNat m) hrec]
      by_cases h : i < n
      { simp [h] }
      { simp [h]
        exact Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (nat_lt_two_pow n)
          (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp h))) }

/-- Syntactic HF trees are not unique; Ackermann codes identify extensionally equal sets. -/
theorem fromNat_toNat_ext (x : HF) : ExtEq (fromNat (toNat x)) x :=
  toNat_fromNat (toNat x)

/-! ### Countable bijection on the OperEq quotient (min-Gödel enumeration) -/

open Classical

/-- The OperEq class of the ISK term with Gödel number `n`. Surjective, not injective. -/
def godelClass (n : Nat) : InvariantLayer :=
  Quotient.mk _ (natToSub n)

theorem godelClass_surjective (q : InvariantLayer) : ∃ n, godelClass n = q :=
  Quotient.inductionOn q fun t => ⟨subToNat t, by rw [godelClass, subToNat_inverse]⟩

/-- Least Gödel number of an OperEq class. -/
noncomputable def minCode (q : InvariantLayer) : Nat :=
  Nat.find (godelClass_surjective q)

theorem minCode_spec (q : InvariantLayer) : godelClass (minCode q) = q :=
  Nat.find_spec (godelClass_surjective q)

theorem minCode_min {q : InvariantLayer} {m : Nat} (hm : m < minCode q) :
    godelClass m ≠ q :=
  Nat.find_min (godelClass_surjective q) hm

/-- `n` is the least Gödel number of its class. -/
def isMinCode (n : Nat) : Prop :=
  ∀ m < n, godelClass m ≠ godelClass n

theorem isMinCode_zero : isMinCode 0 :=
  fun m hm => (Nat.not_lt_zero m hm).elim

theorem minCode_isMin (q : InvariantLayer) : isMinCode (minCode q) := by
  intro m hm hmeq
  exact minCode_min hm (hmeq.trans (minCode_spec q))

theorem minCode_eq_iff (n : Nat) : minCode (godelClass n) = n ↔ isMinCode n := by
  constructor
  { intro h
    simpa [h] using minCode_isMin (godelClass n) }
  { intro hmin
    apply Nat.le_antisymm
    { exact Nat.find_min' (godelClass_surjective (godelClass n)) rfl }
    { by_contra hlt
      exact hmin _ (Nat.lt_of_not_ge hlt) (minCode_spec (godelClass n)) } }

/-- Rank of a min-code among all strictly smaller min-codes. -/
noncomputable def minCodeRank (n : Nat) : Nat :=
  ((Finset.range n).filter isMinCode).card

theorem minCodeRank_mono {n m : Nat} (hn : isMinCode n) (hlt : n < m) :
    minCodeRank n < minCodeRank m := by
  have hmem : n ∈ (Finset.range m).filter isMinCode := by
    simp [Finset.mem_filter, Finset.mem_range, hlt, hn]
  have hnot : n ∉ (Finset.range n).filter isMinCode := by
    simp [Finset.mem_filter, Finset.mem_range]
  have hsub : (Finset.range n).filter isMinCode ⊆ (Finset.range m).filter isMinCode := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨Nat.lt_trans hx.1 hlt, hx.2⟩
  have hss : (Finset.range n).filter isMinCode ⊂ (Finset.range m).filter isMinCode :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩
  exact Finset.card_lt_card hss

theorem minCodeRank_inj {n m : Nat} (hn : isMinCode n) (hm : isMinCode m)
    (heq : minCodeRank n = minCodeRank m) : n = m := by
  rcases Nat.lt_trichotomy n m with h | h | h
  { exact (Nat.ne_of_lt (minCodeRank_mono hn h) heq).elim }
  { exact h }
  { exact (Nat.ne_of_lt (minCodeRank_mono hm h) heq.symm).elim }

theorem minCodeRank_lt_of_mem {N n : Nat}
    (hn : n ∈ (Finset.range N).filter isMinCode) :
    minCodeRank n < ((Finset.range N).filter isMinCode).card := by
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  have hsub : (Finset.range n).filter isMinCode ⊆ (Finset.range N).filter isMinCode := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨Nat.lt_trans hx.1 hn.1, hx.2⟩
  have hnot : n ∉ (Finset.range n).filter isMinCode := by
    simp [Finset.mem_filter, Finset.mem_range]
  have hss : (Finset.range n).filter isMinCode ⊂ (Finset.range N).filter isMinCode :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (by
      have : n ∈ (Finset.range N).filter isMinCode := by
        simp [Finset.mem_filter, Finset.mem_range, hn]
      exact heq ▸ this)⟩
  exact Finset.card_lt_card hss

theorem exists_minCode_of_rank_aux {N k : Nat}
    (hk : k < ((Finset.range N).filter isMinCode).card) :
    ∃ n < N, isMinCode n ∧ minCodeRank n = k := by
  let T := (Finset.range N).filter isMinCode
  have hkT : k < T.card := hk
  by_contra hnone
  have hnone' : ∀ n ∈ T, minCodeRank n ≠ k := by
    intro n hn heq
    have hn' : n ∈ (Finset.range N).filter isMinCode := hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn'
    exact hnone ⟨n, hn'.1, hn'.2, heq⟩
  have h_inj : Set.InjOn minCodeRank (T : Set Nat) := by
    intro n hn m hm heq
    have hnT : n ∈ T := Finset.mem_coe.mp hn
    have hmT : m ∈ T := Finset.mem_coe.mp hm
    exact minCodeRank_inj (Finset.mem_filter.mp hnT).2 (Finset.mem_filter.mp hmT).2 heq
  have himg : T.image minCodeRank ⊆ (Finset.range T.card).erase k := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨n, hnT, rfl⟩
    have hi_lt : minCodeRank n < T.card := minCodeRank_lt_of_mem (N := N) hnT
    have hi_ne := hnone' n hnT
    exact Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_range.mpr hi_lt⟩
  have hcard_img : (T.image minCodeRank).card = T.card :=
    T.card_image_of_injOn h_inj
  have hle := Finset.card_le_card himg
  have hkmem : k ∈ Finset.range T.card := Finset.mem_range.mpr hkT
  have herase : ((Finset.range T.card).erase k).card = T.card - 1 := by
    rw [Finset.card_erase_of_mem hkmem, Finset.card_range]
  omega

/- Nested `K`-spines: infinitely many distinct NFs, hence infinitely many classes. -/
def kSpine : Nat → ITerm
  | 0 => .konst
  | n + 1 => .app .konst (kSpine n)

theorem kSpine_ISK (n : Nat) : ISKTerm (kSpine n) := by
  induction n with
  | zero => exact ISKTerm.konst
  | succ _ ih => exact ISKTerm.app ISKTerm.konst ih

def kSpineSub (n : Nat) : ISKSubtype := ⟨kSpine n, kSpine_ISK n⟩

theorem kSpine_NormalI (n : Nat) : NormalI (kSpine n) := by
  induction n with
  | zero =>
      intro u h; cases h
  | succ n ih =>
      intro u h
      cases h with
      | appL h' => cases h'
      | appR h' => exact ih _ h'

theorem kSpine_injective {i j : Nat} (h : kSpine i = kSpine j) : i = j := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => rfl
      | succ _ => cases h
  | succ i ih =>
      cases j with
      | zero => cases h
      | succ j =>
          simp only [kSpine] at h
          exact congrArg Nat.succ (ih (ITerm.app.inj h).2)

theorem kSpine_OperEq_eq {i j : Nat} (h : OperEq (kSpineSub i) (kSpineSub j)) : i = j := by
  rcases h with ⟨v, hi, hj⟩
  have ei := IRed_normal_eq (kSpine_NormalI i) hi
  have ej := IRed_normal_eq (kSpine_NormalI j) hj
  exact kSpine_injective (ei.trans ej.symm)

theorem kSpine_layer_inj {i j : Nat}
    (h : toInvariantLayer (kSpineSub i) = toInvariantLayer (kSpineSub j)) : i = j :=
  kSpine_OperEq_eq (Quotient.exact h)

theorem minCode_kSpine_inj {i j : Nat}
    (h : minCode (toInvariantLayer (kSpineSub i)) = minCode (toInvariantLayer (kSpineSub j))) :
    i = j := by
  have hi := minCode_spec (toInvariantLayer (kSpineSub i))
  have hj := minCode_spec (toInvariantLayer (kSpineSub j))
  exact kSpine_layer_inj (hi.symm.trans (h ▸ hj))

theorem exists_minCode_of_rank (k : Nat) :
    ∃ n, isMinCode n ∧ minCodeRank n = k := by
  let spines : Finset Nat :=
    (Finset.range (k + 1)).image fun i => minCode (toInvariantLayer (kSpineSub i))
  have hcard : spines.card = k + 1 := by
    change ((Finset.range (k + 1)).image
        (fun i => minCode (toInvariantLayer (kSpineSub i)))).card = k + 1
    rw [Finset.card_image_of_injective]
    · simp [Finset.card_range]
    · intro i j hij
      exact minCode_kSpine_inj hij
  have hne : spines.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at hcard
    exact Nat.succ_ne_zero k hcard.symm
  let N := spines.max' hne + 1
  have hsub : spines ⊆ (Finset.range N).filter isMinCode := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, -, rfl⟩
    have hmin := minCode_isMin (toInvariantLayer (kSpineSub i))
    have hle := Finset.le_max' spines _ hn
    simp [Finset.mem_filter, Finset.mem_range, hmin]
    omega
  have hge : k < ((Finset.range N).filter isMinCode).card := by
    have := Finset.card_le_card hsub
    omega
  rcases exists_minCode_of_rank_aux hge with ⟨n, -, hmin, hrk⟩
  exact ⟨n, hmin, hrk⟩

/-- k-th least min-Gödel code (enumeration of distinct OperEq classes). -/
noncomputable def minCodeEnum (k : Nat) : Nat :=
  Nat.find (exists_minCode_of_rank k)

theorem minCodeEnum_isMin (k : Nat) : isMinCode (minCodeEnum k) :=
  (Nat.find_spec (exists_minCode_of_rank k)).1

theorem minCodeEnum_rank (k : Nat) : minCodeRank (minCodeEnum k) = k :=
  (Nat.find_spec (exists_minCode_of_rank k)).2

/-- Index of an OperEq class in min-Gödel order. Not the raw Gödel number. -/
noncomputable def layerToNat (q : InvariantLayer) : Nat :=
  minCodeRank (minCode q)

/-- The k-th OperEq class in min-Gödel order. Not `Quotient.mk (natToSub k)`. -/
noncomputable def natToLayer (k : Nat) : InvariantLayer :=
  godelClass (minCodeEnum k)

theorem layerToNat_inverse (q : InvariantLayer) : natToLayer (layerToNat q) = q := by
  unfold natToLayer layerToNat
  have hmin := minCode_isMin q
  have hrk : minCodeRank (minCodeEnum (minCodeRank (minCode q))) = minCodeRank (minCode q) :=
    minCodeEnum_rank _
  have heq := minCodeRank_inj (minCodeEnum_isMin _) hmin hrk
  rw [heq, minCode_spec]

theorem natToLayer_inverse (n : Nat) : layerToNat (natToLayer n) = n := by
  unfold layerToNat natToLayer
  rw [(minCode_eq_iff (minCodeEnum n)).mpr (minCodeEnum_isMin n), minCodeEnum_rank]

/-- Raw Gödel number 3 is `norm · norm`, which joins to `norm` (code 0). The inverse
is therefore not `rfl` on non-minimal codes. -/
theorem godelClass_three_eq_zero : godelClass 3 = godelClass 0 := by
  have hred : IRed (natToSub 3).val ITerm.norm := by
    simp [natToSub]
    exact Relation.ReflTransGen.single (IStep.normβ ITerm.norm)
  have hrefl : IRed (natToSub 0).val ITerm.norm := by
    simp [natToSub]
    exact Relation.ReflTransGen.refl
  exact Quotient.sound (s := operEqSetoid) (Exists.intro ITerm.norm ⟨hred, hrefl⟩)

theorem layerToNat_godelClass_three_ne :
    layerToNat (godelClass 3) ≠ 3 := by
  have h : godelClass 3 = natToLayer 0 := by
    have h0 : minCodeEnum 0 = 0 := by
      have hmin : isMinCode 0 := isMinCode_zero
      have hrk : minCodeRank 0 = 0 := by simp [minCodeRank]
      have hspec := Nat.find_spec (exists_minCode_of_rank 0)
      exact minCodeRank_inj (minCodeEnum_isMin 0) hmin (hspec.2.trans hrk.symm)
    rw [natToLayer, h0, godelClass_three_eq_zero]
  rw [h, natToLayer_inverse]
  decide

noncomputable def HF_encode (c : HF) : InvariantLayer :=
  natToLayer (toNat c)

noncomputable def encode_raw (c : HF) : ISKSubtype :=
  InvariantLayer.canonical_rep (HF_encode c)

noncomputable def decode_layer (q : InvariantLayer) : HF :=
  fromNat (layerToNat q)

noncomputable def decode_term (t : ISKSubtype) : HF :=
  decode_layer (Quotient.mk _ t)

theorem decode_layer_HF_encode (c : HF) : ExtEq (decode_layer (HF_encode c)) c := by
  unfold decode_layer HF_encode
  rw [natToLayer_inverse]
  exact fromNat_toNat_ext c

theorem HF_encode_decode_layer (q : InvariantLayer) : HF_encode (decode_layer q) = q := by
  unfold HF_encode decode_layer
  rw [toNat_fromNat, layerToNat_inverse]

theorem decode_term_encode_raw (c : HF) : ExtEq (decode_term (encode_raw c)) c := by
  unfold decode_term encode_raw
  rw [canonical_rep_sound]
  exact decode_layer_HF_encode c

theorem encode_raw_decode_term (t : ISKSubtype) : OperEq (encode_raw (decode_term t)) t := by
  unfold encode_raw decode_term
  have h_eq : HF_encode (decode_layer (Quotient.mk operEqSetoid t)) = Quotient.mk operEqSetoid t :=
    HF_encode_decode_layer (Quotient.mk operEqSetoid t)
  rw [h_eq]
  exact canonical_rep_eq t

theorem HF_encode_eq_of_ExtEq {c1 c2 : HF} (h : ExtEq c1 c2) : HF_encode c1 = HF_encode c2 := by
  unfold HF_encode ExtEq at *
  rw [h]

end ISAR
