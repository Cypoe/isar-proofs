import ISAR.HFSet
import ISAR.CanonicalRepresentative
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace ISAR

/-!
# Encodings: constructed Gödel / Ackermann, named quotient bijection

* `fromNat` / `toNat` is the Ackermann coding of hereditarily finite sets.
  `toNat (fromNat n) = n` is a theorem; the other direction holds as `ExtEq`
  (syntactic HF trees are not unique).
* `subToNat` / `natToSub` is a Gödel numbering of the ISK fragment.
* `layerToNat` / `natToLayer` remains a **named modeling axiom**: a bijection
  `InvariantLayer ≃ Nat`. Defining it via `canonical_rep` cannot give both
  inverses (`nf_of_term` does not preserve Gödel numbers of non-normal terms).
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

/-! ### Named modeling axiom: countable bijection on the OperEq quotient -/

axiom layerToNat : InvariantLayer → Nat
axiom natToLayer : Nat → InvariantLayer
axiom layerToNat_inverse (q : InvariantLayer) : natToLayer (layerToNat q) = q
axiom natToLayer_inverse (n : Nat) : layerToNat (natToLayer n) = n

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
