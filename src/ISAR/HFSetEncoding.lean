import ISAR.HFSet
import ISAR.InvariantLayer

namespace ISAR

axiom subToNat : ISKSubtype → Nat
axiom natToSub : Nat → ISKSubtype
axiom subToNat_inverse (t : ISKSubtype) : natToSub (subToNat t) = t
axiom natToSub_inverse (n : Nat) : subToNat (natToSub n) = n

axiom fromNat : Nat → HF
axiom fromNat_toNat_inverse (x : HF) : fromNat (toNat x) = x
axiom toNat_fromNat_inverse (n : Nat) : toNat (fromNat n) = n

axiom layerToNat : InvariantLayer → Nat
axiom natToLayer : Nat → InvariantLayer
axiom layerToNat_inverse (q : InvariantLayer) : natToLayer (layerToNat q) = q
axiom natToLayer_inverse (n : Nat) : layerToNat (natToLayer n) = n

axiom canonical_rep_eq (t : ISKSubtype) : OperEq (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid t)) t

noncomputable def HF_encode (c : HF) : InvariantLayer :=
  natToLayer (toNat c)

noncomputable def encode_raw (c : HF) : ISKSubtype :=
  InvariantLayer.canonical_rep (HF_encode c)

noncomputable def decode_layer (q : InvariantLayer) : HF :=
  fromNat (layerToNat q)

noncomputable def decode_term (t : ISKSubtype) : HF :=
  decode_layer (Quotient.mk _ t)

theorem decode_layer_HF_encode (c : HF) : decode_layer (HF_encode c) = c := by
  unfold decode_layer HF_encode
  rw [natToLayer_inverse, fromNat_toNat_inverse]

theorem HF_encode_decode_layer (q : InvariantLayer) : HF_encode (decode_layer q) = q := by
  unfold HF_encode decode_layer
  rw [toNat_fromNat_inverse, layerToNat_inverse]

theorem canonical_rep_sound (q : InvariantLayer) :
    Quotient.mk operEqSetoid (InvariantLayer.canonical_rep q) = q := by
  induction q using Quotient.ind with | _ t =>
    dsimp [InvariantLayer.canonical_rep]
    exact Quotient.sound (canonical_rep_eq t)

theorem decode_term_encode_raw (c : HF) : decode_term (encode_raw c) = c := by
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
