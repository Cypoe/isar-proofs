import HFSetSemantics
import KernelCategory

namespace ISAR

theorem HF_sound (t u : ISKSubtype) (h : OperEq t u) : ExtEq (decode_term t) (decode_term u) := by
  have h_mk : Quotient.mk operEqSetoid t = Quotient.mk operEqSetoid u := Quotient.sound h
  unfold decode_term decode_layer
  rw [h_mk]
  exact ExtEq.refl _

theorem HF_decode_eq (c1 c2 : HF) (h : ExtEq c1 c2) : OperEq (encode_raw c1) (encode_raw c2) := by
  have h_encode : HF_encode c1 = HF_encode c2 := HF_encode_eq_of_ExtEq h
  have h_raw : encode_raw c1 = encode_raw c2 := by
    unfold encode_raw
    rw [h_encode]
  rw [h_raw]
  exact OperEq.refl _

/--
The set-theoretic admissible semantic kernel.
Packages hereditarily finite sets as a decoder/view over the ISAR stack.
-/
noncomputable abbrev HF_Kernel : Kernel where
  Carrier := HF
  view_of := decode_term
  view_eq := ExtEq
  is_equiv := {
    refl := ExtEq.refl
    symm := ExtEq.symm
    trans := ExtEq.trans
  }
  sound := HF_sound
  decode := encode_raw
  decode_view := encode_raw_decode_term
  view_eq_decode := fun c => by
    rw [decode_term_encode_raw]
    exact ExtEq.refl _
  decode_eq := HF_decode_eq

/--
ZFC Interpretation Theorem:
The hereditarily finite set fragment admits a faithful interpretation into the ISAR invariant quotient,
and the induced semantic kernel HF_Kernel factors uniquely through ISAR_Kernel in the category of admissible kernels.
-/
theorem HF_Kernel_factorization (f : KernelHom HF_Kernel ISAR_Kernel) (c : HF) :
    OperEq (f.hom c) (encode_raw c) := by
  exact morphism_uniqueness HF_Kernel f c

end ISAR
