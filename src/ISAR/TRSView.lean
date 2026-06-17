import ISAR.DialectKernel
import ISAR.HFSetEncoding

namespace ISAR

/-- A simple term rewriting language representing the pure SKI combinator terms. -/
inductive TTerm : Type where
  | I : TTerm
  | K : TTerm
  | S : TTerm
  | app : TTerm → TTerm → TTerm
deriving DecidableEq, Repr

/-- Compile/encode a `TTerm` into the substrate fragment `ISKSubtype`. -/
def trs_encode : TTerm → ISKSubtype
  | TTerm.I => ⟨ITerm.norm, ISKTerm.norm⟩
  | TTerm.K => ⟨ITerm.konst, ISKTerm.konst⟩
  | TTerm.S => ⟨ITerm.sₛ, ISKTerm.sₛ⟩
  | TTerm.app t1 t2 => app_raw (trs_encode t1) (trs_encode t2)

/-- Constructive decoder over the ITerm structure. -/
def decode_raw_val : ITerm → TTerm
  | ITerm.norm => TTerm.I
  | ITerm.konst => TTerm.K
  | ITerm.sₛ => TTerm.S
  | ITerm.app f x => TTerm.app (decode_raw_val f) (decode_raw_val x)
  | _ => TTerm.I

/-- Decode an `ISKSubtype` back to `TTerm`. -/
def decode_raw (t : ISKSubtype) : TTerm :=
  decode_raw_val t.val

/-- Proof that `decode_raw` after `trs_encode` is the identity on `TTerm`. -/
theorem decode_raw_trs_encode (t : TTerm) : decode_raw (trs_encode t) = t := by
  induction t with
  | I => rfl
  | K => rfl
  | S => rfl
  | app t1 t2 ih1 ih2 =>
      unfold decode_raw at ih1 ih2
      unfold decode_raw
      dsimp [trs_encode, app_raw, decode_raw_val]
      rw [ih1, ih2]

/-- Proof that `trs_encode` after `decode_raw` is the identity on `ISKSubtype`. -/
theorem trs_encode_decode_raw_val (t : ITerm) (h : ISKTerm t) :
    (trs_encode (decode_raw_val t)).val = t := by
  induction h with
  | norm => rfl
  | konst => rfl
  | sₛ => rfl
  | app hf hx ihf ihx =>
      dsimp [decode_raw_val, trs_encode, app_raw]
      rw [ihf, ihx]

theorem trs_encode_decode_raw (t : ISKSubtype) : trs_encode (decode_raw t) = t := by
  let ⟨val, property⟩ := t
  dsimp [decode_raw]
  have h_val := trs_encode_decode_raw_val val property
  exact Subtype.ext h_val

/-- Decode from the Invariant Layer quotient class into a `TTerm`. -/
noncomputable def trs_decode (q : InvariantLayer) : TTerm :=
  decode_raw (InvariantLayer.canonical_rep q)

/-- The observational equivalence relation on `TTerm`, reducing to operational equivalence of encodings. -/
def trs_obs_eq (t1 t2 : TTerm) : Prop :=
  OperEq (trs_encode t1) (trs_encode t2)

/-- Proof that `trs_obs_eq` is an equivalence relation. -/
def trs_obs_equiv : Equivalence trs_obs_eq where
  refl t := OperEq.refl (trs_encode t)
  symm h := OperEq.symm h
  trans h1 h2 := OperEq.trans h1 h2

/-- The concrete `TRS_Dialect : Dialect` instance. -/
noncomputable def TRS_Dialect : Dialect where
  Object := TTerm
  Obs := TTerm
  ObsEq := trs_obs_eq
  is_equiv := trs_obs_equiv
  eval := id
  encode := trs_encode
  decode := trs_decode
  preserves := by
    intro x
    unfold trs_obs_eq trs_decode
    dsimp
    have h_eq : trs_encode (decode_raw (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid (trs_encode x)))) =
                InvariantLayer.canonical_rep (Quotient.mk operEqSetoid (trs_encode x)) := by
      exact trs_encode_decode_raw _
    rw [h_eq]
    exact canonical_rep_eq (trs_encode x)

end ISAR
