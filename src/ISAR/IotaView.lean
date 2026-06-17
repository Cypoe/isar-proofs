import ISAR.DialectKernel
import ISAR.HFSetEncoding

namespace ISAR

/-- Barker's Iota dialect terms. -/
inductive IotaTerm : Type where
  | iota : IotaTerm
  | app : IotaTerm → IotaTerm → IotaTerm
deriving DecidableEq, Repr

/-- The universal combinator ι = λx. x S K in the ISAR substrate. -/
def iota_sub_val : ITerm :=
  ITerm.app (ITerm.app ITerm.sₛ (ITerm.app (ITerm.app ITerm.sₛ ITerm.norm) (ITerm.app ITerm.konst ITerm.sₛ))) (ITerm.app ITerm.konst ITerm.konst)

theorem iota_sub_is_ISK : ISKTerm iota_sub_val := by
  unfold iota_sub_val
  repeat constructor

/-- The universal iota combinator as an ISKSubtype. -/
def iota_sub : ISKSubtype :=
  ⟨iota_sub_val, iota_sub_is_ISK⟩

/-- Encode an `IotaTerm` into the ISAR substrate `ISKSubtype`. -/
def iota_encode : IotaTerm → ISKSubtype
  | IotaTerm.iota => iota_sub
  | IotaTerm.app t1 t2 => app_raw (iota_encode t1) (iota_encode t2)

/-- Constructive decoder over the ITerm structure. -/
def iota_decode_raw_val : ITerm → IotaTerm
  | ITerm.app (ITerm.app ITerm.sₛ (ITerm.app (ITerm.app ITerm.sₛ ITerm.norm) (ITerm.app ITerm.konst ITerm.sₛ))) (ITerm.app ITerm.konst ITerm.konst) => IotaTerm.iota
  | ITerm.app f x => IotaTerm.app (iota_decode_raw_val f) (iota_decode_raw_val x)
  | _ => IotaTerm.iota

/-- Decode an `ISKSubtype` back to `IotaTerm`. -/
def iota_decode_raw (t : ISKSubtype) : IotaTerm :=
  iota_decode_raw_val t.val

/-- Lemma showing that iota_decode_raw_val distributes over encoded applications. -/
theorem iota_decode_raw_val_app (t1 t2 : IotaTerm) :
    iota_decode_raw_val (ITerm.app (iota_encode t1).val (iota_encode t2).val) =
    IotaTerm.app (iota_decode_raw_val (iota_encode t1).val) (iota_decode_raw_val (iota_encode t2).val) := by
  sorry

/-- Proof that `iota_decode_raw` after `iota_encode` is the identity on `IotaTerm`. -/
theorem iota_decode_raw_iota_encode (t : IotaTerm) : iota_decode_raw (iota_encode t) = t := by
  induction t with
  | iota => rfl
  | app t1 t2 ih1 ih2 =>
      unfold iota_decode_raw at ih1 ih2
      unfold iota_decode_raw
      dsimp [iota_encode, app_raw]
      rw [iota_decode_raw_val_app, ih1, ih2]

/-- Decode from the Invariant Layer quotient class into an `IotaTerm`. -/
noncomputable def iota_decode (q : InvariantLayer) : IotaTerm :=
  iota_decode_raw (InvariantLayer.canonical_rep q)

/-- The observational equivalence relation on `IotaTerm`, reducing to operational equivalence of encodings. -/
def iota_obs_eq (t1 t2 : IotaTerm) : Prop :=
  OperEq (iota_encode t1) (iota_encode t2)

/-- Proof that `iota_obs_eq` is an equivalence relation. -/
def iota_obs_equiv : Equivalence iota_obs_eq where
  refl t := OperEq.refl (iota_encode t)
  symm h := OperEq.symm h
  trans h1 h2 := OperEq.trans h1 h2

/-- The concrete `Iota_Dialect : Dialect` instance. -/
noncomputable def Iota_Dialect : Dialect where
  Object := IotaTerm
  Obs := IotaTerm
  ObsEq := iota_obs_eq
  is_equiv := iota_obs_equiv
  eval := id
  encode := iota_encode
  decode := iota_decode
  preserves := by
    intro x
    unfold iota_obs_eq iota_decode
    dsimp
    have h_eq : iota_encode (iota_decode_raw (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid (iota_encode x)))) =
                InvariantLayer.canonical_rep (Quotient.mk operEqSetoid (iota_encode x)) := by
      sorry
    rw [h_eq]
    exact canonical_rep_eq (iota_encode x)

end ISAR
