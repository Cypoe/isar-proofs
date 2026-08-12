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
  cases t1 with
  | iota =>
      cases t2 with
      | iota => rfl
      | app u v =>
          cases u <;> rfl
  | app a b =>
      cases a with
      | iota => rfl
      | app u v => rfl

/-- Proof that `iota_decode_raw` after `iota_encode` is the identity on `IotaTerm`. -/
theorem iota_decode_raw_iota_encode (t : IotaTerm) : iota_decode_raw (iota_encode t) = t := by
  induction t with
  | iota => rfl
  | app t1 t2 ih1 ih2 =>
      unfold iota_decode_raw at ih1 ih2
      unfold iota_decode_raw
      dsimp [iota_encode, app_raw]
      rw [iota_decode_raw_val_app, ih1, ih2]

/--
Observational equivalence on iota terms via substrate OperEq of encodings.
Unlike TRS, `iota_encode ∘ iota_decode_raw` is **not** id on all `ISKSubtype`
(ι is a proper sublanguage), so a syntactic decode `InvariantLayer → IotaTerm`
cannot be lifted without a false “NF stays in ι-image” claim.
-/
def iota_obs_eq (t1 t2 : IotaTerm) : Prop :=
  OperEq (iota_encode t1) (iota_encode t2)

theorem iota_obs_equiv : Equivalence iota_obs_eq where
  refl t := OperEq.refl (iota_encode t)
  symm h := OperEq.symm h
  trans h1 h2 := OperEq.trans h1 h2

/--
`Iota_Dialect` observations are substrate classes (not raw `IotaTerm`).
This keeps the dialect axiom-free and computable: decoding is the
identity on `InvariantLayer`, and `preserves` is definitional. Syntactic
round-trip lives in `iota_decode_raw_iota_encode`.
-/
def Iota_Dialect : Dialect where
  Object := IotaTerm
  Obs := InvariantLayer
  ObsEq := (· = ·)
  is_equiv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }
  eval := fun x => toInvariantLayer (iota_encode x)
  encode := iota_encode
  decode := id
  preserves := fun _ => rfl

/-- Convenience: syntactic decode of a concrete substrate term (not a quotient section). -/
def iota_decode_term (t : ISKSubtype) : IotaTerm :=
  iota_decode_raw t

theorem iota_decode_term_encode (x : IotaTerm) :
    iota_decode_term (iota_encode x) = x :=
  iota_decode_raw_iota_encode x

end ISAR
