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

/-- The observational equivalence relation on `TTerm`, reducing to operational equivalence of encodings. -/
def trs_obs_eq (t1 t2 : TTerm) : Prop :=
  OperEq (trs_encode t1) (trs_encode t2)

/-- Proof that `trs_obs_eq` is an equivalence relation. -/
theorem trs_obs_equiv : Equivalence trs_obs_eq where
  refl t := OperEq.refl (trs_encode t)
  symm h := OperEq.symm h
  trans h1 h2 := OperEq.trans h1 h2

/-- Setoid of TRS observations (OperEq of encodings). -/
def trsObsSetoid : Setoid TTerm where
  r := trs_obs_eq
  iseqv := trs_obs_equiv

/-- Observation space: `TTerm` modulo observational equivalence. -/
abbrev TTermObs := Quotient trsObsSetoid

/--
Decode an OperEq-class to a TRS observation.
Well-defined because `trs_encode ∘ decode_raw = id` on `ISKSubtype`, so OperEq
of substrate terms induces `trs_obs_eq` of decodings — no `canonical_rep` / choice.
-/
def trs_decode (q : InvariantLayer) : TTermObs :=
  Quotient.lift
    (fun t : ISKSubtype => Quotient.mk trsObsSetoid (decode_raw t))
    (fun a b (h : OperEq a b) => by
      apply Quotient.sound
      change trs_obs_eq (decode_raw a) (decode_raw b)
      unfold trs_obs_eq
      simpa [trs_encode_decode_raw] using h)
    q

/-- The concrete `TRS_Dialect : Dialect` instance (computable; OperEq observations). -/
def TRS_Dialect : Dialect where
  Object := TTerm
  Obs := TTermObs
  ObsEq := (· = ·)
  is_equiv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }
  eval := Quotient.mk trsObsSetoid
  encode := trs_encode
  decode := trs_decode
  preserves := by
    intro x
    -- `trs_decode (⟦encode x⟧) = ⟦decode_raw (encode x)⟧ = ⟦x⟧`
    change Quotient.mk trsObsSetoid (decode_raw (trs_encode x)) =
      Quotient.mk trsObsSetoid x
    rw [decode_raw_trs_encode]

end ISAR
