import ISAR.InvariantLayer
import ISAR.DialectKernel
import ISAR.TRSView
import ISAR.BytecodeView

namespace ISAR

/-!
# Admissible observation regimes

Phase 3 deliverable: a first-class observational contract \(\mathcal O\).

Two presentations are equivalent under a regime when their observations agree:

\[
p_1 \sim_{\mathcal O} p_2 \;\iff\;
\operatorname{ObsEq}(\operatorname{observe}(p_1), \operatorname{observe}(p_2))
\]

`OperEq` / `InvariantLayer` is the primary ISAR instance. Dialects supply
`QuotientMapO` maps that **preserve** a declared regime — they do not invent \(\sim\).

EAL and Interaction Combinators are not regimes; they may appear later only as
realization backends \(R_{c,\mathcal O}\). BCWI ⊬ K remains absolute.
-/

/--
Admissible observation regime on a presentation type.

A single bundled `Obs` stands for a family of observers (pair into a product if needed).
-/
structure ObservationRegime (Presentation : Type) where
  Obs : Type
  observe : Presentation → Obs
  ObsEq : Obs → Obs → Prop
  is_equiv : Equivalence ObsEq

/-- Context-indexed observational equivalence \(p_1 \sim_{\mathcal O} p_2\). -/
def ObservationRegime.sim {P : Type} (R : ObservationRegime P) (p1 p2 : P) : Prop :=
  R.ObsEq (R.observe p1) (R.observe p2)

theorem ObservationRegime.sim_refl {P : Type} (R : ObservationRegime P) (p : P) :
    R.sim p p :=
  R.is_equiv.refl (R.observe p)

theorem ObservationRegime.sim_symm {P : Type} (R : ObservationRegime P)
    {p1 p2 : P} (h : R.sim p1 p2) : R.sim p2 p1 :=
  R.is_equiv.symm h

theorem ObservationRegime.sim_trans {P : Type} (R : ObservationRegime P)
    {p1 p2 p3 : P} (h1 : R.sim p1 p2) (h2 : R.sim p2 p3) : R.sim p1 p3 :=
  R.is_equiv.trans h1 h2

/-- Setoid induced by a regime. -/
def ObservationRegime.toSetoid {P : Type} (R : ObservationRegime P) : Setoid P where
  r := R.sim
  iseqv := ⟨R.sim_refl, R.sim_symm, R.sim_trans⟩

/-- Quotient of presentations by \(\sim_{\mathcal O}\). -/
def ObservationRegime.Quot {P : Type} (R : ObservationRegime P) : Type :=
  Quotient (R.toSetoid)

/- =========================================================
   Primary ISAR regime: OperEq / InvariantLayer
   ========================================================= -/

/--
Primary substrate regime: observe an `ISKSubtype` as its `OperEq` class.
-/
def operEqRegime : ObservationRegime ISKSubtype where
  Obs := InvariantLayer
  observe := toInvariantLayer
  ObsEq := (· = ·)
  is_equiv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

theorem operEqRegime_sim_iff (t u : ISKSubtype) :
    operEqRegime.sim t u ↔ OperEq t u := by
  dsimp [ObservationRegime.sim, operEqRegime, toInvariantLayer]
  -- ⊢ Quotient.mk operEqSetoid t = Quotient.mk operEqSetoid u ↔ OperEq t u
  exact (@Quotient.eq ISKSubtype operEqSetoid t u)

/- =========================================================
   Quotient maps that preserve a regime
   ========================================================= -/

/--
A quotient map into the OperEq substrate that states exactly what is preserved:
decoding the class of an encoding recovers the regime's observation of `p`.
-/
structure QuotientMapO (P : Type) (R : ObservationRegime P) where
  encode : P → ISKSubtype
  decode : InvariantLayer → R.Obs
  preserves : ∀ (p : P),
    R.ObsEq (decode (toInvariantLayer (encode p))) (R.observe p)

/-- Encoding is sound for \(\sim_{\mathcal O}\) when decode respects OperEq. -/
theorem QuotientMapO.encode_sound {P : Type} {R : ObservationRegime P}
    (M : QuotientMapO P R)
    (h_resp : ∀ {t u : ISKSubtype}, OperEq t u →
      R.ObsEq (M.decode (toInvariantLayer t)) (M.decode (toInvariantLayer u)))
    {p1 p2 : P}
    (h : OperEq (M.encode p1) (M.encode p2)) :
    R.sim p1 p2 := by
  have h1 := M.preserves p1
  have h2 := M.preserves p2
  have h12 := h_resp h
  exact R.is_equiv.trans (R.is_equiv.symm h1) (R.is_equiv.trans h12 h2)

/- =========================================================
   Dialects as regime-preserving quotient maps
   ========================================================= -/

/-- Regime on dialect objects: observe via the dialect's `eval`. -/
def Dialect.observationRegime (D : Dialect) : ObservationRegime D.Object where
  Obs := D.Obs
  observe := D.eval
  ObsEq := D.ObsEq
  is_equiv := D.is_equiv

/-- Every `Dialect` yields a `QuotientMapO` under its own observation regime. -/
def Dialect.toQuotientMapO (D : Dialect) : QuotientMapO D.Object D.observationRegime where
  encode := D.encode
  decode := D.decode
  preserves := D.preserves

/-- TRS presentations observed as `TTerm` modulo encoding-OperEq. -/
def trsObsRegime : ObservationRegime TTerm :=
  TRS_Dialect.observationRegime

def TRS_QuotientMapO : QuotientMapO TTerm trsObsRegime :=
  TRS_Dialect.toQuotientMapO

/-- Bytecode presentations observed modulo encoding-OperEq. -/
def bytecodeObsRegime : ObservationRegime (List Instruction) :=
  Bytecode_Dialect.observationRegime

def Bytecode_QuotientMapO : QuotientMapO (List Instruction) bytecodeObsRegime :=
  Bytecode_Dialect.toQuotientMapO

/--
Encoding into the substrate respects the primary `operEqRegime`:
observe is `toInvariantLayer` on the encoded term.
-/
theorem dialect_encode_operEq {D : Dialect} (x : D.Object) :
    operEqRegime.observe (D.encode x) = toInvariantLayer (D.encode x) :=
  rfl

end ISAR
