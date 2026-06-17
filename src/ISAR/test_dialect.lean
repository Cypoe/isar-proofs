import ISAR.InvariantLayer
import ISAR.KernelCategory

namespace ISAR

-- 1. Dialect Kernel Abstraction
structure Dialect where
  Object : Type
  Obs : Type
  ObsEq : Obs → Obs → Prop
  is_equiv : Equivalence ObsEq
  eval : Object → Obs
  encode : Object → ISKSubtype
  decode : InvariantLayer → Obs
  preserves : ∀ (x : Object), ObsEq (decode (Quotient.mk operEqSetoid (encode x))) (eval x)

-- 2. View Independence & No Preferred Syntax
def DecodersEquivalent (D1 D2 : Dialect) : Prop :=
  ∃ R : D1.Obs → D2.Obs → Prop,
    (∀ (o1 o2 : D1.Obs) (o3 : D2.Obs), D1.ObsEq o1 o2 → R o1 o3 → R o2 o3) ∧
    (∀ q : InvariantLayer, R (D1.decode q) (D2.decode q))

theorem no_preferred_syntax (D1 D2 : Dialect) (h : DecodersEquivalent D1 D2) (q : InvariantLayer) :
    ∃ R : D1.Obs → D2.Obs → Prop, R (D1.decode q) (D2.decode q) := by
  match h with
  | ⟨R, _, hq⟩ =>
      exact ⟨R, hq q⟩

-- 3. Operational Closure & Open/Closed Systems
structure TransitionSystem where
  State : Type
  step : State → State → Prop

def IsClosed (TS : TransitionSystem) (C : TS.State → Prop) : Prop :=
  ∀ s s', C s → TS.step s s' → C s'

def Reachable (TS : TransitionSystem) (s : TS.State) (t : TS.State) : Prop :=
  Relation.ReflTransGen TS.step s t

def BehavioralTrace (TS : TransitionSystem) (s : TS.State) : TS.State → Prop :=
  Reachable TS s


theorem closure_preserved_under_reachability (TS : TransitionSystem) (C : TS.State → Prop) (hc : IsClosed TS C) :
    ∀ s s', C s → Reachable TS s s' → C s' := by
  intro s s' hs hr
  induction hr with
  | refl => exact hs
  | tail _ hstep ih =>
      exact hc _ _ ih hstep


end ISAR
