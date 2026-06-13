namespace ISAR

/- =========================================================
   1. Operationally Closed Systems
   ========================================================= -/

/-- A standard autonomous transition system. -/
structure TransitionSystem where
  State : Type
  step : State → State → Prop

/-- Reflexive transitive closure of the transition relation. -/
inductive Reachable (TS : TransitionSystem) : TS.State → TS.State → Prop where
  | refl (s : TS.State) : Reachable TS s s
  | tail (s1 s2 s3 : TS.State) : Reachable TS s1 s2 → TS.step s2 s3 → Reachable TS s1 s3

/-- A subset of states C is closed under steps of the transition system. -/
def IsClosed (TS : TransitionSystem) (C : TS.State → Prop) : Prop :=
  ∀ (s1 s2 : TS.State), C s1 → TS.step s1 s2 → C s2

/--
Forward Invariance of Closed Subsystems:
If a system state-space subset C is closed under steps (forward invariant),
then any state reachable from C remains in C.
-/
theorem closure_preserved_under_reachability (TS : TransitionSystem) (C : TS.State → Prop) (hc : IsClosed TS C) :
    ∀ (s1 s2 : TS.State), C s1 → Reachable TS s1 s2 → C s2 := by
  intro s1 s2 hC hReach
  induction hReach with
  | refl => exact hC
  | tail s_mid s_end _ h_step ih =>
      exact hc s_mid s_end ih h_step



/- =========================================================
   2. Referentially Open (Anchor-Dependent) Systems
   ========================================================= -/

/-- A transition system where transitions depend on an external anchor (environment/context). -/
structure AnchorDependentSystem where
  State : Type
  Anchor : Type
  step : State → Anchor → State → Prop

/-- Trace of an anchor-dependent system under a sequence of anchors. -/
inductive Trace (ADS : AnchorDependentSystem) : ADS.State → List ADS.Anchor → ADS.State → Prop where
  | nil (s : ADS.State) : Trace ADS s [] s
  | cons (s1 s2 s3 : ADS.State) (a : ADS.Anchor) (as : List ADS.Anchor) :
      ADS.step s1 a s2 → Trace ADS s2 as s3 → Trace ADS s1 (a :: as) s3

/--
Referentially Open Requires Anchor Theorem:
If a state `s` can lead to different observations under different anchor sequences `as1` and `as2`,
then the trace semantics are not recoverable from the state alone (without the anchors).
-/
theorem referentially_open_requires_anchor (ADS : AnchorDependentSystem) (Obs : Type) (decode : ADS.State → Obs)
    (s s1' s2' : ADS.State) (as1 as2 : List ADS.Anchor)
    (_h1 : Trace ADS s as1 s1') (h2 : Trace ADS s as2 s2')
    (h_diff : decode s1' ≠ decode s2') :
    ∃ (as : List ADS.Anchor), ¬ (∀ (s' : ADS.State), Trace ADS s as s' → decode s' = decode s1') := by
  -- We witness this using the second anchor sequence as2.
  -- If for all states s', Trace ADS s as2 s' implies decode s' = decode s1',
  -- then since s2' is reachable under as2, decode s2' = decode s1', which contradicts h_diff.
  refine ⟨as2, ?_⟩
  intro h_all
  have h_eq := h_all s2' h2
  exact h_diff h_eq.symm

end ISAR
