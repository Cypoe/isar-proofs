import ISAR.FlowDialect

/-!
# GArrowFlow — Generalized Arrows with Choice and Elgot Iteration

Megacz's Generalized Arrows (multi-level languages without `arr : (a → b) → g a b`),
extended with coproduct choice (`fanin`, matching Koru `KArm` branch dispatch) and
Elgot feedback (`iter`, matching `KFlow.preLabel` / `KArmNode.jump`).

This module lifts `ObservationRegime P` (a setoid of closed terms) to a
setoid-enriched category of staged morphisms (`GArrowFlow`):

* `GArrowFlow` — guest category with composition, coproduct choice, and feedback,
  observed modulo `HomEq`. Deliberately omits `arr` so host functions cannot leak
  into guest dialects.
* `GArrowFlowHom` — structure-preserving realization between two `GArrowFlow`
  regimes (flattening / compilation that respects `id`, `comp`, `fanin`, `iter`).
* `FuelHom` & `koruSemanticArrow` — the semantic `GArrowFlow` instance backed by
  fuel-monotone partial transitions, directly reusing `runK_mono`.
* `denoteInvoke` & `denoteFlow` — compositional `FuelHom` denotations of
  `KGraph`/`KOracle` invocations and `KFlow`s, plus a single-step `iter` unfolding
  matching `runK ... (.loop ...)`.
-/

namespace ISAR

/-! ## Core Generalized Arrow with Choice + Elgot Iteration -/

/-- A staged / categorical observation regime: morphisms between typed ports,
    with coproduct choice (`tor` exits) and feedback (`#label` loops),
    observed modulo `HomEq`. No `arr` — host functions are not embedded. -/
structure GArrowFlow : Type 1 where
  Obj      : Type
  Hom      : Obj → Obj → Type
  HomEq    : ∀ {a b}, Hom a b → Hom a b → Prop
  is_equiv : ∀ {a b}, Equivalence (@HomEq a b)

  -- Category
  id   : ∀ {a}, Hom a a
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c

  -- Coproduct choice (multi-exit routing)
  sum   : Obj → Obj → Obj
  inl   : ∀ {a b}, Hom a (sum a b)
  inr   : ∀ {a b}, Hom b (sum a b)
  fanin : ∀ {a b c}, Hom a c → Hom b c → Hom (sum a b) c

  -- Elgot iteration / feedback: `a → (b ⊕ a)` exits on `inl b`, loops on `inr a`
  iter : ∀ {a b}, Hom a (sum b a) → Hom a b

  -- Categorical laws modulo `HomEq`
  comp_id_left  : ∀ {a b} (f : Hom a b), HomEq (comp id f) f
  comp_id_right : ∀ {a b} (f : Hom a b), HomEq (comp f id) f
  comp_assoc    : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
      HomEq (comp (comp f g) h) (comp f (comp g h))
  comp_congr    : ∀ {a b c} {f1 f2 : Hom a b} {g1 g2 : Hom b c},
      HomEq f1 f2 → HomEq g1 g2 → HomEq (comp f1 g1) (comp f2 g2)

  -- Coproduct beta laws modulo `HomEq`
  fanin_inl : ∀ {a b c} (f : Hom a c) (g : Hom b c),
      HomEq (comp inl (fanin f g)) f
  fanin_inr : ∀ {a b c} (f : Hom a c) (g : Hom b c),
      HomEq (comp inr (fanin f g)) g

/-- A structure-preserving realization functor between two `GArrowFlow` regimes
    (flattening / target emission that preserves wiring modulo target `HomEq`). -/
structure GArrowFlowHom (G1 G2 : GArrowFlow) : Type 1 where
  mapObj : G1.Obj → G2.Obj
  mapHom : ∀ {a b}, G1.Hom a b → G2.Hom (mapObj a) (mapObj b)
  map_congr : ∀ {a b} {f g : G1.Hom a b},
      G1.HomEq f g → G2.HomEq (mapHom f) (mapHom g)
  map_id : ∀ {a}, G2.HomEq (mapHom (@G1.id a)) (@G2.id (mapObj a))
  map_comp : ∀ {a b c} (f : G1.Hom a b) (g : G1.Hom b c),
      G2.HomEq (mapHom (G1.comp f g)) (G2.comp (mapHom f) (mapHom g))

/-! ## Fuel-Monotone Semantic Carrier (`koruSemanticArrow`) -/

/-- A fuel-monotone partial transition `Nat → a → Option b`.
    Fuel is a resource cap, never a semantics change. -/
structure FuelHom (a b : Type) where
  run  : Nat → a → Option b
  mono : ∀ fuel x y, run fuel x = some y → run (fuel + 1) x = some y

/-- Monotonicity lifted to arbitrary `k1 ≤ k2`. -/
theorem FuelHom.mono_le {a b : Type} (f : FuelHom a b) :
    ∀ {k1 k2 : Nat} {x : a} {y : b},
      k1 ≤ k2 → f.run k1 x = some y → f.run k2 x = some y := by
  intro k1 k2 x y hle h
  induction hle with
  | refl => exact h
  | step _ ih => exact f.mono _ x y ih

/-- Eventual observational equivalence: two `FuelHom`s agree iff they decide
    the same outputs at some fuel. -/
def FuelHom.equiv {a b : Type} (f g : FuelHom a b) : Prop :=
  ∀ x y, (∃ k, f.run k x = some y) ↔ (∃ k, g.run k x = some y)

/-- Helper loop for `FuelHom` Elgot iteration. -/
def fuelIterGo {a b : Type} (step : FuelHom a (Sum b a)) : Nat → a → Option b
  | 0, _ => none
  | k + 1, x =>
      match step.run k x with
      | some (.inl res) => some res
      | some (.inr next) => fuelIterGo step k next
      | none => none

theorem fuelIterGo_mono {a b : Type} (step : FuelHom a (Sum b a)) :
    ∀ (fuel : Nat) (x : a) (y : b),
      fuelIterGo step fuel x = some y → fuelIterGo step (fuel + 1) x = some y := by
  intro fuel
  induction fuel with
  | zero =>
    intro x y h
    simp [fuelIterGo] at h
  | succ k ih =>
    intro x y h
    simp only [fuelIterGo] at h ⊢
    cases hs : step.run k x with
    | none => simp [hs] at h
    | some r =>
      simp [hs] at h
      rw [step.mono k x r hs]
      cases r with
      | inl res => exact h
      | inr next => exact ih next y h

/-- Semantic `GArrowFlow` instance for fuel-monotone partial computations. -/
def koruSemanticArrow : GArrowFlow where
  Obj := Type
  Hom := FuelHom
  HomEq := @FuelHom.equiv
  is_equiv := by
    intro a b
    exact ⟨fun _ _ _ => Iff.rfl,
           fun h x y => (h x y).symm,
           fun h1 h2 x y => (h1 x y).trans (h2 x y)⟩
  id := {
    run  := fun _ x => some x
    mono := fun _ _ _ h => h
  }
  comp := fun f g => {
    run  := fun fuel x => (f.run fuel x).bind (g.run fuel)
    mono := by
      intro fuel x z h
      cases hf : f.run fuel x with
      | none => simp [hf] at h
      | some y =>
        simp [hf] at h
        rw [f.mono fuel x y hf]
        exact g.mono fuel y z h
  }
  sum := Sum
  inl := {
    run  := fun _ x => some (.inl x)
    mono := fun _ _ _ h => h
  }
  inr := {
    run  := fun _ x => some (.inr x)
    mono := fun _ _ _ h => h
  }
  fanin := fun f g => {
    run := fun fuel s => match s with
      | .inl a => f.run fuel a
      | .inr b => g.run fuel b
    mono := by
      intro fuel s z h
      cases s with
      | inl a => exact f.mono fuel a z h
      | inr b => exact g.mono fuel b z h
  }
  iter := fun step => {
    run  := fuelIterGo step
    mono := fuelIterGo_mono step
  }
  comp_id_left := by
    intro a b f x y
    simp [Option.bind]
  comp_id_right := by
    intro a b f x y
    constructor
    · rintro ⟨k, hk⟩
      cases h : f.run k x with
      | none => simp [h] at hk
      | some z => simp [h] at hk; exact ⟨k, hk ▸ h⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simp [hk]⟩
  comp_assoc := by
    intro a b c d f g h x w
    constructor
    · rintro ⟨k, hk⟩
      cases hf : f.run k x with
      | none => simp [hf] at hk
      | some y =>
        simp [hf] at hk
        cases hg : g.run k y with
        | none => simp [hg] at hk
        | some z =>
          simp [hg] at hk
          exact ⟨k, by simp [hf, hg, hk]⟩
    · rintro ⟨k, hk⟩
      cases hf : f.run k x with
      | none => simp [hf] at hk
      | some y =>
        simp [hf] at hk
        cases hg : g.run k y with
        | none => simp [hg] at hk
        | some z =>
          simp [hg] at hk
          exact ⟨k, by simp [hf, hg, hk]⟩
  comp_congr := by
    intro a b c f1 f2 g1 g2 hf hg x z
    constructor
    · rintro ⟨k, hk⟩
      cases h1 : f1.run k x with
      | none => simp [h1] at hk
      | some y =>
        simp [h1] at hk
        obtain ⟨kf, hkf⟩ := (hf x y).mp ⟨k, h1⟩
        obtain ⟨kg, hkg⟩ := (hg y z).mp ⟨k, hk⟩
        refine ⟨max kf kg, ?_⟩
        rw [f2.mono_le (Nat.le_max_left kf kg) hkf]
        exact g2.mono_le (Nat.le_max_right kf kg) hkg
    · rintro ⟨k, hk⟩
      cases h2 : f2.run k x with
      | none => simp [h2] at hk
      | some y =>
        simp [h2] at hk
        obtain ⟨kf, hkf⟩ := (hf x y).mpr ⟨k, h2⟩
        obtain ⟨kg, hkg⟩ := (hg y z).mpr ⟨k, hk⟩
        refine ⟨max kf kg, ?_⟩
        rw [f1.mono_le (Nat.le_max_left kf kg) hkf]
        exact g1.mono_le (Nat.le_max_right kf kg) hkg
  fanin_inl := by
    intro a b c f g x y
    simp [Option.bind]
  fanin_inr := by
    intro a b c f g x y
    simp [Option.bind]

/-! ## Lifting `FlowDialect` (`runK`) into `FuelHom` -/

/-- Lift any `KGraph`/`KOracle` invocation of a named callable into a
    `FuelHom (List (String × KVal)) KResult`, reusing `runK_mono`. -/
def denoteInvoke (g : KGraph) (o : KOracle) (name : String) :
    FuelHom (List (String × KVal)) KResult where
  run  := fun fuel args => asKResult (runK g o fuel (.invoke name args))
  mono := by
    intro fuel args res h
    unfold asKResult at h ⊢
    cases hr : runK g o fuel (.invoke name args) with
    | none => simp [hr] at h
    | some oc =>
      simp [hr] at h
      cases oc with
      | result r =>
        rw [runK_mono g o fuel (.invoke name args) (.result r) hr]
        exact h
      | jump _ _ => simp at h
      | done => simp at h
      | skip => simp at h

/-- Lift a `KFlow` directly into `FuelHom (List (String × KVal)) KResult`. -/
def denoteFlow (g : KGraph) (o : KOracle) (fl : KFlow) :
    FuelHom (List (String × KVal)) KResult where
  run  := fun fuel args => asKResult (runK g o fuel (.flow fl args))
  mono := by
    intro fuel args res h
    unfold asKResult at h ⊢
    cases hr : runK g o fuel (.flow fl args) with
    | none => simp [hr] at h
    | some oc =>
      simp [hr] at h
      cases oc with
      | result r =>
        rw [runK_mono g o fuel (.flow fl args) (.result r) hr]
        exact h
      | jump _ _ => simp at h
      | done => simp at h
      | skip => simp at h

/-- One iteration step of a `KFlow` loop as a `FuelHom` into a coproduct:
    `inl r` = flow exits with `KResult`, `inr jargs` = flow jumps back to `preLabel`. -/
def denoteFlowStep (g : KGraph) (o : KOracle) (fl : KFlow) (env : KEnv) :
    FuelHom (List (String × KVal)) (Sum KResult (List (String × KVal))) where
  run := fun fuel hargs =>
    match runK g o fuel (.invoke fl.head.1 hargs) with
    | some (.result r) =>
        if fl.arms.isEmpty then some (.inl r)
        else
          let disp := match r.branch with
            | some b => runK g o fuel (.dispatchTag env fl.arms b r)
            | none   => runK g o fuel (.dispatchBare env fl.arms r)
          match disp with
          | some (.result rr) => some (.inl rr)
          | some .done => some (.inl {})
          | some (.jump lbl jargs) =>
              if fl.preLabel == some lbl then some (.inr jargs) else none
          | _ => none
    | _ => none
  mono := by
    intro fuel hargs out h
    cases hr : runK g o fuel (.invoke fl.head.1 hargs) with
    | none => simp [hr] at h
    | some oc =>
      simp [hr] at h
      cases oc with
      | result r =>
        rw [runK_mono g o fuel (.invoke fl.head.1 hargs) (.result r) hr]
        dsimp only at h ⊢
        cases hE : fl.arms.isEmpty with
        | true => simp [hE] at h ⊢; exact h
        | false =>
          simp [hE] at h ⊢
          cases hbr : r.branch with
          | some b =>
            simp [hbr] at h ⊢
            cases hd : runK g o fuel (.dispatchTag env fl.arms b r) with
            | none => simp [hd] at h
            | some oc2 =>
              simp [hd] at h
              rw [runK_mono g o fuel (.dispatchTag env fl.arms b r) oc2 hd]
              exact h
          | none =>
            simp [hbr] at h ⊢
            cases hd : runK g o fuel (.dispatchBare env fl.arms r) with
            | none => simp [hd] at h
            | some oc2 =>
              simp [hd] at h
              rw [runK_mono g o fuel (.dispatchBare env fl.arms r) oc2 hd]
              exact h
      | jump _ _ => simp at h
      | done => simp at h
      | skip => simp at h

/-- Running a `KFlow` via `koruSemanticArrow.iter (denoteFlowStep g o fl env)`
    gives a `FuelHom` for the loop body directly from the GArrow feedback combinator. -/
def denoteFlowLoop (g : KGraph) (o : KOracle) (fl : KFlow) (env : KEnv) :
    FuelHom (List (String × KVal)) KResult :=
  koruSemanticArrow.iter (denoteFlowStep g o fl env)

/-! ## Fixtures — checking `denoteInvoke` against `kArith` -/

theorem denoteInvoke_kArith :
    (denoteInvoke kArith.graph [] "main").run 32 [] =
      evalKProg kArith [] 32 := by
  rfl

end ISAR
