import ISAR.InvariantLayer
import ISAR.LambdaFragment

namespace ISAR

/-!
Term model: tensors *are* `ITerm`s; extensional equality is `IRed`-joinability
(confluence is `IRed_confluence`). Combinators `B`/`C`/`W` are SKI encodings so
`dup`/`swap`/`comp` β-laws are theorems, not axioms.
-/

abbrev TensorSpace := ITerm

def ExtEq (t u : TensorSpace) : Prop := ∃ v, IRed t v ∧ IRed u v

theorem ExtEq.refl (t : TensorSpace) : ExtEq t t :=
  ⟨t, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem ExtEq.symm {t u : TensorSpace} : ExtEq t u → ExtEq u t
  | ⟨v, ht, hu⟩ => ⟨v, hu, ht⟩

theorem ExtEq.trans {t u w : TensorSpace} (h1 : ExtEq t u) (h2 : ExtEq u w) : ExtEq t w := by
  rcases h1 with ⟨v, ht, hu⟩
  rcases h2 with ⟨v', hu', hw⟩
  rcases IRed_confluence hu hu' with ⟨z, hvz, hv'z⟩
  exact ⟨z, Relation.ReflTransGen.trans ht hvz, Relation.ReflTransGen.trans hw hv'z⟩

def t_norm : TensorSpace := ITerm.norm
def t_konst : TensorSpace := ITerm.konst
def t_var : Nat → TensorSpace := ITerm.var
def t_app : TensorSpace → TensorSpace → TensorSpace := ITerm.app

/-- `B = S (K S) K`. -/
def t_comp : TensorSpace :=
  t_app (t_app ITerm.sₛ (t_app ITerm.konst ITerm.sₛ)) ITerm.konst

/-- `W = S S (K I)`. -/
def t_dup : TensorSpace :=
  t_app (t_app ITerm.sₛ ITerm.sₛ) (t_app ITerm.konst ITerm.norm)

/-- `C = S (S (K B) S) (K K)`. -/
def t_swap : TensorSpace :=
  t_app (t_app ITerm.sₛ (t_app (t_app ITerm.sₛ (t_app ITerm.konst t_comp)) ITerm.sₛ))
    (t_app ITerm.konst ITerm.konst)

theorem t_app_congr {t1 t2 u1 u2 : TensorSpace}
    (ht : ExtEq t1 t2) (hu : ExtEq u1 u2) :
    ExtEq (t_app t1 u1) (t_app t2 u2) := by
  rcases ht with ⟨v, ht1, ht2⟩
  rcases hu with ⟨w, hu1, hu2⟩
  exact ⟨t_app v w, IRed_app ht1 hu1, IRed_app ht2 hu2⟩

theorem t_app_congr_left {t1 t2 u : TensorSpace} (h : ExtEq t1 t2) :
    ExtEq (t_app t1 u) (t_app t2 u) :=
  t_app_congr h (ExtEq.refl u)

theorem t_app_congr_right {t u1 u2 : TensorSpace} (h : ExtEq u1 u2) :
    ExtEq (t_app t u1) (t_app t u2) :=
  t_app_congr (ExtEq.refl t) h

theorem t_norm_beta (x : TensorSpace) : ExtEq (t_app t_norm x) x :=
  ⟨x, Relation.ReflTransGen.single (IStep.normβ x), Relation.ReflTransGen.refl⟩

theorem t_konst_beta (x y : TensorSpace) : ExtEq (t_app (t_app t_konst x) y) x :=
  ⟨x, Relation.ReflTransGen.single (IStep.konstβ x y), Relation.ReflTransGen.refl⟩

theorem t_comp_app_f (f : TensorSpace) :
    IRed (t_app t_comp f) (t_app ITerm.sₛ (t_app ITerm.konst f)) := by
  have hstep : IStep (t_app t_comp f)
      (t_app (t_app (t_app ITerm.konst ITerm.sₛ) f) (t_app ITerm.konst f)) := by
    dsimp [t_comp, t_app]
    exact IStep.sβ (ITerm.app ITerm.konst ITerm.sₛ) ITerm.konst f
  have hcong : IStep
      (t_app (t_app (t_app ITerm.konst ITerm.sₛ) f) (t_app ITerm.konst f))
      (t_app ITerm.sₛ (t_app ITerm.konst f)) :=
    IStep.appL (IStep.konstβ ITerm.sₛ f)
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hstep) hcong

theorem t_comp_red (f g x : TensorSpace) :
    IRed (t_app (t_app (t_app t_comp f) g) x) (t_app f (t_app g x)) := by
  have hfgx : IRed (t_app (t_app (t_app t_comp f) g) x)
      (t_app (t_app (t_app ITerm.sₛ (t_app ITerm.konst f)) g) x) :=
    IRed_app_left (IRed_app_left (t_comp_app_f f))
  have hs : IStep (t_app (t_app (t_app ITerm.sₛ (t_app ITerm.konst f)) g) x)
      (t_app (t_app (t_app ITerm.konst f) x) (t_app g x)) :=
    IStep.sβ (t_app ITerm.konst f) g x
  have hk : IStep (t_app (t_app (t_app ITerm.konst f) x) (t_app g x))
      (t_app f (t_app g x)) :=
    IStep.appL (IStep.konstβ f x)
  exact Relation.ReflTransGen.trans hfgx
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs) hk)

theorem t_comp_beta (f g x : TensorSpace) :
    ExtEq (t_app (t_app (t_app t_comp f) g) x) (t_app f (t_app g x)) :=
  ⟨t_app f (t_app g x), t_comp_red f g x, Relation.ReflTransGen.refl⟩

theorem t_dup_red (f x : TensorSpace) :
    IRed (t_app (t_app t_dup f) x) (t_app (t_app f x) x) := by
  have h1 : IStep (t_app t_dup f)
      (t_app (t_app ITerm.sₛ f) (t_app (t_app ITerm.konst ITerm.norm) f)) := by
    dsimp [t_dup, t_app]
    exact IStep.sβ ITerm.sₛ (ITerm.app ITerm.konst ITerm.norm) f
  have h2 : IStep (t_app (t_app ITerm.sₛ f) (t_app (t_app ITerm.konst ITerm.norm) f))
      (t_app (t_app ITerm.sₛ f) ITerm.norm) :=
    IStep.appR (IStep.konstβ ITerm.norm f)
  have hf : IRed (t_app t_dup f) (t_app (t_app ITerm.sₛ f) ITerm.norm) :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2
  have hfx : IRed (t_app (t_app t_dup f) x)
      (t_app (t_app (t_app ITerm.sₛ f) ITerm.norm) x) :=
    IRed_app_left hf
  have hs : IStep (t_app (t_app (t_app ITerm.sₛ f) ITerm.norm) x)
      (t_app (t_app f x) (t_app ITerm.norm x)) :=
    IStep.sβ f ITerm.norm x
  have hi : IStep (t_app (t_app f x) (t_app ITerm.norm x)) (t_app (t_app f x) x) :=
    IStep.appR (IStep.normβ x)
  exact Relation.ReflTransGen.trans hfx
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs) hi)

theorem t_dup_beta (f x : TensorSpace) :
    ExtEq (t_app (t_app t_dup f) x) (t_app (t_app f x) x) :=
  ⟨t_app (t_app f x) x, t_dup_red f x, Relation.ReflTransGen.refl⟩

theorem t_swap_red (f x y : TensorSpace) :
    IRed (t_app (t_app (t_app t_swap f) x) y) (t_app (t_app f y) x) := by
  let P := t_app (t_app ITerm.sₛ (t_app ITerm.konst t_comp)) ITerm.sₛ
  have h1 : IStep (t_app t_swap f)
      (t_app (t_app P f) (t_app (t_app ITerm.konst ITerm.konst) f)) := by
    dsimp [t_swap, t_app, P]
    exact IStep.sβ P (ITerm.app ITerm.konst ITerm.konst) f
  have h2 : IStep (t_app (t_app P f) (t_app (t_app ITerm.konst ITerm.konst) f))
      (t_app (t_app P f) ITerm.konst) :=
    IStep.appR (IStep.konstβ ITerm.konst f)
  have hCf : IRed (t_app t_swap f) (t_app (t_app P f) ITerm.konst) :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2
  have hP : IStep (t_app P f)
      (t_app (t_app (t_app ITerm.konst t_comp) f) (t_app ITerm.sₛ f)) := by
    dsimp [P, t_app]
    exact IStep.sβ (t_app ITerm.konst t_comp) ITerm.sₛ f
  have hP2 : IStep (t_app (t_app (t_app ITerm.konst t_comp) f) (t_app ITerm.sₛ f))
      (t_app t_comp (t_app ITerm.sₛ f)) :=
    IStep.appL (IStep.konstβ t_comp f)
  have hPf : IRed (t_app P f) (t_app t_comp (t_app ITerm.sₛ f)) :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single hP) hP2
  have hCf' : IRed (t_app t_swap f) (t_app (t_app t_comp (t_app ITerm.sₛ f)) ITerm.konst) :=
    Relation.ReflTransGen.trans hCf (IRed_app_left hPf)
  have hCfx : IRed (t_app (t_app t_swap f) x)
      (t_app (t_app (t_app t_comp (t_app ITerm.sₛ f)) ITerm.konst) x) :=
    IRed_app_left hCf'
  have hB := t_comp_red (t_app ITerm.sₛ f) ITerm.konst x
  have hCfx' : IRed (t_app (t_app t_swap f) x)
      (t_app (t_app ITerm.sₛ f) (t_app ITerm.konst x)) :=
    Relation.ReflTransGen.trans hCfx hB
  have hCfxy : IRed (t_app (t_app (t_app t_swap f) x) y)
      (t_app (t_app (t_app ITerm.sₛ f) (t_app ITerm.konst x)) y) :=
    IRed_app_left hCfx'
  have hs : IStep (t_app (t_app (t_app ITerm.sₛ f) (t_app ITerm.konst x)) y)
      (t_app (t_app f y) (t_app (t_app ITerm.konst x) y)) :=
    IStep.sβ f (t_app ITerm.konst x) y
  have hk : IStep (t_app (t_app f y) (t_app (t_app ITerm.konst x) y))
      (t_app (t_app f y) x) :=
    IStep.appR (IStep.konstβ x y)
  exact Relation.ReflTransGen.trans hCfxy
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs) hk)

theorem t_swap_beta (f x y : TensorSpace) :
    ExtEq (t_app (t_app (t_app t_swap f) x) y) (t_app (t_app f y) x) :=
  ⟨t_app (t_app f y) x, t_swap_red f x y, Relation.ReflTransGen.refl⟩

-- Define the derived S combinator term
def t_sₛ : TensorSpace :=
  t_app (t_app t_comp (t_app t_comp t_dup))
    (t_app (t_app t_swap (t_app (t_app t_comp t_comp) (t_app (t_app t_comp t_comp) t_swap))) t_norm)

-- Prove the derived S behavior as a theorem
theorem t_s_beta (x y z : TensorSpace) :
    ExtEq (t_app (t_app (t_app t_sₛ x) y) z) (t_app (t_app x z) (t_app y z)) := by
  let P := t_app (t_app t_swap (t_app (t_app t_comp t_comp) (t_app (t_app t_comp t_comp) t_swap))) t_norm
  have h1 : ExtEq (t_app (t_app (t_app t_comp (t_app t_comp t_dup)) P) x) (t_app (t_app t_comp t_dup) (t_app P x)) :=
    t_comp_beta (t_app t_comp t_dup) P x
  have h2 : ExtEq (t_app (t_app (t_app (t_app (t_app t_comp (t_app t_comp t_dup)) P) x) y) z)
                  (t_app (t_app (t_app (t_app t_comp t_dup) (t_app P x)) y) z) :=
    t_app_congr_left (t_app_congr_left h1)
  have h3 : ExtEq (t_app (t_app (t_app t_comp t_dup) (t_app P x)) y) (t_app t_dup (t_app (t_app P x) y)) :=
    t_comp_beta t_dup (t_app P x) y
  have h4 : ExtEq (t_app (t_app (t_app (t_app t_comp t_dup) (t_app P x)) y) z)
                  (t_app (t_app t_dup (t_app (t_app P x) y)) z) :=
    t_app_congr_left h3
  have h5 : ExtEq (t_app (t_app t_dup (t_app (t_app P x) y)) z) (t_app (t_app (t_app (t_app P x) y) z) z) :=
    t_dup_beta (t_app (t_app P x) y) z
  have h_step1 : ExtEq (t_app (t_app (t_app t_sₛ x) y) z) (t_app (t_app (t_app (t_app P x) y) z) z) :=
    ExtEq.trans h2 (ExtEq.trans h4 h5)
  let Q := t_app (t_app t_comp t_comp) (t_app (t_app t_comp t_comp) t_swap)
  have h6 : ExtEq (t_app P x) (t_app (t_app Q x) t_norm) :=
    t_swap_beta Q t_norm x
  have h7 : ExtEq (t_app (t_app (t_app (t_app P x) y) z) z) (t_app (t_app (t_app (t_app (t_app Q x) t_norm) y) z) z) :=
    t_app_congr_left (t_app_congr_left (t_app_congr_left h6))
  let Q2 := t_app (t_app t_comp t_comp) t_swap
  have h8 : ExtEq (t_app Q x) (t_app t_comp (t_app Q2 x)) :=
    t_comp_beta t_comp Q2 x
  have h9 : ExtEq (t_app (t_app (t_app t_comp (t_app Q2 x)) t_norm) y) (t_app (t_app Q2 x) (t_app t_norm y)) :=
    t_comp_beta (t_app Q2 x) t_norm y
  have h10 : ExtEq (t_app (t_app (t_app Q x) t_norm) y) (t_app (t_app Q2 x) (t_app t_norm y)) :=
    ExtEq.trans (t_app_congr_left (t_app_congr_left h8)) h9
  have h11 : ExtEq (t_app t_norm y) y :=
    t_norm_beta y
  have h12 : ExtEq (t_app (t_app (t_app Q x) t_norm) y) (t_app (t_app Q2 x) y) :=
    ExtEq.trans h10 (t_app_congr_right h11)
  have h13 : ExtEq (t_app Q2 x) (t_app t_comp (t_app t_swap x)) :=
    t_comp_beta t_comp t_swap x
  have h14 : ExtEq (t_app (t_app Q2 x) y) (t_app (t_app t_comp (t_app t_swap x)) y) :=
    t_app_congr_left h13
  have h15 : ExtEq (t_app (t_app (t_app Q x) t_norm) y) (t_app (t_app t_comp (t_app t_swap x)) y) :=
    ExtEq.trans h12 h14
  have h16 : ExtEq (t_app (t_app (t_app (t_app (t_app Q x) t_norm) y) z) z)
                  (t_app (t_app (t_app (t_app t_comp (t_app t_swap x)) y) z) z) :=
    t_app_congr_left (t_app_congr_left h15)
  have h17 : ExtEq (t_app (t_app (t_app t_comp (t_app t_swap x)) y) z) (t_app (t_app t_swap x) (t_app y z)) :=
    t_comp_beta (t_app t_swap x) y z
  have h18 : ExtEq (t_app (t_app (t_app (t_app t_comp (t_app t_swap x)) y) z) z)
                  (t_app (t_app (t_app t_swap x) (t_app y z)) z) :=
    t_app_congr_left h17
  have h19 : ExtEq (t_app (t_app (t_app t_swap x) (t_app y z)) z) (t_app (t_app x z) (t_app y z)) :=
    t_swap_beta x (t_app y z) z
  have h_step2 : ExtEq (t_app (t_app (t_app (t_app P x) y) z) z) (t_app (t_app x z) (t_app y z)) :=
    ExtEq.trans h7 (ExtEq.trans h16 (ExtEq.trans h18 h19))
  exact ExtEq.trans h_step1 h_step2

-- Denotation function from symbolic ISAR into TensorSpace
def denot : ITerm → TensorSpace
  | .var n => t_var n
  | .norm => t_norm
  | .konst => t_konst
  | .dup => t_dup
  | .swap => t_swap
  | .comp => t_comp
  | .sₛ => t_sₛ
  | .app f x => t_app (denot f) (denot x)

-- Prove one-step operational soundness
theorem denot_sound {t u : ITerm} (h : IStep t u) : ExtEq (denot t) (denot u) := by
  induction h with
  | normβ x =>
      exact t_norm_beta (denot x)
  | konst_macro x y =>
      exact t_konst_beta (denot x) (denot y)
  | compβ f g x =>
      exact t_comp_beta (denot f) (denot g) (denot x)
  | sβ x y z =>
      exact t_s_beta (denot x) (denot y) (denot z)
  | appL _ ih =>
      exact t_app_congr ih (ExtEq.refl _)
  | appR _ ih =>
      exact t_app_congr (ExtEq.refl _) ih

-- Prove multi-step soundness
theorem denot_sound_red {t u : ITerm} (h : IRed t u) : ExtEq (denot t) (denot u) := by
  induction h with
  | refl => exact ExtEq.refl _
  | tail _ hstep ih =>
      exact ExtEq.trans ih (denot_sound hstep)

-- Quotient of TensorSpace by extensional equality
instance tensorSetoid : Setoid TensorSpace where
  r := ExtEq
  iseqv := {
    refl := ExtEq.refl
    symm := ExtEq.symm
    trans := ExtEq.trans
  }

def ExtTensor : Type := Quotient ISAR.tensorSetoid

-- Semantic map mapping into ExtTensor
noncomputable def denot_ext (t : ITerm) : ExtTensor :=
  Quotient.mk _ (denot t)

-- Show that denotation factors through the Invariant Layer quotient
theorem denot_factors (t u : ISKSubtype) (h : OperEq t u) :
    denot_ext t.val = denot_ext u.val := by
  match h with
  | ⟨v, ht, hu⟩ =>
      have heq1 := denot_sound_red ht
      have heq2 := denot_sound_red hu
      have heq : ExtEq (denot t.val) (denot u.val) :=
        ExtEq.trans heq1 (ExtEq.symm heq2)
      exact Quotient.sound heq

/-- The final semantic map from Invariant Layer quotient classes into extensional tensors. -/
noncomputable def InvariantLayer.toExtTensor : InvariantLayer → ExtTensor :=
  Quotient.lift (fun t => denot_ext t.val) (by
    intro t u h
    exact denot_factors t u h
  )

/-- Operational equivalence on lambda terms, defined as the equivalence relation generated by LStep. -/
inductive LEq : LTerm → LTerm → Prop where
  | of_step {t u : LTerm} : LStep t u → LEq t u
  | refl (t : LTerm) : LEq t t
  | symm {t u : LTerm} : LEq t u → LEq u t
  | trans {t u w : LTerm} : LEq t u → LEq u w → LEq t w

instance lambdaSetoid : Setoid LTerm where
  r := LEq
  iseqv := {
    refl := LEq.refl
    symm := LEq.symm
    trans := LEq.trans
  }

/-- The operational quotient of lambda terms. -/
def LambdaQuotient : Type := Quotient ISAR.lambdaSetoid

-- Semantic map mapping LTerm into ExtTensor
noncomputable def lambda_denot_ext (t : LTerm) : ExtTensor :=
  Quotient.mk _ (denot (compile t))

-- Prove soundness: operational equivalence implies extensional equality of denotations
theorem lambda_denot_sound (t u : LTerm) (h : LEq t u) :
    ExtEq (denot (compile t)) (denot (compile u)) := by
  induction h with
  | of_step hstep =>
      have hred := compile_simulates_step hstep
      exact denot_sound_red hred
  | refl => exact ExtEq.refl _
  | symm _ ih => exact ExtEq.symm ih
  | trans _ _ ih1 ih2 => exact ExtEq.trans ih1 ih2

-- Prove factorization through the operational quotient
theorem lambda_denot_factors (t u : LTerm) (h : LEq t u) :
    lambda_denot_ext t = lambda_denot_ext u :=
  Quotient.sound (lambda_denot_sound t u h)

/-- The semantic map from the operational quotient of lambda terms into extensional tensors. -/
noncomputable def LambdaQuotient.toExtTensor : LambdaQuotient → ExtTensor :=
  Quotient.lift (fun t => lambda_denot_ext t) (by
    intro t u h
    exact lambda_denot_factors t u h
  )

def lapp_raw (t u : LTerm) : LTerm :=
  .app t u

theorem lapp_congruence_left (t1 t2 : LTerm) (u : LTerm) (h : LEq t1 t2) :
    LEq (.app t1 u) (.app t2 u) := by
  induction h with
  | of_step hstep => exact LEq.of_step (LStep.appL hstep)
  | refl => exact LEq.refl _
  | symm _ ih => exact LEq.symm ih
  | trans _ _ ih1 ih2 => exact LEq.trans ih1 ih2

theorem lapp_congruence_right (t : LTerm) (u1 u2 : LTerm) (h : LEq u1 u2) :
    LEq (.app t u1) (.app t u2) := by
  induction h with
  | of_step hstep => exact LEq.of_step (LStep.appR hstep)
  | refl => exact LEq.refl _
  | symm _ ih => exact LEq.symm ih
  | trans _ _ ih1 ih2 => exact LEq.trans ih1 ih2

theorem lapp_congruence (t1 t2 u1 u2 : LTerm) (ht : LEq t1 t2) (hu : LEq u1 u2) :
    LEq (lapp_raw t1 u1) (lapp_raw t2 u2) :=
  LEq.trans (lapp_congruence_left t1 t2 u1 ht) (lapp_congruence_right t2 u1 u2 hu)

/-- Application of quotient classes in LambdaQuotient. -/
def LambdaQuotient.app (t u : LambdaQuotient) : LambdaQuotient :=
  Quotient.lift₂ (fun t u => Quotient.mk _ (lapp_raw t u)) (by
    intro t1 u1 t2 u2 ht hu
    exact Quotient.sound (lapp_congruence t1 t2 u1 u2 ht hu)
  ) t u

/-- Lifted application in ExtTensor. -/
noncomputable def t_app_ext (t u : ExtTensor) : ExtTensor :=
  Quotient.lift₂ (fun t u => Quotient.mk _ (t_app t u)) (by
    intro t1 u1 t2 u2 ht hu
    exact Quotient.sound (t_app_congr ht hu)
  ) t u

/-- Compilation is a homomorphism for application up to tensor extensional equivalence. -/
theorem toExtTensor_app (t u : LambdaQuotient) :
    LambdaQuotient.toExtTensor (LambdaQuotient.app t u) = t_app_ext (LambdaQuotient.toExtTensor t) (LambdaQuotient.toExtTensor u) := by
  induction t using Quotient.ind with | _ t =>
  induction u using Quotient.ind with | _ u =>
      unfold LambdaQuotient.app LambdaQuotient.toExtTensor t_app_ext Quotient.lift₂ Quotient.lift lambda_denot_ext lapp_raw
      rfl

def obs_a : TensorSpace := t_norm
def obs_b : TensorSpace := t_konst

theorem NormalI.norm : NormalI ITerm.norm := fun _ h => by cases h
theorem NormalI.konst : NormalI ITerm.konst := fun _ h => by cases h

theorem NormalI.konst_konst : NormalI (ITerm.app ITerm.konst ITerm.konst) := by
  intro u h
  cases h with
  | appL hf => cases hf
  | appR hx => cases hx

theorem non_trivial_observable : ¬ ExtEq (t_app obs_a obs_b) obs_a := by
  intro ⟨v, h1, h2⟩
  dsimp [obs_a, obs_b, t_app, t_norm, t_konst] at h1 h2
  have hv : ITerm.norm = v := IRed_normal_eq NormalI.norm h2
  subst hv
  have hkonst : IRed (ITerm.app ITerm.norm ITerm.konst) ITerm.konst :=
    Relation.ReflTransGen.single (IStep.normβ _)
  rcases IRed_confluence h1 hkonst with ⟨w, hw1, hw2⟩
  have hw_norm : ITerm.norm = w := IRed_normal_eq NormalI.norm hw1
  have hw_konst : ITerm.konst = w := IRed_normal_eq NormalI.konst hw2
  cases hw_norm.trans hw_konst.symm

theorem non_trivial_observable2 : ¬ ExtEq (t_app (t_app obs_a obs_b) obs_b) obs_a := by
  intro ⟨v, h1, h2⟩
  dsimp [obs_a, obs_b, t_app, t_norm, t_konst] at h1 h2
  have hv : ITerm.norm = v := IRed_normal_eq NormalI.norm h2
  subst hv
  have hred : IRed (ITerm.app (ITerm.app ITerm.norm ITerm.konst) ITerm.konst)
      (ITerm.app ITerm.konst ITerm.konst) :=
    IRed_app_left (Relation.ReflTransGen.single (IStep.normβ _))
  rcases IRed_confluence h1 hred with ⟨w, hw1, hw2⟩
  have hw_norm : ITerm.norm = w := IRed_normal_eq NormalI.norm hw1
  have hw_kk : ITerm.app ITerm.konst ITerm.konst = w :=
    IRed_normal_eq NormalI.konst_konst hw2
  cases hw_norm.trans hw_kk.symm

-- Separation lemma: if two tensors behave differently when applied to some arguments, they are not extensionally equal
theorem separation_lemma {A B : TensorSpace} (x y : TensorSpace) (h_neq : ¬ ExtEq (t_app (t_app A x) y) (t_app (t_app B x) y)) :
    ¬ ExtEq A B := by
  intro h_eq
  have h_congr : ExtEq (t_app (t_app A x) y) (t_app (t_app B x) y) :=
    t_app_congr (t_app_congr h_eq (ExtEq.refl x)) (ExtEq.refl y)
  exact h_neq h_congr

noncomputable def t_K : TensorSpace :=
  t_app (t_app t_comp t_konst) t_norm

noncomputable def t_K2 : TensorSpace :=
  t_app (t_app t_comp t_konst) (t_app (t_app t_comp t_konst) t_norm)

theorem t_K_beta (x y : TensorSpace) : ExtEq (t_app (t_app t_K x) y) x := by
  have h1 : ExtEq (t_app t_K x) (t_app t_konst (t_app t_norm x)) :=
    t_comp_beta t_konst t_norm x
  have h2 : ExtEq (t_app (t_app t_K x) y) (t_app (t_app t_konst (t_app t_norm x)) y) :=
    t_app_congr_left h1
  have h3 : ExtEq (t_app (t_app t_konst (t_app t_norm x)) y) (t_app t_norm x) :=
    t_konst_beta (t_app t_norm x) y
  have h4 : ExtEq (t_app t_norm x) x :=
    t_norm_beta x
  exact ExtEq.trans h2 (ExtEq.trans h3 h4)

theorem t_K2_beta (x y z : TensorSpace) : ExtEq (t_app (t_app (t_app t_K2 x) y) z) x := by
  have h1 : ExtEq (t_app t_K2 x) (t_app t_konst (t_app t_K x)) :=
    t_comp_beta t_konst t_K x
  have h2 : ExtEq (t_app (t_app t_K2 x) y) (t_app (t_app t_konst (t_app t_K x)) y) :=
    t_app_congr_left h1
  have h3 : ExtEq (t_app (t_app t_konst (t_app t_K x)) y) (t_app t_K x) :=
    t_konst_beta (t_app t_K x) y
  have h4 : ExtEq (t_app (t_app (t_app t_K2 x) y) z) (t_app (t_app t_K x) z) :=
    t_app_congr_left (ExtEq.trans h2 h3)
  have h5 : ExtEq (t_app (t_app t_K x) z) x :=
    t_K_beta x z
  exact ExtEq.trans h4 h5

-- Adequacy / separation theorem: Identity and Constant functions are distinguished by the tensor semantics
theorem adequacy_norm_konst (M N : LTerm)
    (hM : LRed M (LTerm.abs (LTerm.var 0)))
    (hN : LRed N (LTerm.abs (LTerm.abs (LTerm.var 1)))) :
    ¬ ExtEq (denot (compile M)) (denot (compile N)) := by
  have hM_red := compile_simulates_red hM
  have hN_red := compile_simulates_red hN
  have hM_denot := denot_sound_red hM_red
  have hN_denot := denot_sound_red hN_red
  intro h_eq
  have h_norm_eq_const : ExtEq t_norm (t_app (t_app t_comp t_konst) t_norm) := by
    have h_norm : denot (compile (LTerm.abs (LTerm.var 0))) = t_norm := rfl
    have h_const : denot (compile (LTerm.abs (LTerm.abs (LTerm.var 1)))) = t_app (t_app t_comp t_konst) t_norm := rfl
    rw [← h_const, ← h_norm]
    exact ExtEq.trans (ExtEq.symm hM_denot) (ExtEq.trans h_eq hN_denot)
  have h_neq : ¬ ExtEq (t_app (t_app t_norm obs_a) obs_b) (t_app (t_app (t_app (t_app t_comp t_konst) t_norm) obs_a) obs_b) := by
    have h_lhs : ExtEq (t_app (t_app t_norm obs_a) obs_b) (t_app obs_a obs_b) :=
      t_app_congr_left (t_norm_beta obs_a)
    have h_rhs : ExtEq (t_app (t_app (t_app (t_app t_comp t_konst) t_norm) obs_a) obs_b) obs_a := by
      have h1 : ExtEq (t_app (t_app (t_app t_comp t_konst) t_norm) obs_a) (t_app t_konst (t_app t_norm obs_a)) :=
        t_comp_beta t_konst t_norm obs_a
      have h2 : ExtEq (t_app (t_app (t_app t_comp t_konst) t_norm) obs_a) (t_app t_konst obs_a) :=
        ExtEq.trans h1 (t_app_congr_right (t_norm_beta obs_a))
      have h3 : ExtEq (t_app (t_app (t_app (t_app t_comp t_konst) t_norm) obs_a) obs_b) (t_app (t_app t_konst obs_a) obs_b) :=
        t_app_congr_left h2
      exact ExtEq.trans h3 (t_konst_beta obs_a obs_b)
    intro h_eq_applied
    have h_contradiction : ExtEq (t_app obs_a obs_b) obs_a :=
      ExtEq.trans (ExtEq.symm h_lhs) (ExtEq.trans h_eq_applied h_rhs)
    exact non_trivial_observable h_contradiction
  exact separation_lemma obs_a obs_b h_neq h_norm_eq_const

theorem adequacy_konst_k2 (M N : LTerm)
    (hM : LRed M (LTerm.abs (LTerm.abs (LTerm.var 1))))
    (hN : LRed N (LTerm.abs (LTerm.abs (LTerm.abs (LTerm.var 2))))) :
    ¬ ExtEq (denot (compile M)) (denot (compile N)) := by
  have hM_red := compile_simulates_red hM
  have hN_red := compile_simulates_red hN
  have hM_denot := denot_sound_red hM_red
  have hN_denot := denot_sound_red hN_red
  intro h_eq
  have h_K_eq_K2 : ExtEq t_K t_K2 := by
    have h_K : denot (compile (LTerm.abs (LTerm.abs (LTerm.var 1)))) = t_K := rfl
    have h_K2 : denot (compile (LTerm.abs (LTerm.abs (LTerm.abs (LTerm.var 2))))) = t_K2 := rfl
    rw [← h_K2, ← h_K]
    exact ExtEq.trans (ExtEq.symm hM_denot) (ExtEq.trans h_eq hN_denot)
  have h_neq : ¬ ExtEq (t_app (t_app (t_app t_K obs_a) obs_b) obs_b) (t_app (t_app (t_app t_K2 obs_a) obs_b) obs_b) := by
    have h_lhs : ExtEq (t_app (t_app (t_app t_K obs_a) obs_b) obs_b) (t_app obs_a obs_b) :=
      t_app_congr_left (t_K_beta obs_a obs_b)
    have h_rhs : ExtEq (t_app (t_app (t_app t_K2 obs_a) obs_b) obs_b) obs_a :=
      t_K2_beta obs_a obs_b obs_b
    intro h_eq_applied
    have h_contradiction : ExtEq (t_app obs_a obs_b) obs_a :=
      ExtEq.trans (ExtEq.symm h_lhs) (ExtEq.trans h_eq_applied h_rhs)
    exact non_trivial_observable h_contradiction
  have h_congr : ExtEq (t_app (t_app (t_app t_K obs_a) obs_b) obs_b) (t_app (t_app (t_app t_K2 obs_a) obs_b) obs_b) :=
    t_app_congr (t_app_congr (t_app_congr h_K_eq_K2 (ExtEq.refl obs_a)) (ExtEq.refl obs_b)) (ExtEq.refl obs_b)
  exact h_neq h_congr

theorem adequacy_norm_k2 (M N : LTerm)
    (hM : LRed M (LTerm.abs (LTerm.var 0)))
    (hN : LRed N (LTerm.abs (LTerm.abs (LTerm.abs (LTerm.var 2))))) :
    ¬ ExtEq (denot (compile M)) (denot (compile N)) := by
  have hM_red := compile_simulates_red hM
  have hN_red := compile_simulates_red hN
  have hM_denot := denot_sound_red hM_red
  have hN_denot := denot_sound_red hN_red
  intro h_eq
  have h_norm_eq_K2 : ExtEq t_norm t_K2 := by
    have h_norm : denot (compile (LTerm.abs (LTerm.var 0))) = t_norm := rfl
    have h_K2 : denot (compile (LTerm.abs (LTerm.abs (LTerm.abs (LTerm.var 2))))) = t_K2 := rfl
    rw [← h_K2, ← h_norm]
    exact ExtEq.trans (ExtEq.symm hM_denot) (ExtEq.trans h_eq hN_denot)
  have h_neq : ¬ ExtEq (t_app (t_app (t_app t_norm obs_a) obs_b) obs_b) (t_app (t_app (t_app t_K2 obs_a) obs_b) obs_b) := by
    have h_lhs : ExtEq (t_app (t_app (t_app t_norm obs_a) obs_b) obs_b) (t_app (t_app obs_a obs_b) obs_b) :=
      t_app_congr_left (t_app_congr_left (t_norm_beta obs_a))
    have h_rhs : ExtEq (t_app (t_app (t_app t_K2 obs_a) obs_b) obs_b) obs_a :=
      t_K2_beta obs_a obs_b obs_b
    intro h_eq_applied
    have h_contradiction : ExtEq (t_app (t_app obs_a obs_b) obs_b) obs_a :=
      ExtEq.trans (ExtEq.symm h_lhs) (ExtEq.trans h_eq_applied h_rhs)
    exact non_trivial_observable2 h_contradiction
  have h_congr : ExtEq (t_app (t_app (t_app t_norm obs_a) obs_b) obs_b) (t_app (t_app (t_app t_K2 obs_a) obs_b) obs_b) :=
    t_app_congr (t_app_congr (t_app_congr h_norm_eq_K2 (ExtEq.refl obs_a)) (ExtEq.refl obs_b)) (ExtEq.refl obs_b)
  exact h_neq h_congr

inductive Fam3 : Type where
  | I : Fam3
  | K : Fam3
  | K2 : Fam3

def Fam3.toLTerm : Fam3 → LTerm
  | .I => LTerm.abs (LTerm.var 0)
  | .K => LTerm.abs (LTerm.abs (LTerm.var 1))
  | .K2 => LTerm.abs (LTerm.abs (LTerm.abs (LTerm.var 2)))

theorem adequacy_family (a b : Fam3) (h : a ≠ b) :
    ¬ ExtEq (denot (compile (a.toLTerm))) (denot (compile (b.toLTerm))) := by
  cases a with
  | I =>
    cases b with
    | I => contradiction
    | K =>
      intro h_eq
      exact adequacy_norm_konst (Fam3.toLTerm .I) (Fam3.toLTerm .K) Relation.ReflTransGen.refl Relation.ReflTransGen.refl h_eq
    | K2 =>
      intro h_eq
      exact adequacy_norm_k2 (Fam3.toLTerm .I) (Fam3.toLTerm .K2) Relation.ReflTransGen.refl Relation.ReflTransGen.refl h_eq
  | K =>
    cases b with
    | I =>
      intro h_eq
      exact adequacy_norm_konst (Fam3.toLTerm .I) (Fam3.toLTerm .K) Relation.ReflTransGen.refl Relation.ReflTransGen.refl (ExtEq.symm h_eq)
    | K => contradiction
    | K2 =>
      intro h_eq
      exact adequacy_konst_k2 (Fam3.toLTerm .K) (Fam3.toLTerm .K2) Relation.ReflTransGen.refl Relation.ReflTransGen.refl h_eq
  | K2 =>
    cases b with
    | I =>
      intro h_eq
      exact adequacy_norm_k2 (Fam3.toLTerm .I) (Fam3.toLTerm .K2) Relation.ReflTransGen.refl Relation.ReflTransGen.refl (ExtEq.symm h_eq)
    | K =>
      intro h_eq
      exact adequacy_konst_k2 (Fam3.toLTerm .K) (Fam3.toLTerm .K2) Relation.ReflTransGen.refl Relation.ReflTransGen.refl (ExtEq.symm h_eq)
    | K2 => contradiction

end ISAR
