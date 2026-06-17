namespace Relation

inductive ReflTransGen {α : Type _} (r : α → α → Prop) (a : α) : α → Prop where
  | refl : ReflTransGen r a a
  | tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace ReflTransGen

@[refl]
theorem refl' {α : Type _} {r : α → α → Prop} {a : α} : ReflTransGen r a a :=
  refl

theorem trans {α : Type _} {r : α → α → Prop} {a b c : α}
    (h1 : ReflTransGen r a b) (h2 : ReflTransGen r b c) : ReflTransGen r a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact ReflTransGen.tail ih hstep

theorem single {α : Type _} {r : α → α → Prop} {a b : α} (h : r a b) : ReflTransGen r a b :=
  ReflTransGen.tail ReflTransGen.refl h

end ReflTransGen

end Relation

open Relation

namespace ISAR

/- =========================================================
   1. SKI syntax
   ========================================================= -/

inductive SK : Type where
  | S : SK
  | K : SK
  | I : SK
  | app : SK → SK → SK
deriving DecidableEq, Repr

namespace SK
infixl:70 " · " => SK.app
end SK

/- =========================================================
   2. Symbolic ISAR core

   First proof-oriented version:
   - norm  behaves like I
   - konst behaves like K
   - sₛ    behaves like S

   dup / swap / comp are included so the language already
   reflects your operator basis, but only comp is used below.
   Later, sₛ can be replaced by a definable term built from
   dup / swap / comp / app.
   ========================================================= -/

inductive ITerm : Type where
  | var   : Nat → ITerm
  | norm  : ITerm
  | konst : ITerm
  | dup   : ITerm
  | swap  : ITerm
  | comp  : ITerm
  | sₛ    : ITerm
  | app   : ITerm → ITerm → ITerm
deriving DecidableEq, Repr

namespace ITerm
infixl:70 " · " => ITerm.app
end ITerm

/- =========================================================
   3. One-step SKI reduction
   ========================================================= -/

inductive SKStep : SK → SK → Prop where
  | Iβ (x : SK) :
      SKStep (SK.app SK.I x) x
  | Kβ (x y : SK) :
      SKStep (SK.app (SK.app SK.K x) y) x
  | Sβ (x y z : SK) :
      SKStep (SK.app (SK.app (SK.app SK.S x) y) z)
             (SK.app (SK.app x z) (SK.app y z))
  | appL {f f' x : SK} :
      SKStep f f' → SKStep (SK.app f x) (SK.app f' x)
  | appR {f x x' : SK} :
      SKStep x x' → SKStep (SK.app f x) (SK.app f x')

/- =========================================================
   4. One-step ISAR reduction
   ========================================================= -/

inductive IStep : ITerm → ITerm → Prop where
  | normβ (x : ITerm) :
      IStep (ITerm.app ITerm.norm x) x
  | konstβ (x y : ITerm) :
      IStep (ITerm.app (ITerm.app ITerm.konst x) y) x
  | compβ (f g x : ITerm) :
      IStep (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x)
             (ITerm.app f (ITerm.app g x))
  | sβ (x y z : ITerm) :
      IStep (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z)
             (ITerm.app (ITerm.app x z) (ITerm.app y z))
  | appL {f f' x : ITerm} :
      IStep f f' → IStep (ITerm.app f x) (ITerm.app f' x)
  | appR {f x x' : ITerm} :
      IStep x x' → IStep (ITerm.app f x) (ITerm.app f x')

abbrev SKRed := Relation.ReflTransGen SKStep
abbrev IRed  := Relation.ReflTransGen IStep

def NormalSK (t : SK) : Prop := ∀ u, ¬ SKStep t u
def NormalI  (t : ITerm) : Prop := ∀ u, ¬ IStep t u

/- =========================================================
   5. Encoding SKI into ISAR
   ========================================================= -/

def encode : SK → ITerm
  | .S       => .sₛ
  | .K       => .konst
  | .I       => .norm
  | .app f x => .app (encode f) (encode x)

/- =========================================================
   6. Basic simulation lemmas
   ========================================================= -/

theorem encode_I (x : ITerm) :
    IRed (ITerm.app (encode SK.I) x) x := by
  simpa [encode] using
    (Relation.ReflTransGen.single (IStep.normβ x))

theorem encode_K (x y : ITerm) :
    IRed (ITerm.app (ITerm.app (encode SK.K) x) y) x := by
  simpa [encode] using
    (Relation.ReflTransGen.single (IStep.konstβ x y))

theorem encode_S (x y z : ITerm) :
    IRed (ITerm.app (ITerm.app (ITerm.app (encode SK.S) x) y) z)
         (ITerm.app (ITerm.app x z) (ITerm.app y z)) := by
  simpa [encode] using
    (Relation.ReflTransGen.single (IStep.sβ x y z))

/- =========================================================
   7. Congruence lifting for reflexive-transitive closure
   ========================================================= -/

theorem IRed_app_left {f f' x : ITerm} :
    IRed f f' → IRed (ITerm.app f x) (ITerm.app f' x) := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (IStep.appL hstep)

theorem IRed_app_right {f x x' : ITerm} :
    IRed x x' → IRed (ITerm.app f x) (ITerm.app f x') := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (IStep.appR hstep)

theorem IRed_app {f f' x x' : ITerm} (hf : IRed f f') (hx : IRed x x') :
    IRed (ITerm.app f x) (ITerm.app f' x') :=
  Relation.ReflTransGen.trans (IRed_app_left hf) (IRed_app_right hx)

/- =========================================================
   8. One-step simulation
   ========================================================= -/

theorem simulate_step {t u : SK} :
    SKStep t u → IRed (encode t) (encode u) := by
  intro h
  induction h with
  | Iβ x =>
      simpa [encode] using
        (Relation.ReflTransGen.single (IStep.normβ (encode x)))
  | Kβ x y =>
      simpa [encode] using
        (Relation.ReflTransGen.single (IStep.konstβ (encode x) (encode y)))
  | Sβ x y z =>
      simpa [encode] using
        (Relation.ReflTransGen.single (IStep.sβ (encode x) (encode y) (encode z)))
  | appL _ ih =>
      simpa [encode] using (IRed_app_left ih)
  | appR _ ih =>
      simpa [encode] using (IRed_app_right ih)

/- =========================================================
   9. Multi-step simulation
   ========================================================= -/

theorem simulate_red {t u : SK} :
    SKRed t u → IRed (encode t) (encode u) := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih (simulate_step hstep)

/- =========================================================
   10. Sanity examples
   ========================================================= -/

example :
    IRed (encode (SK.app SK.I SK.K)) (encode SK.K) := by
  exact simulate_step (SKStep.Iβ SK.K)

example :
    IRed (encode (SK.app (SK.app SK.K SK.S) SK.I)) (encode SK.S) := by
  exact simulate_step (SKStep.Kβ SK.S SK.I)

example :
    IRed (encode (SK.app (SK.app (SK.app SK.S SK.K) SK.K) SK.I))
         (encode (SK.app (SK.app SK.K SK.I) (SK.app SK.K SK.I))) := by
  exact simulate_step (SKStep.Sβ SK.K SK.K SK.I)

/- =========================================================
   11. Fragment predicate for encoded SKI terms
   ========================================================= -/

/-- Identifies ISAR terms that belong to the pure SKI fragment. -/
inductive ISKTerm : ITerm → Prop where
  | norm  : ISKTerm ITerm.norm
  | konst : ISKTerm ITerm.konst
  | sₛ    : ISKTerm ITerm.sₛ
  | app {f x : ITerm} : ISKTerm f → ISKTerm x → ISKTerm (ITerm.app f x)

/-- Any term produced by `encode` belongs to the ISK fragment. -/
theorem encode_is_ISKTerm (t : SK) : ISKTerm (encode t) := by
  induction t with
  | S => exact ISKTerm.sₛ
  | K => exact ISKTerm.konst
  | I => exact ISKTerm.norm
  | app _ _ ih_f ih_x => exact ISKTerm.app ih_f ih_x

/- =========================================================
   12. Parallel Reduction and Complete Development
   ========================================================= -/

inductive ParStep : ITerm → ITerm → Prop where
  | var (n : Nat) : ParStep (.var n) (.var n)
  | norm : ParStep .norm .norm
  | konst : ParStep .konst .konst
  | dup : ParStep .dup .dup
  | swap : ParStep .swap .swap
  | comp : ParStep .comp .comp
  | sₛ : ParStep .sₛ .sₛ
  | app {f f' x x'} : ParStep f f' → ParStep x x' → ParStep (.app f x) (.app f' x')
  | norm_red {x x'} : ParStep x x' → ParStep (.app .norm x) x'
  | konst_red {x x' y y'} : ParStep x x' → ParStep y y' → ParStep (.app (.app .konst x) y) x'
  | comp_red {f f' g g' x x'} : ParStep f f' → ParStep g g' → ParStep x x' →
      ParStep (.app (.app (.app .comp f) g) x) (.app f' (.app g' x'))
  | s_red {x x' y y' z z'} : ParStep x x' → ParStep y y' → ParStep z z' →
      ParStep (.app (.app (.app .sₛ x) y) z) (.app (.app x' z') (.app y' z'))

def cd : ITerm → ITerm
  | .var n => .var n
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => .sₛ
  | .app (.norm) x => cd x
  | .app (.app (.konst) x) _ => cd x
  | .app (.app (.app (.comp) f) g) x => .app (cd f) (.app (cd g) (cd x))
  | .app (.app (.app (.sₛ) x) y) z => .app (.app (cd x) (cd z)) (.app (cd y) (cd z))
  | .app f x => .app (cd f) (cd x)

theorem ParStep.refl (t : ITerm) : ParStep t t := by
  induction t with
  | var n => exact ParStep.var n
  | norm => exact ParStep.norm
  | konst => exact ParStep.konst
  | dup => exact ParStep.dup
  | swap => exact ParStep.swap
  | comp => exact ParStep.comp
  | sₛ => exact ParStep.sₛ
  | app f x ihf ihx => exact ParStep.app ihf ihx

theorem ParStep_cd : ∀ (t : ITerm) {u : ITerm}, ParStep t u → ParStep u (cd t)
  | .var n, _, h => by
      cases h with
      | var n => exact ParStep.var n
  | .norm, _, h => by
      cases h with
      | norm => exact ParStep.norm
  | .konst, _, h => by
      cases h with
      | konst => exact ParStep.konst
  | .dup, _, h => by
      cases h with
      | dup => exact ParStep.dup
  | .swap, _, h => by
      cases h with
      | swap => exact ParStep.swap
  | .comp, _, h => by
      cases h with
      | comp => exact ParStep.comp
  | .sₛ, _, h => by
      cases h with
      | sₛ => exact ParStep.sₛ
  | .app f x, _, h => by
      cases f with
      | var n =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.app (ParStep.var n) (ParStep_cd x hx)
      | norm =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.norm_red (ParStep_cd x hx)
          | norm_red hx =>
              exact ParStep_cd x hx
      | konst =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.app ParStep.konst (ParStep_cd x hx)
      | dup =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.app ParStep.dup (ParStep_cd x hx)
      | swap =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.app ParStep.swap (ParStep_cd x hx)
      | comp =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.app ParStep.comp (ParStep_cd x hx)
      | sₛ =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStep.app ParStep.sₛ (ParStep_cd x hx)
      | app f1 x1 =>
          cases f1 with
          | var n =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.app (ParStep.app (ParStep.var n) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
          | norm =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.app (ParStep.norm_red (ParStep_cd x1 hx1)) (ParStep_cd x hx)
                  | norm_red hx1 =>
                      exact ParStep.app (ParStep_cd x1 hx1) (ParStep_cd x hx)
          | konst =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.konst_red (ParStep_cd x1 hx1) (ParStep_cd x hx)
              | konst_red hx1 hx =>
                  exact ParStep_cd x1 hx1
          | dup =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.app (ParStep.app ParStep.dup (ParStep_cd x1 hx1)) (ParStep_cd x hx)
          | swap =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.app (ParStep.app ParStep.swap (ParStep_cd x1 hx1)) (ParStep_cd x hx)
          | comp =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.app (ParStep.app ParStep.comp (ParStep_cd x1 hx1)) (ParStep_cd x hx)
          | sₛ =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStep.app (ParStep.app ParStep.sₛ (ParStep_cd x1 hx1)) (ParStep_cd x hx)
          | app f2 x2 =>
              cases f2 with
              | comp =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.comp_red (ParStep_cd x2 hx2) (ParStep_cd x1 hx1) (ParStep_cd x hx)
                  | comp_red hx2 hx1 hx =>
                      exact ParStep.app (ParStep_cd x2 hx2) (ParStep.app (ParStep_cd x1 hx1) (ParStep_cd x hx))
              | sₛ =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.s_red (ParStep_cd x2 hx2) (ParStep_cd x1 hx1) (ParStep_cd x hx)
                  | s_red hx2 hx1 hx =>
                      exact ParStep.app (ParStep.app (ParStep_cd x2 hx2) (ParStep_cd x hx)) (ParStep.app (ParStep_cd x1 hx1) (ParStep_cd x hx))
              | var n =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.app (ParStep.app (ParStep.app (ParStep.var n) (ParStep_cd x2 hx2)) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
              | norm =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.app (ParStep.app (ParStep.norm_red (ParStep_cd x2 hx2)) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
                          | norm_red hx2 =>
                              exact ParStep.app (ParStep.app (ParStep_cd x2 hx2) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
              | konst =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.app (ParStep.konst_red (ParStep_cd x2 hx2) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
                      | konst_red hx2 hx1 =>
                          exact ParStep.app (ParStep_cd x2 hx2) (ParStep_cd x hx)
              | dup =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.app (ParStep.app (ParStep.app ParStep.dup (ParStep_cd x2 hx2)) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
              | swap =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStep.app (ParStep.app (ParStep.app ParStep.swap (ParStep_cd x2 hx2)) (ParStep_cd x1 hx1)) (ParStep_cd x hx)
              | app f3 x3 =>
                  cases h with
                  | app hf hx =>
                      exact ParStep.app (ParStep_cd (ITerm.app (ITerm.app (ITerm.app f3 x3) x2) x1) hf) (ParStep_cd x hx)

theorem ParStep_diamond {t u₁ u₂ : ITerm} (h₁ : ParStep t u₁) (h₂ : ParStep t u₂) :
    ∃ v, ParStep u₁ v ∧ ParStep u₂ v :=
  ⟨cd t, ParStep_cd t h₁, ParStep_cd t h₂⟩

theorem IStep_to_ParStep {t u : ITerm} (h : IStep t u) : ParStep t u := by
  induction h with
  | normβ x => exact ParStep.norm_red (ParStep.refl x)
  | konstβ x y => exact ParStep.konst_red (ParStep.refl x) (ParStep.refl y)
  | compβ f g x => exact ParStep.comp_red (ParStep.refl f) (ParStep.refl g) (ParStep.refl x)
  | sβ x y z => exact ParStep.s_red (ParStep.refl x) (ParStep.refl y) (ParStep.refl z)
  | appL _ ih => exact ParStep.app ih (ParStep.refl _)
  | appR _ ih => exact ParStep.app (ParStep.refl _) ih

theorem ParStep_to_IRed {t u : ITerm} (h : ParStep t u) : IRed t u := by
  induction h with
  | var n => exact Relation.ReflTransGen.refl
  | norm => exact Relation.ReflTransGen.refl
  | konst => exact Relation.ReflTransGen.refl
  | dup => exact Relation.ReflTransGen.refl
  | swap => exact Relation.ReflTransGen.refl
  | comp => exact Relation.ReflTransGen.refl
  | sₛ => exact Relation.ReflTransGen.refl
  | app _ _ ihf ihx => exact IRed_app ihf ihx
  | norm_red _ ihx =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (IStep.normβ _)) ihx
  | konst_red _ _ ihx _ =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (IStep.konstβ _ _)) ihx
  | comp_red _ _ _ ihf ihg ihx =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (IStep.compβ _ _ _)) (IRed_app ihf (IRed_app ihg ihx))
  | s_red _ _ _ ihx ihy ihz =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (IStep.sβ _ _ _)) (IRed_app (IRed_app ihx ihz) (IRed_app ihy ihz))

theorem ParStep_commute_ParTransGen {t u₁ u₂ : ITerm}
    (h₁ : ParStep t u₁) (h₂ : Relation.ReflTransGen ParStep t u₂) :
    ∃ v, Relation.ReflTransGen ParStep u₁ v ∧ ParStep u₂ v := by
  induction h₂ generalizing u₁ with
  | refl =>
      exact ⟨u₁, Relation.ReflTransGen.refl, h₁⟩
  | tail _ hstep ih =>
      match ih h₁ with
      | ⟨v, hv₁, hv₂⟩ =>
          match ParStep_diamond hv₂ hstep with
          | ⟨w, hw₁, hw₂⟩ =>
              exact ⟨w, Relation.ReflTransGen.tail hv₁ hw₁, hw₂⟩

theorem ParTransGen_diamond {t u₁ u₂ : ITerm}
    (h₁ : Relation.ReflTransGen ParStep t u₁) (h₂ : Relation.ReflTransGen ParStep t u₂) :
    ∃ v, Relation.ReflTransGen ParStep u₁ v ∧ Relation.ReflTransGen ParStep u₂ v := by
  induction h₁ generalizing u₂ with
  | refl =>
      exact ⟨u₂, h₂, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      match ih h₂ with
      | ⟨v, hv₁, hv₂⟩ =>
          match ParStep_commute_ParTransGen hstep hv₁ with
          | ⟨w, hw₁, hw₂⟩ =>
              exact ⟨w, hw₁, Relation.ReflTransGen.tail hv₂ hw₂⟩

theorem IRed_to_ParTransGen {t u : ITerm} (h : IRed t u) : Relation.ReflTransGen ParStep t u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (IStep_to_ParStep hstep)

theorem ParTransGen_to_IRed {t u : ITerm} (h : Relation.ReflTransGen ParStep t u) : IRed t u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans ih (ParStep_to_IRed hstep)

theorem IRed_confluence {t u₁ u₂ : ITerm} (h₁ : IRed t u₁) (h₂ : IRed t u₂) :
    ∃ v, IRed u₁ v ∧ IRed u₂ v := by
  have pt1 := IRed_to_ParTransGen h₁
  have pt2 := IRed_to_ParTransGen h₂
  match ParTransGen_diamond pt1 pt2 with
  | ⟨v, hv₁, hv₂⟩ =>
      exact ⟨v, ParTransGen_to_IRed hv₁, ParTransGen_to_IRed hv₂⟩

theorem ISKTerm_preserved {t u : ITerm} (ht : ISKTerm t) (h : IStep t u) : ISKTerm u := by
  induction h with
  | normβ x =>
      cases ht with | app _ hx => exact hx
  | konstβ x y =>
      cases ht with | app hf _ =>
        cases hf with | app _ hx => exact hx
  | compβ f g x =>
      cases ht with | app hf _ =>
        cases hf with | app hfg _ =>
          cases hfg with | app hc _ =>
            cases hc
  | sβ x y z =>
      cases ht with | app hf hz =>
        cases hf with | app hxy hy =>
          cases hxy with | app hs hx =>
            exact ISKTerm.app (ISKTerm.app hx hz) (ISKTerm.app hy hz)
  | appL _ ih =>
      cases ht with | app hf hx =>
        exact ISKTerm.app (ih hf) hx
  | appR _ ih =>
      cases ht with | app hf hx =>
        exact ISKTerm.app hf (ih hx)

theorem ISKTerm_IRed_preserved {t u : ITerm} (ht : ISKTerm t) (h : IRed t u) : ISKTerm u := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact ISKTerm_preserved ih hstep

/- =========================================================
   13. Confluence on the encoded fragment
   ========================================================= -/

/-- The operational semantics restricted to the ISK fragment is confluent. -/
theorem isar_fragment_confluence {t u₁ u₂ : ITerm}
    (ht : ISKTerm t) (r₁ : IRed t u₁) (r₂ : IRed t u₂) :
    ∃ v, IRed u₁ v ∧ IRed u₂ v ∧ ISKTerm v := by
  match IRed_confluence r₁ r₂ with
  | ⟨v, hv₁, hv₂⟩ =>
      have hvt : IRed t v := Relation.ReflTransGen.trans r₁ hv₁
      have hvk : ISKTerm v := ISKTerm_IRed_preserved ht hvt
      exact ⟨v, hv₁, hv₂, hvk⟩

theorem IRed_normal_eq {n v : ITerm} (hn : NormalI n) (h : IRed n v) : n = v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      have heq := ih
      subst heq
      exact False.elim (hn _ hstep)

/- =========================================================
   14. Unique normal forms for the encoded fragment
   ========================================================= -/

/-- An encoded term in the ISK fragment has at most one normal form. -/
theorem isar_fragment_unique_normal_forms {t n₁ n₂ : ITerm}
    (ht : ISKTerm t)
    (r₁ : IRed t n₁) (hn₁ : NormalI n₁)
    (r₂ : IRed t n₂) (hn₂ : NormalI n₂) :
    n₁ = n₂ := by
  match isar_fragment_confluence ht r₁ r₂ with
  | ⟨v, hv₁, hv₂, _⟩ =>
      have heq1 := IRed_normal_eq hn₁ hv₁
      have heq2 := IRed_normal_eq hn₂ hv₂
      exact heq1.trans heq2.symm

/- =========================================================
   15. Basis Reduction and Conservative Definability of S
   ========================================================= -/

open ITerm

local infixl:70 " ◦ " => ITerm.app

def derived_s : ITerm :=
  (comp ◦ (comp ◦ dup)) ◦ ((swap ◦ ((comp ◦ comp) ◦ ((comp ◦ comp) ◦ swap))) ◦ norm)

inductive IStepBasis : ITerm → ITerm → Prop where
  | normβ (x : ITerm) :
      IStepBasis (norm ◦ x) x
  | konstβ (x y : ITerm) :
      IStepBasis (konst ◦ x ◦ y) x
  | compβ (f g x : ITerm) :
      IStepBasis (comp ◦ f ◦ g ◦ x) (f ◦ (g ◦ x))
  | dupβ (f x : ITerm) :
      IStepBasis (dup ◦ f ◦ x) (f ◦ x ◦ x)
  | swapβ (f x y : ITerm) :
      IStepBasis (swap ◦ f ◦ x ◦ y) (f ◦ y ◦ x)
  | appL {f f' x : ITerm} :
      IStepBasis f f' → IStepBasis (f ◦ x) (f' ◦ x)
  | appR {f x x' : ITerm} :
      IStepBasis x x' → IStepBasis (f ◦ x) (f ◦ x')

abbrev IRedBasis := Relation.ReflTransGen IStepBasis

theorem IRedBasis_app_left {f f' x : ITerm} :
    IRedBasis f f' → IRedBasis (f ◦ x) (f' ◦ x) := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (IStepBasis.appL hstep)

theorem IRedBasis_app_right {f x x' : ITerm} :
    IRedBasis x x' → IRedBasis (f ◦ x) (f ◦ x') := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (IStepBasis.appR hstep)

theorem IRedBasis_app {f f' x x' : ITerm} (hf : IRedBasis f f') (hx : IRedBasis x x') :
    IRedBasis (f ◦ x) (f' ◦ x') :=
  Relation.ReflTransGen.trans (IRedBasis_app_left hf) (IRedBasis_app_right hx)

theorem derived_s_beta (x y z : ITerm) :
    IRedBasis (derived_s ◦ x ◦ y ◦ z) (x ◦ z ◦ (y ◦ z)) := by
  let X := comp ◦ dup
  let Y := (comp ◦ comp) ◦ ((comp ◦ comp) ◦ swap)
  let Q := (swap ◦ Y) ◦ norm
  have h1 : IStepBasis (((derived_s ◦ x) ◦ y) ◦ z) (((X ◦ (Q ◦ x)) ◦ y) ◦ z) :=
    IStepBasis.appL (IStepBasis.appL (IStepBasis.compβ X Q x))
  have h2 : IStepBasis (((X ◦ (Q ◦ x)) ◦ y) ◦ z) (((dup ◦ ((Q ◦ x) ◦ y)) ◦ z)) :=
    IStepBasis.appL (IStepBasis.compβ dup (Q ◦ x) y)
  have h3 : IStepBasis (((dup ◦ ((Q ◦ x) ◦ y)) ◦ z)) (((Q ◦ x) ◦ y) ◦ z ◦ z) :=
    IStepBasis.dupβ ((Q ◦ x) ◦ y) z
  have h4 : IStepBasis (((Q ◦ x) ◦ y) ◦ z ◦ z) ((((Y ◦ x) ◦ norm) ◦ y) ◦ z ◦ z) :=
    IStepBasis.appL (IStepBasis.appL (IStepBasis.appL (IStepBasis.swapβ Y norm x)))
  let Z := (comp ◦ comp) ◦ swap
  have h5 : IStepBasis ((((Y ◦ x) ◦ norm) ◦ y) ◦ z ◦ z) (((((comp ◦ (Z ◦ x)) ◦ norm) ◦ y) ◦ z ◦ z)) :=
    IStepBasis.appL (IStepBasis.appL (IStepBasis.appL (IStepBasis.appL (IStepBasis.compβ comp Z x))))
  have h6 : IStepBasis (((((comp ◦ (Z ◦ x)) ◦ norm) ◦ y) ◦ z ◦ z)) ((((Z ◦ x) ◦ (norm ◦ y)) ◦ z ◦ z)) :=
    IStepBasis.appL (IStepBasis.appL (IStepBasis.compβ (Z ◦ x) norm y))
  have h7 : IStepBasis ((((Z ◦ x) ◦ (norm ◦ y)) ◦ z) ◦ z) ((((Z ◦ x) ◦ y) ◦ z) ◦ z) :=
    IStepBasis.appL (IStepBasis.appL (IStepBasis.appR (IStepBasis.normβ y)))
  have h8 : IStepBasis ((((Z ◦ x) ◦ y) ◦ z) ◦ z) (((((comp ◦ (swap ◦ x)) ◦ y) ◦ z) ◦ z)) :=
    IStepBasis.appL (IStepBasis.appL (IStepBasis.appL (IStepBasis.compβ comp swap x)))
  have h9 : IStepBasis (((((comp ◦ (swap ◦ x)) ◦ y) ◦ z) ◦ z)) ((((swap ◦ x) ◦ (y ◦ z)) ◦ z)) :=
    IStepBasis.appL (IStepBasis.compβ (swap ◦ x) y z)
  have h10 : IStepBasis ((((swap ◦ x) ◦ (y ◦ z)) ◦ z)) ((x ◦ z) ◦ (y ◦ z)) :=
    IStepBasis.swapβ x (y ◦ z) z

  have r1 := Relation.ReflTransGen.single h1
  have r2 := Relation.ReflTransGen.tail r1 h2
  have r3 := Relation.ReflTransGen.tail r2 h3
  have r4 := Relation.ReflTransGen.tail r3 h4
  have r5 := Relation.ReflTransGen.tail r4 h5
  have r6 := Relation.ReflTransGen.tail r5 h6
  have r7 := Relation.ReflTransGen.tail r6 h7
  have r8 := Relation.ReflTransGen.tail r7 h8
  have r9 := Relation.ReflTransGen.tail r8 h9
  have r10 := Relation.ReflTransGen.tail r9 h10
  exact r10

def translate_to_basis : ITerm → ITerm
  | .var n => .var n
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => derived_s
  | .app f x => (translate_to_basis f) ◦ (translate_to_basis x)

theorem translate_preserves_step {t u : ITerm} (h : IStep t u) :
    IRedBasis (translate_to_basis t) (translate_to_basis u) := by
  induction h with
  | normβ x =>
      exact Relation.ReflTransGen.single (IStepBasis.normβ (translate_to_basis x))
  | konstβ x y =>
      exact Relation.ReflTransGen.single (IStepBasis.konstβ (translate_to_basis x) (translate_to_basis y))
  | compβ f g x =>
      exact Relation.ReflTransGen.single (IStepBasis.compβ (translate_to_basis f) (translate_to_basis g) (translate_to_basis x))
  | sβ x y z =>
      exact derived_s_beta (translate_to_basis x) (translate_to_basis y) (translate_to_basis z)
  | appL _ ih =>
      exact IRedBasis_app_left ih
  | appR _ ih =>
      exact IRedBasis_app_right ih

inductive NoS : ITerm → Prop where
  | var (n : Nat) : NoS (.var n)
  | norm : NoS .norm
  | konst : NoS .konst
  | dup : NoS .dup
  | swap : NoS .swap
  | comp : NoS .comp
  | app {f x : ITerm} : NoS f → NoS x → NoS (f ◦ x)

theorem derived_s_NoS : NoS derived_s := by
  repeat constructor

theorem translate_NoS (t : ITerm) : NoS (translate_to_basis t) := by
  induction t with
  | var n => exact NoS.var n
  | norm => exact NoS.norm
  | konst => exact NoS.konst
  | dup => exact NoS.dup
  | swap => exact NoS.swap
  | comp => exact NoS.comp
  | sₛ => exact derived_s_NoS
  | app f x ihf ihx => exact NoS.app ihf ihx

theorem IStepBasis_preserves_NoS {t u : ITerm} (h : IStepBasis t u) (ht : NoS t) : NoS u := by
  induction h with
  | normβ x =>
      cases ht with | app _ hx => exact hx
  | konstβ x y =>
      cases ht with | app hf _ =>
        cases hf with | app _ hx => exact hx
  | compβ f g x =>
      cases ht with | app hf hx =>
        cases hf with | app hfg hg =>
          cases hfg with | app hc hf =>
            exact NoS.app hf (NoS.app hg hx)
  | dupβ f x =>
      cases ht with | app hf hx =>
        cases hf with | app hd hf =>
          exact NoS.app (NoS.app hf hx) hx
  | swapβ f x y =>
      cases ht with | app h_swap_f_x hy =>
        cases h_swap_f_x with | app h_swap_f hx =>
          cases h_swap_f with | app h_swap hf =>
            exact NoS.app (NoS.app hf hy) hx
  | appL _ ih =>
      cases ht with | app hf hx =>
        exact NoS.app (ih hf) hx
  | appR _ ih =>
      cases ht with | app hf hx =>
        exact NoS.app hf (ih hx)

theorem IRedBasis_preserves_NoS {t u : ITerm} (h : IRedBasis t u) (ht : NoS t) : NoS u := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact IStepBasis_preserves_NoS hstep ih
end ISAR
