import ISAR.Kernel

/-!
# BasisDev — parallel development at the *basis* level

The host executors (`graph_runtime` lo/cd, the native routines modules)
implement the **basis** semantics: `IStepCore` (norm/comp/dup/swap) ∪
`IStepKMacro` (konst), with `sₛ` expanded to `derived_s` at import.  The
complete-development machinery in `Kernel.lean` (`ParStep`, `cd`,
`ParStep_diamond`, `ParN`) lives one level up at the **surface**
(`IStep`: konst_macro + sβ; dup/swap are inert atoms there).

This file provides the basis-level counterpart the hosts actually run:

* `ParStepBasis` — parallel step firing `norm/konst/dup/comp/swap`
  redexes (the host `Graph.cd` clause set; `sₛ` is an inert atom — the
  host rejects it at import; `translate_to_basis` is the lowering).
* `cdBasis` — the deterministic complete development, clause-for-clause
  the host `Graph.cd`.
* `ParStepBasis_cd` — the Takahashi triangle.
* `ParStepBasis_diamond`, `IRedBasis_confluence` — confluence of the
  basis rewrite, matching the surface package.

Honest bound: nothing here says the basis is *terminating* (it isn't).
`cdBasis` is a strategy: confluence says orders that reach a normal form
agree on it.
-/

namespace ISAR

/-- Parallel step over the basis rules (fires dup/swap; `sₛ` inert). -/
inductive ParStepBasis : ITerm → ITerm → Prop where
  | var (n : Nat) : ParStepBasis (.var n) (.var n)
  | norm : ParStepBasis .norm .norm
  | konst : ParStepBasis .konst .konst
  | dup : ParStepBasis .dup .dup
  | swap : ParStepBasis .swap .swap
  | comp : ParStepBasis .comp .comp
  | sₛ : ParStepBasis .sₛ .sₛ
  | app {f f' x x'} : ParStepBasis f f' → ParStepBasis x x' →
      ParStepBasis (.app f x) (.app f' x')
  | norm_red {x x'} : ParStepBasis x x' → ParStepBasis (.app .norm x) x'
  | konst_red {x x' y y'} : ParStepBasis x x' → ParStepBasis y y' →
      ParStepBasis (.app (.app .konst x) y) x'
  | dup_red {f f' x x'} : ParStepBasis f f' → ParStepBasis x x' →
      ParStepBasis (.app (.app .dup f) x) (.app (.app f' x') x')
  | comp_red {f f' g g' x x'} : ParStepBasis f f' → ParStepBasis g g' →
      ParStepBasis x x' →
      ParStepBasis (.app (.app (.app .comp f) g) x) (.app f' (.app g' x'))
  | swap_red {f f' x x' y y'} : ParStepBasis f f' → ParStepBasis x x' →
      ParStepBasis y y' →
      ParStepBasis (.app (.app (.app .swap f) x) y) (.app (.app f' y') x')

/-- Complete development at basis level — mirrors host `Graph.cd`. -/
def cdBasis : ITerm → ITerm
  | .var n => .var n
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => .sₛ
  | .app .norm x => cdBasis x
  | .app (.app .konst x) _ => cdBasis x
  | .app (.app .dup f) x =>
      .app (.app (cdBasis f) (cdBasis x)) (cdBasis x)
  | .app (.app (.app .comp f) g) x =>
      .app (cdBasis f) (.app (cdBasis g) (cdBasis x))
  | .app (.app (.app .swap f) x) y =>
      .app (.app (cdBasis f) (cdBasis y)) (cdBasis x)
  | .app f x => .app (cdBasis f) (cdBasis x)

theorem ParStepBasis.refl (t : ITerm) : ParStepBasis t t := by
  induction t with
  | var n => exact ParStepBasis.var n
  | norm => exact ParStepBasis.norm
  | konst => exact ParStepBasis.konst
  | dup => exact ParStepBasis.dup
  | swap => exact ParStepBasis.swap
  | comp => exact ParStepBasis.comp
  | sₛ => exact ParStepBasis.sₛ
  | app f x ihf ihx => exact ParStepBasis.app ihf ihx

theorem IStepCore_to_ParStepBasis {t u : ITerm} (h : IStepCore t u) :
    ParStepBasis t u := by
  induction h with
  | normβ x => exact ParStepBasis.norm_red (ParStepBasis.refl x)
  | compβ f g x =>
      exact ParStepBasis.comp_red (ParStepBasis.refl f)
        (ParStepBasis.refl g) (ParStepBasis.refl x)
  | dupβ f x =>
      exact ParStepBasis.dup_red (ParStepBasis.refl f) (ParStepBasis.refl x)
  | swapβ f x y =>
      exact ParStepBasis.swap_red (ParStepBasis.refl f)
        (ParStepBasis.refl x) (ParStepBasis.refl y)
  | appL _ ih => exact ParStepBasis.app ih (ParStepBasis.refl _)
  | appR _ ih => exact ParStepBasis.app (ParStepBasis.refl _) ih

theorem IStepKMacro_to_ParStepBasis {t u : ITerm} (h : IStepKMacro t u) :
    ParStepBasis t u := by
  induction h with
  | konstβ x y =>
      exact ParStepBasis.konst_red (ParStepBasis.refl x) (ParStepBasis.refl y)
  | appL _ ih => exact ParStepBasis.app ih (ParStepBasis.refl _)
  | appR _ ih => exact ParStepBasis.app (ParStepBasis.refl _) ih

theorem IStepBasis_to_ParStepBasis {t u : ITerm} (h : IStepBasis t u) :
    ParStepBasis t u := by
  cases h with
  | ofCore hc => exact IStepCore_to_ParStepBasis hc
  | ofMacro hm => exact IStepKMacro_to_ParStepBasis hm

/-- Every parallel step is a basis multi-step. -/
theorem ParStepBasis_to_IRedBasis {t u : ITerm} (h : ParStepBasis t u) :
    IRedBasis t u := by
  induction h with
  | var n => exact Relation.ReflTransGen.refl
  | norm => exact Relation.ReflTransGen.refl
  | konst => exact Relation.ReflTransGen.refl
  | dup => exact Relation.ReflTransGen.refl
  | swap => exact Relation.ReflTransGen.refl
  | comp => exact Relation.ReflTransGen.refl
  | sₛ => exact Relation.ReflTransGen.refl
  | app _ _ ihf ihx => exact IRedBasis_app ihf ihx
  | norm_red _ ihx =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (IStepBasis.normβ _)) ihx
  | konst_red _ _ ihx _ =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (IStepBasis.konstβ _ _)) ihx
  | dup_red _ _ ihf ihx =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (IStepBasis.dupβ _ _))
        (IRedBasis_app (IRedBasis_app ihf ihx) ihx)
  | comp_red _ _ _ ihf ihg ihx =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (IStepBasis.compβ _ _ _))
        (IRedBasis_app ihf (IRedBasis_app ihg ihx))
  | swap_red _ _ _ ihf ihx ihy =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (IStepBasis.swapβ _ _ _))
        (IRedBasis_app (IRedBasis_app ihf ihy) ihx)

/-- `cdBasis t` is one parallel step from `t` — rounds are real reductions. -/
theorem ParStepBasis_t_cd : ∀ (t : ITerm), ParStepBasis t (cdBasis t)
  | .var n => ParStepBasis.var n
  | .norm => ParStepBasis.norm
  | .konst => ParStepBasis.konst
  | .dup => ParStepBasis.dup
  | .swap => ParStepBasis.swap
  | .comp => ParStepBasis.comp
  | .sₛ => ParStepBasis.sₛ
  | .app f x => by
      cases f with
      | norm => exact ParStepBasis.norm_red (ParStepBasis_t_cd x)
      | konst =>
          exact ParStepBasis.app (ParStepBasis_t_cd _) (ParStepBasis_t_cd x)
      | dup =>
          exact ParStepBasis.app (ParStepBasis_t_cd _) (ParStepBasis_t_cd x)
      | swap =>
          exact ParStepBasis.app (ParStepBasis_t_cd _) (ParStepBasis_t_cd x)
      | comp =>
          exact ParStepBasis.app (ParStepBasis_t_cd _) (ParStepBasis_t_cd x)
      | sₛ =>
          exact ParStepBasis.app (ParStepBasis_t_cd _) (ParStepBasis_t_cd x)
      | var n =>
          exact ParStepBasis.app (ParStepBasis_t_cd _) (ParStepBasis_t_cd x)
      | app f1 x1 =>
          cases f1 with
          | konst =>
              exact ParStepBasis.konst_red (ParStepBasis_t_cd x1)
                (ParStepBasis_t_cd x)
          | dup =>
              exact ParStepBasis.dup_red (ParStepBasis_t_cd x1)
                (ParStepBasis_t_cd x)
          | app f2 x2 =>
              cases f2 with
              | comp =>
                  exact ParStepBasis.comp_red (ParStepBasis_t_cd x2)
                    (ParStepBasis_t_cd x1) (ParStepBasis_t_cd x)
              | swap =>
                  exact ParStepBasis.swap_red (ParStepBasis_t_cd x2)
                    (ParStepBasis_t_cd x1) (ParStepBasis_t_cd x)
              | _ =>
                  exact ParStepBasis.app (ParStepBasis_t_cd _)
                    (ParStepBasis_t_cd x)
          | _ =>
              exact ParStepBasis.app (ParStepBasis_t_cd _)
                (ParStepBasis_t_cd x)

theorem cdBasis_ired (t : ITerm) : IRedBasis t (cdBasis t) :=
  ParStepBasis_to_IRedBasis (ParStepBasis_t_cd t)

/-- The Takahashi triangle: `cdBasis t` is the greatest parallel-step
    target of `t`.  Clause-for-clause the host `Graph.cd` recursion. -/
theorem ParStepBasis_cd : ∀ (t : ITerm) {u : ITerm},
    ParStepBasis t u → ParStepBasis u (cdBasis t)
  | .var n, _, h => by
      cases h with
      | var n => exact ParStepBasis.var n
  | .norm, _, h => by
      cases h with
      | norm => exact ParStepBasis.norm
  | .konst, _, h => by
      cases h with
      | konst => exact ParStepBasis.konst
  | .dup, _, h => by
      cases h with
      | dup => exact ParStepBasis.dup
  | .swap, _, h => by
      cases h with
      | swap => exact ParStepBasis.swap
  | .comp, _, h => by
      cases h with
      | comp => exact ParStepBasis.comp
  | .sₛ, _, h => by
      cases h with
      | sₛ => exact ParStepBasis.sₛ
  | .app f x, _, h => by
      cases f with
      | var n =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.app (ParStepBasis.var n)
                (ParStepBasis_cd x hx)
      | norm =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.norm_red (ParStepBasis_cd x hx)
          | norm_red hx =>
              exact ParStepBasis_cd x hx
      | konst =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.app ParStepBasis.konst
                (ParStepBasis_cd x hx)
      | dup =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.app ParStepBasis.dup
                (ParStepBasis_cd x hx)
      | swap =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.app ParStepBasis.swap
                (ParStepBasis_cd x hx)
      | comp =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.app ParStepBasis.comp
                (ParStepBasis_cd x hx)
      | sₛ =>
          cases h with
          | app hf hx =>
              cases hf
              exact ParStepBasis.app ParStepBasis.sₛ
                (ParStepBasis_cd x hx)
      | app f1 x1 =>
          cases f1 with
          | var n =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.app
                        (ParStepBasis.app (ParStepBasis.var n)
                          (ParStepBasis_cd x1 hx1))
                        (ParStepBasis_cd x hx)
          | norm =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.app
                        (ParStepBasis.norm_red (ParStepBasis_cd x1 hx1))
                        (ParStepBasis_cd x hx)
                  | norm_red hx1 =>
                      exact ParStepBasis.app (ParStepBasis_cd x1 hx1)
                        (ParStepBasis_cd x hx)
          | konst =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.konst_red
                        (ParStepBasis_cd x1 hx1) (ParStepBasis_cd x hx)
              | konst_red hx1 hx =>
                  exact ParStepBasis_cd x1 hx1
          | dup =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.dup_red (ParStepBasis_cd x1 hx1)
                        (ParStepBasis_cd x hx)
              | dup_red hx1 hx =>
                  exact ParStepBasis.app
                    (ParStepBasis.app (ParStepBasis_cd x1 hx1)
                      (ParStepBasis_cd x hx))
                    (ParStepBasis_cd x hx)
          | swap =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.app
                        (ParStepBasis.app ParStepBasis.swap
                          (ParStepBasis_cd x1 hx1))
                        (ParStepBasis_cd x hx)
          | comp =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.app
                        (ParStepBasis.app ParStepBasis.comp
                          (ParStepBasis_cd x1 hx1))
                        (ParStepBasis_cd x hx)
          | sₛ =>
              cases h with
              | app hf hx =>
                  cases hf with
                  | app hf1 hx1 =>
                      cases hf1
                      exact ParStepBasis.app
                        (ParStepBasis.app ParStepBasis.sₛ
                          (ParStepBasis_cd x1 hx1))
                        (ParStepBasis_cd x hx)
          | app f2 x2 =>
              cases f2 with
              | var n =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.app
                                (ParStepBasis.app
                                  (ParStepBasis.app (ParStepBasis.var n)
                                    (ParStepBasis_cd x2 hx2))
                                  (ParStepBasis_cd x1 hx1))
                                (ParStepBasis_cd x hx)
              | norm =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.app
                                (ParStepBasis.app
                                  (ParStepBasis.norm_red
                                    (ParStepBasis_cd x2 hx2))
                                  (ParStepBasis_cd x1 hx1))
                                (ParStepBasis_cd x hx)
                          | norm_red hx2 =>
                              exact ParStepBasis.app
                                (ParStepBasis.app (ParStepBasis_cd x2 hx2)
                                  (ParStepBasis_cd x1 hx1))
                                (ParStepBasis_cd x hx)
              | konst =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.app
                                (ParStepBasis.konst_red
                                  (ParStepBasis_cd x2 hx2)
                                  (ParStepBasis_cd x1 hx1))
                                (ParStepBasis_cd x hx)
                      | konst_red hx2 hx1 =>
                          exact ParStepBasis.app (ParStepBasis_cd x2 hx2)
                            (ParStepBasis_cd x hx)
              | dup =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.app
                                (ParStepBasis.dup_red
                                  (ParStepBasis_cd x2 hx2)
                                  (ParStepBasis_cd x1 hx1))
                                (ParStepBasis_cd x hx)
                      | dup_red hx2 hx1 =>
                          exact ParStepBasis.app
                            (ParStepBasis.app
                              (ParStepBasis.app
                                (ParStepBasis_cd x2 hx2)
                                (ParStepBasis_cd x1 hx1))
                              (ParStepBasis_cd x1 hx1))
                            (ParStepBasis_cd x hx)
              | comp =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.comp_red
                                (ParStepBasis_cd x2 hx2)
                                (ParStepBasis_cd x1 hx1)
                                (ParStepBasis_cd x hx)
                  | comp_red hx2 hx1 hx =>
                      exact ParStepBasis.app (ParStepBasis_cd x2 hx2)
                        (ParStepBasis.app (ParStepBasis_cd x1 hx1)
                          (ParStepBasis_cd x hx))
              | swap =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.swap_red
                                (ParStepBasis_cd x2 hx2)
                                (ParStepBasis_cd x1 hx1)
                                (ParStepBasis_cd x hx)
                  | swap_red hx2 hx1 hx =>
                      exact ParStepBasis.app
                        (ParStepBasis.app (ParStepBasis_cd x2 hx2)
                          (ParStepBasis_cd x hx))
                        (ParStepBasis_cd x1 hx1)
              | sₛ =>
                  cases h with
                  | app hf hx =>
                      cases hf with
                      | app hf1 hx1 =>
                          cases hf1 with
                          | app hf2 hx2 =>
                              cases hf2
                              exact ParStepBasis.app
                                (ParStepBasis.app
                                  (ParStepBasis.app ParStepBasis.sₛ
                                    (ParStepBasis_cd x2 hx2))
                                  (ParStepBasis_cd x1 hx1))
                                (ParStepBasis_cd x hx)
              | app f3 x3 =>
                  cases h with
                  | app hf hx =>
                      exact ParStepBasis.app
                        (ParStepBasis_cd
                          (.app (.app (.app f3 x3) x2) x1) hf)
                        (ParStepBasis_cd x hx)

theorem ParStepBasis_diamond {t u₁ u₂ : ITerm}
    (h₁ : ParStepBasis t u₁) (h₂ : ParStepBasis t u₂) :
    ∃ v, ParStepBasis u₁ v ∧ ParStepBasis u₂ v :=
  ⟨cdBasis t, ParStepBasis_cd t h₁, ParStepBasis_cd t h₂⟩

theorem ParStepBasis_commute {t u₁ u₂ : ITerm}
    (h₁ : ParStepBasis t u₁)
    (h₂ : Relation.ReflTransGen ParStepBasis t u₂) :
    ∃ v, Relation.ReflTransGen ParStepBasis u₁ v ∧
      ParStepBasis u₂ v := by
  induction h₂ generalizing u₁ with
  | refl =>
      exact ⟨u₁, Relation.ReflTransGen.refl, h₁⟩
  | tail _ hstep ih =>
      match ih h₁ with
      | ⟨v, hv₁, hv₂⟩ =>
          match ParStepBasis_diamond hv₂ hstep with
          | ⟨w, hw₁, hw₂⟩ =>
              exact ⟨w, Relation.ReflTransGen.tail hv₁ hw₁, hw₂⟩

theorem ParTransGenBasis_diamond {t u₁ u₂ : ITerm}
    (h₁ : Relation.ReflTransGen ParStepBasis t u₁)
    (h₂ : Relation.ReflTransGen ParStepBasis t u₂) :
    ∃ v, Relation.ReflTransGen ParStepBasis u₁ v ∧
      Relation.ReflTransGen ParStepBasis u₂ v := by
  induction h₁ generalizing u₂ with
  | refl =>
      exact ⟨u₂, h₂, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      match ih h₂ with
      | ⟨v, hv₁, hv₂⟩ =>
          match ParStepBasis_commute hstep hv₁ with
          | ⟨w, hw₁, hw₂⟩ =>
              exact ⟨w, hw₁, Relation.ReflTransGen.tail hv₂ hw₂⟩

theorem IRedBasis_to_ParTransGenBasis {t u : ITerm} (h : IRedBasis t u) :
    Relation.ReflTransGen ParStepBasis t u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (IStepBasis_to_ParStepBasis hstep)

theorem ParTransGenBasis_to_IRedBasis {t u : ITerm}
    (h : Relation.ReflTransGen ParStepBasis t u) : IRedBasis t u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (ParStepBasis_to_IRedBasis hstep)

/-- Basis confluence: the property that makes multi-witness NF
    comparison meaningful at the level the hosts execute. -/
theorem IRedBasis_confluence {t u₁ u₂ : ITerm}
    (h₁ : IRedBasis t u₁) (h₂ : IRedBasis t u₂) :
    ∃ v, IRedBasis u₁ v ∧ IRedBasis u₂ v := by
  have pt1 := IRedBasis_to_ParTransGenBasis h₁
  have pt2 := IRedBasis_to_ParTransGenBasis h₂
  match ParTransGenBasis_diamond pt1 pt2 with
  | ⟨v, hv₁, hv₂⟩ =>
      exact ⟨v, ParTransGenBasis_to_IRedBasis hv₁,
        ParTransGenBasis_to_IRedBasis hv₂⟩

end ISAR
