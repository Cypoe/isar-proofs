import ISAR

namespace ISAR

/-- Substitution function replacing variables with terms. -/
def subst (t : ITerm) (env : Nat → ITerm) : ITerm :=
  match t with
  | ITerm.var n => env n
  | ITerm.norm => ITerm.norm
  | ITerm.konst => ITerm.konst
  | ITerm.dup => ITerm.dup
  | ITerm.swap => ITerm.swap
  | ITerm.comp => ITerm.comp
  | ITerm.sₛ => ITerm.sₛ
  | ITerm.app f x => ITerm.app (subst f env) (subst x env)

/-- Specializer (partial evaluator) replacing static variables. -/
def specialize (t : ITerm) (static_env : Nat → Option ITerm) : ITerm :=
  match t with
  | ITerm.var n =>
      match static_env n with
      | some val => val
      | none => ITerm.var n
  | ITerm.norm => ITerm.norm
  | ITerm.konst => ITerm.konst
  | ITerm.dup => ITerm.dup
  | ITerm.swap => ITerm.swap
  | ITerm.comp => ITerm.comp
  | ITerm.sₛ => ITerm.sₛ
  | ITerm.app f x => ITerm.app (specialize f static_env) (specialize x static_env)

/-- Coherence condition relating full environment and partial environments. -/
def Coherent (env : Nat → ITerm) (static_env : Nat → Option ITerm) (dynamic_env : Nat → ITerm) : Prop :=
  ∀ n, subst (match static_env n with | some val => val | none => ITerm.var n) dynamic_env = env n

/-- Theorem: Substitution preserves single-step ISAR reduction. -/
theorem subst_preserves_step {t u : ITerm} (env : Nat → ITerm) (h : IStep t u) :
    IStep (subst t env) (subst u env) := by
  induction h generalizing env with
  | normβ x =>
      dsimp [subst]
      exact IStep.normβ (subst x env)
  | konstβ x y =>
      dsimp [subst]
      exact IStep.konstβ (subst x env) (subst y env)
  | compβ f g x =>
      dsimp [subst]
      exact IStep.compβ (subst f env) (subst g env) (subst x env)
  | sβ x y z =>
      dsimp [subst]
      exact IStep.sβ (subst x env) (subst y env) (subst z env)
  | appL hf ih =>
      dsimp [subst]
      exact IStep.appL (ih env)
  | appR hx ih =>
      dsimp [subst]
      exact IStep.appR (ih env)

/-- Theorem: Substitution preserves multi-step ISAR reduction. -/
theorem subst_preserves_red {t u : ITerm} (env : Nat → ITerm) (h : IRed t u) :
    IRed (subst t env) (subst u env) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (subst_preserves_step env hstep)

/--
Theorem: First Futamura Projection (Specialization Soundness).
Evaluating the specialized program with the dynamic environment is identical
to evaluating the original program with the full environment.
-/
theorem futamura_first (t : ITerm) (env : Nat → ITerm) (static_env : Nat → Option ITerm) (dynamic_env : Nat → ITerm)
    (h_coh : Coherent env static_env dynamic_env) :
    subst (specialize t static_env) dynamic_env = subst t env := by
  induction t with
  | var n =>
    dsimp [specialize]
    split
    next val h_val =>
      have h_coh_n := h_coh n
      dsimp [subst] at *
      rw [h_val] at h_coh_n
      exact h_coh_n
    next h_val =>
      have h_coh_n := h_coh n
      dsimp [subst] at *
      rw [h_val] at h_coh_n
      exact h_coh_n
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f x ihf ihx =>
      dsimp [specialize, subst]
      rw [ihf, ihx]

end ISAR
