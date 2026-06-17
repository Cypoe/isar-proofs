import ISAR.InvariantLayer

namespace ISAR

/-- Substitution function replacing variables with terms. -/
def subst_env (t : ITerm) (env : Nat → ITerm) : ITerm :=
  match t with
  | ITerm.var n => env n
  | ITerm.norm => ITerm.norm
  | ITerm.konst => ITerm.konst
  | ITerm.dup => ITerm.dup
  | ITerm.swap => ITerm.swap
  | ITerm.comp => ITerm.comp
  | ITerm.sₛ => ITerm.sₛ
  | ITerm.app f x => ITerm.app (subst_env f env) (subst_env x env)

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
  ∀ n, subst_env (match static_env n with | some val => val | none => ITerm.var n) dynamic_env = env n

/-- Theorem: Substitution preserves single-step ISAR reduction. -/
theorem subst_env_preserves_step {t u : ITerm} (env : Nat → ITerm) (h : IStep t u) :
    IStep (subst_env t env) (subst_env u env) := by
  induction h generalizing env with
  | normβ x =>
      dsimp [subst_env]
      exact IStep.normβ (subst_env x env)
  | konstβ x y =>
      dsimp [subst_env]
      exact IStep.konstβ (subst_env x env) (subst_env y env)
  | compβ f g x =>
      dsimp [subst_env]
      exact IStep.compβ (subst_env f env) (subst_env g env) (subst_env x env)
  | sβ x y z =>
      dsimp [subst_env]
      exact IStep.sβ (subst_env x env) (subst_env y env) (subst_env z env)
  | appL hf ih =>
      dsimp [subst_env]
      exact IStep.appL (ih env)
  | appR hx ih =>
      dsimp [subst_env]
      exact IStep.appR (ih env)

/-- Theorem: Substitution preserves multi-step ISAR reduction. -/
theorem subst_env_preserves_red {t u : ITerm} (env : Nat → ITerm) (h : IRed t u) :
    IRed (subst_env t env) (subst_env u env) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (subst_env_preserves_step env hstep)

/--
Theorem: First Futamura Projection (Specialization Soundness).
Evaluating the specialized program with the dynamic environment is identical
to evaluating the original program with the full environment.
-/
theorem futamura_first (t : ITerm) (env : Nat → ITerm) (static_env : Nat → Option ITerm) (dynamic_env : Nat → ITerm)
    (h_coh : Coherent env static_env dynamic_env) :
    subst_env (specialize t static_env) dynamic_env = subst_env t env := by
  induction t with
  | var n =>
    dsimp [specialize]
    split
    next val h_val =>
      have h_coh_n := h_coh n
      dsimp [subst_env] at *
      rw [h_val] at h_coh_n
      exact h_coh_n
    next h_val =>
      have h_coh_n := h_coh n
      dsimp [subst_env] at *
      rw [h_val] at h_coh_n
      exact h_coh_n
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f x ihf ihx =>
      dsimp [specialize, subst_env]
      rw [ihf, ihx]

/-- Correctness predicate for a specializer term. -/
def SpecializerCorrect (spec_term : ITerm) (make_env : ITerm → (Nat → Option ITerm) → (Nat → ITerm)) : Prop :=
  ∀ (p : ITerm) (s_env : Nat → Option ITerm),
    subst_env spec_term (make_env p s_env) = specialize p s_env

/--
Theorem: Second Futamura Projection (Compiler Generation Correctness).
Specializing the specializer with respect to the interpreter yields a compiler, which
when applied to the dynamic environment, behaves exactly like specializing the interpreter directly.
-/
theorem futamura_second
    (spec_term : ITerm)
    (make_env : ITerm → (Nat → Option ITerm) → (Nat → ITerm))
    (h_corr : SpecializerCorrect spec_term make_env)
    (interp : ITerm)
    (static_env_for_interp : Nat → Option ITerm)
    (static_env_for_spec : Nat → Option ITerm)
    (dynamic_env_for_spec : Nat → ITerm)
    (h_coh : Coherent (make_env interp static_env_for_interp) static_env_for_spec dynamic_env_for_spec) :
    subst_env (specialize spec_term static_env_for_spec) dynamic_env_for_spec =
      specialize interp static_env_for_interp := by
  have h_first := futamura_first spec_term (make_env interp static_env_for_interp) static_env_for_spec dynamic_env_for_spec h_coh
  have h_spec := h_corr interp static_env_for_interp
  rw [h_first, h_spec]

/--
Theorem: Third Futamura Projection (Compiler Generator Correctness).
Specializing the specializer with respect to itself yields a compiler generator (cogen), which
when applied to an interpreter, behaves exactly like specializing the specializer directly with respect to that interpreter.
-/
theorem futamura_third
    (spec_term : ITerm)
    (make_env : ITerm → (Nat → Option ITerm) → (Nat → ITerm))
    (h_corr : SpecializerCorrect spec_term make_env)
    (static_env_for_spec_interp : Nat → Option ITerm)
    (static_env_for_cogen : Nat → Option ITerm)
    (dynamic_env_for_cogen : Nat → ITerm)
    (h_coh : Coherent (make_env spec_term static_env_for_spec_interp) static_env_for_cogen dynamic_env_for_cogen) :
    subst_env (specialize spec_term static_env_for_cogen) dynamic_env_for_cogen =
      specialize spec_term static_env_for_spec_interp := by
  have h_first := futamura_first spec_term (make_env spec_term static_env_for_spec_interp) static_env_for_cogen dynamic_env_for_cogen h_coh
  have h_spec := h_corr spec_term static_env_for_spec_interp
  rw [h_first, h_spec]

/-- Theorem: For any term in the pure ISK fragment, specialization is the identity. -/
theorem specialize_ISKTerm (t : ITerm) (ht : ISKTerm t) (s_env : Nat → Option ITerm) :
    specialize t s_env = t := by
  induction ht with
  | norm => rfl
  | konst => rfl
  | sₛ => rfl
  | app hf hx ihf ihx =>
      dsimp [specialize]
      rw [ihf, ihx]

/-- Theorem: Specialization of any ISKTerm is itself an ISKTerm. -/
theorem specialize_is_ISKTerm (t : ITerm) (ht : ISKTerm t) (s_env : Nat → Option ITerm) :
    ISKTerm (specialize t s_env) := by
  rw [specialize_ISKTerm t ht s_env]
  exact ht

/--
Theorem: Syntactic specialization respects operational equivalence (OperEq) on the ISKSubtype fragment.
Since specialization acts as the identity on variable-free terms, it trivially preserves equivalence classes.
-/
theorem specialize_respects_OperEq (t u : ITerm) (ht : ISKTerm t) (hu : ISKTerm u)
    (h : OperEq ⟨t, ht⟩ ⟨u, hu⟩) (s_env : Nat → Option ITerm) :
    ∃ (ht_spec : ISKTerm (specialize t s_env)) (hu_spec : ISKTerm (specialize u s_env)),
      OperEq ⟨specialize t s_env, ht_spec⟩ ⟨specialize u s_env, hu_spec⟩ := by
  have ht_spec := specialize_is_ISKTerm t ht s_env
  have hu_spec := specialize_is_ISKTerm u hu s_env
  have h_t_eq : specialize t s_env = t := specialize_ISKTerm t ht s_env
  have h_u_eq : specialize u s_env = u := specialize_ISKTerm u hu s_env
  have h_goal : ⟨specialize t s_env, ht_spec⟩ = (⟨t, ht⟩ : ISKSubtype) := Subtype.ext h_t_eq
  have h_goal2 : ⟨specialize u s_env, hu_spec⟩ = (⟨u, hu⟩ : ISKSubtype) := Subtype.ext h_u_eq
  have h_eq_eq : OperEq ⟨specialize t s_env, ht_spec⟩ ⟨specialize u s_env, hu_spec⟩ := by
    rw [h_goal, h_goal2]
    exact h
  exact ⟨ht_spec, hu_spec, h_eq_eq⟩


end ISAR



