import ISAR.InvariantLayer
import ISAR.CanonicalRepresentative

namespace ISAR

/-!
# Partial evaluation and Futamura projections

Honest formulation (Jones/Gomard/Sestoft): the three projections follow from the mix
equation once the specializer is reflected as an object-level term (`specTerm`) with
`selfApp`. Mix alone admits a trivial specializer; nontriviality is a separate obligation.
-/

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

/-- Meta-level specializer (partial evaluator) replacing static variables. -/
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

/-- Pairing of terms as a binary application spine. -/
def pair (s d : ITerm) : ITerm := ITerm.app (ITerm.app ITerm.konst s) d

/-- Coherence condition relating full environment and partial environments. -/
def Coherent (env : Nat → ITerm) (static_env : Nat → Option ITerm) (dynamic_env : Nat → ITerm) : Prop :=
  ∀ n, subst_env (match static_env n with | some val => val | none => ITerm.var n) dynamic_env = env n

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

theorem subst_env_preserves_red {t u : ITerm} (env : Nat → ITerm) (h : IRed t u) :
    IRed (subst_env t env) (subst_env u env) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (subst_env_preserves_step env hstep)

/-- Mix equation at the subst layer (first Futamura projection / specialization soundness). -/
theorem futamura_first (t : ITerm) (env : Nat → ITerm) (static_env : Nat → Option ITerm)
    (dynamic_env : Nat → ITerm) (h_coh : Coherent env static_env dynamic_env) :
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

/--
Setup for object-level Futamura projections.
`spec` is the meta specializer; `specTerm` is its reflection as an `ITerm`;
`mix` is the characterizing equation; `selfApp` says evaluating `specTerm` implements `spec`.

Constructing a real self-applicable ISAR `specTerm` (binding-time analysis / Jones–Gomard–Sestoft)
is left as future work; the projections below are the mix instantiations.
-/
structure PESetup where
  eval : ITerm → ITerm → Option ITerm
  spec : ITerm → ITerm → ITerm
  specTerm : ITerm
  mix : ∀ p s d, eval (spec p s) d = eval p (pair s d)
  selfApp : ∀ p s, eval specTerm (pair p s) = some (spec p s)

/-- Second Futamura projection: specializing the specializer w.r.t. an interpreter. -/
theorem futamura_second (S : PESetup) (int src : ITerm) :
    S.eval (S.spec S.specTerm int) src = some (S.spec int src) := by
  rw [S.mix]
  exact S.selfApp int src

/-- Third Futamura projection: self-application yields a compiler generator. -/
theorem futamura_third (S : PESetup) (int : ITerm) :
    S.eval (S.spec S.specTerm S.specTerm) int = some (S.spec S.specTerm int) := by
  rw [S.mix]
  exact S.selfApp S.specTerm int

/-- Cost measure for nontriviality (term size). -/
def pe_cost : ITerm → Nat := term_size

/--
Nontriviality: specialization strictly reduces cost on some nonempty class of programs.
Without this, mix+selfApp alone are satisfied by residualizers that do no optimization
(e.g. the identity residualizer `spec p s = p`).
-/
def Nontrivial (S : PESetup) : Prop :=
  ∃ p s, pe_cost (S.spec p s) < pe_cost p

/-- Identity residualizer (ignores static data). Satisfies mix for `eval prog _ := some prog`. -/
def identity_spec (p _s : ITerm) : ITerm := p

theorem identity_spec_mix (p s d : ITerm) :
    (some (identity_spec p s) : Option ITerm) = some p :=
  rfl

/-- Vacuity witness: identity residualization never shrinks under `pe_cost`. -/
theorem identity_spec_not_shrinking :
    ¬ ∃ p s : ITerm, pe_cost (identity_spec p s) < pe_cost p := by
  intro h
  rcases h with ⟨p, s, hlt⟩
  simp [identity_spec, pe_cost] at hlt

/--
A `PESetup` with identity `spec` would need an `eval`/`specTerm` pair satisfying `selfApp`
without collapsing the carrier. Packaging that instance is deferred with the real
self-applicable specializer; the cost vacuity above already shows why `Nontrivial`
is an independent obligation from mix alone.
-/

theorem specialize_ISKTerm (t : ITerm) (ht : ISKTerm t) (s_env : Nat → Option ITerm) :
    specialize t s_env = t := by
  induction ht with
  | norm => rfl
  | konst => rfl
  | sₛ => rfl
  | app hf hx ihf ihx =>
      dsimp [specialize]
      rw [ihf, ihx]

theorem specialize_is_ISKTerm (t : ITerm) (ht : ISKTerm t) (s_env : Nat → Option ITerm) :
    ISKTerm (specialize t s_env) := by
  rw [specialize_ISKTerm t ht s_env]
  exact ht

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
