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

`TrivialPE` is a sorry-free non-optimizing instance (`¬ Nontrivial`).
`OptimizingPE` is a sorry-free fragment specializer with proved `Nontrivial`
(identity / konstβ folds + tagged residual fallback). Full Jones–Gomard–Sestoft BTA
for all of ISAR remains dissertation-scale future work; the projections below are
the mix instantiations.
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

/-- Identity residualizer (ignores static data). Cost-vacuous, but cannot be packaged as
`PESetup` with `eval prog _ := some prog`: `selfApp` forces `specTerm` to behave like a
realizer, colliding when programs can equal `specTerm`. -/
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

/-! ### Principled trivial `PESetup` (tagged residual, recursive unpack)

Identity `spec` cannot satisfy `selfApp` for a universal `eval prog _ := some prog`.
Instead residualize under a `dup` tag and reflect the specializer as bare `swap`.
Evaluation recursively unpacks residuals so mix holds for **all** `p` (including when
`p` is itself tagged); `selfApp` is the `swap` clause. Cost never shrinks, so
`¬ Nontrivial`. A real self-applicable optimizing `specTerm` / BTA remains future work.
-/

/-- Tagged residual: `dup · (pair p s)`. Strictly larger than `p` under `pe_cost`. -/
def trivial_spec (p s : ITerm) : ITerm :=
  ITerm.app ITerm.dup (pair p s)

/--
Object-level evaluator for the toy specializer.
* `swap` on `pair p s` returns the tagged residual (`selfApp`).
* A tagged residual applied to dynamic `d` continues as `run p (pair s d)` (mix),
  recursively, so residual-shaped programs do not break the mix equation.
* Otherwise return the syntactic application.
-/
def trivial_run : ITerm → ITerm → ITerm
  | ITerm.swap, data =>
      match data with
      | ITerm.app (ITerm.app ITerm.konst p) s => trivial_spec p s
      | _ => ITerm.app ITerm.swap data
  | ITerm.app ITerm.dup (ITerm.app (ITerm.app ITerm.konst p) s), d =>
      trivial_run p (pair s d)
  | p, d => ITerm.app p d

def trivial_eval (prog data : ITerm) : Option ITerm :=
  some (trivial_run prog data)

theorem trivial_mix (p s d : ITerm) :
    trivial_eval (trivial_spec p s) d = trivial_eval p (pair s d) := by
  rfl

theorem trivial_selfApp (p s : ITerm) :
    trivial_eval ITerm.swap (pair p s) = some (trivial_spec p s) := by
  rfl

/-- Toy `PESetup`: mix and selfApp by `rfl`; residualizer is cost-non-shrinking. -/
def TrivialPE : PESetup where
  eval := trivial_eval
  spec := trivial_spec
  specTerm := ITerm.swap
  mix := trivial_mix
  selfApp := trivial_selfApp

theorem pe_cost_trivial_spec (p s : ITerm) :
    pe_cost (trivial_spec p s) = pe_cost p + pe_cost s + 5 := by
  dsimp [trivial_spec, pair, pe_cost, term_size]
  omega

theorem trivial_spec_not_shrinking :
    ¬ ∃ p s : ITerm, pe_cost (trivial_spec p s) < pe_cost p := by
  rintro ⟨p, s, hlt⟩
  have hge : pe_cost p ≤ pe_cost (trivial_spec p s) := by
    dsimp [trivial_spec, pair, pe_cost, term_size]
    omega
  exact Nat.not_lt_of_ge hge hlt

/-- Mix+selfApp alone do not imply optimization: `TrivialPE` is not `Nontrivial`. -/
theorem TrivialPE_not_nontrivial : ¬ Nontrivial TrivialPE := by
  rintro ⟨p, s, hlt⟩
  exact trivial_spec_not_shrinking ⟨p, s, hlt⟩

/-! ### Optimizing fragment PE (identity / konstβ folding)

Not a full Jones–Gomard–Sestoft BTA for all of ISAR. This is a principled
**optimizing** specializer on a fragment:

* Peel `norm · body` (identity elimination) and `(konst · x) · y` (konstβ / dead elim).
* Atomic combinators (except `swap`, reserved as `specTerm`) residualize to themselves.
* Remaining programs get a `dup`-tagged residual (same packaging as `TrivialPE`).

`mix` / `selfApp` hold by computation on this evaluator; `Nontrivial` is witnessed by
stripping a `norm` redex. Full self-applicable optimizing mix for the whole calculus
remains dissertation-scale future work.
-/

/-- Meta specializer with static identity / konstβ folds. -/
def opt_spec (p s : ITerm) : ITerm :=
  match p with
  | ITerm.app ITerm.norm body => opt_spec body s
  | ITerm.app (ITerm.app ITerm.konst x) _y => opt_spec x s
  | ITerm.norm => ITerm.norm
  | ITerm.konst => ITerm.konst
  | ITerm.sₛ => ITerm.sₛ
  | ITerm.dup => ITerm.dup
  | ITerm.comp => ITerm.comp
  | ITerm.var n => ITerm.var n
  | _ => ITerm.app ITerm.dup (pair p s)

/--
Object-level evaluator matching `opt_spec`:
* `swap` on `pair p s` implements `selfApp`.
* Tagged residuals unpack via mix.
* Program-position `norm` / `konstβ` peels mirror `opt_spec`.
* Atomic values are data-insensitive (so constant residuals satisfy mix).
-/
def opt_run : ITerm → ITerm → ITerm
  | ITerm.swap, data =>
      match data with
      | ITerm.app (ITerm.app ITerm.konst p) s => opt_spec p s
      | _ => ITerm.app ITerm.swap data
  | ITerm.app ITerm.dup (ITerm.app (ITerm.app ITerm.konst p) s), d =>
      opt_run p (pair s d)
  | ITerm.app ITerm.norm body, d =>
      opt_run body d
  | ITerm.app (ITerm.app ITerm.konst x) _y, d =>
      opt_run x d
  | ITerm.norm, _ => ITerm.norm
  | ITerm.konst, _ => ITerm.konst
  | ITerm.sₛ, _ => ITerm.sₛ
  | ITerm.dup, _ => ITerm.dup
  | ITerm.comp, _ => ITerm.comp
  | ITerm.var n, _ => ITerm.var n
  | p, d => ITerm.app p d

def opt_eval (prog data : ITerm) : Option ITerm :=
  some (opt_run prog data)

theorem opt_mix (p s d : ITerm) :
    opt_eval (opt_spec p s) d = opt_eval p (pair s d) := by
  cases p with
  | var _ => rfl
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f x =>
      cases f with
      | norm =>
          have h := opt_mix x s d
          simpa [opt_spec, opt_eval, opt_run] using h
      | app f1 x1 =>
          cases f1 with
          | konst =>
              have h := opt_mix x1 s d
              simpa [opt_spec, opt_eval, opt_run] using h
          | var _ => rfl
          | norm => rfl
          | dup => rfl
          | swap => rfl
          | comp => rfl
          | sₛ => rfl
          | app _ _ => rfl
      | var _ => rfl
      | konst => rfl
      | dup => rfl
      | swap => rfl
      | comp => rfl
      | sₛ => rfl
termination_by term_size p
decreasing_by
  all_goals (simp [term_size]; omega)

theorem opt_selfApp (p s : ITerm) :
    opt_eval ITerm.swap (pair p s) = some (opt_spec p s) := by
  rfl

/-- Optimizing fragment `PESetup`: mix/selfApp by induction/`rfl`; `Nontrivial` below. -/
def OptimizingPE : PESetup where
  eval := opt_eval
  spec := opt_spec
  specTerm := ITerm.swap
  mix := opt_mix
  selfApp := opt_selfApp

/-- Witness program: `norm · konst` strips to `konst`. -/
def opt_witness_p : ITerm := ITerm.app ITerm.norm ITerm.konst

theorem opt_spec_norm_konst (s : ITerm) :
    opt_spec opt_witness_p s = ITerm.konst := by
  rfl

theorem pe_cost_opt_witness (s : ITerm) :
    pe_cost (opt_spec opt_witness_p s) < pe_cost opt_witness_p := by
  simp only [opt_witness_p, opt_spec, pe_cost, term_size]
  omega

theorem OptimizingPE_nontrivial : Nontrivial OptimizingPE :=
  ⟨opt_witness_p, ITerm.konst, pe_cost_opt_witness ITerm.konst⟩

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
