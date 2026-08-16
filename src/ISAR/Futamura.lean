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

`TrivialPE` is a sorry-free non-optimizing instance (`¬ Nontrivial`, `¬ JonesOptimal`).
`OptimizingPE` is a sorry-free fragment specializer with proved `Nontrivial`
(identity / konstβ folds + tagged residual fallback). `JGS_PE` is online PE for
the whole `IStep` signature (`Nontrivial`, `¬ JonesOptimal`). Jones-optimality is
the cost criterion (`JonesOptimal`); a toy self-interpreter pair `JonesIdPE`
meets it. Full Jones–Gomard–Sestoft 1993 polyvariant BTA / cogen remains open;
`specTerm` is still `swap`, not an encoding of `jgs_spec` / `offline_spec`.
The projections below are the mix instantiations.
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

theorem term_size_pos (t : ITerm) : 1 ≤ term_size t := by
  induction t <;> simp [term_size]

/--
Nontriviality: specialization strictly reduces cost on some nonempty class of programs.
Without this, mix+selfApp alone are satisfied by residualizers that do no optimization
(e.g. the identity residualizer `spec p s = p`).
-/
def Nontrivial (S : PESetup) : Prop :=
  ∃ p s, pe_cost (S.spec p s) < pe_cost p

/-- Self-interpreter: running `int` on `(src, d)` agrees with running `src` on `d`. -/
def SelfInterpreter (S : PESetup) (int : ITerm) : Prop :=
  ∀ src d, S.eval int (pair src d) = S.eval src d

/--
Jones-optimality (Neil Jones): some self-interpreter specializes to a residual
no more expensive than the source, for every source. Cost/`pe_cost` form matches
`Nontrivial`. This is **not** 1993 polyvariant mix / compiler-generator quality;
`specTerm` is not an encoding of `jgs_spec` or `offline_spec`.
-/
def JonesOptimal (S : PESetup) : Prop :=
  ∃ int, SelfInterpreter S int ∧ ∀ src, pe_cost (S.spec int src) ≤ pe_cost src

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

/-- `trivial_run` returns `konst · norm` only by the default clause on those atoms. -/
theorem trivial_run_result_konst_norm :
    ∀ (n : Nat) (p d : ITerm), term_size p ≤ n →
      trivial_run p d = ITerm.app ITerm.konst ITerm.norm →
        p = ITerm.konst ∧ d = ITerm.norm := by
  intro n
  induction n with
  | zero =>
      intro p d hsz h
      have := term_size_pos p
      omega
  | succ n ih =>
      intro p d hsz h
      cases p with
      | var _ | norm | dup | comp | sₛ =>
          simp [trivial_run] at h
      | konst =>
          simp [trivial_run] at h
          exact ⟨rfl, h⟩
      | swap =>
          cases d with
          | app d1 d2 =>
              cases d1 with
              | app d11 d12 =>
                  cases d11 with
                  | konst => simp [trivial_run, trivial_spec, pair] at h
                  | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                      simp [trivial_run] at h
              | var _ | norm | konst | dup | swap | comp | sₛ =>
                  simp [trivial_run] at h
          | var _ | norm | konst | dup | swap | comp | sₛ =>
              simp [trivial_run] at h
      | app f x =>
          cases f with
          | dup =>
              cases x with
              | app x1 x2 =>
                  cases x1 with
                  | app x11 p' =>
                      cases x11 with
                      | konst =>
                          have hrec : trivial_run p' (pair x2 d) =
                              ITerm.app ITerm.konst ITerm.norm := by
                            simpa [trivial_run, pair] using h
                          have hszp : term_size p' ≤ n := by
                            simp [term_size] at hsz ⊢
                            omega
                          have ⟨_, hpair⟩ := ih p' (pair x2 d) hszp hrec
                          simp [pair] at hpair
                      | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                          simp [trivial_run] at h
                  | var _ | norm | konst | dup | swap | comp | sₛ =>
                      simp [trivial_run] at h
              | var _ | norm | konst | dup | swap | comp | sₛ =>
                  simp [trivial_run] at h
          | var _ | norm | konst | swap | comp | sₛ | app _ _ =>
              simp [trivial_run] at h

theorem TrivialPE_not_self_interpreter (int : ITerm) :
    ¬ SelfInterpreter TrivialPE int := by
  intro hSI
  have hrun : trivial_run int (pair ITerm.konst ITerm.norm) =
      ITerm.app ITerm.konst ITerm.norm := by
    have := hSI ITerm.konst ITerm.norm
    simpa [SelfInterpreter, TrivialPE, trivial_eval, trivial_run, pair] using this
  have ⟨_, hpair⟩ :=
    trivial_run_result_konst_norm (term_size int) int (pair ITerm.konst ITerm.norm)
      (Nat.le_refl _) hrun
  simp [pair] at hpair

/-- Tagged residuals are strictly larger than the source, so no self-interpreter
can meet the Jones cost bound either — `TrivialPE` is not Jones-optimal. -/
theorem TrivialPE_not_jonesOptimal : ¬ JonesOptimal TrivialPE := by
  rintro ⟨int, hSI, _⟩
  exact TrivialPE_not_self_interpreter int hSI

/-! ### Toy Jones-optimal pair (identity interpreter, not 1993 mix)

`norm` as a degenerate self-interpreter: running it on `(src, d)` continues as
`src` on `d`. Specializing that interpreter copies the source (`spec norm src = src`),
so the Jones cost bound holds with equality. Mix/selfApp still use tagged residuals
for every other program. This is a cost-criterion toy, **not** a 1993 compiler-generator.
-/

def jones_spec (p s : ITerm) : ITerm :=
  if p = ITerm.norm then s else trivial_spec p s

def jones_run : ITerm → ITerm → ITerm
  | ITerm.swap, data =>
      match data with
      | ITerm.app (ITerm.app ITerm.konst p) s => jones_spec p s
      | _ => ITerm.app ITerm.swap data
  | ITerm.app ITerm.dup (ITerm.app (ITerm.app ITerm.konst p) s), d =>
      jones_run p (pair s d)
  | ITerm.norm, data =>
      match data with
      | ITerm.app (ITerm.app ITerm.konst p) d => jones_run p d
      | _ => ITerm.app ITerm.norm data
  | p, d => ITerm.app p d
termination_by p d => term_size p + term_size d
decreasing_by
  all_goals (simp [pair, term_size]; omega)

def jones_eval (prog data : ITerm) : Option ITerm :=
  some (jones_run prog data)

theorem jones_mix (p s d : ITerm) :
    jones_eval (jones_spec p s) d = jones_eval p (pair s d) := by
  by_cases hp : p = ITerm.norm
  { subst hp
    simp [jones_eval, jones_spec, jones_run, pair] }
  { simp [jones_eval, jones_spec, hp, trivial_spec, jones_run, pair] }

theorem jones_selfApp (p s : ITerm) :
    jones_eval ITerm.swap (pair p s) = some (jones_spec p s) := by
  simp [jones_eval, jones_run, pair, jones_spec]

def JonesIdPE : PESetup where
  eval := jones_eval
  spec := jones_spec
  specTerm := ITerm.swap
  mix := jones_mix
  selfApp := jones_selfApp

theorem JonesIdPE_self_interpreter_norm : SelfInterpreter JonesIdPE ITerm.norm := by
  intro src d
  simp [JonesIdPE, jones_eval, jones_run, pair]

theorem JonesIdPE_jonesOptimal : JonesOptimal JonesIdPE :=
  ⟨ITerm.norm, JonesIdPE_self_interpreter_norm, fun src => by
    simp [JonesIdPE, jones_spec, pe_cost]⟩

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

/-! ### Jones–Gomard–Sestoft online PE for the whole `IStep` signature

Offline BTA classifies subterms; online PE *is* the 1985 mix technique once every
object-language redex can fire at specialization time. ISAR's object reductions
are exactly `normβ`, `konstβ`, `compβ`, `sβ`. This specializer folds all four.

* Size-decreasing folds (`norm`, `konst`, `comp`) recurse.
* `sβ` can grow `term_size`; we unfold once into a tagged residual (no recursion).
* `swap` remains `specTerm`. Polyvariant *offline* mix that generates a
  compiler-generator of Jones–Gomard–Sestoft 1993 quality is still open;
  the object-language signature is covered.
-/

/-- Offline binding-time sketch: `swap` is the dynamic hole; other atoms are static;
    application is static iff both sides are. Monovariant: no call strings, no
    program-point splitting. Unused by `jgs_spec` (online PE). Lemmas below
    relate `bta` to specialization; they do **not** give 1993 polyvariant mix. -/
inductive BindingTime where
  | static
  | dynamic
  deriving DecidableEq, Repr

def bta : ITerm → BindingTime
  | ITerm.swap => BindingTime.dynamic
  | ITerm.app f x =>
      match bta f, bta x with
      | BindingTime.static, BindingTime.static => BindingTime.static
      | _, _ => BindingTime.dynamic
  | _ => BindingTime.static

def containsSwap : ITerm → Bool
  | ITerm.swap => true
  | ITerm.app f x => containsSwap f || containsSwap x
  | _ => false

theorem bta_swap : bta ITerm.swap = BindingTime.dynamic := rfl

theorem bta_norm : bta ITerm.norm = BindingTime.static := rfl

theorem bta_konst : bta ITerm.konst = BindingTime.static := rfl

theorem bta_dup : bta ITerm.dup = BindingTime.static := rfl

theorem bta_comp : bta ITerm.comp = BindingTime.static := rfl

theorem bta_s : bta ITerm.sₛ = BindingTime.static := rfl

theorem bta_var (n : Nat) : bta (ITerm.var n) = BindingTime.static := rfl

theorem bta_app_static (f x : ITerm) :
    bta (ITerm.app f x) = BindingTime.static ↔
      bta f = BindingTime.static ∧ bta x = BindingTime.static := by
  cases hf : bta f <;> cases hx : bta x <;> simp [bta, hf, hx]

theorem bta_eq_dynamic_iff_containsSwap (t : ITerm) :
    bta t = BindingTime.dynamic ↔ containsSwap t = true := by
  induction t with
  | var n => simp [bta, containsSwap]
  | norm => simp [bta, containsSwap]
  | konst => simp [bta, containsSwap]
  | dup => simp [bta, containsSwap]
  | swap => simp [bta, containsSwap]
  | comp => simp [bta, containsSwap]
  | sₛ => simp [bta, containsSwap]
  | app f x ihf ihx =>
      cases hf : bta f <;> cases hx : bta x
      { have hf' : containsSwap f = false := by
          have : ¬ bta f = BindingTime.dynamic := by simp [hf]
          simpa [ihf] using this
        have hx' : containsSwap x = false := by
          have : ¬ bta x = BindingTime.dynamic := by simp [hx]
          simpa [ihx] using this
        simp [bta, containsSwap, hf, hx, hf', hx'] }
      { have hx' : containsSwap x = true := (ihx.mp hx)
        simp [bta, containsSwap, hf, hx, hx'] }
      { have hf' : containsSwap f = true := (ihf.mp hf)
        simp [bta, containsSwap, hf, hx, hf'] }
      { have hf' : containsSwap f = true := (ihf.mp hf)
        simp [bta, containsSwap, hf, hx, hf'] }

/-- Online specializer covering every `IStep` constructor. -/
def jgs_spec : ITerm → ITerm → ITerm
  | ITerm.app ITerm.norm body, s => jgs_spec body s
  | ITerm.app (ITerm.app ITerm.konst x) _y, s => jgs_spec x s
  | ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x, s =>
      jgs_spec (ITerm.app f (ITerm.app g x)) s
  | ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z, s =>
      ITerm.app (ITerm.var 0) (pair (ITerm.app (ITerm.app x z) (ITerm.app y z)) s)
  | ITerm.norm, _ => ITerm.norm
  | ITerm.konst, _ => ITerm.konst
  | ITerm.sₛ, _ => ITerm.sₛ
  | ITerm.dup, _ => ITerm.dup
  | ITerm.comp, _ => ITerm.comp
  | ITerm.var n, _ => ITerm.var n
  | p, s => ITerm.app ITerm.dup (pair p s)
termination_by p => term_size p
decreasing_by
  all_goals (simp [term_size]; omega)

theorem jgs_spec_norm (s : ITerm) : jgs_spec ITerm.norm s = ITerm.norm := by
  simp [jgs_spec]

theorem jgs_spec_konst (s : ITerm) : jgs_spec ITerm.konst s = ITerm.konst := by
  simp [jgs_spec]

theorem jgs_spec_comp_atom (s : ITerm) : jgs_spec ITerm.comp s = ITerm.comp := by
  simp [jgs_spec]

theorem jgs_spec_s_atom (s : ITerm) : jgs_spec ITerm.sₛ s = ITerm.sₛ := by
  simp [jgs_spec]

theorem jgs_spec_static_atom_independent (s₁ s₂ : ITerm) :
    jgs_spec ITerm.norm s₁ = jgs_spec ITerm.norm s₂ ∧
    jgs_spec ITerm.konst s₁ = jgs_spec ITerm.konst s₂ ∧
    jgs_spec ITerm.comp s₁ = jgs_spec ITerm.comp s₂ ∧
    jgs_spec ITerm.sₛ s₁ = jgs_spec ITerm.sₛ s₂ ∧
    jgs_spec ITerm.dup s₁ = jgs_spec ITerm.dup s₂ := by
  simp [jgs_spec]

/--
Monovariant *offline* specializer: fold a redex only when `bta` classifies the
whole redex as static. Static S unfolds once into a residual with no `s` tag
(no recursion — size may grow). Dynamic terms are tagged residuals.
This is still monovariant (one division). It is **not** 1993 polyvariant mix.
-/
def offline_spec : ITerm → ITerm → ITerm
  | ITerm.app ITerm.norm body, s =>
      if bta (ITerm.app ITerm.norm body) = BindingTime.static then
        offline_spec body s
      else
        ITerm.app ITerm.dup (pair (ITerm.app ITerm.norm body) s)
  | ITerm.app (ITerm.app ITerm.konst x) y, s =>
      if bta (ITerm.app (ITerm.app ITerm.konst x) y) = BindingTime.static then
        offline_spec x s
      else
        ITerm.app ITerm.dup (pair (ITerm.app (ITerm.app ITerm.konst x) y) s)
  | ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x, s =>
      if bta (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x) = BindingTime.static then
        offline_spec (ITerm.app f (ITerm.app g x)) s
      else
        ITerm.app ITerm.dup
          (pair (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x) s)
  | ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z, s =>
      if bta (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z) = BindingTime.static then
        ITerm.app (ITerm.app x z) (ITerm.app y z)
      else
        ITerm.app ITerm.dup
          (pair (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z) s)
  | ITerm.norm, _ => ITerm.norm
  | ITerm.konst, _ => ITerm.konst
  | ITerm.sₛ, _ => ITerm.sₛ
  | ITerm.dup, _ => ITerm.dup
  | ITerm.comp, _ => ITerm.comp
  | ITerm.var n, _ => ITerm.var n
  | p, s =>
      if bta p = BindingTime.static then p
      else ITerm.app ITerm.dup (pair p s)
termination_by p => term_size p
decreasing_by
  all_goals (simp [term_size]; omega)

theorem offline_spec_static_atom_independent (s₁ s₂ : ITerm) :
    offline_spec ITerm.norm s₁ = offline_spec ITerm.norm s₂ ∧
    offline_spec ITerm.konst s₁ = offline_spec ITerm.konst s₂ ∧
    offline_spec ITerm.comp s₁ = offline_spec ITerm.comp s₂ ∧
    offline_spec ITerm.sₛ s₁ = offline_spec ITerm.sₛ s₂ ∧
    offline_spec ITerm.dup s₁ = offline_spec ITerm.dup s₂ := by
  simp [offline_spec]

theorem offline_spec_I_static (body s₁ s₂ : ITerm)
    (ht : bta (ITerm.app ITerm.norm body) = BindingTime.static) :
    offline_spec (ITerm.app ITerm.norm body) s₁ =
      offline_spec body s₁ := by
  simp [offline_spec, ht]

theorem offline_spec_K_static (x y s₁ : ITerm)
    (ht : bta (ITerm.app (ITerm.app ITerm.konst x) y) = BindingTime.static) :
    offline_spec (ITerm.app (ITerm.app ITerm.konst x) y) s₁ =
      offline_spec x s₁ := by
  simp [offline_spec, ht]

theorem offline_spec_B_static (f g x s₁ : ITerm)
    (ht : bta (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x) =
      BindingTime.static) :
    offline_spec (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x) s₁ =
      offline_spec (ITerm.app f (ITerm.app g x)) s₁ := by
  simp [offline_spec, ht]

theorem offline_spec_S_static (x y z s₁ s₂ : ITerm)
    (ht : bta (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z) =
      BindingTime.static) :
    offline_spec (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z) s₁ =
      offline_spec (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z) s₂ := by
  simp [offline_spec, ht]

def jgs_run : ITerm → ITerm → ITerm
  | ITerm.swap, data =>
      match data with
      | ITerm.app (ITerm.app ITerm.konst p) s => jgs_spec p s
      | _ => ITerm.app ITerm.swap data
  | ITerm.app ITerm.dup (ITerm.app (ITerm.app ITerm.konst p) s), d =>
      jgs_run p (pair s d)
  | ITerm.app ITerm.norm body, d =>
      jgs_run body d
  | ITerm.app (ITerm.app ITerm.konst x) _y, d =>
      jgs_run x d
  | ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x, d =>
      jgs_run (ITerm.app f (ITerm.app g x)) d
  | ITerm.app (ITerm.var 0) (ITerm.app (ITerm.app ITerm.konst c) s), d =>
      ITerm.app c (pair s d)
  | ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z, d =>
      ITerm.app (ITerm.app (ITerm.app x z) (ITerm.app y z)) d
  | ITerm.norm, _ => ITerm.norm
  | ITerm.konst, _ => ITerm.konst
  | ITerm.sₛ, _ => ITerm.sₛ
  | ITerm.dup, _ => ITerm.dup
  | ITerm.comp, _ => ITerm.comp
  | ITerm.var n, _ => ITerm.var n
  | p, d => ITerm.app p d
termination_by p => term_size p
decreasing_by
  all_goals (simp [term_size]; omega)

def jgs_eval (prog data : ITerm) : Option ITerm :=
  some (jgs_run prog data)

theorem jgs_mix (p s d : ITerm) :
    jgs_eval (jgs_spec p s) d = jgs_eval p (pair s d) := by
  cases p with
  | var _ => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | norm => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | konst => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | dup => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | swap => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | comp => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | sₛ => simp [jgs_spec, jgs_eval, jgs_run, pair]
  | app f x =>
      cases f with
      | norm =>
          have h := jgs_mix x s d
          simpa [jgs_spec, jgs_eval, jgs_run] using h
      | app f1 x1 =>
          cases f1 with
          | konst =>
              have h := jgs_mix x1 s d
              simpa [jgs_spec, jgs_eval, jgs_run] using h
          | app f2 x2 =>
              cases f2 with
              | comp =>
                  have h := jgs_mix (ITerm.app x2 (ITerm.app x1 x)) s d
                  simpa [jgs_spec, jgs_eval, jgs_run] using h
              | sₛ =>
                  simp [jgs_spec, jgs_eval, jgs_run, pair]
              | var _ => simp [jgs_spec, jgs_eval, jgs_run, pair]
              | norm => simp [jgs_spec, jgs_eval, jgs_run, pair]
              | konst => simp [jgs_spec, jgs_eval, jgs_run, pair]
              | dup => simp [jgs_spec, jgs_eval, jgs_run, pair]
              | swap => simp [jgs_spec, jgs_eval, jgs_run, pair]
              | app _ _ => simp [jgs_spec, jgs_eval, jgs_run, pair]
          | var _ => simp [jgs_spec, jgs_eval, jgs_run, pair]
          | norm => simp [jgs_spec, jgs_eval, jgs_run, pair]
          | dup => simp [jgs_spec, jgs_eval, jgs_run, pair]
          | swap => simp [jgs_spec, jgs_eval, jgs_run, pair]
          | comp => simp [jgs_spec, jgs_eval, jgs_run, pair]
          | sₛ => simp [jgs_spec, jgs_eval, jgs_run, pair]
      | var _ => simp [jgs_spec, jgs_eval, jgs_run, pair]
      | konst => simp [jgs_spec, jgs_eval, jgs_run, pair]
      | dup => simp [jgs_spec, jgs_eval, jgs_run, pair]
      | swap => simp [jgs_spec, jgs_eval, jgs_run, pair]
      | comp => simp [jgs_spec, jgs_eval, jgs_run, pair]
      | sₛ => simp [jgs_spec, jgs_eval, jgs_run, pair]
termination_by term_size p
decreasing_by
  all_goals (simp [term_size]; omega)

theorem jgs_selfApp (p s : ITerm) :
    jgs_eval ITerm.swap (pair p s) = some (jgs_spec p s) := by
  simp [jgs_eval, jgs_run, pair]

/-- Full-signature online PE: every `IStep` rule has a specialization clause. -/
def JGS_PE : PESetup where
  eval := jgs_eval
  spec := jgs_spec
  specTerm := ITerm.swap
  mix := jgs_mix
  selfApp := jgs_selfApp

theorem JGS_PE_nontrivial : Nontrivial JGS_PE :=
  ⟨opt_witness_p, ITerm.konst, by
    simp only [JGS_PE, jgs_spec, opt_witness_p, pe_cost, term_size]
    omega⟩

/-- Extra `Nontrivial` witness: a static `compβ` redex folds to `norm`. -/
def jgs_comp_witness : ITerm :=
  ITerm.app (ITerm.app (ITerm.app ITerm.comp ITerm.norm) ITerm.norm) ITerm.norm

theorem jgs_spec_comp_witness (s : ITerm) :
    jgs_spec jgs_comp_witness s = ITerm.norm := by
  simp [jgs_spec, jgs_comp_witness]

theorem JGS_PE_nontrivial_comp : Nontrivial JGS_PE :=
  ⟨jgs_comp_witness, ITerm.konst, by
    simp only [JGS_PE, jgs_spec, jgs_comp_witness, pe_cost, term_size]
    omega⟩

/-- Residual `konst` does not depend on the static argument. Used to rule out
`swap` as a self-interpreter (it specializes via `jgs_spec`). -/
theorem jgs_spec_eq_konst_independent :
    ∀ (n : Nat) (a s1 s2 : ITerm), term_size a ≤ n →
      jgs_spec a s1 = ITerm.konst → jgs_spec a s2 = ITerm.konst := by
  intro n
  induction n with
  | zero =>
      intro a s1 s2 hsz h
      have := term_size_pos a
      omega
  | succ n ih =>
      intro a s1 s2 hsz h
      cases a with
      | var _ | norm | konst | dup | swap | comp | sₛ =>
          simp [jgs_spec] at h ⊢
      | app f x =>
          cases f with
          | norm =>
              have hszx : term_size x ≤ n := by simp [term_size] at hsz ⊢; omega
              have hx : jgs_spec x s1 = ITerm.konst := by simpa [jgs_spec] using h
              have := ih x s1 s2 hszx hx
              simpa [jgs_spec] using this
          | app f1 x1 =>
              cases f1 with
              | konst =>
                  have hszx : term_size x1 ≤ n := by simp [term_size] at hsz ⊢; omega
                  have hx : jgs_spec x1 s1 = ITerm.konst := by simpa [jgs_spec] using h
                  have := ih x1 s1 s2 hszx hx
                  simpa [jgs_spec] using this
              | app f2 x2 =>
                  cases f2 with
                  | comp =>
                      have hsz' : term_size (ITerm.app x2 (ITerm.app x1 x)) ≤ n := by
                        simp [term_size] at hsz ⊢; omega
                      have hx : jgs_spec (ITerm.app x2 (ITerm.app x1 x)) s1 = ITerm.konst := by
                        simpa [jgs_spec] using h
                      have := ih (ITerm.app x2 (ITerm.app x1 x)) s1 s2 hsz' hx
                      simpa [jgs_spec] using this
                  | sₛ =>
                      simp [jgs_spec] at h
                  | var _ | norm | konst | dup | swap | app _ _ =>
                      simp [jgs_spec] at h
              | var _ | norm | dup | swap | comp | sₛ =>
                  simp [jgs_spec] at h
          | var _ | konst | dup | swap | comp | sₛ =>
              simp [jgs_spec] at h

/-- If the first argument of `pair` is shared, `jgs_run` cannot return both
`konst` and `dup` (atoms ignore data; `swap` specializes independently of
the remaining static payload). -/
theorem jgs_run_not_konst_dup_same_static :
    ∀ (n : Nat) (p s e1 e2 : ITerm), term_size p ≤ n →
      ¬ (jgs_run p (pair s e1) = ITerm.konst ∧
         jgs_run p (pair s e2) = ITerm.dup) := by
  intro n
  induction n with
  | zero =>
      intro p s e1 e2 hsz h
      have := term_size_pos p
      omega
  | succ n ih =>
      intro p s e1 e2 hsz ⟨h1, h2⟩
      cases p with
      | var _ | norm | konst | dup | comp | sₛ =>
          simp [jgs_run, pair] at h1 h2
      | swap =>
          have h1' : jgs_spec s e1 = ITerm.konst := by simpa [jgs_run, pair] using h1
          have h2' : jgs_spec s e2 = ITerm.dup := by simpa [jgs_run, pair] using h2
          have hconst :=
            jgs_spec_eq_konst_independent (term_size s) s e1 e2 (Nat.le_refl _) h1'
          simp [hconst] at h2'
      | app f x =>
          cases f with
          | norm =>
              have hszx : term_size x ≤ n := by simp [term_size] at hsz ⊢; omega
              exact ih x s e1 e2 hszx ⟨by simpa [jgs_run] using h1,
                by simpa [jgs_run] using h2⟩
          | app f1 x1 =>
              cases f1 with
              | konst =>
                  have hszx : term_size x1 ≤ n := by simp [term_size] at hsz ⊢; omega
                  exact ih x1 s e1 e2 hszx ⟨by simpa [jgs_run] using h1,
                    by simpa [jgs_run] using h2⟩
              | app f2 x2 =>
                  cases f2 with
                  | comp =>
                      have hsz' : term_size (ITerm.app x2 (ITerm.app x1 x)) ≤ n := by
                        simp [term_size] at hsz ⊢; omega
                      exact ih (ITerm.app x2 (ITerm.app x1 x)) s e1 e2 hsz'
                        ⟨by simpa [jgs_run] using h1, by simpa [jgs_run] using h2⟩
                  | sₛ =>
                      simp [jgs_run, pair] at h1
                  | var _ | norm | konst | dup | swap | app _ _ =>
                      simp [jgs_run, pair] at h1
              | var n =>
                  cases n with
                  | zero =>
                      cases x with
                      | app x1 x2 =>
                          cases x1 with
                          | app x11 _ =>
                              cases x11 with
                              | konst => simp [jgs_run, pair] at h1
                              | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                                  simp [jgs_run, pair] at h1
                          | var _ | norm | konst | dup | swap | comp | sₛ =>
                              simp [jgs_run, pair] at h1
                      | var _ | norm | konst | dup | swap | comp | sₛ =>
                          simp [jgs_run, pair] at h1
                  | succ _ =>
                      simp [jgs_run, pair] at h1
              | norm | dup | swap | comp | sₛ =>
                  simp [jgs_run, pair] at h1
          | dup =>
              cases x with
              | app x1 x2 =>
                  cases x1 with
                  | app x11 p' =>
                      cases x11 with
                      | konst =>
                          have hszp : term_size p' ≤ n := by
                            simp [term_size] at hsz ⊢; omega
                          exact ih p' x2 (pair s e1) (pair s e2) hszp
                            ⟨by simpa [jgs_run, pair] using h1,
                             by simpa [jgs_run, pair] using h2⟩
                      | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                          simp [jgs_run, pair] at h1
                  | var _ | norm | konst | dup | swap | comp | sₛ =>
                      simp [jgs_run, pair] at h1
              | var _ | norm | konst | dup | swap | comp | sₛ =>
                  simp [jgs_run, pair] at h1
          | var n =>
              cases n with
              | zero =>
                  cases x with
                  | app x1 x2 =>
                      cases x1 with
                      | app x11 _ =>
                          cases x11 with
                          | konst => simp [jgs_run, pair] at h1
                          | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                              simp [jgs_run, pair] at h1
                      | var _ | norm | konst | dup | swap | comp | sₛ =>
                          simp [jgs_run, pair] at h1
                  | var _ | norm | konst | dup | swap | comp | sₛ =>
                      simp [jgs_run, pair] at h1
              | succ _ =>
                  simp [jgs_run, pair] at h1
          | konst | swap | comp | sₛ =>
              simp [jgs_run, pair] at h1

/-- Online one-step `JGS_PE` has no self-interpreter: the three atom tests
(`konst`, `dup`, `swap` as sources) cannot hold together. Not Jones-optimal.
This is **not** a 1993 polyvariant mix / cogen claim. -/
theorem jgs_run_not_three :
    ∀ (n : Nat) (p : ITerm), term_size p ≤ n →
      ¬ (jgs_run p (pair ITerm.konst ITerm.norm) = ITerm.konst ∧
         jgs_run p (pair ITerm.dup ITerm.norm) = ITerm.dup ∧
         jgs_run p (pair ITerm.swap ITerm.norm) =
           ITerm.app ITerm.swap ITerm.norm) := by
  intro n
  induction n with
  | zero =>
      intro p hsz h
      have := term_size_pos p
      omega
  | succ n ih =>
      intro p hsz ⟨h1, h2, h3⟩
      cases p with
      | var _ =>
          simp [jgs_run, pair] at h1
      | norm =>
          simp [jgs_run, pair] at h1
      | konst =>
          simp [jgs_run, pair] at h2
      | dup =>
          simp [jgs_run, pair] at h1
      | swap =>
          have h3' : jgs_spec ITerm.swap ITerm.norm =
              ITerm.app ITerm.swap ITerm.norm := by
            simpa [jgs_run, pair] using h3
          simp [jgs_spec, pair] at h3'
      | comp =>
          simp [jgs_run, pair] at h1
      | sₛ =>
          simp [jgs_run, pair] at h1
      | app f x =>
          cases f with
          | norm =>
              have hszx : term_size x ≤ n := by simp [term_size] at hsz ⊢; omega
              refine ih x hszx ⟨?_, ?_, ?_⟩
              { simpa [jgs_run] using h1 }
              { simpa [jgs_run] using h2 }
              { simpa [jgs_run] using h3 }
          | app f1 x1 =>
              cases f1 with
              | konst =>
                  have hszx : term_size x1 ≤ n := by simp [term_size] at hsz ⊢; omega
                  refine ih x1 hszx ⟨?_, ?_, ?_⟩
                  { simpa [jgs_run] using h1 }
                  { simpa [jgs_run] using h2 }
                  { simpa [jgs_run] using h3 }
              | app f2 x2 =>
                  cases f2 with
                  | comp =>
                      have hsz' : term_size (ITerm.app x2 (ITerm.app x1 x)) ≤ n := by
                        simp [term_size] at hsz ⊢; omega
                      refine ih (ITerm.app x2 (ITerm.app x1 x)) hsz' ⟨?_, ?_, ?_⟩
                      { simpa [jgs_run] using h1 }
                      { simpa [jgs_run] using h2 }
                      { simpa [jgs_run] using h3 }
                  | sₛ =>
                      simp [jgs_run, pair] at h1
                  | var _ | norm | konst | dup | swap | app _ _ =>
                      simp [jgs_run, pair] at h1
              | var n =>
                  cases n with
                  | zero =>
                      cases x with
                      | app x1 x2 =>
                          cases x1 with
                          | app x11 c =>
                              cases x11 with
                              | konst =>
                                  simp [jgs_run, pair] at h1
                              | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                                  simp [jgs_run, pair] at h1
                          | var _ | norm | konst | dup | swap | comp | sₛ =>
                              simp [jgs_run, pair] at h1
                      | var _ | norm | konst | dup | swap | comp | sₛ =>
                          simp [jgs_run, pair] at h1
                  | succ _ =>
                      simp [jgs_run, pair] at h1
              | norm | dup | swap | comp | sₛ =>
                  simp [jgs_run, pair] at h1
          | dup =>
              cases x with
              | app x1 x2 =>
                  cases x1 with
                  | app x11 p' =>
                      cases x11 with
                      | konst =>
                          have hszp : term_size p' ≤ n := by
                            simp [term_size] at hsz ⊢
                            omega
                          exact jgs_run_not_konst_dup_same_static n p' x2
                            (pair ITerm.konst ITerm.norm)
                            (pair ITerm.dup ITerm.norm) hszp
                            ⟨by simpa [jgs_run, pair] using h1,
                             by simpa [jgs_run, pair] using h2⟩
                      | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                          simp [jgs_run, pair] at h1
                  | var _ | norm | konst | dup | swap | comp | sₛ =>
                      simp [jgs_run, pair] at h1
              | var _ | norm | konst | dup | swap | comp | sₛ =>
                  simp [jgs_run, pair] at h1
          | var n =>
              cases n with
              | zero =>
                  cases x with
                  | app x1 x2 =>
                      cases x1 with
                      | app x11 c =>
                          cases x11 with
                          | konst =>
                              simp [jgs_run, pair] at h1
                          | var _ | norm | dup | swap | comp | sₛ | app _ _ =>
                              simp [jgs_run, pair] at h1
                      | var _ | norm | konst | dup | swap | comp | sₛ =>
                          simp [jgs_run, pair] at h1
                  | var _ | norm | konst | dup | swap | comp | sₛ =>
                      simp [jgs_run, pair] at h1
              | succ _ =>
                  simp [jgs_run, pair] at h1
          | konst | swap | comp | sₛ =>
              simp [jgs_run, pair] at h1

theorem JGS_PE_not_self_interpreter (int : ITerm) :
    ¬ SelfInterpreter JGS_PE int := by
  intro hSI
  have h1 := hSI ITerm.konst ITerm.norm
  have h2 := hSI ITerm.dup ITerm.norm
  have h3 := hSI ITerm.swap ITerm.norm
  apply jgs_run_not_three (term_size int) int (Nat.le_refl _)
  refine ⟨?_, ?_, ?_⟩
  { simpa [JGS_PE, jgs_eval, jgs_run, pair] using h1 }
  { simpa [JGS_PE, jgs_eval, jgs_run, pair] using h2 }
  { simpa [JGS_PE, jgs_eval, jgs_run, pair] using h3 }

/-- One-step online `JGS_PE` is not Jones-optimal. 1993 polyvariant division / cogen
remains open; `specTerm` is still `swap`. -/
theorem JGS_PE_not_jonesOptimal : ¬ JonesOptimal JGS_PE := by
  rintro ⟨int, hSI, _⟩
  exact JGS_PE_not_self_interpreter int hSI

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
