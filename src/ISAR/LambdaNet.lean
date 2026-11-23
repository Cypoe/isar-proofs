import ISAR.InteractionNet
import ISAR.LambdaFragment

/-!
# λ over the interaction combinators — the degenerate fragment

The carrier is Lafont's interaction combinators *in the abstract*:
three agent shapes — `γ` (constructor, arity 2), `δ` (duplicator,
arity 2), `ε` (eraser, arity 0) — under the universal `γδε` rule
table.  No λ-specific labels: `λ` and `@` are **both γ**, told apart
only by *which port faces the consumer* (Taelin's reading of Asperti:
interaction combinators = the λ-calculus + superposition):

- `λx.M` → γ: port 0 principal (faces the consumer), port 1 body,
  port 2 the bound variable's use-sites.
- `f x` → γ: port 0 principal *is the fun-seeker* (wired to `f`'s
  root), port 1 result (the application's root), port 2 argument.

A β-redex is therefore a γ⋈γ principal pair, and β **is**
annihilation — the same index-wise splice that deletes γγ pairs:
`peer(λ,1) ↔ peer(@,1)` (body↔result), `peer(λ,2) ↔ peer(@,2)`
(var↔arg).  Shared variables fan out through δ-trees on the binder's
var-port; unused binders get ε; free variables are interface binders
with their own δ-trees.

## Readback — the degenerate classifier

`readback` inverts the encoding *on the fragment where it inverts*.
At a term slot it inspects the facing end's port index: `γ.0` is a
λ-root, `γ.1` an @-root, `λ.2`/`δ.aux` a variable leaf.  A `δ`
principal or `ε` facing a term slot is a *superposition* — a
well-formed net with no λ-denotation — and readback refuses it.
`readback.isSome` is literally the classification "degenerate": the
subset of net-space where Lamping's abstract algorithm is defined.

## Observation through the Invariant Layer

`lambdaObs` composes `nfBounded → readback → compileISK → ⟦·⟧`, so
the λ regime's observation of a net is a class in the **same**
`InvariantLayer` (`Quotient operEqSetoid`) that observes ISK terms —
cross-carrier `sim` is literal, not a bespoke per-regime mapping.
`LObs` is four-valued: `.nf` a layer class, `.superposed` a
non-degenerate nf (each its own class — no semantic quotient claimed),
`.divergent`, `.refused`.  `DegNFNet` — nets already normal *and*
degenerate — carries the honest `QuotientMap` into the ISK substrate:
`preserves` holds by construction there; extending it past the nf
subtype *is* the simulation theorem and is deliberately not asserted.

Mechanical evidence at the bottom — including `(λx. x x) y`, which
reduces leaving δ on the *shared* argument edge, and a bare δ at the
interface, whose nf is `.superposed` (it is not a λ-term and readback
says so).
-/

namespace ISAR

/-- The constructor combinator γ — both λ and @. -/
def ctorLbl : Nat := 1
/-- The duplicator δ. -/
def dupLbl : Nat := 2
/-- The eraser ε. -/
def eraLbl : Nat := 0

/-- Free-variable binder ids sit above this base — they never collide
    with real binders (which are de-Bruijn depths). -/
def freeBase : Nat := 100000

namespace LambdaNet

/-- A compiled subtree's root: a concrete end, or a reference to a
    binder's var-slot resolved by the enclosing `abs`. -/
inductive Root where
  | end_ (e : PortEnd)
  | varRef (binder : Nat)

/-- Compilation state: agents, wires, and the open var-ends still
    awaiting their binder's slot. -/
structure Ctx where
  agents : Array (Option Agent)
  wires : List (PortEnd × PortEnd)
  openEnds : List (Nat × PortEnd)    -- (binder id, use-side end)

/-- Connect a port to a subtree root — either wire it now, or register
    it as an open end for a later binder. -/
def Ctx.attach (c : Ctx) (p : PortEnd) (r : Root) : Ctx :=
  match r with
  | .end_ e => { c with wires := (p, e) :: c.wires }
  | .varRef b => { c with openEnds := (b, p) :: c.openEnds }

/-- Fan a binder's slot out to its use-ends: ε when unused, a bare
    wire when single, a right-linear δ chain when shared. -/
def dupTree (c : Ctx) (uses : List PortEnd) (slot : PortEnd) : Ctx :=
  match uses with
  | [] =>
    let e := c.agents.size
    let c := { c with agents := c.agents.push (some ⟨eraLbl, 0⟩) }
    { c with wires := (slot, .port e 0) :: c.wires }
  | u :: rest =>
    if rest.isEmpty then { c with wires := (slot, u) :: c.wires }
    else
      let g := c.agents.size
      let c := { c with agents := c.agents.push (some ⟨dupLbl, 2⟩) }
      let c := { c with wires := (slot, .port g 0) :: (u, .port g 1) :: c.wires }
      dupTree c rest (.port g 2)

/-- Compile a term at binder depth `depth`. -/
def go (t : LTerm) (depth : Nat) (c : Ctx) : Option (Root × Ctx) :=
  match t with
  | .var i =>
    if i < depth then some (.varRef (depth - 1 - i), c)
    else some (.varRef (freeBase + (i - depth)), c)
  | .app f x => do
    let (rf, c) ← go f depth c
    let (rx, c) ← go x depth c
    let a := c.agents.size
    let c := { c with agents := c.agents.push (some ⟨ctorLbl, 2⟩) }
    let c := (c.attach (.port a 0) rf).attach (.port a 2) rx
    some (.end_ (.port a 1), c)
  | .abs b => do
    let (rb, c) ← go b (depth + 1) c
    let a := c.agents.size
    let c := { c with agents := c.agents.push (some ⟨ctorLbl, 2⟩) }
    let c := c.attach (.port a 1) rb
    let (mine, rest) := c.openEnds.partition (·.1 = depth)
    let c := { c with openEnds := rest }
    let c := dupTree c (mine.map (·.2)) (.port a 2)
    some (.end_ (.port a 0), c)

/-- Compile a term to a net.  Each distinct free variable is an
    interface binder: one free port fanned out to all its uses through
    its own δ-tree (interface sharing is net data, like any other
    sharing).  The root is the last free index; a root variable reads
    through its binder's port like any other use. -/
def compile (t : LTerm) : Option Net := do
  let (r, c) ← go t 0 ⟨#[], [], []⟩
  let rawBinders := match r with
    | .varRef b => b :: c.openEnds.map (fun (p : Nat × PortEnd) => p.1)
    | .end_ _ => c.openEnds.map (fun (p : Nat × PortEnd) => p.1)
  let binders := rawBinders.foldl
    (fun (acc : List Nat) b => if acc.contains b then acc else acc ++ [b]) []
  let rootIdx := binders.length
  let c := match r with
    | .varRef b => { c with openEnds := (b, .free rootIdx) :: c.openEnds }
    | .end_ _ => c
  let c := (binders.foldl (fun (cj : Ctx × Nat) b =>
      (dupTree cj.1 ((cj.1.openEnds.filter
        (fun (p : Nat × PortEnd) => p.1 = b)).map
        (fun (p : Nat × PortEnd) => p.2)) (.free cj.2), cj.2 + 1)) (c, 0)).1
  match r with
  | .end_ e =>
    some ⟨c.agents, (e, .free rootIdx) :: c.wires, rootIdx + 1⟩
  | .varRef _ => some ⟨c.agents, c.wires, rootIdx + 1⟩

/-- Normal form net or `none` — the evaluable half of `nfBounded`. -/
def nfNet (rt : RuleTable) (fuel : Nat) (n : Net) : Option Net :=
  match nfBounded rt fuel n with | .nf n' => some n' | _ => none

/-- Compile, defaulting only for concrete evaluation sites. -/
def compile! (t : LTerm) : Net := (compile t).getD ⟨#[], [], 0⟩

/-! ## Readback — the degenerate classifier -/

/-- Leaf ends of the var-tree below a binder-side end `e`: descend
    δ principals; `ε` swallows; anything else means `e` itself is the
    binder-side leaf of a single-use wire. -/
def varLeaves (n : Net) : Nat → PortEnd → List PortEnd
  | 0, _ => []
  | fuel + 1, e =>
    match n.peerOf e with
    | some (.port g 0) =>
      match n.agents[g]? with
      | some (some ag) =>
        if ag.label = dupLbl then
          varLeaves n fuel (.port g 1) ++ varLeaves n fuel (.port g 2)
        else if ag.label = eraLbl then []
        else [e]
      | _ => [e]
    | _ => [e]

/-- Read the term at slot `e`.  `stack` is the leaf-sets of the
    enclosing binders, innermost first; `freeSets` the leaf-sets of the
    interface ports.  `none` on superposed/misshapen shapes — the
    classification, not an error path. -/
def readAt (n : Net) (freeSets : List (List PortEnd)) :
    Nat → List (List PortEnd) → PortEnd → Option LTerm
  | 0, _, _ => none
  | fuel + 1, stack, e =>
    match n.peerOf e with
    | none => none
    | some (.free i) => some (.var (stack.length + i))
    | some r@(.port a k) =>
      match n.agents[a]? with
      | some (some ag) =>
        if k = 0 then
          if ag.label = ctorLbl then
            match readAt n freeSets fuel
                ((varLeaves n (n.agents.size + 1) (.port a 2)) :: stack)
                (.port a 1) with
            | some body => some (.abs body)
            | none => none
          else none                -- δ.0/ε.0 facing a term: superposed
        else
          match stack.findIdx? (fun s => s.contains r) with
          | some i => some (.var i)
          | none =>
            match freeSets.findIdx? (fun s => s.contains r) with
            | some j => some (.var (stack.length + j))
            | none =>
              if k = 1 && ag.label = ctorLbl then
                match readAt n freeSets fuel stack (.port a 0),
                      readAt n freeSets fuel stack (.port a 2) with
                | some f, some x => some (.app f x)
                | _, _ => none
              else none
      | _ => none

/-- Read a net back to an `LTerm` — defined exactly on the degenerate
    fragment.  The root is the last interface port (compile's
    convention). -/
def readback (n : Net) : Option LTerm :=
  match n.freeArity with
  | 0 => none
  | root + 1 =>
    let freeSets := (List.range root).map
      (fun i => varLeaves n (n.agents.size + 1) (.free i))
    readAt n freeSets (n.wires.length + n.agents.size + 1) [] (.free root)

/-! ## `LTerm → ISKSubtype` — pure S/K/I, for the layer route

`LambdaFragment.compile` optimizes with `comp` (B), which leaves the
`ISKTerm` fragment; the observation route needs provably-ISK outputs,
so this pass uses the unoptimized abstraction and injects free
variables as a closed family `varEnc` (distinct normal forms — an
honest injection).  `isISKD d` tracks "every leaf is an ISK atom or a
bound var below `d`"; `d = 0` at the top is exactly `ISKTerm`. -/

/-- Free variable `i` as a closed ISK term: `I, K I, K (K I), …` —
    pairwise distinct normal forms, so injection is faithful. -/
def varEnc : Nat → ITerm
  | 0 => .norm
  | i + 1 => .app .konst (varEnc i)

/-- Unoptimized S/K/I bracket abstraction (no `comp`): `var 0` → `I`,
    constant parts → `K`, both-live → `S`, one-side-live → `S K`. -/
def absISK : ITerm → ITerm
  | .var 0 => .norm
  | .var (i + 1) => .app .konst (.var i)
  | .app f x =>
    if occurs0 f = true then
      if occurs0 x = true then .app (.app .sₛ (absISK f)) (absISK x)
      else .app (.app .sₛ (absISK f)) (.app .konst (shift_down x))
    else
      if occurs0 x = true then
        .app (.app .sₛ (.app .konst (shift_down f))) (absISK x)
      else .app .konst (shift_down (.app f x))
  | a => .app .konst a

/-- "Leaves are ISK atoms or bound vars below `d`" — the depth-indexed
    predicate whose `d = 0` case is ISK-shaped. -/
def isISKD (d : Nat) : ITerm → Bool
  | .var i => decide (i < d)
  | .norm | .konst | .sₛ => true
  | .dup | .swap | .comp => false
  | .app f x => isISKD d f && isISKD d x

theorem isISKD_shift_down {t : ITerm} {d : Nat}
    (h : isISKD (d + 1) t = true) (h0 : occurs0 t = false) :
    isISKD d (shift_down t) = true := by
  induction t with
  | var i =>
    cases i with
    | zero => simp [occurs0] at h0
    | succ j =>
      have hj : j + 1 < d + 1 := of_decide_eq_true (by simpa [isISKD] using h)
      show isISKD d (.var j) = true
      exact decide_eq_true (by omega)
  | app f x ihf ihx =>
    simp only [isISKD, Bool.and_eq_true] at h
    simp only [occurs0, Bool.or_eq_false_iff] at h0
    simp only [shift_down, isISKD, Bool.and_eq_true]
    exact ⟨ihf h.1 h0.1, ihx h.2 h0.2⟩
  | norm => rfl
  | konst => rfl
  | sₛ => rfl
  | dup => simp [isISKD] at h
  | swap => simp [isISKD] at h
  | comp => simp [isISKD] at h

theorem isISKD_abs {t : ITerm} {d : Nat}
    (h : isISKD (d + 1) t = true) : isISKD d (absISK t) = true := by
  induction t with
  | var i =>
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j + 1 < d + 1 := of_decide_eq_true (by simpa [isISKD] using h)
      show isISKD d (.app .konst (.var j)) = true
      exact decide_eq_true (by omega)
  | app f x ihf ihx =>
    simp only [isISKD, Bool.and_eq_true] at h
    by_cases hf : occurs0 f = true
    · by_cases hx : occurs0 x = true
      · simp [absISK, hf, hx, isISKD, ihf h.1, ihx h.2]
      · simp only [Bool.not_eq_true] at hx
        simp [absISK, hf, hx, isISKD, ihf h.1,
          isISKD_shift_down h.2 hx]
    · simp only [Bool.not_eq_true] at hf
      by_cases hx : occurs0 x = true
      · simp [absISK, hf, hx, isISKD, ihx h.2,
          isISKD_shift_down h.1 hf]
      · simp only [Bool.not_eq_true] at hx
        have h0 : occurs0 (.app f x) = false := by simp [occurs0, hf, hx]
        have h' : isISKD (d + 1) (.app f x) = true := by
          simp only [isISKD, Bool.and_eq_true]; exact h
        simp [absISK, hf, hx, isISKD, isISKD_shift_down h' h0]
  | norm => rfl
  | konst => rfl
  | sₛ => rfl
  | dup => simp [isISKD] at h
  | swap => simp [isISKD] at h
  | comp => simp [isISKD] at h

theorem isISKD_varEnc (k d : Nat) : isISKD d (varEnc k) = true := by
  induction k with
  | zero => rfl
  | succ j ih => simp [varEnc, isISKD, ih]

/-- `LTerm → ITerm` with free vars injected as `varEnc` and bound vars
    left as indices for `absISK` to eliminate. -/
def compileITerm : LTerm → Nat → ITerm
  | .var i, d => if i < d then .var i else varEnc (i - d)
  | .app f x, d => .app (compileITerm f d) (compileITerm x d)
  | .abs b, d => absISK (compileITerm b (d + 1))

theorem isISKD_compile (t : LTerm) (d : Nat) :
    isISKD d (compileITerm t d) = true := by
  induction t generalizing d with
  | var i =>
    simp only [compileITerm]
    by_cases h : i < d
    · rw [if_pos h]; simp only [isISKD]; exact decide_eq_true h
    · rw [if_neg h]; exact isISKD_varEnc _ _
  | app f x ihf ihx => simp [compileITerm, isISKD, ihf, ihx]
  | abs b ih => simp [compileITerm, isISKD_abs (ih (d + 1))]

/-- The bridge: `isISKD 0` means no bound vars survive — the term is
    genuinely `ISKTerm`. -/
theorem isISK_isk {t : ITerm} (h : isISKD 0 t = true) : ISKTerm t := by
  induction t with
  | var i => simp [isISKD] at h
  | norm => exact ISKTerm.norm
  | konst => exact ISKTerm.konst
  | sₛ => exact ISKTerm.sₛ
  | app f x ihf ihx =>
    simp only [isISKD, Bool.and_eq_true] at h
    exact ISKTerm.app (ihf h.1) (ihx h.2)
  | dup => simp [isISKD] at h
  | swap => simp [isISKD] at h
  | comp => simp [isISKD] at h

/-- An `LTerm` as a provably-ISK term — the readback side's path into
    the substrate. -/
def compileISK (t : LTerm) : ISKSubtype :=
  ⟨compileITerm t 0, isISK_isk (isISKD_compile t 0)⟩

/-! ## Observation through the Invariant Layer -/

/-- The λ regime's observation: the normal form's class **in the
    Invariant Layer** (same `Quotient operEqSetoid` that observes ISK
    terms), the non-degenerate remainder as itself, or the two
    failure modes. -/
inductive LObs where
  | nf : InvariantLayer → LObs
  | superposed : Net → LObs
  | divergent
  | refused

/-- Observe a net by running it, then reading the normal form back and
    landing its term in the Invariant Layer.  A non-degenerate normal
    form is `.superposed` — its own class, honestly named. -/
def lambdaObs (rt : RuleTable) (fuel : Nat) (n : Net) : LObs :=
  match nfBounded rt fuel n with
  | .nf n' =>
    match readback n' with
    | some t => .nf (toInvariantLayer (compileISK t))
    | none => .superposed n'
  | .divergent => .divergent
  | .refused => .refused

/-- The λ-observational regime on nets: `sim` is "same layer class of
    the residual term" on the degenerate fragment, literal equality on
    the superposed remainder. -/
def lambdaRegime (rt : RuleTable) (fuel : Nat) : ObservationRegime Net where
  Obs := LObs
  observe := lambdaObs rt fuel
  ObsEq := (· = ·)
  is_equiv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def lambdaKernel (rt : RuleTable) (fuel : Nat) :
    Kernel Net (lambdaRegime rt fuel) :=
  substrateKernel (lambdaRegime rt fuel)

/-- Nets already normal *and* degenerate — the fragment where the
    ISK-bound quotient map is honest by construction. -/
def DegNFNet (rt : RuleTable) (fuel : Nat) : Type :=
  { n : Net // ∃ t : LTerm, readback n = some t ∧ nfBounded rt fuel n = .nf n }

def degNFRegime (rt : RuleTable) (fuel : Nat) :
    ObservationRegime (DegNFNet rt fuel) where
  Obs := LObs
  observe := fun n => lambdaObs rt fuel n.1
  ObsEq := (· = ·)
  is_equiv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def degEncode (rt : RuleTable) (fuel : Nat) (n : DegNFNet rt fuel) :
    ISKSubtype :=
  match readback n.1 with
  | some t => compileISK t
  | none => ⟨.norm, .norm⟩     -- unreachable on the DegNF subtype

/-- The cross-carrier quotient map: decode the ISK substrate's
    observation (a layer class) as the net regime's `.nf`.  `preserves`
    is definitional on the DegNF fragment — the general statement is
    the simulation theorem, deliberately not asserted. -/
def degMap (rt : RuleTable) (fuel : Nat) :
    QuotientMap (DegNFNet rt fuel) (degNFRegime rt fuel)
      ISKSubtype operEqRegime where
  encode := degEncode rt fuel
  decode := .nf
  preserves := fun n => by
    obtain ⟨t, hr, hnf⟩ := n.2
    have hdeg : degEncode rt fuel n = compileISK t := by
      simp only [degEncode, hr]
    show LObs.nf (operEqRegime.observe (degEncode rt fuel n)) =
      lambdaObs rt fuel n.1
    simp only [hdeg, operEqRegime, lambdaObs, hnf, hr]

end LambdaNet

/-! ## Evidence — evaluated, not asserted -/

open LambdaNet

/-- `(λx.x) y` — internal body-var wire, collapses to the bare wire. -/
def idApp : LTerm := .app (.abs (.var 0)) (.var 0)
/-- `(λx.λy.x) z` — K on one argument → `λy.z` with ε on y's slot. -/
def kApp : LTerm := .app (.abs (.abs (.var 1))) (.var 0)
/-- `(λx. x x) y` — the sharing demo: δ on the shared argument edge. -/
def dupApp : LTerm := .app (.abs (.app (.var 0) (.var 0))) (.var 0)
/-- `x` alone — the interface wire, no agents. -/
def loneVar : LTerm := .var 0
/-- `(λx.x)(λx.x)` — closed round-trip. -/
def idId : LTerm := .app (.abs (.var 0)) (.abs (.var 0))
/-- A bare δ with its *principal* at the root — the canonical
    superposition: well-formed, but no λ-term faces the consumer
    there (a δ's aux ports alone are just shared free vars). -/
def supNet : Net :=
  ⟨#[some ⟨dupLbl, 2⟩],
   [wire (.port 0 0) (.free 2), wire (.port 0 1) (.free 0),
    wire (.port 0 2) (.free 1)], 3⟩

example : (LambdaNet.compile idApp).isSome = true := rfl
example : (LambdaNet.compile kApp).isSome = true := rfl
example : (LambdaNet.compile dupApp).isSome = true := rfl
example : (LambdaNet.compile loneVar).isSome = true := rfl
example : (LambdaNet.compile idId).isSome = true := rfl

-- compiled nets pass the wiring check — including loneVar's bare wire
example : (compile! idApp).check = true := by decide
example : (compile! kApp).check = true := by decide
example : (compile! dupApp).check = true := by decide
example : (compile! loneVar).check = true := by decide
example : (compile! idId).check = true := by decide
example : supNet.check = true := by decide

-- readback on normal forms: (λx.x) y ↦ the free var; (λx.xx) y ↦ y y;
-- (λx.x)(λx.x) ↦ λx.x — β correct, sharing unfolded at readback.
example : (nfNet γδε 16 (compile! idApp)).bind readback
    = some (.var 0) := by decide
example : (nfNet γδε 16 (compile! dupApp)).bind readback
    = some (.app (.var 0) (.var 0)) := by decide
example : (nfNet γδε 16 (compile! idId)).bind readback
    = some (.abs (.var 0)) := by decide
example : (nfNet γδε 16 (compile! kApp)).bind readback
    = some (.abs (.var 1)) := by decide

-- The cross-carrier evidence: (λx.x) y and bare y observe to the SAME
-- Invariant Layer class — observational equivalence of running
-- programs, literal.
example : lambdaObs γδε 16 (compile! idApp)
    = .nf (toInvariantLayer (compileISK (.var 0))) := rfl
example : lambdaObs γδε 16 (compile! idApp)
    = lambdaObs γδε 8 (compile! (.var 0)) := rfl
example : lambdaObs γδε 16 (compile! dupApp)
    = .nf (toInvariantLayer (compileISK (.app (.var 0) (.var 0)))) := rfl
example : lambdaObs γδε 16 (compile! idId)
    = .nf (toInvariantLayer (compileISK (.abs (.var 0)))) := rfl

-- The non-degenerate class: a bare δ at the interface reads back to
-- nothing — superposition, honestly named, not refused.
example : (match lambdaObs γδε 8 supNet with
    | .superposed _ => true | _ => false) = true := rfl

-- divergence stays divergence through the λ lens
example : lambdaObs γδε 6 loopNet = .divergent := rfl
example : lambdaObs γδε 0 gammaDeltaNet = .divergent := rfl

end ISAR
