import ISAR.InteractionNet
import ISAR.LambdaFragment

/-!
# λ→Net compilation — where Lafont's sharing pays

The standard interaction-net encoding of the λ-calculus:

- `λx.M` → a `λ` agent (arity 2): port 0 principal (faces the
  application's fun-seeker), port 1 body, port 2 the bound variable's
  use-sites.
- `f x` → an `@` agent (arity 2): port 0 principal *is the fun-seeker*
  (wired to `f`'s root), port 1 result (the application's root), port 2
  argument.
- Repeated variable uses share through a γ-dup tree hanging off the
  binder's var-port; unused binders get an ε.
- Free variables are interface ports.

Because `@`'s *principal* is the fun-seeker, a redex puts λ and @
principal-to-principal and the rule is **annihilation** — the same
index-wise splice that deletes γγ pairs is β-reduction:

    peer(λ,1) ↔ peer(@,1)   — body ↔ result
    peer(λ,2) ↔ peer(@,2)   — var  ↔ arg

The `lamRules` table is declared data: `ε` erases, `γγ` annihilates,
`λ⋈@` annihilates, `γ` against anything else commutes (lazy copying —
the duplicator only descends when it actually meets a constructor),
and unhandled pairs (`λλ`, `@@`, `γε` already claimed by erasure)
refuse by `none`.

Mechanical evidence at the bottom: `(λx.x) y` reduces to a bare wire —
the internal-body collapse that the earlier `livePeer` implementation
refused — and `(λx. x x) y` leaves a γ sitting on the shared argument
rather than copying it, which *is* optimal sharing made visible.
-/

namespace ISAR

/-- `LTerm` is the de-Bruijn syntax from `LambdaFragment` — the same
    terms that bracket abstraction compiles to ISK compile here to nets:
    one source language, two carriers.  `var i` with `i ≥ depth` is a
    free variable, compiled to an interface port. -/
def eraLbl : Nat := 0
def lamLbl : Nat := 1
def appLbl : Nat := 2
def dupLbl : Nat := 3

def lamRules : RuleTable where
  eraser := eraLbl
  action := fun l1 l2 =>
    if l1 = eraLbl then some .eraseL
    else if l2 = eraLbl then some .eraseR
    else if l1 = dupLbl && l2 = dupLbl then some .annihilate
    else if (l1 = lamLbl && l2 = appLbl) || (l1 = appLbl && l2 = lamLbl)
      then some .annihilate
    else if l1 = dupLbl || l2 = dupLbl then some .commute
    else none

namespace LambdaNet

/-- Free-variable binder ids sit above this base — they never collide
    with real binders (which are de-Bruijn depths). -/
def freeBase : Nat := 100000

/-- A compiled subtree's root: a concrete end, or a reference to a
    binder's var-slot resolved by the enclosing `lam`. -/
inductive Root where
  | end_ (e : PortEnd)
  | varRef (binder : Nat)

/-- Compilation state: agents, wires, and the open var-ends still
    awaiting their binder's slot. -/
structure Ctx where
  agents : Array (Option Agent)
  wires : List (PortEnd × PortEnd)
  openEnds : List (Nat × PortEnd)    -- (binder id, parent-side end)
deriving Repr

def Ctx.addAgent (c : Ctx) (ag : Agent) : Nat × Ctx :=
  (c.agents.size, { c with agents := c.agents.push (some ag) })

/-- Connect a port to a subtree root — either wire it now, or register
    it as an open end for a later binder. -/
def Ctx.attach (c : Ctx) (p : PortEnd) (r : Root) : Ctx :=
  match r with
  | .end_ e => { c with wires := (p, e) :: c.wires }
  | .varRef b => { c with openEnds := (b, p) :: c.openEnds }

/-- Fan a binder's var-slot out to its use-ends: ε when unused, a bare
    wire when single, a right-linear γ chain when shared. -/
def dupTree (c : Ctx) (uses : List PortEnd) (slot : PortEnd) : Ctx :=
  match uses with
  | [] =>
    let (e, c) := c.addAgent ⟨eraLbl, 0⟩
    { c with wires := (slot, .port e 0) :: c.wires }
  | u :: rest =>
    if rest.isEmpty then { c with wires := (slot, u) :: c.wires }
    else
      let (g, c) := c.addAgent ⟨dupLbl, 2⟩
      let c := { c with wires := (slot, .port g 0) :: (u, .port g 1) :: c.wires }
      dupTree c rest (.port g 2)

/-- Compile a term at binder depth `depth`.  `none` on unbound-variable
    shape violations — refusal, not a default. -/
def go (t : LTerm) (depth : Nat) (c : Ctx) : Option (Root × Ctx) :=
  match t with
  | .var i =>
    if i < depth then some (.varRef (depth - 1 - i), c)
    else some (.varRef (freeBase + (i - depth)), c)
  | .app f x => do
    let (rf, c) ← go f depth c
    let (rx, c) ← go x depth c
    let (a, c) := c.addAgent ⟨appLbl, 2⟩
    let c := (c.attach (.port a 0) rf).attach (.port a 2) rx
    some (.end_ (.port a 1), c)
  | .abs b => do
    let (rb, c) ← go b (depth + 1) c
    let (a, c) := c.addAgent ⟨lamLbl, 2⟩
    let c := c.attach (.port a 1) rb
    let (mine, rest) := c.openEnds.partition (·.1 = depth)
    let c := { c with openEnds := rest }
    let c := dupTree c (mine.map (·.2)) (.port a 2)
    some (.end_ (.port a 0), c)

/-- Compile a closed-or-free term to a net: open ends become interface
    ports, one free end each (external sharing isn't the net's business).
    The last free end is the term's root. -/
def compile (t : LTerm) : Option Net := do
  let (r, c) ← go t 0 ⟨#[], [], []⟩
  let c := match r with
    | .end_ e => { c with wires := (e, .free c.openEnds.length) :: c.wires }
    | .varRef b => { c with openEnds := (b, .free c.openEnds.length) :: c.openEnds }
  let freeWires := c.openEnds.mapIdx (fun i (_, p) => (p, .free i))
  some ⟨c.agents, freeWires ++ c.wires, c.openEnds.length + 1⟩

end LambdaNet

/-! ## Evidence

All evaluated — `check` on the compiled nets, then `nfBounded`. -/

open LambdaNet

/-- `(λx. x) y` — body is the var itself: an internal `λ.1↔λ.2` wire that
    the old `livePeer` refused and the subst-resolve collapses to the
    bare wire `y↔result`. -/
def idApp : LTerm := .app (.abs (.var 0)) (.var 0)

/-- `(λx. λy. x) z` — K on one argument: result should be `λy. z`, i.e. a
    λ whose var-port is an ε (y unused) and whose body-port faces `z`. -/
def kApp : LTerm := .app (.abs (.abs (.var 1))) (.var 0)

/-- `(λx. x x) y` — the sharing demo: β leaves a γ on the shared
    argument's edge, *not* two copies of `y`. -/
def dupApp : LTerm := .app (.abs (.app (.var 0) (.var 0))) (.var 0)

/-- `x` alone — a lone free variable: the net is just the interface. -/
def loneVar : LTerm := .var 0

example : (LambdaNet.compile idApp).isSome = true := rfl
example : (LambdaNet.compile kApp).isSome = true := rfl
example : (LambdaNet.compile dupApp).isSome = true := rfl

#eval (LambdaNet.compile idApp).map Net.check
#eval (LambdaNet.compile kApp).map Net.check
#eval (LambdaNet.compile dupApp).map Net.check

#eval (LambdaNet.compile idApp).map (nfBounded lamRules 16)
#eval (LambdaNet.compile kApp).map (nfBounded lamRules 16)
#eval (LambdaNet.compile dupApp).map (nfBounded lamRules 16)
#eval (LambdaNet.compile loneVar).map (nfBounded lamRules 8)

end ISAR
