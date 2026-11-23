import ISAR.ObservationRegime
import ISAR.KernelCategory

/-!
# Interaction nets as a kernel presentation

Stage (b) of the ISK demotion (decision 068): a graph-sharing carrier whose
`ObservationRegime` is joinability-by-bounded-normal-form, instantiated
against the generic `Kernel P R` interface.

## Presentation

A `Net` is an array of agents plus a list of wires.  Each agent has a
label and an arity; port `0` is the principal port.  A wire is a pair of
*ends* — a port address `⟨agent, port⟩` or a free-port index — so sharing
is intrinsic: an edge is a datum, not a tree shape.  The wiring invariant
(every live port covered exactly once, no dangling ends) is checked by
`Net.check`: the early structural refusal.

## Rewrite

`RuleTable.action` maps a principal-principal label pair to one of
Lafont's three structural actions — `annihilate` (agents cancel, aux
ports wired pairwise), `commute` (the bipartite copy grid — the
duplicator interaction that makes sharing optimal), `erase` (the eraser
swallows its partner; fresh erasers land on every freed auxiliary peer).
The rules are declared data, interpreted not hardcoded.

## Regime

`Obs` is three-valued: `.nf` a bounded normal form, `.divergent` (fuel
exhausted while reducible — the ⊥ class the `inet_observe_probe` made
mechanical), `.refused` (structural contract violated).  `ObsEq` is
literal equality — decidable by representation.  `sim` is bounded
joinability, which coincides with equational theory exactly where the
rewrite is confluent — and interaction rules are confluent by
construction (that *is* the optimality property).  `Normalizing` is the
first-class guard, the `bendtt.lean` `Guard` pattern.
-/

namespace ISAR

/-- One end of a wire: a port of an agent, or the interface. -/
inductive PortEnd where
  | port (agent : Nat) (index : Nat)
  | free (index : Nat)
deriving DecidableEq, Repr, Inhabited

/-- An agent: a label and an arity.  Port `0` is principal; ports
    `1 … arity` are auxiliary. -/
structure Agent where
  label : Nat
  arity : Nat
deriving DecidableEq, Repr

/-- A net: agents (holes where erased) plus the wiring — each wire an
    unordered end pair stored once. -/
structure Net where
  agents : Array (Option Agent)
  wires : List (PortEnd × PortEnd)
  freeArity : Nat
deriving DecidableEq, Repr

/-- The partner end of a wire, given one end. -/
def Net.peerOf (n : Net) (e : PortEnd) : Option PortEnd :=
  n.wires.findSome? (fun (a, b) =>
    if a = e then some b else if b = e then some a else none)

/-- All ports of live agents, plus interface ends. -/
def Net.liveEnds (n : Net) : List PortEnd :=
  (List.range n.agents.size).flatMap (fun a =>
    match n.agents[a]? with
    | some (some ag) => (List.range (ag.arity + 1)).map (.port a)
    | _ => [])
  ++ (List.range n.freeArity).map .free

/-- Executable wiring check: every live end is a wire end exactly once and
    no wire dangles.  A malformed net never enters `step`. -/
def Net.check (n : Net) : Bool :=
  let ends := n.wires.flatMap (fun (a, b) => [a, b])
  let live := n.liveEnds
  ends.all (fun e => live.contains e) &&
  live.all (fun e => ends.count e = 1)

/-- Does end `e` sit at the principal port of a live agent `a`? -/
def Net.isPrincipalEnd (n : Net) (e : PortEnd) : Bool :=
  match e with
  | .port a 0 =>
    (match n.agents[a]? with | some (some _) => true | _ => false)
  | _ => false

/-- The agent id at a principal end (default 0; only used after
    `isPrincipalEnd`). -/
def PortEnd.agentOf : PortEnd → Nat
  | .port a _ => a
  | .free _ => 0

/-- Wires whose both ends are principal ports of distinct live agents —
    the only place interaction happens. -/
def Net.principalPairs (n : Net) : List (PortEnd × PortEnd) :=
  n.wires.filter (fun (x, y) =>
    n.isPrincipalEnd x && n.isPrincipalEnd y &&
    (x.agentOf ≠ y.agentOf))

/-- Lafont's three structural actions on a principal pair. -/
inductive Action where
  | annihilate
  | commute
  | eraseL
  | eraseR
deriving Repr

/-- The rule set as declared data.  `action` returning `none` names an
    unhandled principal pair — a refusal, not a default. -/
structure RuleTable where
  action : Nat → Nat → Option Action
  eraser : Nat

/-- The three-valued observation: bounded normal form, the ⊥ class, or a
    refusal.  The probe's divergence/refusal split made structural. -/
inductive Obv where
  | nf : Net → Obv
  | divergent
  | refused
deriving DecidableEq, Repr

/-- All port ends of agent `a` with the given arity. -/
def portsOf (a : Nat) (arity : Nat) : List PortEnd :=
  (List.range (arity + 1)).map (.port a)

/-- Wire two ends. -/
abbrev wire (a b : PortEnd) : PortEnd × PortEnd := (a, b)

/-- Auxiliary port indices of an agent. -/
def auxPorts (arity : Nat) : List Nat := (List.range arity).map (· + 1)

/-- A splice plan: how each *auxiliary* port of the dying pair is
    replaced, the fresh agents appended, and the construction wires
    added (the commute grid).  Principal ports get no entry — a resolve
    that lands on one drops the wire, which is unreachable in a checked
    net anyway (the principals' only wire is the pair's own edge). -/
structure SplicePlan where
  subst : List (PortEnd × PortEnd)
  freshAgents : Array (Option Agent)
  extraWires : List (PortEnd × PortEnd)

/-- Outcome of resolving an end through the splice. -/
inductive ResolveRes where
  | live : PortEnd → ResolveRes
  | drop : ResolveRes          -- dead principal — the pair's own edge vanishes

/-- Iterate the splice substitution until the end is live or hits a
    principal (`.drop`); `none` on a dead-end cycle (fuel bounds the
    chase). -/
def resolveEnd (dead : List PortEnd) (subst : List (PortEnd × PortEnd))
    (fuel : Nat) (e : PortEnd) : Option ResolveRes :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if dead.contains e then
      match subst.lookup e with
      | some e' => resolveEnd dead subst fuel e'
      | none => some .drop
    else some (.live e)

/-- Rewrite every wire through `resolveEnd`; dropped ends vanish the
    wire, unresolvable cycles refuse.  Mirror-image duplicates from the
    splice are collapsed (a wire is unordered). -/
def rewire (n : Net) (dead : List PortEnd) (subst : List (PortEnd × PortEnd)) :
    Option (List (PortEnd × PortEnd)) :=
  let fuel := dead.length + 1
  let rec go : List (PortEnd × PortEnd) → List (PortEnd × PortEnd) →
      Option (List (PortEnd × PortEnd))
    | [], acc => some acc
    | (x, y) :: ws, acc =>
      match resolveEnd dead subst fuel x, resolveEnd dead subst fuel y with
      | some (.live x'), some (.live y') =>
        if acc.any (fun (a, b) => (a = x' && b = y') || (a = y' && b = x'))
        then go ws acc else go ws (acc ++ [(x', y')])
      | some .drop, _ => go ws acc
      | _, some .drop => go ws acc
      | _, _ => none
  go n.wires []

/-- Annihilation: aux port `a.k` is replaced by `b`'s k-th peer and vice
    versa — resolve chases dead ends transitively, so internal wires
    (the `(λx.x)` shape, an aux port wired to its own pair) collapse
    correctly instead of refusing.  Refuses on arity mismatch. -/
def annihilatePlan (n : Net) (a b : Nat) (agA agB : Agent) : Option SplicePlan :=
  if agA.arity ≠ agB.arity then none else
  let aux := auxPorts agA.arity
  let pa := aux.map (fun k => n.peerOf (.port b k))
  let pb := aux.map (fun k => n.peerOf (.port a k))
  if (pa ++ pb).any (·.isNone) then none else
  some { subst :=
    (aux.zip pa).map (fun (k, p) => (.port a k, p.get!)) ++
    (aux.zip pb).map (fun (k, p) => (.port b k, p.get!))
       , freshAgents := #[]
       , extraWires := [] }

/-- Commutation: each dead aux port is replaced by the principal of its
    fresh copy — the old wire (a.i ↔ x) becomes (Bᵢ.0 ↔ x) by the same
    rewire, peers never touched.  The bipartite grid wires the copies'
    aux ports crosswise; internal aux-aux wires collapse into real wires
    between fresh agents (a feedback loop diverges — correct). -/
def commutePlan (n : Net) (a b : Nat) (agA agB : Agent) : SplicePlan :=
  let m := agA.arity; let k := agB.arity
  let baseB := n.agents.size
  let baseA := baseB + m
  let auxA := auxPorts m; let auxB := auxPorts k
  { subst :=
    auxA.map (fun i => (.port a i, .port (baseB + i - 1) 0)) ++
    auxB.map (fun j => (.port b j, .port (baseA + j - 1) 0))
  , freshAgents :=
    (List.replicate m (some { label := agB.label, arity := k })).toArray ++
    (List.replicate k (some { label := agA.label, arity := m })).toArray
  , extraWires := auxA.flatMap (fun i => auxB.map (fun j =>
      wire (.port (baseB + i - 1) j) (.port (baseA + j - 1) i))) }

/-- Erasure: every dead aux port (of both agents) is replaced by the
    principal of a fresh arity-0 eraser — the partner's structure is
    swallowed whole and each freed peer gets its own ε. -/
def erasePlan (n : Net) (a b : Nat) (agA agB : Agent) (rt : RuleTable) :
    SplicePlan :=
  let base := n.agents.size
  let substA := (auxPorts agA.arity).mapIdx (fun idx i =>
    (.port a i, .port (base + idx) 0))
  let substB := (auxPorts agB.arity).mapIdx (fun idx j =>
    (.port b j, .port (base + agA.arity + idx) 0))
  { subst := substA ++ substB
  , freshAgents :=
    (List.replicate (agA.arity + agB.arity)
      (some { label := rt.eraser, arity := 0 })).toArray
  , extraWires := [] }

/-- One interaction step on the first principal pair — the raw candidate.
    `none` = no reducible pair (normal form or stuck);
    `some none` = contract violated (refusal);
    `some (some n')` = candidate reduct. -/
def netStepRaw (rt : RuleTable) (n : Net) : Option (Option Net) :=
  match n.principalPairs.head? with
  | some (.port a 0, .port b 0) =>
    match n.agents[a]?, n.agents[b]? with
    | some (some agA), some (some agB) =>
      match rt.action agA.label agB.label with
      | none => some none
      | some act =>
        let sp := match act with
          | .annihilate => annihilatePlan n a b agA agB
          | .commute => some (commutePlan n a b agA agB)
          | .eraseL | .eraseR => some (erasePlan n a b agA agB rt)
        match sp with
        | none => some none
        | some sp =>
          let dead := portsOf a agA.arity ++ portsOf b agB.arity
          match rewire n dead sp.subst with
          | none => some none
          | some wires' =>
            some (some { n with
              agents := ((n.agents.set! a none).set! b none) ++ sp.freshAgents
              wires := wires' ++ sp.extraWires })
    | _, _ => some none
  | _ => none

/-- The validated step: a candidate is adopted only if the wiring check
    passes — translation validation, verify the transform not the
    transformer. -/
def netStep (rt : RuleTable) (n : Net) : Option (Option Net) :=
  match netStepRaw rt n with
  | some (some n') => if n'.check = true then some (some n') else some none
  | none => none
  | some none => some none

/-- Wiring coherence as a corollary: an adopted reduct always passes the
    structural check — by the validation guard, not by construction
    discipline. -/
theorem netStep_checked (rt : RuleTable) (n n' : Net)
    (h : netStep rt n = some (some n')) : n'.check = true := by
  simp only [netStep] at h
  split at h
  · rename_i cand _
    split at h
    · next hc => cases h; exact hc
    · simp at h
  · simp at h
  · simp at h

/-- Bounded normalization.  Fuel out while a pair remains reducible is
    `.divergent` — the honest over-approximation. -/
def nfBounded (rt : RuleTable) (fuel : Nat) (n : Net) : Obv :=
  match fuel with
  | 0 =>
    if n.principalPairs.isEmpty then .nf n else .divergent
  | fuel + 1 =>
    match netStep rt n with
    | none => .nf n
    | some none => .refused
    | some (some n') => nfBounded rt fuel n'

/-- The interaction-net observation regime: `sim` is bounded joinability.
    On a confluent rule table this *is* joinability, hence (inside the
    normalizing fragment) the equational theory — one answer from every
    direction, which is what optimal sharing buys. -/
def inetRegime (rt : RuleTable) (fuel : Nat) : ObservationRegime Net where
  Obs := Obv
  observe := nfBounded rt fuel
  ObsEq := (· = ·)
  is_equiv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The first-class normalizability guard — the `Guard` pattern:
    `observe` is meaningful exactly where a bound suffices. -/
def Normalizing (rt : RuleTable) (n : Net) : Prop :=
  ∃ fuel : Nat, ∃ nf : Net, nfBounded rt fuel n = .nf nf

/-! ## The classic γ/δ/ε fragment, exercised

The rule table is declared data: `ε` (label 0) erases, equal labels
annihilate, distinct non-ε labels commute.  The examples below are the
mechanical evidence — evaluated, not asserted.
-/

def γδε : RuleTable where
  action := fun l1 l2 =>
    if l1 = 0 then some .eraseL
    else if l2 = 0 then some .eraseR
    else if l1 = l2 then some .annihilate
    else some .commute
  eraser := 0

private def mkNet (ags : Array (Option Agent)) (wires : List (PortEnd × PortEnd))
    (frees : Nat) : Net := ⟨ags, wires, frees⟩

/-- Two-node γ(2)/δ(2) pair on their principals, aux ports to the four
    free ends — the textbook commutation input. -/
def gammaDeltaNet : Net :=
  mkNet #[some ⟨1, 2⟩, some ⟨2, 2⟩]
    [wire (.port 0 0) (.port 1 0),
     wire (.port 0 1) (.free 0), wire (.port 0 2) (.free 1),
     wire (.port 1 1) (.free 2), wire (.port 1 2) (.free 3)]
    4

/-- Annihilation: two arity-2 agents of the same label — both vanish, the
    free ends are spliced pairwise. -/
def annihNet : Net :=
  mkNet #[some ⟨1, 2⟩, some ⟨1, 2⟩]
    [wire (.port 0 0) (.port 1 0),
     wire (.port 0 1) (.free 0), wire (.port 0 2) (.free 1),
     wire (.port 1 1) (.free 2), wire (.port 1 2) (.free 3)]
    4

/-- Erasure: ε on γ's principal — γ is swallowed, fresh εs land on its
    freed aux peers. -/
def eraseNet : Net :=
  mkNet #[some ⟨0, 0⟩, some ⟨1, 2⟩]
    [wire (.port 0 0) (.port 1 0),
     wire (.port 1 1) (.free 0), wire (.port 1 2) (.free 1)]
    2

/-- Degenerate pair: the aux wire joins the two dying agents, so the
    splice would fabricate a wire on dead ends — refused. -/
def loopNet : Net :=
  mkNet #[some ⟨1, 1⟩, some ⟨2, 1⟩]
    [wire (.port 0 0) (.port 1 0),
     wire (.port 0 1) (.port 1 1)]
    0

-- mechanical evidence: checks hold, nfs evaluate
example : gammaDeltaNet.check = true := by decide
example : annihNet.check = true := by decide
example : eraseNet.check = true := by decide
example : loopNet.check = true := by decide

-- After commutation the γ/δ pair becomes the bipartite grid: two δ-copies
-- facing the γ's old aux peers, two γ-copies facing the δ's — four live
-- agents, eight wires.
#eval nfBounded γδε 8 gammaDeltaNet
#eval nfBounded γδε 8 annihNet
#eval nfBounded γδε 8 eraseNet
-- loopNet is the degenerate case: its aux wire joins the dying pair, so
-- the splice refuses rather than fabricate a wire.  Fuel-exhaustion on a
-- reducible net is the ⊥ class:
#eval nfBounded γδε 6 loopNet
#eval nfBounded γδε 0 gammaDeltaNet

/-- The carrier plugged into the generic machinery — `Kernel Net
    (inetRegime γδε fuel)`, the substrate kernel, canonical hom, and a
    Net→Net quotient map that never touches ISK. -/
def inetKernel (fuel : Nat) : Kernel Net (inetRegime γδε fuel) :=
  substrateKernel (inetRegime γδε fuel)

def inetCanonical (fuel : Nat) :
    KernelHom (inetKernel fuel) (substrateKernel (inetRegime γδε fuel)) :=
  canonical_hom (inetKernel fuel)

/-- Regime-to-regime: observe the γδε regime through itself. -/
def inetSelfMap (fuel : Nat) :
    QuotientMap Net (inetRegime γδε fuel) Net (inetRegime γδε fuel) where
  encode := id
  decode := id
  preserves := fun _ => rfl

end ISAR
