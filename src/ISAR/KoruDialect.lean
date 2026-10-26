import ISAR.FlowDialect

/-!
# KoruDialect — the Koru dialect assembled as declared layers

The third file of the Koru dialect story, and its registry.
`FlowView` declares the *encoding* (`encProg`/`decProg`, proved);
`FlowDialect` declares the *semantics* (`runK`/`evalKProg`,
`runK_mono`, the deferred `FlowEvalCongruent`); this file declares
the *dialect itself* — the layer separation the host story
mirrors:

  * `KEncoding` — the codec layer: an encode/decode pair with a
    round-trip law. Realized: `koruEncoding` (FlowView's
    `decProg_encProg`).
  * `KGrammar` — the admissibility layer: a decidable
    well-formedness check over `KProg`. `wfProg` checks the static
    half of the walker's walls — entry resolves, every invocation
    name resolves in the graph, every `@jump` names its enclosing
    `#label` (the nested-label refusal made static). Malformed
    programs are refused by the grammar before evaluation ever
    runs.
  * `KSurface` — the syntax layer: surface text (`*.k` files) to
    `KProg`. Declared-not-realized: `koruSurface` parses nothing —
    a total refusal is the honest state of a layer with no
    implementation, matching the toolchain contract's "declared
    component gets its refusal path".
  * `KBackend` — the emission layer: registered target rows
    `KProg → Option String`. `koruC99` is the first declared row —
    the C99 bootstrap backend — also a total refusal until the
    emission leg lands.

`KoruLayers` bundles them; `koruLayers` is the current instance —
encoding and grammar realized, surface and backends refusing.

What is deliberately NOT here: any claim that a backend or the
surface exists, and any claim that Koru self-hosts. `SelfHosting`
states the self-host obligation at full strength — a compiler
program `comp : KProg` whose `runK` evaluation on a source-as-call
agrees with the backend's emission on the same source, refusals
included — parameterized on the same shape as
`FlowEvalCongruent` so it can cite it. Nothing asserts it.

This is the Futamura shape (`ISAR.Futamura`) at dialect altitude:
the compiler spec is a `KProg`, the bootstrap backend is a
`KBackend`, and the fixpoint is the stated proposition — not a
smuggled consequence.
-/

namespace ISAR

/-! ## Layer structures -/

/-- The encoding layer: a codec into `TTerm` with a proved
round-trip — refusal (`dec` returning `none` on malformed shapes)
is part of the layer, not an afterthought. -/
structure KEncoding (α : Type) where
  enc : α → TTerm
  dec : TTerm → Option α
  roundtrip : ∀ x, dec (enc x) = some x

/-- The grammar layer: admissibility as a decidable check.
`grammar p = false` refuses the program before evaluation. -/
abbrev KGrammar (α : Type) := α → Bool

/-- The syntax layer: surface text to objects. A layer with no
implementation refuses totally — `parse = fun _ => none` is the
declared-not-realized state, not a silent default. -/
structure KSurface (α : Type) where
  name : String
  parse : String → Option α

/-- A registered backend: emission to a target's spelling
(C source text for `c99`). Unrealized backends refuse totally —
a row in `backends` is a declaration of intent plus its refusal
path, matching the toolchain contract. -/
structure KBackend (α : Type) where
  name : String
  emit : α → Option String

/-- The dialect assembled: encoding + grammar + surface +
registered backends. -/
structure KoruLayers (α : Type) where
  encoding : KEncoding α
  grammar : KGrammar α
  surface : KSurface α
  backends : List (KBackend α)

/-! ## The grammar layer — `wfProg`

The static half of the walker's loud walls:

  * `entry` resolves in `graph`;
  * every `invoke`/`head` name resolves in `graph` (thunks included —
    the oracle supplies leaves, not declarations);
  * every `jump` names the enclosing flow's `preLabel` — the
    nested-label refusal checked statically;
  * `bare` impls are expression-closed: no static name check needed
    beyond the call sites, since only `invoke`/`head`/`jump` carry
    names. -/

/-- Names a `KExpr` can't mention (expressions carry no call names
except builtin names, which the builtin table resolves at eval
time — no static check). -/
def wfExpr (_ : KExpr) : Bool := true

/-- Arm-level checks under an enclosing flow: `invoke`/`jump` nodes
name-check, and nested `conts` arms recurse (they dispatch in the
same flow, so they share the enclosing label). The arm is
destructured in the pattern so `conts` is a literal subterm — the
well-founded checker cannot see through the `KArm.conts` accessor. -/
def wfArms (g : KGraph) (preLabel : Option String) : List KArm → Bool
  | [] => true
  | .mk _ _ _ _ node conts :: rest =>
      let nodeOk := match node with
        | none | some .terminal => true
        | some (.jump lbl _) => preLabel == some lbl
        | some (.invoke name _) => g.any (·.1 == name)
        | some (.produce _) | some (.retCtor _ _) => true
      nodeOk && wfArms g preLabel conts && wfArms g preLabel rest
termination_by l => sizeOf l
decreasing_by
  all_goals (simp_wf <;> omega)

/-- Flow-level checks: head name resolves, arms check. -/
def wfFlow (g : KGraph) (fl : KFlow) : Bool :=
  g.any (·.1 == fl.head.1) && wfArms g fl.preLabel fl.arms

/-- Program-level grammar: entry resolves, and every callable in
the graph is well-formed. -/
def wfProg (p : KProg) : Bool :=
  p.graph.any (·.1 == p.entry) &&
  p.graph.all fun (_, c) =>
    match c with
    | .thunk => true
    | .bare e => wfExpr e
    | .subflow fl => wfFlow p.graph fl

/-! ## The realized and refusing layers -/

/-- Encoding: realized — FlowView's codec with its proved
round-trip. -/
def koruEncoding : KEncoding KProg where
  enc := encProg
  dec := decProg
  roundtrip := decProg_encProg

/-- Surface: declared-not-realized — no `.k` parser is claimed; the
layer refuses everything until one lands. -/
def koruSurface : KSurface KProg where
  name := ".k"
  parse := fun _ => none

/-- The C99 bootstrap backend: the first registered target row —
declared-not-realized, refuses totally until the emission leg
lands. -/
def koruC99 : KBackend KProg where
  name := "c99"
  emit := fun _ => none

/-- The current dialect instance: encoding and grammar realized,
surface and the C99 backend declared with their refusal paths. -/
def koruLayers : KoruLayers KProg where
  encoding := koruEncoding
  grammar := wfProg
  surface := koruSurface
  backends := [koruC99]

/-! ## Grammar fixtures — the layer refuses what the walker would

Static walls checked before evaluation: unknown callables, dangling
jump labels, unresolvable entry. -/

/-- `kArith` is well-formed: every name resolves, no jumps. -/
theorem wf_karith : wfProg kArith == true := by native_decide

/-- `kCount` is well-formed: the `again` jump names its enclosing
`#label`. -/
theorem wf_kcount : wfProg kCount == true := by native_decide

/-- A program whose entry is not in the graph is refused by the
grammar — before evaluation. -/
theorem wf_bad_entry :
    wfProg { kArith with entry := "missing" } == false := by
  native_decide

/-- A jump to a label other than the enclosing `#label` is a
grammar refusal — the walker's nested-label wall, checked
statically. -/
def kBadJump : KProg := {
  graph := [
    ("tick", .thunk)
  , ("count", .subflow {
      preLabel := some "again"
      head := ("tick", [])
      arms := [ .mk "go" false none none
                  (some (.jump "elsewhere" [])) [] ] })
  , ("main", .subflow {
      preLabel := none
      head := ("count", [])
      arms := [] }) ]
  entry := "main"
  args := [] }

theorem wf_bad_jump : wfProg kBadJump == false := by native_decide

/-- An invocation of a name that resolves nowhere is a grammar
refusal — the dynamic `invoke → none` wall, checked statically. -/
def kBadInvoke : KProg := {
  graph := [
    ("main", .subflow {
      preLabel := none
      head := ("ghost", [])
      arms := [] }) ]
  entry := "main"
  args := [] }

theorem wf_bad_invoke : wfProg kBadInvoke == false := by native_decide

/-! ## The self-host obligation

What "Koru hosts itself" means at this altitude, stated — not
claimed. A compiler is a `KProg`; a backend emission is
`KProg → Option String`; self-hosting is the existence of a
compiler program whose kernel evaluation of a source presented as
a call agrees with the backend's emission of that source —
refusals included (the `=` on `Option`, both directions). -/

/-- The self-host obligation: `comp` is a compiler when evaluating
`src` as a call (under `comp.graph`, fuel-bounded, oracle-free)
renders to exactly what `emit` produces for `src`. `asCall` names
the calling convention (entry + arg encoding); `renderRes` decodes
a `KResult` to emitted text. Nothing asserts an instance exists —
this is the Futamura fixpoint stated as a proposition. -/
def SelfHosting (emit : KProg → Option String)
    (asCall : KProg → String × List (String × KVal))
    (renderRes : KResult → Option String) : Prop :=
  ∃ (comp : KProg), ∃ (fuel : Nat),
    ∀ (src : KProg),
      (asKResult (runK comp.graph [] fuel
        (.invoke (asCall src).1 (asCall src).2))).bind renderRes
        = emit src

/-- The C99-flavored instance of the obligation — what the first
bootstrap chain must eventually witness. `emit` is left existential
rather than fixed to `koruC99.emit`: the current row refuses
everywhere, which would make the claim vacuous (a compiler that
refuses everything agrees with a backend that refuses everything).
The productivity conjunct `∃ src, emit src ≠ none` is what makes
discharge meaningful — the backend must actually emit something. -/
def SelfHostingC99 : Prop :=
  ∃ (emit : KProg → Option String)
    (asCall : KProg → String × List (String × KVal))
    (renderRes : KResult → Option String),
    SelfHosting emit asCall renderRes ∧ ∃ src, emit src ≠ none

end ISAR
