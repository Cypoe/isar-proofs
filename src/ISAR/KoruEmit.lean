import ISAR.KoruDialect

/-!
# KoruEmit — quotation, the C99 subset backend, and the witnessed fixpoint

The self-host leg's first real rung. Three artefacts and a checked
agreement:

  * **Quotation** (`quoteProg` and friends): `KProg → KVal`, the same
    tagged structure as `encProg` (`node tag kids`, tags 1–31) but
    materialized as wire *values* — `cell` nodes, `arr` lists, `str`/
    `int` atoms — so a compiler program can navigate its source as
    data with `field`/`index`/`len`/`eq`. This is the self-reference
    substrate: `asCall` presents `src` to `comp` as a quoted arg.

  * **`emitC99`**: the first realized emission row — for the declared
    subset `main = bare (lit (int i))` (and nothing else) it emits
    `int main(void) { return i; }`. Everything else refuses. The
    emitted fragment is deep inside the CompCert-accepted C subset —
    no VLA/`_Complex`/etc. — so the machine-checked leg
    (`KProg → C99 → CompCert → machine code`) stays checkable end to
    end. Subset growth is mechanical; the refusal contract is the
    point.

  * **`kEmit`**: the same emission *in the flow language* — a
    `KProg` whose `emit` callable is a bare expr that shape-checks
    the quoted source (tag/length/name navigation) and concatenates
    the C text. Refusals align with `emitC99` because failed
    navigation produces `none` exactly where the pattern match fails.

  * **The witnessed fixpoint**: `SelfHostingOn` — `SelfHosting`
    restricted to a declared corpus — is discharged by
    `native_decide` over `koruEmitCorpus` (one accept + seven
    refuse directions). `SelfHostingC99` stays stated at full
    strength: the `∀ src` discharge is the compiler-correctness
    theorem, a later rung — this corpus check is the honest witness,
    the same discipline as the corpus-facing FlowCheck leg.

What is deliberately absent: no string-payload emission (the wire
has no char-level ops to C-escape safely — the escape row is a
recorded obligation), no unquote round-trip (comp navigates the
quotation directly; `unquote` is only needed for host tooling).
-/

namespace ISAR

/-! ## Quotation — `KProg` as `KVal` data

Mirrors `encProg`'s tag table exactly (`FlowView`), materialized as
values a program can inspect: nodes are `cell [("tag", int n),
("kids", arr children)]`, pairs are `cell [("name", str), ("v", _)]`,
lists are `arr` (so `len` works), `Option` is tags 23/24, strings and
ints stay themselves. -/

def qnode (tag : Int) (kids : List KVal) : KVal :=
  .cell [("tag", .int tag), ("kids", .arr kids)]

def qpair (n : String) (v : KVal) : KVal :=
  .cell [("name", .str n), ("v", v)]

def qopt : Option KVal → KVal
  | none => qnode 23 []
  | some v => qnode 24 [v]

mutual
def quoteVal : KVal → KVal
  | .int i => qnode 1 [.int i]
  | .float n d => qnode 2 [.int n, .int d]
  | .bool b => qnode 3 [.int (if b then 1 else 0)]
  | .str s => qnode 4 [.str s]
  | .arr xs => qnode 5 [.arr (quoteValList xs)]
  | .cell fs => qnode 6 [.arr (quoteNamedVals fs)]

def quoteValList : List KVal → List KVal
  | [] => []
  | x :: xs => quoteVal x :: quoteValList xs

def quoteNamedVals : List (String × KVal) → List KVal
  | [] => []
  | (n, v) :: xs => qpair n (quoteVal v) :: quoteNamedVals xs

def quoteExpr : KExpr → KVal
  | .lit v => qnode 8 [quoteVal v]
  | .var n => qnode 9 [.str n]
  | .bin op l r =>
      qnode 10 [.int (encBinOpN op : Int), quoteExpr l, quoteExpr r]
  | .un op e => qnode 11 [.int (encUnOpN op : Int), quoteExpr e]
  | .cond c t e => qnode 12 [quoteExpr c, quoteExpr t, quoteExpr e]
  | .field o n => qnode 13 [quoteExpr o, .str n]
  | .index o i => qnode 14 [quoteExpr o, quoteExpr i]
  | .builtin n args => qnode 15 [.str n, .arr (quoteExprList args)]

def quoteExprList : List KExpr → List KVal
  | [] => []
  | x :: xs => quoteExpr x :: quoteExprList xs

def quoteNamedExprs : List (String × KExpr) → List KVal
  | [] => []
  | (n, e) :: xs => qpair n (quoteExpr e) :: quoteNamedExprs xs

def quoteArmNode : KArmNode → KVal
  | .terminal => qnode 16 []
  | .jump t args => qnode 17 [.str t, .arr (quoteNamedExprs args)]
  | .invoke t args => qnode 18 [.str t, .arr (quoteNamedExprs args)]
  | .produce e => qnode 19 [quoteExpr e]
  | .retCtor c e => qnode 20 [.str c, quoteExpr e]

def quoteArm : KArm → KVal
  | .mk branch catchall bind cond node conts =>
      qnode 22 [.str branch, .int (if catchall then 1 else 0),
                qopt (bind.map .str), qopt (cond.map quoteExpr),
                qopt (node.map quoteArmNode), .arr (quoteArmList conts)]

def quoteArmList : List KArm → List KVal
  | [] => []
  | a :: xs => quoteArm a :: quoteArmList xs
end

def quoteHead (h : String × List (String × KExpr)) : KVal :=
  qnode 26 [.str h.1, .arr (quoteNamedExprs h.2)]

def quoteFlow (f : KFlow) : KVal :=
  qnode 25 [qopt (f.preLabel.map .str), quoteHead f.head,
            .arr (quoteArmList f.arms)]

def quoteCallable : KCallable → KVal
  | .bare e => qnode 27 [quoteExpr e]
  | .thunk => qnode 28 []
  | .subflow f => qnode 29 [quoteFlow f]

def quoteNamedCallable (nc : String × KCallable) : KVal :=
  qpair nc.1 (quoteCallable nc.2)

def quoteNamedVal (nv : String × KVal) : KVal :=
  qpair nv.1 (quoteVal nv.2)

/-- The program quotation — `asCall`'s argument encoding. -/
def quoteProg (p : KProg) : KVal :=
  qnode 30 [.arr (p.graph.map quoteNamedCallable), .str p.entry,
            .arr (p.args.map quoteNamedVal)]

/-! ## The C99 subset backend — `emitC99`

`emitC99` lives in `KoruDialect` beside the `koruC99` row it
implements (import direction: this file builds on the registry).
Declared subset: a single-entry graph
`[("main", .bare (.lit (.int i)))]`, entry `main`, empty args —
emitted as `int main(void) { return i; }`. Everything else refuses.
The emitted fragment is deep inside the CompCert-accepted C subset —
the machine-checked leg (`KProg → C99 → CompCert → machine code`)
stays checkable end to end. -/

/-! ## The calling convention and the renderer -/

/-- `asCall`: a source program is presented to the compiler as the
`src` argument of the `emit` call — quotation is the calling
convention. -/
def emitCall (src : KProg) : String × List (String × KVal) :=
  ("emit", [("src", quoteProg src)])

/-- `renderRes`: the renderer only extracts a string payload — the
compiler did the compiling. -/
def renderC99 (r : KResult) : Option String :=
  r.payload.bind fun | .str s => some s | _ => none

/-! ## The compiler as a `KProg` — `kEmit`

`kEmit` is a `KProg` implementing `emitC99` for the subset: a single
bare `emit` callable whose expr shape-checks the quoted source and
concatenates the C text. Every check mirrors an `emitC99` match arm;
failed navigation (`field`/`index`/`len` on the wrong shape) produces
`none` exactly where the match fails — refusal agreement is
structural, not asserted.

Meta-level helpers (`qf`/`qi`/`qlen`/`qand`/…) are expr constructors,
not runtime syntax — they exist to keep the object expr readable. -/

/-- `e.name` — cell field access. -/
def qf (e : KExpr) (n : String) : KExpr := .field e n

/-- `e[i]` — array index. -/
def qi (e : KExpr) (i : Int) : KExpr := .index e (.lit (.int i))

/-- `len e` — array length builtin. -/
def qlen (e : KExpr) : KExpr := .builtin "len" [e]

/-- `itoa e` — decimal render builtin. -/
def qitoa (e : KExpr) : KExpr := .builtin "intToString" [e]

/-- `a == b` on ints/strings. -/
def qeq (a b : KExpr) : KExpr := .bin .eq a b

/-- `a && b` on bools. -/
def qand (a b : KExpr) : KExpr := .bin .and a b

/-- `a ++ b` string concat. -/
def qcat (a b : KExpr) : KExpr := .bin .concat a b

/- The navigation paths into the quoted program — each is an expr
that evaluates to a piece of `src`'s quotation. -/
namespace KEmit

def graphN : KExpr := qi (qf (.var "src") "kids") 0
def entryN : KExpr := qi (qf (.var "src") "kids") 1
def argsN : KExpr := qi (qf (.var "src") "kids") 2
def pair0 : KExpr := qi graphN 0
def callN : KExpr := qf pair0 "v"
def exprN : KExpr := qi (qf callN "kids") 0
def valN : KExpr := qi (qf exprN "kids") 0
def intN : KExpr := qi (qf valN "kids") 0

/-- The shape check: `src` is `qnode 30 [arr[pair "main" (node27
[node8 [node1 [int]]])], "main", arr[]]`. Any navigation failure
or tag mismatch refuses — mirroring `emitC99`'s match. -/
def shapeOk : KExpr :=
  qand (qeq (qf (.var "src") "tag") (.lit (.int 30))) (
  qand (qeq (qlen (qf (.var "src") "kids")) (.lit (.int 3))) (
  qand (qeq (qlen graphN) (.lit (.int 1))) (
  qand (qeq (qf pair0 "name") (.lit (.str "main"))) (
  qand (qeq entryN (.lit (.str "main"))) (
  qand (qeq (qlen argsN) (.lit (.int 0))) (
  qand (qeq (qf callN "tag") (.lit (.int 27))) (
  qand (qeq (qlen (qf callN "kids")) (.lit (.int 1))) (
  qand (qeq (qf exprN "tag") (.lit (.int 8))) (
  qand (qeq (qlen (qf exprN "kids")) (.lit (.int 1))) (
  qand (qeq (qf valN "tag") (.lit (.int 1))) (
        (qeq (qlen (qf valN "kids")) (.lit (.int 1)))
  )))))))))))

/-- The produced string — `int main(void) { return <i>; }`. -/
def produced : KExpr :=
  qcat (.lit (.str "int main(void) { return ")) (
       qcat (qitoa intN) (.lit (.str "; }")))

/-- A navigation that cannot succeed — the refusal arm. `src` is a
quoted program cell; `__missing` is never a field → `none`.  Spelled
this way (rather than `(0).x`) because real koru refuses
field-access on a literal in produce position as call-shaped
(KORU104). -/
def refused : KExpr := .field (.var "src") "__missing"

end KEmit

/-- `emit`'s body: shape-check → produce | refuse. -/
def kEmitExpr : KExpr := .cond KEmit.shapeOk KEmit.produced KEmit.refused

/-- The compiler program: one bare `emit` callable. -/
def kEmit : KProg := {
  graph := [("emit", .bare kEmitExpr)]
  entry := "emit"
  args := [] }

/-! ## The witnessed fixpoint

`SelfHostingOn` restricts the `∀ src` of `SelfHosting` to a declared
corpus — the honest finite witness: `comp` evaluated on each corpus
member (through `emitCall`/`renderC99`) agrees with `emitC99`,
refusals included. The corpus exercises both directions: one
accept, seven different refusal shapes. -/

def SelfHostingOn (emit : KProg → Option String)
    (asCall : KProg → String × List (String × KVal))
    (renderRes : KResult → Option String) (corpus : List KProg) : Prop :=
  ∃ (comp : KProg), ∃ (fuel : Nat),
    ∀ src, src ∈ corpus →
      (asKResult (runK comp.graph [] fuel
        (.invoke (asCall src).1 (asCall src).2))).bind renderRes
        = emit src

/-- The corpus: accept + every refusal shape the subset owns. -/
def koruEmitCorpus : List KProg :=
  [ -- accept: the subset's one shape
    ⟨[("main", .bare (.lit (.int 5)))], "main", []⟩
  , ⟨[("main", .bare (.lit (.int (-3))))], "main", []⟩
    -- refuse: wrong entry name
  , ⟨[("main", .bare (.lit (.int 5)))], "other", []⟩
    -- refuse: entry args present
  , ⟨[("main", .bare (.lit (.int 5)))], "main", [("x", .int 1)]⟩
    -- refuse: graph not singleton
  , ⟨[("main", .bare (.lit (.int 5))), ("aux", .thunk)], "main", []⟩
    -- refuse: callable not a bare int literal (bin expr)
  , ⟨[("main", .bare (.bin .add (.lit (.int 1)) (.lit (.int 2))))],
     "main", []⟩
    -- refuse: the value is not an int (float literal)
  , ⟨[("main", .bare (.lit (.float 1 2)))], "main", []⟩
    -- refuse: not a callable at all in the right slot (thunk)
  , ⟨[("main", .thunk)], "main", []⟩ ]

/-- The witnessed fixpoint: `kEmit` on every corpus member agrees
with `emitC99` — accepted C text byte-for-byte, refusals `none`. -/
theorem koru_emit_fixpoint :
    SelfHostingOn emitC99 emitCall renderC99 koruEmitCorpus := by
  refine ⟨kEmit, 64, ?_⟩
  intro src h
  simp only [koruEmitCorpus, List.mem_cons,
             List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

/-! ## The flow-grammar corpus — the whole declared subset, gated

`koruEmitCorpus` covers the *emission* fixpoint's shapes. This corpus
covers the *flow grammar*: every arm node (`produce`/`retCtor`/
`invoke`/`jump`/terminal), every dispatch path (tag/bare/catchall/
void), guards, labels, oracle leaves — the shapes `korufe` parses and
`krun` decides. Each row carries its own oracle (asserted-call
leaves ride the case row, matching the wire's `(oracle (leaf …))`);
`expect` is generated from `evalKProg`, and `koru_flow_evals` pins
the decided outcomes as a checked fact.

Emission expectation for every row is `refuse` — all of these are
outside `emitC99`'s single-shape subset; their emit legs assert the
refusal. -/

/-- The `tor`-line contract real koru requires — declared params and
branch arms (PARSE006 / KORU021 parity). Declared data, not
inferred: the corpus author states the contract the surface printer
spells and `korufe` checks call-arg names and arm branches against
it. `branches` entries are `name` + optional payload type. -/
structure KDecl where
  /-- `false` = no `tor` line — a legal koru implicit decl (impls
  and call sites are unconstrained when no decl exists). -/
  declared : Bool := true
  params : List (String × String) := []
  branches : List (String × Option String) := []

/-- One flow-grammar corpus row: program + asserted oracle leaves +
the declared `tor` contracts the surface file must carry. -/
structure KFlowRow where
  prog : KProg
  oracle : KOracle := []
  decls : List (String × KDecl) := []
  /-- `true` when the program has no koru surface spelling in the
  subset — the corpus carries the `[flow-eval]` claim as generated
  data rather than a `.k` file.  (Residual `|*` produce arms need a
  metatype binding upstream; the wire's bare catchall has none.) -/
  wire : Bool := false

/-- Subflow + oracle leaf + `when` guard + invoke continuation:
`tick(n:5)` leafs `(go 5)`; guard passes → `dec(4)` → `3`. -/
def flowSubflow : KFlowRow where
  prog := ⟨[
      ("main", .subflow {
          preLabel := none
          head := ("tick", [("n", .lit (.int 5))])
          arms := [ .mk "go" false (some "i")
            (some (.bin .lt (.lit (.int 0)) (.var "i")))
            (some (.invoke "dec"
              [("n", .bin .sub (.var "i") (.lit (.int 1)))])) []
          , .mk "go" false (some "i") none
            (some (.produce (.var "i"))) [] ] })
    , ("tick", .thunk)
    , ("dec", .bare (.bin .sub (.var "n") (.lit (.int 1)))) ],
    "main", []⟩
  oracle := [(("tick", [("n", .int 5)]), ⟨some "go", some (.int 5)⟩)]
  decls := [ ("tick", { params := [("n", "i64")]
                      , branches := [("go", some "i64"), ("stop", none)] })
           , ("dec", { params := [("n", "i64")] }) ]

/-- `#loop` + `@loop` jump: oracle leafs per arg-tuple; the jump
re-enters with `i-1`; guard exit produces `0`. -/
def flowLoop : KFlowRow where
  prog := ⟨[
      ("count", .subflow {
          preLabel := some "loop"
          head := ("tick", [("i", .var "i")])
          arms := [ .mk "next" false (some "i")
            (some (.bin .lt (.lit (.int 0)) (.var "i")))
            (some (.jump "loop"
              [("i", .bin .sub (.var "i") (.lit (.int 1)))])) []
          , .mk "next" false (some "i") none
            (some (.produce (.var "i"))) [] ] })
    , ("tick", .thunk) ],
    "count", [("i", .int 2)]⟩
  oracle := [ (("tick", [("i", .int 2)]), ⟨some "next", some (.int 2)⟩)
           , (("tick", [("i", .int 1)]), ⟨some "next", some (.int 1)⟩)
           , (("tick", [("i", .int 0)]), ⟨some "next", some (.int 0)⟩) ]
  decls := [ ("tick", { params := [("i", "i64")]
                      , branches := [("next", some "i64"), ("stop", none)] }) ]

/-- `=>` retCtor + tag dispatch: `sign` produces a bare bool; the
guarded `ok` arms are the walker's bare-dispatch convention (names
decorative, guards select — the KORU021-relaxed shape). `classify`
declares `pos`/`neg` for the `=>` arms; `main` dispatches on them. -/
def flowCtor : KFlowRow where
  prog := ⟨[
      ("classify", .subflow {
          preLabel := none
          head := ("sign", [("x", .var "x")])
          arms := [ .mk "ok" false (some "p") (some (.var "p"))
            (some (.retCtor "pos" (.var "x"))) []
          , .mk "ok" false (some "_") none
            (some (.retCtor "neg" (.var "x"))) [] ] })
    , ("sign", .bare (.bin .lt (.var "x") (.lit (.int 0))))
    , ("main", .subflow {
          preLabel := none
          head := ("classify", [("x", .lit (.int (-5)))])
          arms := [ .mk "pos" false (some "v") none
            (some (.produce (.var "v"))) []
          , .mk "neg" false (some "v") none
            (some (.produce (.var "v"))) [] ] }) ],
    "main", []⟩
  decls := [ ("sign", { declared := false })
           , ("classify", { params := [("x", "i64")]
                          , branches := [("pos", some "i64")
                                        ,("neg", some "i64")] }) ]

/-- Terminal arm: `| go` with no step ends the chain — `.done`
surfaces as a VOID result `{none, none}`. -/
def flowTerm : KFlowRow where
  prog := ⟨[
      ("main", .subflow {
          preLabel := none
          head := ("tick", [])
          arms := [ .mk "go" false none none none [] ] })
    , ("tick", .thunk) ],
    "main", []⟩
  oracle := [(("tick", []), ⟨some "go", some (.int 0)⟩)]
  decls := [ ("tick", { branches := [("go", some "i64"), ("stop", none)] }) ]

/-- Catchall skipped on tag dispatch: `*` never equals a produced
tag — the named `go` arm wins.  `wire := true`: `|* ->` is refused
upstream (residuals bind through metatypes), so the corpus carries
the claim, not a `.k`. -/
def flowCatchTag : KFlowRow where
  prog := ⟨[
      ("main", .subflow {
          preLabel := none
          head := ("tick", [])
          arms := [ .mk "" true none none
            (some (.produce (.lit (.int 1)))) []
          , .mk "go" false none none
            (some (.produce (.lit (.int 2)))) [] ] })
    , ("tick", .thunk) ],
    "main", []⟩
  oracle := [(("tick", []), ⟨some "go", some (.int 0)⟩)]
  decls := [ ("tick", { branches := [("go", some "i64"), ("stop", none)] }) ]
  wire := true

/-- Catchall hit during bare dispatch refuses outright — the
walker's loud wall. `wire := true`: same residual-arm axis as
flowCatchTag — `dispatchBare` + catchall refuses, and no koru
surface spells that dispatch arm. -/
def flowCatchBare : KFlowRow where
  prog := ⟨[
      ("main", .subflow {
          preLabel := none
          head := ("tick", [])
          arms := [ .mk "" true none none
            (some (.produce (.lit (.int 9)))) [] ] })
    , ("tick", .bare (.lit (.int 5))) ],
    "main", []⟩
  decls := [ ("tick", { declared := false }) ]
  wire := true

/-- Thunk head with an empty oracle — the trust boundary refuses. -/
def flowThunkMiss : KFlowRow where
  prog := ⟨[
      ("main", .subflow {
          preLabel := none
          head := ("tick", [])
          arms := [ .mk "go" false none none
            (some (.produce (.lit (.int 1)))) [] ] })
    , ("tick", .thunk) ],
    "main", []⟩
  decls := [ ("tick", { branches := [("go", some "i64"), ("stop", none)] }) ]

/-- `if(c) a else b` — the conditional expression. -/
def flowCond : KFlowRow where
  prog := ⟨[ ("main", .bare (.cond (.lit (.bool true))
      (.lit (.int 7)) (.lit (.int 8)))) ], "main", []⟩

/-- `++` — string concat. -/
def flowConcat : KFlowRow where
  prog := ⟨[ ("main", .bare (.bin .concat
      (.lit (.str "a")) (.lit (.str "b")))) ], "main", []⟩

/-- `{x: e}.x` — cell literal + field access. -/
def flowCell : KFlowRow where
  prog := ⟨[ ("main", .bare (.field (.lit (.cell [("x", .int 3)]))
      "x")) ], "main", []⟩

/-- `[a, b][i]` — array literal + index. -/
def flowIndex : KFlowRow where
  prog := ⟨[ ("main", .bare (.index
      (.lit (.arr [.int 10, .int 20])) (.lit (.int 1)))) ], "main", []⟩

/-- The corpus as (key, row) pairs — keys become case-row ids and
`flow-*.k` file names. -/
def koruFlowCorpus : List (String × KFlowRow) :=
  [ ("flow-subflow", flowSubflow)
  , ("flow-loop", flowLoop)
  , ("flow-ctor", flowCtor)
  , ("flow-term", flowTerm)
  , ("flow-catchall-tag", flowCatchTag)
  , ("flow-catchall-bare", flowCatchBare)
  , ("flow-thunk-miss", flowThunkMiss)
  , ("flow-cond", flowCond)
  , ("flow-concat", flowConcat)
  , ("flow-cell", flowCell)
  , ("flow-index", flowIndex) ]

/-- The decided outcomes, pinned: what `runK` decides per row is
exactly this — the generated `expect` rows are checked facts, not
hopes. -/
theorem koru_flow_evals :
    (koruFlowCorpus.map fun (_, r) =>
        evalKProg r.prog r.oracle 64) ==
    [ some ⟨none, some (.int 3)⟩            -- subflow
    , some ⟨none, some (.int 0)⟩            -- loop
    , some ⟨none, some (.int (-5))⟩         -- ctor
    , some ⟨none, none⟩                     -- term → void
    , some ⟨none, some (.int 2)⟩            -- catchall-tag
    , none                                  -- catchall-bare
    , none                                  -- thunk-miss
    , some ⟨none, some (.int 7)⟩            -- cond
    , some ⟨none, some (.str "ab")⟩         -- concat
    , some ⟨none, some (.int 3)⟩            -- cell
    , some ⟨none, some (.int 20)⟩ ] := by   -- index
  native_decide

end ISAR
