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
    subset `main = bare e` with `e` a closed integer expression
    (`lit int`, `bin {add,sub,mul,div,mod}`, `un neg` — nested) it
    emits `int main(void) { return <e>; }` through `renderCExpr`.
    Everything else refuses. The emitted fragment is deep inside
    the CompCert-accepted C subset — no VLA/`_Complex`/etc. — so the
    machine-checked leg (`KProg → C99 → CompCert → machine code`)
    stays checkable end to end. `div`/`mod` render to C's `/`/`%`
    because `runK`'s `ktdiv`/`ktmod` are already truncating — the
    same semantics CompCert models.

  * **`kEmit`**: the same emission *in the flow language* — a
    nine-callable `KProg` compiler: `emit`'s gate subflow hands the
    quoted expr to `render`'s recursive walk (lit/bin/un dispatch
    on the expr tag), `op-str` maps op numbers to C symbols, and
    `join4`/`paren-neg`/`wrap` assemble the text. Refusals align
    with `emitC99` because a failed gate or a non-matching render
    arm produces `none` exactly where the pattern match fails —
    structural, not asserted.

  * **The witnessed fixpoint**: `SelfHostingOn` — `SelfHosting`
    restricted to a declared corpus — is discharged by
    `native_decide` over `koruEmitCorpus` (accepts across the
    expression subset + refusal walls in both directions).
    `SelfHostingC99` stays stated at full strength: the `∀ src`
    discharge is the compiler-correctness theorem, a later rung —
    this corpus check is the honest witness, the same discipline
    as the corpus-facing FlowCheck leg.

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
Declared subset: a single-entry graph `[("main", .bare e)]`, entry
`main`, empty args, with `e` in `renderCExpr`'s closed-int subset —
emitted as `int main(void) { return <e>; }`. Everything else
refuses. The emitted fragment is deep inside the CompCert-accepted
C subset — the machine-checked leg
(`KProg → C99 → CompCert → machine code`) stays checkable end to
end. -/

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
that evaluates to a piece of `src`'s quotation. `emit`'s flow binds
the echoed program as `s` (via the `ident` head), so paths navigate
`s`, not `src` — the flow-level spelling. -/
namespace KEmit

def skids : KExpr := qf (.var "s") "kids"
def graphN : KExpr := qi skids 0
def entryN : KExpr := qi skids 1
def argsN : KExpr := qi skids 2
def pair0 : KExpr := qi graphN 0
def callN : KExpr := qf pair0 "v"
def exprN : KExpr := qi (qf callN "kids") 0

/-- `e.kids[i]` inside `render`'s walk (`e` is render's param). -/
def ek (i : Int) : KExpr := qi (qf (.var "e") "kids") i

/-- `emit`'s gate: `src` is `qnode 30 [arr[pair "main" (node27 [_])],
"main", arr[]]` — the *program* shape `emitC99`'s match draws. The
expression subset is `render`'s wall, not this gate's — the same
separation `renderCExpr` draws inside `emitC99`. -/
def shapeOk : KExpr :=
  qand (qeq (qf (.var "s") "tag") (.lit (.int 30))) (
  qand (qeq (qlen skids) (.lit (.int 3))) (
  qand (qeq (qlen graphN) (.lit (.int 1))) (
  qand (qeq (qf pair0 "name") (.lit (.str "main"))) (
  qand (qeq entryN (.lit (.str "main"))) (
  qand (qeq (qlen argsN) (.lit (.int 0))) (
  qand (qeq (qf callN "tag") (.lit (.int 27))) (
        (qeq (qlen (qf callN "kids")) (.lit (.int 1)))
  )))))))

end KEmit

/-- `emit`: gate the program shape on the echoed `src`, then hand
`main`'s expr node to the recursive `render` walk and wrap the
result in the `main` skeleton. Refusal is structural: a failed gate
leaves no `go` arm (refuse); a bad expr kills `render` (refuse) —
the same `none` `emitC99` produces. -/
def kEmitEmit : KCallable := .subflow {
  preLabel := none
  head := ("ident", [("x", .var "src")])
  arms := [ .mk "go" false (some "s") (some KEmit.shapeOk)
      (some (.invoke "render" [("e", KEmit.exprN)]))
      [ .mk "_chain" false (some "c") none
          (some (.invoke "wrap" [("c", .var "c")])) [] ] ] }

/-- `render`: the recursive walk — dispatch on the expr tag,
guarded arms own the subset:

  * `lit`: tag 8 and the value is an int (`kids[0].tag == 1`) →
    `@intToString` of the payload. Float/bool/str/cell/arr values
    fail the guard → refuse.
  * `bin`: tag 10 → `op-str` maps the op number (refusing ops
    outside 0–4), then render each child and `join4` the parens.
  * `un`: tag 11 and op is `neg` (0) → render the child, wrap
    `(-…)`. `not` (1) fails the guard → refuse.
  * every other tag (var 9, cond 12, field 13, index 14, builtin
    15) fails all guards → refuse.

All walls are structural — a non-matching arm `skip`s and the walk
runs out of arms, exactly where `renderCExpr` returns `none`. -/
def kEmitRender : KCallable := .subflow {
  preLabel := none
  head := ("tag-num", [("e", .var "e")])
  arms := [
    .mk "lit" false (some "t")
      (some (qand (qeq (.var "t") (.lit (.int 8)))
                  (qeq (qf (KEmit.ek 0) "tag") (.lit (.int 1)))))
      (some (.produce (qitoa (qi (qf (KEmit.ek 0) "kids") 0)))) []
  , .mk "bin" false (some "t")
      (some (qeq (.var "t") (.lit (.int 10))))
      (some (.invoke "op-str" [("n", KEmit.ek 0)]))
      [ .mk "_chain" false (some "op") none
          (some (.invoke "render" [("e", KEmit.ek 1)]))
          [ .mk "_chain" false (some "l") none
              (some (.invoke "render" [("e", KEmit.ek 2)]))
              [ .mk "_chain" false (some "r") none
                  (some (.invoke "join4"
                    [("l", .var "l"), ("op", .var "op"),
                     ("r", .var "r")]))
                  [] ] ] ]
  , .mk "un" false (some "t")
      (some (qand (qeq (.var "t") (.lit (.int 11)))
                  (qeq (KEmit.ek 0) (.lit (.int 0)))))
      (some (.invoke "render" [("e", KEmit.ek 1)]))
      [ .mk "_chain" false (some "s") none
          (some (.invoke "paren-neg" [("s", .var "s")])) [] ]
  ] }

/-- `op-str`: the arithmetic binop table as a walk — `idnum` echoes
the op number and each arm's `when` selects its C symbol. Ops
outside `0–4` (comparisons, logicals, concat) match no arm →
refuse; the same wall `renderCExpr`'s `sym?` draws. -/
def kEmitOpStr : KCallable := .subflow {
  preLabel := none
  head := ("idnum", [("x", .var "n")])
  arms := [
    .mk "add" false (some "m") (some (qeq (.var "m") (.lit (.int 0))))
      (some (.produce (.lit (.str "+")))) []
  , .mk "sub" false (some "m") (some (qeq (.var "m") (.lit (.int 1))))
      (some (.produce (.lit (.str "-")))) []
  , .mk "mul" false (some "m") (some (qeq (.var "m") (.lit (.int 2))))
      (some (.produce (.lit (.str "*")))) []
  , .mk "div" false (some "m") (some (qeq (.var "m") (.lit (.int 3))))
      (some (.produce (.lit (.str "/")))) []
  , .mk "mod" false (some "m") (some (qeq (.var "m") (.lit (.int 4))))
      (some (.produce (.lit (.str "%")))) []
  ] }

/-- The compiler program — a real multi-callable koru program:
`emit`'s gate → `render`'s recursive walk → the `op-str`/`join4`/
`paren-neg`/`wrap` assembler legs. Nine callables; refusal is
structural throughout, matching `emitC99`'s `Option`. -/
def kEmit : KProg := {
  graph := [
    ("emit", kEmitEmit),
    ("render", kEmitRender),
    ("op-str", kEmitOpStr),
    ("ident", .bare (.var "x")),
    ("tag-num", .bare (qf (.var "e") "tag")),
    ("idnum", .bare (.var "x")),
    ("join4", .bare (qcat (.lit (.str "("))
      (qcat (.var "l") (qcat (.lit (.str " "))
      (qcat (.var "op") (qcat (.lit (.str " "))
      (qcat (.var "r") (.lit (.str ")"))))))))),
    ("paren-neg", .bare (qcat (.lit (.str "(-"))
      (qcat (.var "s") (.lit (.str ")"))))),
    ("wrap", .bare (qcat (.lit (.str "int main(void) { return "))
      (qcat (.var "c") (.lit (.str "; }"))))) ]
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

/-- The corpus: accepts across the expression subset + every
refusal shape it owns — program-shape walls and expression-shape
walls exercised independently, including nested-refusal
propagation (`bin` with a non-subset child). -/
def koruEmitCorpus : List KProg :=
  [ -- accept: closed int arithmetic — lit, all five binops, neg,
    -- nesting
    ⟨[("main", .bare (.lit (.int 5)))], "main", []⟩
  , ⟨[("main", .bare (.lit (.int (-3))))], "main", []⟩
  , ⟨[("main", .bare (.bin .add (.lit (.int 1)) (.lit (.int 2))))],
     "main", []⟩
  , ⟨[("main", .bare (.bin .mul
        (.bin .add (.lit (.int 1)) (.lit (.int 2)))
        (.bin .sub (.lit (.int 10)) (.lit (.int 3)))))], "main", []⟩
  , ⟨[("main", .bare (.bin .div (.lit (.int 10)) (.lit (.int 3))))],
     "main", []⟩
  , ⟨[("main", .bare (.bin .mod (.lit (.int 10)) (.lit (.int 3))))],
     "main", []⟩
  , ⟨[("main", .bare (.un .neg (.lit (.int 4))))], "main", []⟩
  , ⟨[("main", .bare (.un .neg
        (.bin .add (.lit (.int 1)) (.lit (.int 2)))))], "main", []⟩
    -- H2 changed input: boundary literal, deeper mixing, and the
    -- trunc-division witnesses (`ktdiv`/`ktmod` match C `/` `%` on
    -- negative operands — floor-division would diverge here)
  , ⟨[("main", .bare (.lit (.int 2147483647)))], "main", []⟩
  , ⟨[("main", .bare (.bin .sub
        (.bin .mul (.lit (.int 7)) (.lit (.int 8)))
        (.bin .mod (.lit (.int 100)) (.lit (.int 30)))))], "main", []⟩
  , ⟨[("main", .bare (.bin .div
        (.bin .mul (.bin .sub (.lit (.int 8)) (.lit (.int 3)))
          (.bin .add (.lit (.int 2)) (.lit (.int 1))))
        (.bin .sub (.lit (.int 5)) (.lit (.int 2)))))], "main", []⟩
  , ⟨[("main", .bare (.bin .div
        (.un .neg (.lit (.int 7))) (.lit (.int 2))))], "main", []⟩
  , ⟨[("main", .bare (.bin .mod
        (.un .neg (.lit (.int 7))) (.lit (.int 3))))], "main", []⟩
  , ⟨[("main", .bare (.un .neg (.bin .div
        (.un .neg (.lit (.int 9))) (.lit (.int 4)))))], "main", []⟩
    -- refuse: program shape
  , ⟨[("main", .bare (.lit (.int 5)))], "other", []⟩
  , ⟨[("main", .bare (.lit (.int 5)))], "main", [("x", .int 1)]⟩
  , ⟨[("main", .bare (.lit (.int 5))), ("aux", .thunk)], "main", []⟩
    -- refuse: expression subset walls
  , ⟨[("main", .bare (.var "x"))], "main", []⟩
  , ⟨[("main", .bare (.bin .eq (.lit (.int 1)) (.lit (.int 1))))],
     "main", []⟩
  , ⟨[("main", .bare (.un .not (.lit (.bool true))))], "main", []⟩
  , ⟨[("main", .bare (.cond (.lit (.bool true)) (.lit (.int 1))
        (.lit (.int 2))))], "main", []⟩
    -- refuse: nested child outside the subset propagates
  , ⟨[("main", .bare (.bin .add (.lit (.int 1)) (.var "x")))],
     "main", []⟩
  , ⟨[("main", .bare (.lit (.float 1 2)))], "main", []⟩
  , ⟨[("main", .bare (.lit (.str "hi")))], "main", []⟩
  , ⟨[("main", .thunk)], "main", []⟩
    -- refuse: value/expression walls the earlier corpus never
    -- touched — non-int literal kinds and non-renderable nodes
  , ⟨[("main", .bare (.lit (.bool true)))], "main", []⟩
  , ⟨[("main", .bare (.lit (.arr [.int 1, .int 2])))], "main", []⟩
  , ⟨[("main", .bare (.lit (.cell [("x", .int 1)])))], "main", []⟩
  , ⟨[("main", .bare (.field
        (.lit (.cell [("x", .int 1)])) "x"))], "main", []⟩
  , ⟨[("main", .bare (.index
        (.lit (.arr [.int 1, .int 2])) (.lit (.int 0))))], "main", []⟩
    -- `divTrunc` (not `len`): the authority's FlowKernel builtin
    -- table is {as,intCast,truncate,divTrunc,rem,mod} — `len`/
    -- `intToString` are OUR extension axis and undecidable there.
    -- A conformance-unwitnessable claim is worse than a narrower
    -- wall: `divTrunc` lets FlowCheck re-decide the refusal row too.
  , ⟨[("main", .bare (.builtin "divTrunc"
        [.lit (.int 7), .lit (.int 2)]))], "main", []⟩ ]

/-- The witnessed fixpoint: `kEmit` on every corpus member agrees
with `emitC99` — accepted C text byte-for-byte, refusals `none`.
Fuel is sized for the recursive walk: each `render` recursion level
rides invoke frames plus the chain steps. -/
theorem koru_emit_fixpoint :
    SelfHostingOn emitC99 emitCall renderC99 koruEmitCorpus := by
  refine ⟨kEmit, 1024, ?_⟩
  intro src h
  simp only [koruEmitCorpus, List.mem_cons,
             List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl <;>
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
  /-- Return annotation on the `tor` line (`-> string`); `none`
  omits it (koru infers). -/
  ret : Option String := none

/-- `kEmit`'s declared `tor` contracts — every callable's params
and return annotation spelled as data so the surface file is a
real, `koruc`-checked koru program. `expr`/`program`/`string`/
`i64` are koru's own type names. -/
def kEmitDecls : List (String × KDecl) := [
    ("emit", { params := [("src", "program")], ret := some "string" })
  , ("render", { params := [("e", "expr")], ret := some "string" })
  , ("op-str", { params := [("n", "i64")], ret := some "string" })
  , ("ident", { params := [("x", "program")], ret := some "program" })
  , ("tag-num", { params := [("e", "expr")], ret := some "i64" })
  , ("idnum", { params := [("x", "i64")], ret := some "i64" })
  , ("join4", { params := [("l", "string"), ("op", "string"),
                            ("r", "string")], ret := some "string" })
  , ("paren-neg", { params := [("s", "string")], ret := some "string" })
  , ("wrap", { params := [("c", "string")], ret := some "string" }) ]

/-! ## `kLex` — a koru-spelled lexer over char-code arrays

The first frontend-shaped program: `main(chars)` scans an
`(arr int)` of character codes with a bounds-checked `peek`,
classifies each code point through ordered guards, and accumulates
the token stream as `out` sexpr text.  Iteration is tail `invoke`
with empty `conts` — the invoked result propagates — because the
`#label`/`@jump` idiom rebinds only the head call's args while the
flow env stays fixed, and the multi-var scan state (`i`, `out`)
cannot ride a single payload without runtime cell construction
(which nothing in the subset can express).  Recursion depth is the
named boundary: O(input length) nested calls, fuel- and stack-
bounded — the label idiom returns when a payload-carried state
shape exists.

Token map:

* `(`/`)` → `(lparen)` `(rparen)`
* `+` `*` `/` → `(op <code>)`
* `[0-9]+` → `(num <value>)` — folded on the fly
* `[A-Za-z0-9_-]+` → `(atom <start> <len>)` — a span, not a slice:
  no substring builtin exists, so the token is the *location* a
  downstream parser re-indexes.  That is the honest zero-copy
  contract anyway — `-`/`9`-led atoms classify downstream.
* anything else → `(bad <pos> <code>)` in-band and stop — refusal
  as data.

Every form consumed is already modeled: `cond`, `index`, `len`,
`intToString`, `++`, ordered bare dispatch, `#label` + `jump`,
invoke tails.  Nothing new enters the builtin table — this is the
F3 step measured against need, not breadth. -/

def qint (i : Int) : KExpr := .lit (.int i)
def qge (a b : KExpr) : KExpr := .bin .ge a b
def qle (a b : KExpr) : KExpr := .bin .le a b
def qlt (a b : KExpr) : KExpr := .bin .lt a b
def qadd (a b : KExpr) : KExpr := .bin .add a b
def qsub (a b : KExpr) : KExpr := .bin .sub a b
def qmul (a b : KExpr) : KExpr := .bin .mul a b
def qor (a b : KExpr) : KExpr := .bin .or a b

/-- `[0-9]` — a digit code point. -/
def qDigit (c : KExpr) : KExpr :=
  qand (qge c (qint 48)) (qle c (qint 57))

/-- `[A-Za-z0-9_-]` — an atom code point (koru identifiers carry
`-`; `+`/`*`/`/` deliberately stay operators). -/
def qAtom (c : KExpr) : KExpr :=
  qor (qand (qge c (qint 97)) (qle c (qint 122))) (
  qor (qand (qge c (qint 65)) (qle c (qint 90))) (
  qor (qeq c (qint 95)) (
  qor (qeq c (qint 45)) (qDigit c))))

/-- ` ` `\t` `\n` `\r` — whitespace. -/
def qWs (c : KExpr) : KExpr :=
  qor (qeq c (qint 32)) (
  qor (qeq c (qint 9)) (
  qor (qeq c (qint 10)) (qeq c (qint 13))))

/-- `+` `*` `/` — the operator code points this lexer knows. -/
def qOp (c : KExpr) : KExpr :=
  qor (qeq c (qint 43)) (
  qor (qeq c (qint 42)) (qeq c (qint 47)))

/-- The scan loop's recurring self-invoke arg record — `lex`'s
params rebound for the next character. -/
def kScanArgs (i' out' : KExpr) : List (String × KExpr) :=
  [("chars", .var "chars"), ("i", i'), ("n", .var "n"), ("out", out')]

/-- `peek`: bounds-checked `chars[i]` — `-1` at end.  `cond`
evaluates one arm, so the index never runs out of bounds. -/
def kLexPeek : KCallable := .bare
  (.cond (qge (.var "i") (.var "n"))
    (qsub (qint 0) (qint 1))
    (.index (.var "chars") (.var "i")))

/-- `lex`: the scan loop.  Each arm classifies `peek`'s bare code;
`ws`/`lp`/`rp`/`op` tail-invoke `lex` one character on, `dg`/`at`
hand the token to a sub-scanner that re-enters `lex` at the span
end, `bad` produces the in-band refusal. -/
def kLexScan : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "fin" false (some "c") (some (qlt (.var "c") (qint 0)))
      (some (.produce (.var "out"))) []
  , .mk "ws" false (some "c") (some (qWs (.var "c")))
      (some (.invoke "lex" (kScanArgs
        (qadd (.var "i") (qint 1)) (.var "out")))) []
  , .mk "lp" false (some "c") (some (qeq (.var "c") (qint 40)))
      (some (.invoke "lex" (kScanArgs
        (qadd (.var "i") (qint 1))
        (qcat (.var "out") (.lit (.str "(lparen) ")))))) []
  , .mk "rp" false (some "c") (some (qeq (.var "c") (qint 41)))
      (some (.invoke "lex" (kScanArgs
        (qadd (.var "i") (qint 1))
        (qcat (.var "out") (.lit (.str "(rparen) ")))))) []
  , .mk "op" false (some "c") (some (qOp (.var "c")))
      (some (.invoke "lex" (kScanArgs
        (qadd (.var "i") (qint 1))
        (qcat (.var "out") (qcat (.lit (.str "(op "))
          (qcat (qitoa (.var "c")) (.lit (.str ") ")))))))) []
  , .mk "dg" false (some "c") (some (qDigit (.var "c")))
      (some (.invoke "digits"
        [("chars", .var "chars"), ("j", .var "i"), ("n", .var "n"),
         ("v", qint 0), ("out", .var "out")])) []
  , .mk "at" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "atom-end"
        [("chars", .var "chars"), ("i", .var "i"), ("j", .var "i"),
         ("n", .var "n"), ("out", .var "out")])) []
  , .mk "bad" false (some "c") none
      (some (.produce
        (qcat (.var "out") (qcat (.lit (.str "(bad "))
          (qcat (qitoa (.var "i")) (qcat (.lit (.str " "))
            (qcat (qitoa (.var "c")) (.lit (.str ") "))))))))) []
  ] }

/-- `digits`: fold `[0-9]+` into `v`, then tail-invoke `lex` at the
span end appending `(num v)`. -/
def kLexDigits : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "j"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c") (some (qDigit (.var "c")))
      (some (.invoke "digits"
        [("chars", .var "chars"), ("j", qadd (.var "j") (qint 1)),
         ("n", .var "n"),
         ("v", qadd (qmul (.var "v") (qint 10))
                    (qsub (.var "c") (qint 48))),
         ("out", .var "out")])) []
  , .mk "stop" false none none
      (some (.invoke "lex"
        [("chars", .var "chars"), ("i", .var "j"), ("n", .var "n"),
         ("out", qcat (.var "out") (qcat (.lit (.str "(num "))
           (qcat (qitoa (.var "v")) (.lit (.str ") ")))))])) []
  ] }

/-- `atom-end`: extend `[A-Za-z0-9_-]+` from `j`, then tail-invoke
`lex` appending the `(atom start len)` span. -/
def kLexAtomEnd : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "j"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "atom-end"
        [("chars", .var "chars"), ("i", .var "i"),
         ("j", qadd (.var "j") (qint 1)),
         ("n", .var "n"), ("out", .var "out")])) []
  , .mk "stop" false none none
      (some (.invoke "lex"
        [("chars", .var "chars"), ("i", .var "j"), ("n", .var "n"),
         ("out", qcat (.var "out") (qcat (.lit (.str "(atom "))
           (qcat (qitoa (.var "i")) (qcat (.lit (.str " "))
             (qcat (qitoa (qsub (.var "j") (.var "i")))
               (.lit (.str ") ")))))))])) []
  ] }

/-- `main`: hand the entry `chars` to the scanner at `(0, len)`. -/
def kLexMain : KCallable := .subflow {
  preLabel := none
  head := ("lex",
    [("chars", .var "chars"), ("i", qint 0),
     ("n", .builtin "len" [.var "chars"]), ("out", .lit (.str ""))])
  arms := [ .mk "done" false (some "s") none
      (some (.produce (.var "s"))) [] ] }

/-- The lexer program — five callables, jump-loops, invoke tails. -/
def kLex : KProg := {
  graph := [
    ("peek", kLexPeek),
    ("lex", kLexScan),
    ("digits", kLexDigits),
    ("atom-end", kLexAtomEnd),
    ("main", kLexMain) ]
  entry := "main"
  args := [] }

/-- `kLex`'s declared `tor` contracts — `chars` spells koru's own
`[]const i64` slice type (documentary; the wire is untyped), the
rest are `i64`/`string`. -/
def kLexDecls : List (String × KDecl) := [
    ("peek", { params := [("chars", "[]const i64"), ("i", "i64"),
                          ("n", "i64")], ret := some "i64" })
  , ("lex", { params := [("chars", "[]const i64"), ("i", "i64"),
                         ("n", "i64"), ("out", "string")],
              ret := some "string" })
  , ("digits", { params := [("chars", "[]const i64"), ("j", "i64"),
                            ("n", "i64"), ("v", "i64"),
                            ("out", "string")], ret := some "string" })
  , ("atom-end", { params := [("chars", "[]const i64"), ("i", "i64"),
                              ("j", "i64"), ("n", "i64"),
                              ("out", "string")],
                   ret := some "string" })
  , ("main", { params := [("chars", "[]const i64")],
               ret := some "string" }) ]

/-! ## `kSexp` — a koru-spelled sexpr parser/normalizer

The second frontend-shaped program and the first *parser*-shaped
one: `main(chars)` validates and annotates the claim wire's own
grammar — `(`, `)`, atoms, numbers, op code points, whitespace —
emitting a span-tagged tree as `out` text:

    (a (b c) d)  →  (seq (atom 1 2) (seq (atom 4 5) (atom 6 7)) (atom 9 10))

Two shape constraints of the subset made the design, both honest:

* **No pair-return** — a recursive-descent `parse-expr` would need
  `{tree, next-i}` back, and the kernel cannot construct cells
  dynamically.  But sexpr text is self-delimiting, so the parser is
  an *explicit-stack* machine: `depth` is the stack register,
  `(` appends `(seq ` and pushes, `)` appends `)` and pops.  The
  stack a recursive parser would hide in call frames is declared
  data — the honest shape for a dispatch-driven calculus.
* **No `chr`/slice** — nodes print as *spans* `(atom start end)`,
  like real parse trees carrying source locations; downstream
  indexing recovers the text.

Structure is enforced, not just balanced: a bare token at depth 0,
a `)` underflow, a second top-level form (`seen`), and EOF mid-list
all produce in-band `(bad pos code)` — refusal as data, same idiom
as `kLex`.  `need` is the sibling-spacing flag: a token gets a
leading space unless it is a list's first child. -/

/-- `(seq ` / `(num i j)` / `(bad i c)` are appended with a
leading space only between siblings — `need` tracks it. -/
def qGap : KExpr :=
  .cond (qeq (.var "need") (qint 1)) (.lit (.str " ")) (.lit (.str ""))

/-- `out ++ gap ++ text` — the recurring append-with-spacing. -/
def qEmit (text : KExpr) : KExpr :=
  qcat (qcat (.var "out") qGap) text

/-- `out ++ gap ++ "(bad i c)"` — in-band structural refusal. -/
def qBadTok (i c : KExpr) : KExpr :=
  qEmit (qcat (.lit (.str "(bad "))
    (qcat (qitoa i) (qcat (.lit (.str " "))
      (qcat (qitoa c) (.lit (.str ")"))))))

/-- The scan loop's recurring self-invoke arg record — all seven
state slots explicit, as the subset demands. -/
def kSxArgs (i' depth' need' seen' out' : KExpr)
    : List (String × KExpr) :=
  [("chars", .var "chars"), ("i", i'), ("n", .var "n"),
   ("depth", depth'), ("need", need'), ("seen", seen'),
   ("out", out')]

/-- `sx`: the structural scan.  Ordered arms: `fin` accepts only a
completed single top-level form; `lp`/`rp` each have a `-bad` arm
ahead of them for the underflow/repeated-topform cases; `tok-bad`
ahead of `dg`/`at`/`op` enforces tokens-inside-lists; `bad` is the
code-point catchall. -/
def kSexpScan : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "fin" false (some "c") (some (qlt (.var "c") (qint 0)))
      (some (.produce
        (.cond (qand (qeq (.var "depth") (qint 0))
                     (qeq (.var "seen") (qint 1)))
          (.var "out")
          (qBadTok (.var "n") (qsub (qint 0) (qint 1)))))) []
  , .mk "ws" false (some "c") (some (qWs (.var "c")))
      (some (.invoke "sx" (kSxArgs
        (qadd (.var "i") (qint 1)) (.var "depth") (.var "need")
        (.var "seen") (.var "out")))) []
  , .mk "lp-bad" false (some "c")
      (some (qand (qeq (.var "c") (qint 40))
        (qand (qeq (.var "depth") (qint 0))
             (qeq (.var "seen") (qint 1)))))
      (some (.produce (qBadTok (.var "i") (.var "c")))) []
  , .mk "lp" false (some "c") (some (qeq (.var "c") (qint 40)))
      (some (.invoke "sx" (kSxArgs
        (qadd (.var "i") (qint 1)) (qadd (.var "depth") (qint 1))
        (qint 0) (qint 1)
        (qEmit (.lit (.str "(seq ")))))) []
  , .mk "rp-bad" false (some "c")
      (some (qand (qeq (.var "c") (qint 41))
                  (qeq (.var "depth") (qint 0))))
      (some (.produce (qBadTok (.var "i") (.var "c")))) []
  , .mk "rp" false (some "c") (some (qeq (.var "c") (qint 41)))
      (some (.invoke "sx" (kSxArgs
        (qadd (.var "i") (qint 1)) (qsub (.var "depth") (qint 1))
        (qint 1) (.var "seen")
        (qcat (.var "out") (.lit (.str ")")))))) []
  , .mk "tok-bad" false (some "c")
      (some (qand (qor (qDigit (.var "c"))
                       (qor (qAtom (.var "c")) (qOp (.var "c"))))
                  (qeq (.var "depth") (qint 0))))
      (some (.produce (qBadTok (.var "i") (.var "c")))) []
  , .mk "dg" false (some "c") (some (qDigit (.var "c")))
      (some (.invoke "num"
        [("chars", .var "chars"), ("i", .var "i"), ("j", .var "i"),
         ("n", .var "n"), ("depth", .var "depth"),
         ("need", .var "need"), ("seen", .var "seen"),
         ("out", .var "out")])) []
  , .mk "at" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "atom"
        [("chars", .var "chars"), ("i", .var "i"), ("j", .var "i"),
         ("n", .var "n"), ("depth", .var "depth"),
         ("need", .var "need"), ("seen", .var "seen"),
         ("out", .var "out")])) []
  , .mk "op" false (some "c") (some (qOp (.var "c")))
      (some (.invoke "sx" (kSxArgs
        (qadd (.var "i") (qint 1)) (.var "depth") (qint 1)
        (.var "seen")
        (qEmit (qcat (.lit (.str "(op "))
          (qcat (qitoa (.var "i")) (qcat (.lit (.str " "))
            (qcat (qitoa (qadd (.var "i") (qint 1)))
              (.lit (.str ")")))))))))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qBadTok (.var "i") (.var "c")))) []
  ] }

/-- `num`: extend the digit run from `j`, then re-enter `sx` at the
span end emitting `(num start end)`. -/
def kSexpNum : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "j"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c") (some (qDigit (.var "c")))
      (some (.invoke "num"
        [("chars", .var "chars"), ("i", .var "i"),
         ("j", qadd (.var "j") (qint 1)), ("n", .var "n"),
         ("depth", .var "depth"), ("need", .var "need"),
         ("seen", .var "seen"), ("out", .var "out")])) []
  , .mk "stop" false none none
      (some (.invoke "sx"
        (kSxArgs (.var "j") (.var "depth") (qint 1) (.var "seen")
          (qEmit (qcat (.lit (.str "(num "))
            (qcat (qitoa (.var "i")) (qcat (.lit (.str " "))
              (qcat (qitoa (.var "j")) (.lit (.str ")")))))))))) []
  ] }

/-- `atom`: extend the atom run from `j`, then re-enter `sx`
emitting `(atom start end)`. -/
def kSexpAtom : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "j"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "atom"
        [("chars", .var "chars"), ("i", .var "i"),
         ("j", qadd (.var "j") (qint 1)), ("n", .var "n"),
         ("depth", .var "depth"), ("need", .var "need"),
         ("seen", .var "seen"), ("out", .var "out")])) []
  , .mk "stop" false none none
      (some (.invoke "sx"
        (kSxArgs (.var "j") (.var "depth") (qint 1) (.var "seen")
          (qEmit (qcat (.lit (.str "(atom "))
            (qcat (qitoa (.var "i")) (qcat (.lit (.str " "))
              (qcat (qitoa (.var "j")) (.lit (.str ")")))))))))) []
  ] }

/-- `main`: hand `chars` to the structural scan in its initial
state — depth 0, no siblings, no top-level form seen. -/
def kSexpMain : KCallable := .subflow {
  preLabel := none
  head := ("sx",
    [("chars", .var "chars"), ("i", qint 0),
     ("n", .builtin "len" [.var "chars"]), ("depth", qint 0),
     ("need", qint 0), ("seen", qint 0), ("out", .lit (.str ""))])
  arms := [ .mk "done" false (some "s") none
      (some (.produce (.var "s"))) [] ] }

/-- The sexpr parser program — five callables sharing `peek`. -/
def kSexp : KProg := {
  graph := [
    ("peek", kLexPeek),
    ("sx", kSexpScan),
    ("num", kSexpNum),
    ("atom", kSexpAtom),
    ("main", kSexpMain) ]
  entry := "main"
  args := [] }

/-- `kSexp`'s declared `tor` contracts. -/
def kSexpDecls : List (String × KDecl) := [
    ("peek", { params := [("chars", "[]const i64"), ("i", "i64"),
                          ("n", "i64")], ret := some "i64" })
  , ("sx", { params := [("chars", "[]const i64"), ("i", "i64"),
                        ("n", "i64"), ("depth", "i64"),
                        ("need", "i64"), ("seen", "i64"),
                        ("out", "string")], ret := some "string" })
  , ("num", { params := [("chars", "[]const i64"), ("i", "i64"),
                         ("j", "i64"), ("n", "i64"), ("depth", "i64"),
                         ("need", "i64"), ("seen", "i64"),
                         ("out", "string")], ret := some "string" })
  , ("atom", { params := [("chars", "[]const i64"), ("i", "i64"),
                          ("j", "i64"), ("n", "i64"), ("depth", "i64"),
                          ("need", "i64"), ("seen", "i64"),
                          ("out", "string")], ret := some "string" })
  , ("main", { params := [("chars", "[]const i64")],
               ret := some "string" }) ]

/-! ## `kAst` — a koru-spelled surface parser → flat AST rows

The third frontend TU and the first to consume *koru surface*:
`main(chars)` parses the item-level grammar our generated corpus
exercises — `tor` declarations, `->` immediate impls, `=` flow
impls with head invocations and `|` arm bars — and emits flat node
rows over source *spans*:

    tor main {x: i64} -> i64
    main -> if((x > 0)) x else (0 - x)

      →  (ev 4 8) (fld 11 12 14 17) (ret 22 25) (impl 27 31 35 52)

Every name/type/expression is a `(start end)` span — the shape the
authority's own `ast_json` uses too (its `condition`, `arg.value`,
`plain_value` fields are verbatim source text; spans are the
zero-copy equivalent).  The race leg in `check.py` normalizes
`koruc --ast-json` to this row format and diffs — same structure,
same spans, independent derivations.

### Architecture under the subset's walls

* **Int-returning flows** (`ws`, `word`, `toeol`, `toarrow`,
  `toargend`, `typend`, `kwtor`) produce a *position* — a single
  `i64`, the only carryable payload.  Rules that need a token's
  span hold its start in env while a helper scans its end:
  `| e |> rule(chars, j, e, ...)` — the pair rides two legs.
* **`depth`/`ins` registers** in `toargend` are the explicit-stack
  trick again — paren nesting and in-string state as data.
* Ordering in arms implements lookahead-free dispatch; `-bad`
  variants first, catchall `bad` last — refusal as data. -/

/-- `ws`: whitespace and `//` line comments → next significant
index.  The comment tail is a sub-flow re-entering `ws` — a comment
only suspends skipping, it doesn't end it. -/
def kAstWs : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "ws" false (some "c") (some (qWs (.var "c")))
      (some (.invoke "ws"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) []
  , .mk "cm" false (some "c")
      (some (qand (qeq (.var "c") (qint 47))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 47))))
      (some (.invoke "comment"
        [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])) []
  , .mk "stop" false (some "c") none
      (some (.produce (.var "i"))) [] ] }

/-- `comment`: inside `//` — consume to newline, then re-enter `ws`
at the newline (it re-classifies as whitespace). -/
def kAstComment : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c")
      (some (qand (qge (.var "c") (qint 0))
                  (.un .not (qeq (.var "c") (qint 10)))))
      (some (.invoke "comment"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) []
  , .mk "eol" false (some "c") none
      (some (.invoke "ws"
        [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])) []
  ] }

/-- `word`: an atom run's end — `[A-Za-z0-9_-]+` starting at `i`. -/
def kAstWord : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) []
  , .mk "stop" false (some "c") none
      (some (.produce (.var "i"))) [] ] }

/-- `toeol`: scan to newline or EOF — the impl/variant tail span's
end.  Single-line expressions only (multi-line expr bodies are a
named axis, not silently consumed). -/
def kAstToEol : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c")
      (some (qand (qge (.var "c") (qint 0))
                  (.un .not (qeq (.var "c") (qint 10)))))
      (some (.invoke "toeol"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) []
  , .mk "stop" false (some "c") none
      (some (.produce (.var "i"))) [] ] }

/-- `toarrow`: scan to the tail token — `->`, `|>`, or `=>`, since
produce-, step-, and ctor-arms all carry `when` guards.  The
returned position is the condition's end; the token itself is
re-classified by `arm-tok`.  (Nested tokens inside condition
parens/strings is a named axis — no depth tracking.) -/
def kAstToArrow : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "arr" false (some "c")
      (some (qand (qeq (.var "c") (qint 45))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.produce (.var "i"))) []
  , .mk "stp" false (some "c")
      (some (qand (qeq (.var "c") (qint 124))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.produce (.var "i"))) []
  , .mk "ctr" false (some "c")
      (some (qand (qeq (.var "c") (qint 61))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.produce (.var "i"))) []
  , .mk "more" false (some "c") none
      (some (.invoke "toarrow"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) [] ] }

/-- `toargend`: scan an arg *value* to its `,` or `)` at paren
depth 0 — `d` is the explicit stack, `ins` the in-string flag
(`"` toggles it; `bs` skips the byte after `\` so `\"` stays
inside the string — upstream lexer parity). -/
def kAstToArgEnd : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "fin" false (some "c") (some (qlt (.var "c") (qint 0)))
      (some (.produce (.var "i"))) []
  , .mk "str" false (some "c") (some (qeq (.var "c") (qint 34)))
      (some (.invoke "toargend"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n"),
         ("d", .var "d"),
         ("ins", .cond (qeq (.var "ins") (qint 1))
                       (qint 0) (qint 1))])) []
  , .mk "bs" false (some "c")
      (some (qand (qeq (.var "ins") (qint 1))
                  (qeq (.var "c") (qint 92))))
      (some (.invoke "toargend"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 2)), ("n", .var "n"),
         ("d", .var "d"), ("ins", .var "ins")])) []
  , .mk "deep" false (some "c")
      (some (qand (qeq (.var "ins") (qint 0))
                  (qeq (.var "c") (qint 40))))
      (some (.invoke "toargend"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n"),
         ("d", qadd (.var "d") (qint 1)), ("ins", .var "ins")])) []
  , .mk "end" false (some "c")
      (some (qand (qeq (.var "ins") (qint 0))
        (qand (qeq (.var "d") (qint 0))
          (qor (qeq (.var "c") (qint 44)) (qeq (.var "c") (qint 41))))))
      (some (.produce (.var "i"))) []
  , .mk "shal" false (some "c")
      (some (qand (qeq (.var "ins") (qint 0))
                  (qeq (.var "c") (qint 41))))
      (some (.invoke "toargend"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n"),
         ("d", qsub (.var "d") (qint 1)), ("ins", .var "ins")])) []
  , .mk "more" false (some "c") none
      (some (.invoke "toargend"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n"),
         ("d", .var "d"), ("ins", .var "ins")])) [] ] }

/-- `typend`: a type annotation's end — scan to `,` or `}` (`[]const`
brackets pass through; param types carry no parens in the subset). -/
def kAstTypEnd : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "stop" false (some "c")
      (some (qor (qeq (.var "c") (qint 44))
                (qeq (.var "c") (qint 125))))
      (some (.produce (.var "i"))) []
  , .mk "fin" false (some "c") (some (qlt (.var "c") (qint 0)))
      (some (.produce (.var "i"))) []
  , .mk "more" false (some "c") none
      (some (.invoke "typend"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) [] ] }

/-- `kwtor`: is `(j,e)` the `tor` keyword — a `.bare` int predicate
since the whole check is expr-level. -/
def kAstKwTor : KCallable := .bare
  (.cond
    (qand (qeq (.var "e") (qadd (.var "j") (qint 3)))
      (qand (qeq (.index (.var "chars") (.var "j")) (qint 116))
        (qand (qeq (.index (.var "chars") (qadd (.var "j") (qint 1)))
                   (qint 111))
             (qeq (.index (.var "chars") (qadd (.var "j") (qint 2)))
                   (qint 114)))))
    (qint 1) (qint 0))

/-- `kwwhen`: is `(j,e)` the `when` keyword — arm-guard dispatch. -/
def kAstKwWhen : KCallable := .bare
  (.cond
    (qand (qeq (.var "e") (qadd (.var "j") (qint 4)))
      (qand (qeq (.index (.var "chars") (.var "j")) (qint 119))
        (qand (qeq (.index (.var "chars") (qadd (.var "j") (qint 1)))
                   (qint 104))
          (qand (qeq (.index (.var "chars") (qadd (.var "j") (qint 2)))
                     (qint 101))
               (qeq (.index (.var "chars") (qadd (.var "j") (qint 3)))
                     (qint 110))))))
    (qint 1) (qint 0))

/-- `kwimport`: is `(j,e)` the `import` keyword — the second
top-level dispatch after `tor`. -/
def kAstKwImport : KCallable := .bare
  (.cond
    (qand (qeq (.var "e") (qadd (.var "j") (qint 6)))
      (qand (qeq (.index (.var "chars") (.var "j")) (qint 105))
        (qand (qeq (.index (.var "chars") (qadd (.var "j") (qint 1)))
                   (qint 109))
          (qand (qeq (.index (.var "chars") (qadd (.var "j") (qint 2)))
                     (qint 112))
            (qand (qeq (.index (.var "chars")
                            (qadd (.var "j") (qint 3))) (qint 111))
              (qand (qeq (.index (.var "chars")
                              (qadd (.var "j") (qint 4))) (qint 114))
                (qeq (.index (.var "chars")
                          (qadd (.var "j") (qint 5))) (qint 116))))))))
    (qint 1) (qint 0))

/-- `hws`: *horizontal* whitespace only — space/tab.  Branch
declarations decide "type follows" by whether the next non-space
char is still on the same line. -/
def kAstHws : KCallable := .subflow {
  preLabel := none
  head := ("peek",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [
    .mk "more" false (some "c")
      (some (qor (qeq (.var "c") (qint 32)) (qeq (.var "c") (qint 9))))
      (some (.invoke "hws"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")])) []
  , .mk "stop" false (some "c") none
      (some (.produce (.var "i"))) [] ] }

/-! ### kAst row emission — `(kind i j …) ` appended to `out`,
trailing-space convention as kLex/kSexp. -/

/-- `(KIND a) ` row. -/
def qRow1 (k : String) (a : KExpr) : KExpr :=
  qcat (.var "out") (qcat (.lit (.str ("(" ++ k ++ " ")))
    (qcat (qitoa a) (.lit (.str ") "))))

/-- `(KIND a b) ` row. -/
def qRow2 (k : String) (a b : KExpr) : KExpr :=
  qcat (.var "out") (qcat (.lit (.str ("(" ++ k ++ " ")))
    (qcat (qitoa a) (qcat (.lit (.str " "))
      (qcat (qitoa b) (.lit (.str ") "))))))

/-- `(KIND a b c d) ` row. -/
def qRow4 (k : String) (a b c d : KExpr) : KExpr :=
  qcat (.var "out") (qcat (.lit (.str ("(" ++ k ++ " ")))
    (qcat (qitoa a) (qcat (.lit (.str " ")) (qcat (qitoa b)
      (qcat (.lit (.str " ")) (qcat (qitoa c)
        (qcat (.lit (.str " ")) (qcat (qitoa d)
          (.lit (.str ") "))))))))))

/-- `(bad i c) ` — structural refusal row. -/
def qAstBad (i c : KExpr) : KExpr := qRow2 "bad" i c

/-- `(KIND TAG a b) ` row — `TAG` a literal atom (step kinds). -/
def qRowS (k t : String) (a b : KExpr) : KExpr :=
  qcat (.var "out") (qcat (.lit (.str ("(" ++ k ++ " " ++ t ++ " ")))
    (qcat (qitoa a) (qcat (.lit (.str " "))
      (qcat (qitoa b) (.lit (.str ") "))))))

/-- `(KIND a b) ` row TEXT — no `out` prefix; for composing a
second row onto an already-extended `out`. -/
def qRowTxt (k : String) (a b : KExpr) : KExpr :=
  qcat (.lit (.str ("(" ++ k ++ " ")))
    (qcat (qitoa a) (qcat (.lit (.str " "))
      (qcat (qitoa b) (.lit (.str ") ")))))

/-- `next` invoked with the standard state — `chars`, position
under `i`, `n`, `out` — plus extra spans the rule needs.  An
`("out", _)` in `extra` REPLACES the default (row emission), so a
single name never appears twice.  Convention: the position param
of every flow is `i`; other names are real extra spans. -/
def qNext (i' : KExpr) (extra : List (String × KExpr))
    : List (String × KExpr) :=
  [("chars", .var "chars"), ("i", i'), ("n", .var "n")]
    ++ (if extra.any (·.1 == "out") then [] else [("out", .var "out")])
    ++ extra

/-- `H(args) | bind |> NEXT(nextArgs)` — the one-dispatch chain a
sequence rule collapses to (`ws`/`word`/`typend` results feed the
next rule's position). -/
def qSeq (h : String × List (String × KExpr)) (bind : String)
    (next : String) (nextArgs : List (String × KExpr)) : KCallable :=
  .subflow {
    preLabel := none
    head := h
    arms := [.mk "go" false (some bind) none
      (some (.invoke next nextArgs)) []] }

/-- `ws` invoked at `i` — chain head for "skip trivia then …". -/
def qWsAt (i' : KExpr) : String × List (String × KExpr) :=
  ("ws", [("chars", .var "chars"), ("i", i'), ("n", .var "n")])

/-- `word` invoked at `i`. -/
def qWordAt (i' : KExpr) : List (String × KExpr) :=
  [("chars", .var "chars"), ("i", i'), ("n", .var "n")]

/-- `peek` invoked at `i`. -/
def qPeekAt (i' : KExpr) : List (String × KExpr) :=
  [("chars", .var "chars"), ("i", i'), ("n", .var "n")]

/-- `top`: the item dispatcher's ws leg. -/
def kAstTop : KCallable :=
  qSeq (qWsAt (.var "i")) "j" "top-at" (qNext (.var "j") [])

/-- `top-at`: classify the token — EOF ends, an atom-char starts a
word (whose end `e` re-enters at `kwd`), anything else is a
structural refusal. -/
def kAstTopAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "fin" false (some "c") (some (qlt (.var "c") (qint 0)))
      (some (.produce (.var "out"))) []
  , .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "e" false (some "e") none
          (some (.invoke "kwd"
            (qNext (.var "i") [("e", .var "e")]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `kwd`: `tor` opens a declaration; other words chain to `kwd2`
for the `import`/item-name split.  `i` is the word's start, `e`
its end. -/
def kAstKwd : KCallable := .subflow {
  preLabel := none
  head := ("kwtor",
    [("chars", .var "chars"), ("j", .var "i"), ("e", .var "e"),
     ("n", .var "n")])
  arms := [
    .mk "decl" false (some "k") (some (qeq (.var "k") (qint 1)))
      (some (.invoke "decl" (qNext (.var "e") []))) []
  , .mk "item" false (some "k") none
      (some (.invoke "kwd2" (qNext (.var "i") [("e", .var "e")]))) [] ] }

/-- `kwd2`: `import` opens a path row; any other word is an item
name → impl-or-flow. -/
def kAstKwd2 : KCallable := .subflow {
  preLabel := none
  head := ("kwimport",
    [("chars", .var "chars"), ("j", .var "i"), ("e", .var "e"),
     ("n", .var "n")])
  arms := [
    .mk "imp" false (some "k") (some (qeq (.var "k") (qint 1)))
      (some (.invoke "imp-path" (qNext (.var "e") []))) []
  , .mk "item" false (some "k") none
      (some (.invoke "morf" (qNext (.var "e")
        [("j", .var "i"), ("ne", .var "e")]))) [] ] }

/-- `imp-path`: ws, then the import path runs to end-of-line —
`(imp …)` row and back to `top`. -/
def kAstImpPath : KCallable :=
  qSeq (qWsAt (.var "i")) "p" "imp-path2" (qNext (.var "p") [])

/-- `imp-path2`. -/
def kAstImpPath2 : KCallable := .subflow {
  preLabel := none
  head := ("toeol",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "p1") none
      (some (.invoke "top"
        (qNext (.var "p1")
          [("out", qRow2 "imp" (.var "i") (.var "p1"))]))) [] ] }

/-- `morf`: `name ->` immediate impl or `name =` flow — ws between
name and the `->`/`=` marker.  `j`/`ne` carry the name span. -/
def kAstMorf : KCallable :=
  qSeq (qWsAt (.var "i")) "s" "morf-at"
    (qNext (.var "s") [("j", .var "j"), ("ne", .var "ne")])

/-- `morf-at`: `-`+`>` is `->` impl; `=` not followed by `>` is a
flow head.  (`=>` refused: ctor impls are outside the subset.) -/
def kAstMorfAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "impl" false (some "c")
      (some (qand (qeq (.var "c") (qint 45))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.invoke "impl-body" (qNext (qadd (.var "i") (qint 2))
        [("j", .var "j"), ("ne", .var "ne")]))) []
  , .mk "flow" false (some "c")
      (some (qand (qeq (.var "c") (qint 61))
        (.un .not (qeq (.index (.var "chars")
                            (qadd (.var "i") (qint 1))) (qint 62)))))
      (some (.invoke "flow-pre" (qNext (qadd (.var "i") (qint 1))
        [("j", .var "j"), ("ne", .var "ne")]))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `impl-body`: ws then the value runs to end-of-line. -/
def kAstImplBody : KCallable :=
  qSeq (qWsAt (.var "i")) "v0" "impl-val"
    (qNext (.var "v0") [("j", .var "j"), ("ne", .var "ne")])

/-- `impl-val`: `toeol` bounds the value span; emit `(impl …)` and
re-enter `top` at the value's end. -/
def kAstImplVal : KCallable := .subflow {
  preLabel := none
  head := ("toeol",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "v1") none
      (some (.invoke "top"
        (qNext (.var "v1")
          [("out", qRow4 "impl" (.var "j") (.var "ne")
                            (.var "i") (.var "v1"))]))) [] ] }

/-- `flow-pre`: after `=` — ws, then `#label` or the head
callable. -/
def kAstFlowPre : KCallable :=
  qSeq (qWsAt (.var "i")) "p" "flow-pre0"
    (qNext (.var "p") [("j", .var "j"), ("ne", .var "ne")])

/-- `flow-pre0`: the post-`=` token — `#` opens a label, an atom
char the head callable.  `j`/`ne` carry the flow's name span. -/
def kAstFlowPre0 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "lbl" false (some "c") (some (qeq (.var "c") (qint 35)))
      (some (.invoke "word" (qWordAt (qadd (.var "i") (qint 1)))))
      [ .mk "le" false (some "le") none
          (some (.invoke "flow-lbl"
            (qNext (.var "le")
              [("j", .var "j"), ("ne", .var "ne"),
               ("out", qRow2 "lbl"
                 (qadd (.var "i") (qint 1)) (.var "le"))]))) [] ]
  , .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "he" false (some "he") none
          (some (.invoke "call-open"
            (qNext (.var "he")
              [("out", qcat
                 (qRow2 "flw" (.var "j") (.var "ne"))
                 (qRowTxt "call" (.var "i") (.var "he")))]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `flow-lbl`: `#label` consumed — ws, then the head callable. -/
def kAstFlowLbl : KCallable :=
  qSeq (qWsAt (.var "i")) "h" "flow-pre2"
    (qNext (.var "h") [("j", .var "j"), ("ne", .var "ne")])

/-- `flow-pre2`: the head callable word after a `#label`. -/
def kAstFlowPre2 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "he" false (some "he") none
          (some (.invoke "call-open"
            (qNext (.var "he")
              [("out", qcat
                 (qRow2 "flw" (.var "j") (.var "ne"))
                 (qRowTxt "call" (.var "i") (.var "he")))]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `call-open`: `(flw …)(call …)`/`(step …)` rows are appended;
skip ws and require `(`, else structural refusal. -/
def kAstCallOpen : KCallable :=
  qSeq (qWsAt (.var "i")) "a" "call-at" (qNext (.var "a") [])

/-- `call-at`: `(` opens the arg list, else bad. -/
def kAstCallAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "open" false (some "c") (some (qeq (.var "c") (qint 40)))
      (some (.invoke "args" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `args`: the invocation arg loop — ws, then `)` closes into
`armloop` or an arg (named `x:` or positional). -/
def kAstArgs : KCallable :=
  qSeq (qWsAt (.var "i")) "a" "args-at" (qNext (.var "a") [])

/-- `args-at`. -/
def kAstArgsAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "close" false (some "c") (some (qeq (.var "c") (qint 41)))
      (some (.invoke "armloop" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "we" false (some "we") none
          (some (.invoke "argname"
            (qNext (.var "i") [("we", .var "we")]))) [] ]
  , .mk "pos" false (some "c") none
      (some (.invoke "argval" (qNext (.var "i") []))) [] ] }

/-- `argname`: word scanned — ws to the `:` decision point.  `i`
is the word's start, `we` its end. -/
def kAstArgName : KCallable :=
  qSeq (qWsAt (.var "we")) "d" "argname-at"
    (qNext (.var "d") [("aj", .var "i"), ("ae", .var "we")])

/-- `argname-at`: `:` makes the word a name; anything else means
the word was the value's head — rescan the value from its start. -/
def kAstArgNameAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "named" false (some "c") (some (qeq (.var "c") (qint 58)))
      (some (.invoke "ws"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")]))
      [ .mk "v0" false (some "v0") none
          (some (.invoke "argvaln"
            (qNext (.var "v0")
              [("aj", .var "aj"), ("ae", .var "ae")]))) [] ]
  , .mk "pos" false (some "c") none
      (some (.invoke "argval" (qNext (.var "aj") []))) [] ] }

/-- `argvaln`: a named arg — `toargend` bounds the value; emit
`(arg nj ne v0 v1)`. -/
def kAstArgValN : KCallable := .subflow {
  preLabel := none
  head := ("toargend",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n"),
     ("d", qint 0), ("ins", qint 0)])
  arms := [ .mk "done" false (some "v1") none
      (some (.invoke "argnext"
        (qNext (.var "v1")
          [("out", qRow4 "arg" (.var "aj") (.var "ae")
                            (.var "i") (.var "v1"))]))) [] ] }

/-- `argval`: a positional arg — `(arg 0 0 v0 v1)` marks the
unnamed name-span; the normalizer re-lexes `chars[v0:v1]` to
recognize authority puns. -/
def kAstArgVal : KCallable := .subflow {
  preLabel := none
  head := ("toargend",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n"),
     ("d", qint 0), ("ins", qint 0)])
  arms := [ .mk "done" false (some "v1") none
      (some (.invoke "argnext"
        (qNext (.var "v1")
          [("out", qRow4 "arg" (qint 0) (qint 0)
                            (.var "i") (.var "v1"))]))) [] ] }

/-- `argnext`: after a value — `,` loops, `)` closes to `postcall`
(the retbind decision point). -/
def kAstArgNext : KCallable :=
  qSeq (qWsAt (.var "i")) "d" "argnext-at" (qNext (.var "d") [])

/-- `argnext-at`. -/
def kAstArgNextAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "more" false (some "c") (some (qeq (.var "c") (qint 44)))
      (some (.invoke "args" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "close" false (some "c") (some (qeq (.var "c") (qint 41)))
      (some (.invoke "postcall" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `postcall`: horizontal ws after a call's `)` — a `:` opens a
retbind; anything else ends the arm/call into `armloop`. -/
def kAstPostCall : KCallable :=
  qSeq ("hws",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
    "p" "postcall-at" (qNext (.var "p") [])

/-- `postcall-at`. -/
def kAstPostCallAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "rb" false (some "c") (some (qeq (.var "c") (qint 58)))
      (some (.invoke "rb-word" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "done" false (some "c") none
      (some (.invoke "armloop" (qNext (.var "i") []))) [] ] }

/-- `rb-word`: ws to the result name of `: name`. -/
def kAstRbWord : KCallable :=
  qSeq (qWsAt (.var "i")) "w" "rb-word-at" (qNext (.var "w") [])

/-- `rb-word-at`: the name word — `(rbind w we)`; the tail then
requires `|>` (`->`/`=>` after a retbind is a named axis). -/
def kAstRbWordAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "we" false (some "we") none
          (some (.invoke "rb-tail"
            (qNext (.var "we")
              [("out", qRow2 "rbind" (.var "i") (.var "we"))]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `rb-tail`: horizontal ws after the name — `|>` recurses into
the step chain (its `)` lands back at `postcall`, so `: a |> : b`
chains work). -/
def kAstRbTail : KCallable :=
  qSeq ("hws",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
    "t" "rb-tail-at" (qNext (.var "t") [])

/-- `rb-tail-at`. -/
def kAstRbTailAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "step" false (some "c")
      (some (qand (qeq (.var "c") (qint 124))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.invoke "arm-step"
        (qNext (qadd (.var "i") (qint 2)) []))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `armloop`: between arm bars and the next item — `|` (not `|>`)
opens an arm; anything else is the next item for `top`. -/
def kAstArmLoop : KCallable :=
  qSeq (qWsAt (.var "i")) "a" "armloop-at" (qNext (.var "a") [])

/-- `armloop-at`. -/
def kAstArmLoopAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "bar" false (some "c")
      (some (qand (qeq (.var "c") (qint 124))
        (.un .not (qeq (.index (.var "chars")
                            (qadd (.var "i") (qint 1))) (qint 62)))))
      (some (.invoke "arm" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "item" false (some "c") none
      (some (.invoke "top-at" (qNext (.var "i") []))) [] ] }

/-- `arm`: the branch word opens a continuation row. -/
def kAstArm : KCallable :=
  qSeq (qWsAt (.var "i")) "b" "arm1" (qNext (.var "b") [])

/-- `arm1`: branch word, then the tail decides. -/
def kAstArm1 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "be" false (some "be") none
          (some (.invoke "arm-tail"
            (qNext (.var "be")
              [("out", qRow2 "cont" (.var "i") (.var "be"))]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `arm-tail`: after the branch — `when`, a bind word, `->`
produce, `|>` step, `=>` ctor, or end-of-line (bare terminal arm).
Horizontal ws only — a newline ends the arm; the next `|` or item
is `armloop`'s job.  Shared tail for post-branch/post-bind. -/
def kAstArmTail : KCallable :=
  qSeq ("hws",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
    "t" "arm-tok" (qNext (.var "t") [])

/-- `arm-tok`: classify the tail token.  `->`/`|`>`/`=>` precede
the word arm — `-` is itself an atom char, so order does the
lookahead.  A bare line-end is a terminal arm → `armloop`. -/
def kAstArmTok : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "prod" false (some "c")
      (some (qand (qeq (.var "c") (qint 45))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.invoke "arm-prod"
        (qNext (qadd (.var "i") (qint 2)) []))) []
  , .mk "step" false (some "c")
      (some (qand (qeq (.var "c") (qint 124))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.invoke "arm-step"
        (qNext (qadd (.var "i") (qint 2)) []))) []
  , .mk "ctor" false (some "c")
      (some (qand (qeq (.var "c") (qint 61))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.invoke "arm-ctor"
        (qNext (qadd (.var "i") (qint 2)) []))) []
  , .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "we" false (some "we") none
          (some (.invoke "arm-kw"
            (qNext (.var "i") [("we", .var "we")]))) [] ]
  , .mk "eol" false (some "c")
      (some (qor (qeq (.var "c") (qint 10)) (qlt (.var "c") (qint 0))))
      (some (.invoke "armloop" (qNext (.var "i") []))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `arm-ctor`: `=>` — the branch-constructor step: ws, the ctor
name word, then the payload expr runs to EOL.  Row `(ctor nj ne
v0 v1)`; ends the arm → `armloop`. -/
def kAstArmCtor : KCallable :=
  qSeq (qWsAt (.var "i")) "w" "arm-ctor1" (qNext (.var "w") [])

/-- `arm-ctor1`: the ctor name word. -/
def kAstArmCtor1 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "ce" false (some "ce") none
          (some (.invoke "arm-ctor2"
            (qNext (.var "ce")
              [("cj", .var "i"), ("ce", .var "ce")]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `arm-ctor2`: ws then the payload span to EOL.  `cj`/`ce` carry
the ctor-name span. -/
def kAstArmCtor2 : KCallable :=
  qSeq (qWsAt (.var "i")) "p" "arm-ctor3"
    (qNext (.var "p") [("cj", .var "cj"), ("ce", .var "ce")])

/-- `arm-ctor3`. -/
def kAstArmCtor3 : KCallable := .subflow {
  preLabel := none
  head := ("toeol",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "t1") none
      (some (.invoke "armloop"
        (qNext (.var "t1")
          [("out", qRow4 "ctor" (.var "cj") (.var "ce")
                            (.var "i") (.var "t1"))]))) [] ] }

/-- `arm-kw`: a word in tail position is `when` (guard) or a bind
name.  `i` is the word start, `we` its end. -/
def kAstArmKw : KCallable := .subflow {
  preLabel := none
  head := ("kwwhen",
    [("chars", .var "chars"), ("j", .var "i"), ("e", .var "we"),
     ("n", .var "n")])
  arms := [
    .mk "cond" false (some "k") (some (qeq (.var "k") (qint 1)))
      (some (.invoke "arm-cond" (qNext (.var "we") []))) []
  , .mk "bind" false (some "k") none
      (some (.invoke "arm-tail"
        (qNext (.var "we")
          [("out", qRow2 "bind" (.var "i") (.var "we"))]))) [] ] }

/-- `arm-cond`: ws, then the condition runs to the `->`. -/
def kAstArmCond : KCallable :=
  qSeq (qWsAt (.var "i")) "c0" "arm-cond2" (qNext (.var "c0") [])

/-- `arm-cond2`: `toarrow` bounds the condition; after it the
produce/step split is the same `arm-tok` at the arrow. -/
def kAstArmCond2 : KCallable := .subflow {
  preLabel := none
  head := ("toarrow",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "c1") none
      (some (.invoke "arm-tok"
        (qNext (.var "c1")
          [("out", qRow2 "cond" (.var "i") (.var "c1"))]))) [] ] }

/-- `arm-prod`: ws, then the produce value runs to end-of-line —
`(step expr …)` and back to `armloop` at the value's end. -/
def kAstArmProd : KCallable :=
  qSeq (qWsAt (.var "i")) "v0" "arm-prod2" (qNext (.var "v0") [])

/-- `arm-prod2`. -/
def kAstArmProd2 : KCallable := .subflow {
  preLabel := none
  head := ("toeol",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "v1") none
      (some (.invoke "armloop"
        (qNext (.var "v1")
          [("out", qRowS "step" "expr" (.var "i") (.var "v1"))]))) [] ] }

/-- `arm-step`: after `|>` — `@label` jump or `name(` invoke. -/
def kAstArmStep : KCallable :=
  qSeq (qWsAt (.var "i")) "s" "arm-step2" (qNext (.var "s") [])

/-- `arm-step2`. -/
def kAstArmStep2 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "jump" false (some "c") (some (qeq (.var "c") (qint 64)))
      (some (.invoke "word" (qWordAt (qadd (.var "i") (qint 1)))))
      [ .mk "le" false (some "le") none
          (some (.invoke "call-open"
            (qNext (.var "le")
              [("out", qRowS "step" "jump"
                 (qadd (.var "i") (qint 1)) (.var "le"))]))) [] ]
  , .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "se" false (some "se") none
          (some (.invoke "call-open"
            (qNext (.var "se")
              [("out", qRowS "step" "invoke"
                 (.var "i") (.var "se"))]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `decl`: after `tor` — ws, the declared name, `(ev …)` row. -/
def kAstDecl : KCallable :=
  qSeq (qWsAt (.var "i")) "d" "decl1" (qNext (.var "d") [])

/-- `decl1`. -/
def kAstDecl1 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "de" false (some "de") none
          (some (.invoke "decl-brace"
            (qNext (.var "de")
              [("out", qRow2 "ev" (.var "i") (.var "de"))]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `decl-brace`: ws then `{` opens the param list. -/
def kAstDeclBrace : KCallable :=
  qSeq (qWsAt (.var "i")) "b" "decl-brace2" (qNext (.var "b") [])

/-- `decl-brace2`. -/
def kAstDeclBrace2 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "open" false (some "c") (some (qeq (.var "c") (qint 123)))
      (some (.invoke "fields" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `fields`: the param/variant loop inside `{…}`. -/
def kAstFields : KCallable :=
  qSeq (qWsAt (.var "i")) "f" "fields-at" (qNext (.var "f") [])

/-- `fields-at`: `}` closes to the optional `-> ret`; `|` opens a
union variant; a word opens `name: type`. -/
def kAstFieldsAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "close" false (some "c") (some (qeq (.var "c") (qint 125)))
      (some (.invoke "decl-ret" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "var" false (some "c") (some (qeq (.var "c") (qint 124)))
      (some (.invoke "variant" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "fe" false (some "fe") none
          (some (.invoke "fld"
            (qNext (.var "i") [("fe", .var "fe")]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `field`: `name :` then a type span to `,`/`}`.  `i` is the
name start, `fe` its end. -/
def kAstFld : KCallable :=
  qSeq (qWsAt (.var "fe")) "c" "fld2"
    (qNext (.var "c") [("fj", .var "i"), ("fe", .var "fe")])

/-- `field2`: `:` confirmed — the type scans to `,`/`}`. -/
def kAstFld2 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "ty" false (some "k") (some (qeq (.var "k") (qint 58)))
      (some (.invoke "ws"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 1)), ("n", .var "n")]))
      [ .mk "t0" false (some "t0") none
          (some (.invoke "fld3"
            (qNext (.var "t0")
              [("fj", .var "fj"), ("fe", .var "fe")]))) [] ]
  , .mk "bad" false (some "k") none
      (some (.produce (qAstBad (.var "i") (.var "k")))) [] ] }

/-- `field3`: `typend` bounds the type — `(fld …)` row, then the
`,`/`}` decision.  `i` is the type start. -/
def kAstFld3 : KCallable := .subflow {
  preLabel := none
  head := ("typend",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "t1") none
      (some (.invoke "fields2"
        (qNext (.var "t1")
          [("out", qRow4 "fld" (.var "fj") (.var "fe")
                            (.var "i") (.var "t1"))]))) [] ] }

/-- `fields2`: `,` loops to the next field; `}` closes. -/
def kAstFields2 : KCallable :=
  qSeq (qWsAt (.var "i")) "d" "fields2-at" (qNext (.var "d") [])

/-- `fields2-at`. -/
def kAstFields2At : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "more" false (some "c") (some (qeq (.var "c") (qint 44)))
      (some (.invoke "fields" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "close" false (some "c") (some (qeq (.var "c") (qint 125)))
      (some (.invoke "decl-ret" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `variant`: `| go i64` inside braces — a `(var name type)` row,
then back to the field loop's decision. -/
def kAstVariant : KCallable :=
  qSeq (qWsAt (.var "i")) "v" "variant1" (qNext (.var "v") [])

/-- `variant1`. -/
def kAstVariant1 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "ve" false (some "ve") none
          (some (.invoke "variant2"
            (qNext (.var "i") [("ve", .var "ve")]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `variant2`: ws then the payload type to EOL — `(var …)`, then
the field loop resumes at the next line.  `i` is the variant-name
start, `ve` its end. -/
def kAstVariant2 : KCallable :=
  qSeq (qWsAt (.var "ve")) "t0" "variant3"
    (qNext (.var "t0") [("vj", .var "i"), ("ve", .var "ve")])

/-- `variant3`. -/
def kAstVariant3 : KCallable := .subflow {
  preLabel := none
  head := ("toeol",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "t1") none
      (some (.invoke "fields"
        (qNext (.var "t1")
          [("out", qRow4 "brd" (.var "vj") (.var "ve")
                            (.var "i") (.var "t1"))]))) [] ] }

/-- `decl-ret`: after `}` — `-> ret` runs to EOL, else the next
item starts (a bare `}` decl). -/
def kAstDeclRet : KCallable :=
  qSeq (qWsAt (.var "i")) "r" "decl-ret-at" (qNext (.var "r") [])

/-- `decl-ret-at`. -/
def kAstDeclRetAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "ret" false (some "c")
      (some (qand (qeq (.var "c") (qint 45))
        (qeq (.index (.var "chars") (qadd (.var "i") (qint 1)))
             (qint 62))))
      (some (.invoke "ws"
        [("chars", .var "chars"),
         ("i", qadd (.var "i") (qint 2)), ("n", .var "n")]))
      [ .mk "t0" false (some "t0") none
          (some (.invoke "decl-ret2"
            (qNext (.var "t0") []))) [] ]
  , .mk "next" false (some "c") none
      (some (.invoke "branches" (qNext (.var "i") []))) [] ] }

/-- `decl-ret2`: the return type runs to EOL — `(ret …)`, then the
branch-declaration lines.  `i` is the type start. -/
def kAstDeclRet2 : KCallable := .subflow {
  preLabel := none
  head := ("toeol",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "done" false (some "t1") none
      (some (.invoke "branches"
        (qNext (.var "t1")
          [("out", qRow2 "ret" (.var "i") (.var "t1"))]))) [] ] }

/-- `branches`: post-decl `| name type` lines — `|` (not `|>`)
opens a `(brd …)` row; anything else ends the decl and re-enters
`top-at` for the next item. -/
def kAstBranches : KCallable :=
  qSeq (qWsAt (.var "i")) "b" "branches-at" (qNext (.var "b") [])

/-- `branches-at`. -/
def kAstBranchesAt : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "br" false (some "c")
      (some (qand (qeq (.var "c") (qint 124))
        (.un .not (qeq (.index (.var "chars")
                            (qadd (.var "i") (qint 1))) (qint 62)))))
      (some (.invoke "branch" (qNext (qadd (.var "i") (qint 1)) []))) []
  , .mk "next" false (some "c") none
      (some (.invoke "top-at" (qNext (.var "i") []))) [] ] }

/-- `branch`: ws then the branch name word. -/
def kAstBranch : KCallable :=
  qSeq (qWsAt (.var "i")) "w" "branch1" (qNext (.var "w") [])

/-- `branch1`: the branch name, then horizontal-ws decides whether
a payload type follows on the same line.  `i` is the name start. -/
def kAstBranch1 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "id" false (some "c") (some (qAtom (.var "c")))
      (some (.invoke "word" (qWordAt (.var "i"))))
      [ .mk "be" false (some "be") none
          (some (.invoke "branch-ty"
            (qNext (.var "be")
              [("bj", .var "i"), ("be", .var "be")]))) [] ]
  , .mk "bad" false (some "c") none
      (some (.produce (qAstBad (.var "i") (.var "c")))) [] ] }

/-- `branch-ty`: horizontal ws — a type on the same line binds the
branch payload; a newline/EOF means `| stop`-shape (no payload). -/
def kAstBranchTy : KCallable := .subflow {
  preLabel := none
  head := ("hws",
    [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")])
  arms := [ .mk "h" false (some "h") none
      (some (.invoke "branch-ty2"
        (qNext (.var "h") [("bj", .var "bj"), ("be", .var "be")]))) [] ] }

/-- `branch-ty2`. -/
def kAstBranchTy2 : KCallable := .subflow {
  preLabel := none
  head := ("peek", qPeekAt (.var "i"))
  arms := [
    .mk "eol" false (some "c")
      (some (qor (qeq (.var "c") (qint 10)) (qlt (.var "c") (qint 0))))
      (some (.invoke "branches"
        (qNext (.var "i")
          [("out", qRow4 "brd" (.var "bj") (.var "be")
                            (qint 0) (qint 0))]))) []
  , .mk "ty" false (some "c") none
      (some (.invoke "toeol"
        [("chars", .var "chars"), ("i", .var "i"), ("n", .var "n")]))
      [ .mk "t1" false (some "t1") none
          (some (.invoke "branches"
            (qNext (.var "t1")
              [("out", qRow4 "brd" (.var "bj") (.var "be")
                                (.var "i") (.var "t1"))]))) [] ] ] }

/-- `main`: hand `chars` to `top` — the item loop carries
`(0, len, "")`. -/
def kAstMain : KCallable := .subflow {
  preLabel := none
  head := ("top",
    [("chars", .var "chars"), ("i", qint 0),
     ("n", .builtin "len" [.var "chars"]), ("out", .lit (.str ""))])
  arms := [ .mk "done" false (some "s") none
      (some (.produce (.var "s"))) [] ] }

/-- The surface parser — scanners, the grammar machine, `main`. -/
def kAst : KProg := {
  graph := [
    ("peek", kLexPeek),
    ("ws", kAstWs),
    ("comment", kAstComment),
    ("word", kAstWord),
    ("toeol", kAstToEol),
    ("toarrow", kAstToArrow),
    ("toargend", kAstToArgEnd),
    ("typend", kAstTypEnd),
    ("kwtor", kAstKwTor),
    ("kwwhen", kAstKwWhen),
    ("kwimport", kAstKwImport),
    ("hws", kAstHws),
    ("top", kAstTop),
    ("top-at", kAstTopAt),
    ("kwd", kAstKwd),
    ("kwd2", kAstKwd2),
    ("imp-path", kAstImpPath),
    ("imp-path2", kAstImpPath2),
    ("morf", kAstMorf),
    ("morf-at", kAstMorfAt),
    ("impl-body", kAstImplBody),
    ("impl-val", kAstImplVal),
    ("flow-pre", kAstFlowPre),
    ("flow-pre0", kAstFlowPre0),
    ("flow-lbl", kAstFlowLbl),
    ("flow-pre2", kAstFlowPre2),
    ("call-open", kAstCallOpen),
    ("call-at", kAstCallAt),
    ("args", kAstArgs),
    ("args-at", kAstArgsAt),
    ("argname", kAstArgName),
    ("argname-at", kAstArgNameAt),
    ("argvaln", kAstArgValN),
    ("argval", kAstArgVal),
    ("argnext", kAstArgNext),
    ("argnext-at", kAstArgNextAt),
    ("postcall", kAstPostCall),
    ("postcall-at", kAstPostCallAt),
    ("rb-word", kAstRbWord),
    ("rb-word-at", kAstRbWordAt),
    ("rb-tail", kAstRbTail),
    ("rb-tail-at", kAstRbTailAt),
    ("armloop", kAstArmLoop),
    ("armloop-at", kAstArmLoopAt),
    ("arm", kAstArm),
    ("arm1", kAstArm1),
    ("arm-tail", kAstArmTail),
    ("arm-tok", kAstArmTok),
    ("arm-kw", kAstArmKw),
    ("arm-cond", kAstArmCond),
    ("arm-cond2", kAstArmCond2),
    ("arm-prod", kAstArmProd),
    ("arm-prod2", kAstArmProd2),
    ("arm-step", kAstArmStep),
    ("arm-step2", kAstArmStep2),
    ("arm-ctor", kAstArmCtor),
    ("arm-ctor1", kAstArmCtor1),
    ("arm-ctor2", kAstArmCtor2),
    ("arm-ctor3", kAstArmCtor3),
    ("decl", kAstDecl),
    ("decl1", kAstDecl1),
    ("decl-brace", kAstDeclBrace),
    ("decl-brace2", kAstDeclBrace2),
    ("fields", kAstFields),
    ("fields-at", kAstFieldsAt),
    ("fld", kAstFld),
    ("fld2", kAstFld2),
    ("fld3", kAstFld3),
    ("fields2", kAstFields2),
    ("fields2-at", kAstFields2At),
    ("variant", kAstVariant),
    ("variant1", kAstVariant1),
    ("variant2", kAstVariant2),
    ("variant3", kAstVariant3),
    ("decl-ret", kAstDeclRet),
    ("decl-ret-at", kAstDeclRetAt),
    ("decl-ret2", kAstDeclRet2),
    ("branches", kAstBranches),
    ("branches-at", kAstBranchesAt),
    ("branch", kAstBranch),
    ("branch1", kAstBranch1),
    ("branch-ty", kAstBranchTy),
    ("branch-ty2", kAstBranchTy2),
    ("main", kAstMain) ]
  entry := "main"
  args := [] }

/-- `kAst`'s declared `tor` contracts — every structural flow is
`[]const i64 × i64 × i64 × string → string`; the int-returning
scanners return `i64`; `peek`/`kwtor`/`kwwhen` are small enough to
spell by hand.  Position params are all named `i`. -/
def kAstDecls : List (String × KDecl) :=
  let flow (ps : List String) : KDecl :=
    { params := ("chars", "[]const i64") :: ps.map (·, "i64")
        ++ [("out", "string")], ret := some "string" }
  let scan (extra : List String) : KDecl :=
    { params := ("chars", "[]const i64")
        :: (["i", "n"] ++ extra).map (·, "i64"),
      ret := some "i64" }
  [ ("peek", { params := [("chars", "[]const i64"), ("i", "i64"),
                          ("n", "i64")], ret := some "i64" })
  , ("ws", scan []), ("comment", scan []), ("word", scan [])
  , ("toeol", scan []), ("toarrow", scan [])
  , ("toargend", scan ["d", "ins"]), ("typend", scan [])
  , ("kwtor", { params := [("chars", "[]const i64"), ("j", "i64"),
                           ("e", "i64"), ("n", "i64")],
                ret := some "i64" })
  , ("kwwhen", { params := [("chars", "[]const i64"), ("j", "i64"),
                            ("e", "i64"), ("n", "i64")],
                 ret := some "i64" })
  , ("kwimport", { params := [("chars", "[]const i64"), ("j", "i64"),
                              ("e", "i64"), ("n", "i64")],
                   ret := some "i64" })
  , ("hws", scan [])
  , ("top", flow ["i", "n"])
  , ("top-at", flow ["i", "n"])
  , ("kwd", flow ["i", "e", "n"])
  , ("kwd2", flow ["i", "e", "n"])
  , ("imp-path", flow ["i", "n"])
  , ("imp-path2", flow ["i", "n"])
  , ("morf", flow ["i", "n", "j", "ne"])
  , ("morf-at", flow ["i", "n", "j", "ne"])
  , ("impl-body", flow ["i", "n", "j", "ne"])
  , ("impl-val", flow ["i", "n", "j", "ne"])
  , ("flow-pre", flow ["i", "n", "j", "ne"])
  , ("flow-pre0", flow ["i", "n", "j", "ne"])
  , ("flow-lbl", flow ["i", "n", "j", "ne"])
  , ("flow-pre2", flow ["i", "n", "j", "ne"])
  , ("call-open", flow ["i", "n"])
  , ("call-at", flow ["i", "n"])
  , ("args", flow ["i", "n"])
  , ("args-at", flow ["i", "n"])
  , ("argname", flow ["i", "we", "n"])
  , ("argname-at", flow ["i", "n", "aj", "ae"])
  , ("argvaln", flow ["i", "n", "aj", "ae"])
  , ("argval", flow ["i", "n"])
  , ("argnext", flow ["i", "n"])
  , ("argnext-at", flow ["i", "n"])
  , ("postcall", flow ["i", "n"])
  , ("postcall-at", flow ["i", "n"])
  , ("rb-word", flow ["i", "n"])
  , ("rb-word-at", flow ["i", "n"])
  , ("rb-tail", flow ["i", "n"])
  , ("rb-tail-at", flow ["i", "n"])
  , ("armloop", flow ["i", "n"])
  , ("armloop-at", flow ["i", "n"])
  , ("arm", flow ["i", "n"])
  , ("arm1", flow ["i", "n"])
  , ("arm-tail", flow ["i", "n"])
  , ("arm-tok", flow ["i", "n"])
  , ("arm-kw", flow ["i", "we", "n"])
  , ("arm-cond", flow ["i", "n"])
  , ("arm-cond2", flow ["i", "n"])
  , ("arm-prod", flow ["i", "n"])
  , ("arm-prod2", flow ["i", "n"])
  , ("arm-step", flow ["i", "n"])
  , ("arm-step2", flow ["i", "n"])
  , ("arm-ctor", flow ["i", "n"])
  , ("arm-ctor1", flow ["i", "n"])
  , ("arm-ctor2", flow ["i", "n", "cj", "ce"])
  , ("arm-ctor3", flow ["i", "n", "cj", "ce"])
  , ("decl", flow ["i", "n"])
  , ("decl1", flow ["i", "n"])
  , ("decl-brace", flow ["i", "n"])
  , ("decl-brace2", flow ["i", "n"])
  , ("fields", flow ["i", "n"])
  , ("fields-at", flow ["i", "n"])
  , ("fld", flow ["i", "fe", "n"])
  , ("fld2", flow ["i", "n", "fj", "fe"])
  , ("fld3", flow ["i", "n", "fj", "fe"])
  , ("fields2", flow ["i", "n"])
  , ("fields2-at", flow ["i", "n"])
  , ("variant", flow ["i", "n"])
  , ("variant1", flow ["i", "n"])
  , ("variant2", flow ["i", "ve", "n"])
  , ("variant3", flow ["i", "n", "vj", "ve"])
  , ("decl-ret", flow ["i", "n"])
  , ("decl-ret-at", flow ["i", "n"])
  , ("decl-ret2", flow ["i", "n"])
  , ("branches", flow ["i", "n"])
  , ("branches-at", flow ["i", "n"])
  , ("branch", flow ["i", "n"])
  , ("branch1", flow ["i", "n"])
  , ("branch-ty", flow ["i", "n", "bj", "be"])
  , ("branch-ty2", flow ["i", "n", "bj", "be"])
  , ("main", { params := [("chars", "[]const i64")],
               ret := some "string" }) ]

/-! ## `kLow` — a koru-spelled reifier: flat rows + src → ast.json

`klow` is the lowering leg of the koru lane — it consumes the
*flat* row wire kast produces (six ints per row: kind, sub, v0..v3)
plus the source byte array, and emits the `program.ast.json`
document as a string (span bytes as `\u00xx` escapes, structural
quotes as `\"` — the koru literal `"\""`).  It mirrors
`host2/src/korufe/reify.c`'s state machine arm-for-arm and
`astio.c`'s `write_ast_json` shape; the race is parsed-JSON
deep-equal, not byte equality (`\u0069` ≡ `i` after decode).

The row→flat-int projection is declared data in the check
harness; refusal parity on `(bad …)`/dangling-`rbind` rows.

Self-parse files (900–903) overflow the interpreter's native
stack — the named trampolined-invokes axis (frag 0047). -/

def kLowPkb : KCallable := .bare (.cond (.bin .or (.bin .lt (.var "i") (qint 0)) (.bin .ge (.var "i") (.var "n"))) (.bin .sub (qint 0) (qint 1)) (.index (.var "t") (.var "i")))

def kLowLxt : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [
    .mk "fin" false (some "c") (some (.bin .lt (.var "c") (qint 0)))
      (some (.produce (.var "hi"))) []
  ,     .mk "ql" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (qint 1)) (.bin .eq (.var "c") (qint 34))))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (qint 0))])) []
  ,     .mk "bs" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (qint 1)) (.bin .eq (.var "c") (qint 92))))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 2))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) []
  ,     .mk "iq" false (some "c") (some (.bin .eq (.var "ins") (qint 1)))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) []
  ,     .mk "qo" false (some "c") (some (.bin .eq (.var "c") (qint 34)))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (qint 1))])) []
  ,     .mk "dop" false (some "c") (some (.bin .or (.bin .eq (.var "c") (qint 40)) (.bin .or (.bin .eq (.var "c") (qint 91)) (.bin .eq (.var "c") (qint 123)))))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.bin .add (.var "d") (qint 1))), ("ins", (.var "ins"))])) []
  ,     .mk "dcl" false (some "c") (some (.bin .or (.bin .eq (.var "c") (qint 41)) (.bin .or (.bin .eq (.var "c") (qint 93)) (.bin .eq (.var "c") (qint 125)))))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.bin .sub (.var "d") (qint 1))), ("ins", (.var "ins"))])) []
  ,     .mk "oo" false (some "c") (some (.bin .and (.bin .eq (.var "d") (qint 0)) (.bin .and (.bin .eq (.var "c") (qint 124)) (.bin .and (.bin .lt (.bin .add (.var "i") (qint 1)) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 1))) (qint 124))))))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 2))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) []
  ,     .mk "ob" false (some "c") (some (.bin .and (.bin .eq (.var "d") (qint 0)) (.bin .and (.bin .eq (.var "c") (qint 124)) (.bin .and (.bin .gt (.var "i") (qint 0)) (.bin .eq (.index (.var "src") (.bin .sub (.var "i") (qint 1))) (qint 124))))))
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) []
  ,     .mk "pp" false (some "c") (some (.bin .and (.bin .eq (.var "d") (qint 0)) (.bin .eq (.var "c") (qint 124))))
      (some (.produce (.var "i"))) []
  ,     .mk "aw" false (some "c") (some (.bin .and (.bin .eq (.var "d") (qint 0)) (.bin .and (.bin .or (.bin .eq (.var "c") (qint 61)) (.bin .eq (.var "c") (qint 45))) (.bin .and (.bin .lt (.bin .add (.var "i") (qint 1)) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 1))) (qint 62))))))
      (some (.produce (.var "i"))) []
  ,     .mk "cm" false (some "c") (some (.bin .and (.bin .eq (.var "d") (qint 0)) (.bin .and (.bin .eq (.var "c") (qint 47)) (.bin .and (.bin .lt (.bin .add (.var "i") (qint 1)) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 1))) (qint 47))))))
      (some (.produce (.var "i"))) []
  ,     .mk "mo" false (some "c") none
      (some (.invoke "lxt" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) [] ] }


def kLowLtma : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [
    .mk "ws" false (some "c") (some (.bin .or (.bin .eq (.var "c") (qint 32)) (.bin .or (.bin .eq (.var "c") (qint 9)) (.bin .or (.bin .eq (.var "c") (qint 10)) (.bin .eq (.var "c") (qint 13))))))
      (some (.invoke "ltma" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi"))])) []
  ,     .mk "dn" false (some "c") none
      (some (.produce (.var "i"))) [] ] }


def kLowLtmb : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "j")), ("n", (.var "n"))])
  arms := [
    .mk "ws" false (some "c") (some (.bin .and (.bin .ge (.var "j") (.var "lo")) (.bin .or (.bin .eq (.var "c") (qint 32)) (.bin .or (.bin .eq (.var "c") (qint 9)) (.bin .or (.bin .eq (.var "c") (qint 10)) (.bin .eq (.var "c") (qint 13)))))))
      (some (.invoke "ltmb" [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "j") (qint 1))), ("n", (.var "n"))])) []
  ,     .mk "dn" false (some "c") none
      (some (.produce (.bin .add (.var "j") (qint 1)))) [] ] }


def kLowLtk1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [
    .mk "fin" false (some "c") (some (.bin .lt (.var "c") (qint 0)))
      (some (.produce (.var "hi"))) []
  ,     .mk "ct" false (some "c") (some (.bin .and (.bin .eq (.var "c") (qint 47)) (.bin .and (.bin .lt (.bin .add (.var "i") (qint 1)) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 1))) (qint 47)))))
      (some (.produce (.var "i"))) []
  ,     .mk "ws" false (some "c") (some (.bin .or (.bin .eq (.var "c") (qint 32)) (.bin .or (.bin .eq (.var "c") (qint 9)) (.bin .or (.bin .eq (.var "c") (qint 10)) (.bin .eq (.var "c") (qint 13))))))
      (some (.produce (.var "i"))) []
  ,     .mk "mo" false (some "c") none
      (some (.invoke "ltk1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi"))])) [] ] }


def kLowLty1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [
    .mk "fin" false (some "c") (some (.bin .lt (.var "c") (qint 0)))
      (some (.produce (.var "hi"))) []
  ,     .mk "ct" false (some "c") (some (.bin .and (.bin .eq (.var "c") (qint 47)) (.bin .and (.bin .lt (.bin .add (.var "i") (qint 1)) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 1))) (qint 47)))))
      (some (.produce (.var "i"))) []
  ,     .mk "mo" false (some "c") none
      (some (.invoke "lty1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi"))])) [] ] }


def kLowLtm2 : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "j")), ("n", (.var "n"))])
  arms := [
    .mk "ws" false (some "c") (some (.bin .and (.bin .ge (.var "j") (.var "lo")) (.bin .or (.bin .eq (.var "c") (qint 32)) (.bin .eq (.var "c") (qint 9)))))
      (some (.invoke "ltm2" [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "j") (qint 1))), ("n", (.var "n"))])) []
  ,     .mk "dn" false (some "c") none
      (some (.produce (.bin .add (.var "j") (qint 1)))) [] ] }


def kLowLln : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "n"))])
  arms := [
    .mk "fin" false (some "c") (some (.bin .or (.bin .ge (.var "i") (.var "off")) (.bin .lt (.var "c") (qint 0))))
      (some (.produce (.var "l"))) []
  ,     .mk "nl" false (some "c") (some (.bin .eq (.var "c") (qint 10)))
      (some (.invoke "lln" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("off", (.var "off")), ("n", (.var "n")), ("l", (.bin .add (.var "l") (qint 1)))])) []
  ,     .mk "ch" false (some "c") none
      (some (.invoke "lln" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("off", (.var "off")), ("n", (.var "n")), ("l", (.var "l"))])) [] ] }


def kLowLbs : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.bin .sub (.var "i") (qint 1))), ("n", (.var "n"))])
  arms := [
    .mk "nl" false (some "c") (some (.bin .or (.bin .le (.var "i") (qint 0)) (.bin .eq (.var "c") (qint 10))))
      (some (.produce (.var "i"))) []
  ,     .mk "ch" false (some "c") none
      (some (.invoke "lbs" [("src", (.var "src")), ("i", (.bin .sub (.var "i") (qint 1))), ("n", (.var "n"))])) [] ] }


def kLowLpb : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "n"))])
  arms := [
    .mk "pb" false (some "c") (some (.bin .and (.bin .le (.bin .add (.var "i") (qint 4)) (.var "j")) (.bin .and (.bin .eq (.var "c") (qint 112)) (.bin .and (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 1))) (qint 117)) (.bin .and (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 2))) (qint 98)) (.bin .and (.bin .or (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 3))) (qint 32)) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (qint 3))) (qint 9))) (.bin .or (.bin .eq (.var "i") (.var "ls")) (.bin .or (.bin .eq (.index (.var "src") (.bin .sub (.var "i") (qint 1))) (qint 32)) (.bin .eq (.index (.var "src") (.bin .sub (.var "i") (qint 1))) (qint 9))))))))))
      (some (.produce (qint 1))) []
  ,     .mk "nx" false (some "c") (some (.bin .lt (.var "i") (.var "j")))
      (some (.invoke "lpb" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("ls", (.var "ls")), ("j", (.var "j")), ("n", (.var "n"))])) []
  ,     .mk "no" false (some "c") none
      (some (.produce (qint 0))) [] ] }


def kLowLpub : KCallable := .subflow {
  preLabel := none
  head := ("lbs",
    [("src", (.var "src")), ("i", (.var "j")), ("n", (.var "n"))])
  arms := [
    .mk "s" false (some "ls") none
      (some (.invoke "lpb" [("src", (.var "src")), ("i", (.var "ls")), ("ls", (.var "ls")), ("j", (.var "j")), ("n", (.var "n"))])) [] ] }


def kLowLhx : KCallable := .bare (.cond (.bin .lt (.var "d") (qint 10)) (.builtin "intToString" [(.var "d")]) (.cond (.bin .eq (.var "d") (qint 10)) (.lit (.str "a")) (.cond (.bin .eq (.var "d") (qint 11)) (.lit (.str "b")) (.cond (.bin .eq (.var "d") (qint 12)) (.lit (.str "c")) (.cond (.bin .eq (.var "d") (qint 13)) (.lit (.str "d")) (.cond (.bin .eq (.var "d") (qint 14)) (.lit (.str "e")) (.lit (.str "f"))))))))

def kLowEscl : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [
    .mk "fin" false (some "c") (some (.bin .lt (.var "c") (qint 0)))
      (some (.produce (.var "out"))) []
  ,     .mk "ch" false (some "c") (some (.bin .le (.var "c") (qint 127)))
      (some (.invoke "esca" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("out", (.var "out")), ("c", (.var "c"))])) [] ] }


def kLowEsca : KCallable := .subflow {
  preLabel := none
  head := ("lhx",
    [("d", (.bin .div (.var "c") (qint 16)))])
  arms := [
    .mk "hd" false (some "a") none
      (some (.invoke "escb" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("out", (.var "out")), ("c", (.var "c")), ("a", (.var "a"))])) [] ] }


def kLowEscb : KCallable := .subflow {
  preLabel := none
  head := ("lhx",
    [("d", (.bin .mod (.var "c") (qint 16)))])
  arms := [
    .mk "hd" false (some "b") none
      (some (.invoke "escl" [("src", (.var "src")), ("i", (.bin .add (.var "i") (qint 1))), ("hi", (.var "hi")), ("out", (.bin .concat (.var "out") (.bin .concat (.lit (.str "\\u00")) (.bin .concat (.var "a") (.var "b")))))])) [] ] }


def kLowEscx : KCallable := .subflow {
  preLabel := none
  head := ("lxt",
    [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "hi")), ("d", (qint 0)), ("ins", (qint 0))])
  arms := [
    .mk "cut" false (some "c") none
      (some (.invoke "escx1" [("src", (.var "src")), ("lo", (.var "lo")), ("xt", (.var "c")), ("n", (.var "n")), ("out", (.var "out"))])) [] ] }


def kLowEscx1 : KCallable := .subflow {
  preLabel := none
  head := ("ltma",
    [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "xt"))])
  arms := [
    .mk "at" false (some "a") none
      (some (.invoke "escx2" [("src", (.var "src")), ("a", (.var "a")), ("xt", (.var "xt")), ("n", (.var "n")), ("out", (.var "out"))])) [] ] }


def kLowEscx2 : KCallable := .subflow {
  preLabel := none
  head := ("ltmb",
    [("src", (.var "src")), ("lo", (.var "a")), ("j", (.bin .sub (.var "xt") (qint 1))), ("n", (.var "n"))])
  arms := [
    .mk "bt" false (some "b") none
      (some (.invoke "escl" [("src", (.var "src")), ("i", (.var "a")), ("hi", (.var "b")), ("out", (.var "out"))])) [] ] }


def kLowEsct : KCallable := .subflow {
  preLabel := none
  head := ("ltmb",
    [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "hi") (qint 1))), ("n", (.var "n"))])
  arms := [
    .mk "tb" false (some "b") none
      (some (.invoke "esct1" [("src", (.var "src")), ("lo", (.var "lo")), ("b", (.var "b")), ("n", (.var "n")), ("out", (.var "out"))])) [] ] }


def kLowEsct1 : KCallable := .subflow {
  preLabel := none
  head := ("ltk1",
    [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "b"))])
  arms := [
    .mk "ct" false (some "c") none
      (some (.invoke "escl" [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "c")), ("out", (.var "out"))])) [] ] }


def kLowEscty : KCallable := .subflow {
  preLabel := none
  head := ("ltmb",
    [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "hi") (qint 1))), ("n", (.var "n"))])
  arms := [
    .mk "tb" false (some "b") none
      (some (.invoke "escty1" [("src", (.var "src")), ("lo", (.var "lo")), ("b", (.var "b")), ("n", (.var "n")), ("out", (.var "out"))])) [] ] }


def kLowEscty1 : KCallable := .subflow {
  preLabel := none
  head := ("lty1",
    [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "b"))])
  arms := [
    .mk "ct" false (some "c") none
      (some (.invoke "escty2" [("src", (.var "src")), ("lo", (.var "lo")), ("c", (.var "c")), ("n", (.var "n")), ("out", (.var "out"))])) [] ] }


def kLowEscty2 : KCallable := .subflow {
  preLabel := none
  head := ("ltm2",
    [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "c") (qint 1))), ("n", (.var "n"))])
  arms := [
    .mk "db" false (some "d") none
      (some (.invoke "escl" [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "d")), ("out", (.var "out"))])) [] ] }


def kLowLcls : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "mod")), ("i", (qint 0)), ("n", (.var "nmod"))])
  arms := [
    .mk "done" false (some "c") (some (.bin .eq (.var "dp") (qint 0)))
      (some (.produce (.var "out"))) []
  ,     .mk "more" false (some "c") none
      (some (.invoke "lclsm" [("dp", (.var "dp")), ("mod", (.var "mod")), ("fln", (.var "fln")), ("nmod", (.var "nmod")), ("out", (.var "out"))])) [] ] }


def kLowLclsm : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.var "nmod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"location\":{\"file\":\""))))])
  arms := [
    .mk "md" false (some "e") none
      (some (.invoke "lclsn" [("dp", (.var "dp")), ("mod", (.var "mod")), ("fln", (.var "fln")), ("nmod", (.var "nmod")), ("out", (.var "e"))])) [] ] }


def kLowLclsn : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "mod")), ("i", (qint 0)), ("n", (.var "nmod"))])
  arms := [
    .mk "go" false (some "c") none
      (some (.invoke "lcls" [("dp", (.bin .sub (.var "dp") (qint 1))), ("mod", (.var "mod")), ("fln", (.var "fln")), ("nmod", (.var "nmod")), ("out", (.bin .concat (.var "out") (.bin .concat (.lit (.str "\",\"line\":")) (.bin .concat (.builtin "intToString" [(.var "fln")]) (.lit (.str ",\"col\":0}}"))))))])) [] ] }


def kLowLtail : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.var "nmod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"main_module_name\":\""))))])
  arms := [
    .mk "done" false (some "e") none
      (some (.produce (.bin .concat (.var "e") (.lit (.str "\",\"parts\":[]}"))))) [] ] }


def kLowLimp : KCallable := .subflow {
  preLabel := none
  head := ("esct",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.lit (.str ",{\"import_decl\":{\"path\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "limp2" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "e")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLimp2 : KCallable := .subflow {
  preLabel := none
  head := ("esct",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.lit (.str "\",\"local_name\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "limpm" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "e")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLimpm : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.builtin "len" [(.var "mod")])), ("out", (.bin .concat (.var "out") (.lit (.str "\",\"module\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "ltop" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"}}")))), ("p0", (.var "p0")), ("p1", (.var "p1")), ("q0", (.bin .sub (qint 0) (qint 1)))])) [] ] }


def kLowLimpl : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str ",{\"immediate_impl\":{\"event_path\":{\"module_qualifier\":null,\"segments\":[\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "limpl2" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "e")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLimpl2 : KCallable := .subflow {
  preLabel := none
  head := ("escx",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.lit (.str "\"]},\"value\":{\"branch_name\":\"\",\"fields\":[],\"plain_value\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "limplm" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "e")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLimplm : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.builtin "len" [(.var "mod")])), ("out", (.bin .concat (.var "out") (.lit (.str "\",\"has_expressions\":true,\"is_bare_return\":true},\"annotations\":[],\"module\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "ltop" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\",\"is_impl\":false}}")))), ("p0", (.var "p0")), ("p1", (.var "p1")), ("q0", (.bin .sub (qint 0) (qint 1)))])) [] ] }


def kLowLevo : KCallable := .subflow {
  preLabel := none
  head := ("lpub",
    [("src", (.var "src")), ("j", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "pb" false (some "evp") none
      (some (.invoke "levoe" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLevoe : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str ",{\"event_decl\":{\"path\":{\"module_qualifier\":null,\"segments\":[\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "levf" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"]},\"input\":{\"fields\":[")))), ("ff", (qint 0)), ("bf", (qint 0)), ("r0", (.bin .sub (qint 0) (qint 1))), ("r1", (.bin .sub (qint 0) (qint 1))), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLevf : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "fld" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 2)) (.bin .and (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))
      (some (.invoke "lfld" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("ff", (.var "ff")), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "ret" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 3)) (.bin .and (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))
      (some (.invoke "levf" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("ff", (.var "ff")), ("bf", (.var "bf")), ("r0", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("r1", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "brf" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 4)) (.bin .and (.bin .eq (.var "bf") (qint 0)) (.bin .and (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lbrdf" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "brn" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 4)) (.bin .and (.bin .eq (.var "bf") (qint 1)) (.bin .and (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lbrdn" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "clo" false (some "c") (some (.bin .eq (.var "bf") (qint 0)))
      (some (.invoke "levcc" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "clb" false (some "c") (some (.bin .eq (.var "bf") (qint 1)))
      (some (.invoke "levcc2" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLfld : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.bin .concat (.cond (.bin .eq (.var "ff") (qint 1)) (.lit (.str ",")) (.lit (.str ""))) (.lit (.str "{\"name\":\"")))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "lfldn" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "e")), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLfldn : KCallable := .subflow {
  preLabel := none
  head := ("escty",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.lit (.str "\",\"type\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "levf" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\",\"module_path\":null,\"phantom\":null,\"is_source\":false,\"is_file\":false,\"is_embed_file\":false,\"is_expression\":false,\"is_invocation_meta\":false,\"expression\":null,\"expression_str\":null,\"owns_expression\":false,\"default\":null}")))), ("ff", (qint 1)), ("bf", (qint 0)), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLbrdf : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str "],\"is_wildcard\":false},\"branches\":[{\"name\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "levf" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}")))), ("ff", (qint 1)), ("bf", (qint 1)), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLbrdn : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str ",{\"name\":\""))))])
  arms := [
    .mk "p" false (some "e") none
      (some (.invoke "levf" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}")))), ("ff", (qint 1)), ("bf", (qint 1)), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLevcc : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "r0")), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "hasr" false (some "c") (some (.bin .ge (.var "r0") (qint 0)))
      (some (.invoke "levc1" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"is_wildcard\":false},\"branches\":[],\"return_type\":\"")))), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "nor" false (some "c") none
      (some (.invoke "levcm" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"is_wildcard\":false},\"branches\":[],\"return_type\":null")))), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLevcc2 : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "r0")), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "hasr" false (some "c") (some (.bin .ge (.var "r0") (qint 0)))
      (some (.invoke "levc1" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"return_type\":\"")))), ("r0", (.var "r0")), ("r1", (.var "r1")), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "nor" false (some "c") none
      (some (.invoke "levcm" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"return_type\":null")))), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLevc1 : KCallable := .subflow {
  preLabel := none
  head := ("esct",
    [("src", (.var "src")), ("lo", (.var "r0")), ("hi", (.var "r1")), ("n", (.builtin "len" [(.var "src")])), ("out", (.var "out"))])
  arms := [
    .mk "t" false (some "e") none
      (some (.invoke "levcm" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"")))), ("evp", (.var "evp")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowLevcm : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.builtin "len" [(.var "mod")])), ("out", (.bin .concat (.var "out") (.bin .concat (.lit (.str ",\"return_phantom\":null,\"is_public\":")) (.bin .concat (.cond (.bin .eq (.var "evp") (qint 1)) (.lit (.str "true")) (.lit (.str "false"))) (.lit (.str ",\"is_implicit_flow\":false,\"annotations\":[],\"prose\":\"\",\"is_pure\":false,\"is_transitively_pure\":false,\"module\":\""))))))])
  arms := [
    .mk "m" false (some "e") none
      (some (.invoke "ltop" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"}}")))), ("p0", (.var "p0")), ("p1", (.var "p1")), ("q0", (.bin .sub (qint 0) (qint 1)))])) [] ] }


def kLowLflw : KCallable := .subflow {
  preLabel := none
  head := ("lln",
    [("src", (.var "src")), ("i", (qint 0)), ("off", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("n", (.builtin "len" [(.var "src")])), ("l", (qint 1))])
  arms := [
    .mk "ln" false (some "l") none
      (some (.invoke "lhead" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str ",{\"flow\":{\"invocation\":")))), ("f0", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("f1", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("fln", (.var "l")), ("k4", (qint 0)), ("pr0", (.var "p0")), ("pr1", (.var "p1")), ("q0", (.bin .sub (qint 0) (qint 1))), ("q1", (.bin .sub (qint 0) (qint 1))), ("dp", (qint 0)), ("af", (qint 0)), ("cs", (qint 0)), ("hn", (qint 0))])) [] ] }


def kLowLhead : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "call" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 8)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lcall" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLcall : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str "{\"event\":[\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "linv" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\"],\"args\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.cond (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (.var "f0")) (qint 1) (qint 0))), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (qint 0)), ("as", (qint 0))])) [] ] }


def kLowLinv : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "arg" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 9)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5))) (.builtin "len" [(.var "src")])))))))
      (some (.invoke "larg" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh")), ("as", (.var "as"))])) []
  ,     .mk "rb" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 10)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lrb" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh"))])) []
  ,     .mk "oth" false (some "c") none
      (some (.invoke "lconts" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.bin .concat (.lit (.str "],\"variant\":null,\"return_binding\":null")) (.bin .concat (.cond (.bin .eq (.var "wh") (qint 1)) (.lit (.str "}}")) (.lit (.str "}"))) (.lit (.str ",\"continuations\":[")))))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.bin .add (.var "dp") (qint 1))), ("af", (qint 0)), ("cs", (.cond (.bin .eq (.var "wh") (qint 1)) (qint 1) (qint 0))), ("hn", (.var "hn"))])) [] ] }


def kLowLarg : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "nm" false (some "c") (some (.bin .gt (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)))
      (some (.invoke "largn" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh")), ("as", (.var "as"))])) []
  ,     .mk "ps" false (some "c") none
      (some (.invoke "largp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh")), ("as", (.var "as"))])) [] ] }


def kLowLargn : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.bin .concat (.cond (.bin .eq (.var "as") (qint 1)) (.lit (.str ",")) (.lit (.str ""))) (.lit (.str "{\"name\":\"")))))])
  arms := [
    .mk "nm" false (some "e") none
      (some (.invoke "largm" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\",\"value\":\"")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh"))])) [] ] }


def kLowLargp : KCallable := .subflow {
  preLabel := none
  head := ("escx",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.bin .concat (.cond (.bin .eq (.var "as") (qint 1)) (.lit (.str ",")) (.lit (.str ""))) (.lit (.str "{\"name\":\"\",\"value\":\"")))))])
  arms := [
    .mk "v" false (some "e") none
      (some (.invoke "linv" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"}")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh")), ("as", (qint 1))])) [] ] }


def kLowLargm : KCallable := .subflow {
  preLabel := none
  head := ("escx",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.var "out"))])
  arms := [
    .mk "v" false (some "e") none
      (some (.invoke "linv" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"}")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (.var "wh")), ("as", (qint 1))])) [] ] }


def kLowLrb : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str "],\"variant\":null,\"return_binding\":\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lconts" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.bin .concat (.lit (.str "\"")) (.bin .concat (.cond (.bin .eq (.var "wh") (qint 1)) (.lit (.str "}}")) (.lit (.str "}"))) (.lit (.str ",\"continuations\":[")))))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("q1", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("dp", (.bin .add (.var "dp") (qint 1))), ("af", (qint 0)), ("cs", (.cond (.bin .eq (.var "wh") (qint 1)) (qint 1) (qint 0))), ("hn", (.var "hn"))])) [] ] }


def kLowLbind : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "bd" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 12)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lbd" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "oth" false (some "c") none
      (some (.invoke "lcond" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "null,\"binding_type\":\"branch_payload\",\"condition\":")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLbd : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str "\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lcond" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\",\"binding_type\":\"branch_payload\",\"condition\":")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLcond : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "cd" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 13)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lcd" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "oth" false (some "c") none
      (some (.invoke "lstep" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "null,\"step\":")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLcd : KCallable := .subflow {
  preLabel := none
  head := ("escx",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.lit (.str "\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lstep" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\",\"step\":")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLstep : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "se" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 14)) (.bin .and (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 1)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))))
      (some (.invoke "lsxp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "si" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 14)) (.bin .and (.bin .or (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 2)) (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 3))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))))
      (some (.invoke "lsiv" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "ct" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 15)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lctor" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "oth" false (some "c") none
      (some (.invoke "lconts" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "{\"type\":\"terminal\"},\"continuations\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.bin .add (.var "dp") (qint 1))), ("af", (qint 0)), ("cs", (qint 0)), ("hn", (.var "hn"))])) [] ] }


def kLowLsxp : KCallable := .subflow {
  preLabel := none
  head := ("escx",
    [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("n", (.builtin "len" [(.var "src")])), ("out", (.bin .concat (.var "out") (.lit (.str "{\"type\":\"produce\",\"plain_value\":\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lconts" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\"},\"continuations\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.bin .add (.var "dp") (qint 1))), ("af", (qint 0)), ("cs", (qint 0)), ("hn", (.var "hn"))])) [] ] }


def kLowLsiv : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.bin .concat (.lit (.str "{\"type\":\"invocation\",\"invocation\":{\"event\":[")) (.cond (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 3)) (.lit (.str "\"@")) (.lit (.str "\""))))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "linv" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\"],\"args\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("wh", (qint 1)), ("as", (qint 0))])) [] ] }


def kLowLctor : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str "{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lctor1" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\",\"fields\":[],\"plain_value\":")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLctor1 : KCallable := .subflow {
  preLabel := none
  head := ("lxt",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5)))), ("d", (qint 0)), ("ins", (qint 0))])
  arms := [
    .mk "x" false (some "xt") none
      (some (.invoke "lctor2" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("xt", (.var "xt"))])) [] ] }


def kLowLctor2 : KCallable := .subflow {
  preLabel := none
  head := ("ltma",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))), ("hi", (.var "xt"))])
  arms := [
    .mk "a" false (some "a") none
      (some (.invoke "lctor3" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("xt", (.var "xt")), ("a", (.var "a"))])) [] ] }


def kLowLctor3 : KCallable := .subflow {
  preLabel := none
  head := ("ltmb",
    [("src", (.var "src")), ("lo", (.var "a")), ("j", (.bin .sub (.var "xt") (qint 1))), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "b" false (some "b") none
      (some (.invoke "lctor4" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("xt", (.var "xt")), ("a", (.var "a")), ("b", (.var "b"))])) [] ] }


def kLowLctor4 : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "a")), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "has" false (some "c") (some (.bin .lt (.var "a") (.var "b")))
      (some (.invoke "lctor5" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn")), ("a", (.var "a")), ("b", (.var "b"))])) []
  ,     .mk "non" false (some "c") (some (.bin .and (.bin .ge (.var "a") (.var "b")) (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4))) (.var "xt"))))
      (some (.invoke "lconts" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "null,\"has_expressions\":false,\"is_bare_return\":false}},\"continuations\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.bin .add (.var "dp") (qint 1))), ("af", (qint 0)), ("cs", (qint 0)), ("hn", (.var "hn"))])) [] ] }


def kLowLctor5 : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.var "a")), ("hi", (.var "b")), ("out", (.bin .concat (.var "out") (.lit (.str "\""))))])
  arms := [
    .mk "v" false (some "e") none
      (some (.invoke "lconts" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\",\"has_expressions\":true,\"is_bare_return\":false}},\"continuations\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.bin .add (.var "dp") (qint 1))), ("af", (qint 0)), ("cs", (qint 0)), ("hn", (.var "hn"))])) [] ] }


def kLowLconts : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "cn" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 11)) (.bin .and (.bin .and (.bin .lt (.var "q0") (qint 0)) (.bin .eq (.var "hn") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))))
      (some (.invoke "larmc" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "st" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 14)) (.bin .and (.bin .or (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 2)) (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 3))) (.bin .or (.bin .eq (.var "cs") (qint 1)) (.bin .and (.bin .and (.bin .eq (.var "dp") (qint 1)) (.bin .eq (.var "af") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))))))
      (some (.invoke "llink" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "oth" false (some "c") none
      (some (.invoke "litemc" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLarmc : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "deep" false (some "c") (some (.bin .gt (.var "dp") (qint 1)))
      (some (.invoke "larmd" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "shal" false (some "c") (some (.bin .eq (.var "dp") (qint 1)))
      (some (.invoke "lcarmp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.cond (.bin .eq (.var "af") (qint 1)) (.lit (.str ",")) (.lit (.str ""))))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLarmd : KCallable := .subflow {
  preLabel := none
  head := ("lcls",
    [("dp", (.bin .sub (.var "dp") (qint 1))), ("mod", (.var "mod")), ("fln", (.var "fln")), ("nmod", (.builtin "len" [(.var "mod")])), ("out", (.var "out"))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lcarmp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str ",")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (qint 1)), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLcarmp : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.bin .concat (.var "out") (.lit (.str "{\"branch\":\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "lbind" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.bin .sub (qint 0) (qint 1))), ("q1", (.bin .sub (qint 0) (qint 1))), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (qint 0)), ("hn", (.var "hn"))])) [] ] }


def kLowLlink : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "q0")), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "pb" false (some "c") (some (.bin .ge (.var "q0") (qint 0)))
      (some (.invoke "llinkb" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.bin .concat (.cond (.bin .eq (.var "af") (qint 1)) (.lit (.str ",")) (.lit (.str ""))) (.lit (.str "{\"branch\":\"\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":\""))))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "nb" false (some "c") (some (.bin .lt (.var "q0") (qint 0)))
      (some (.invoke "llinkn" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.bin .concat (.cond (.bin .eq (.var "af") (qint 1)) (.lit (.str ",")) (.lit (.str ""))) (.lit (.str "{\"branch\":\"\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":null"))))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLlinkb : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.var "q0")), ("hi", (.var "q1")), ("out", (.var "out"))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "llinkn" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\"")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLlinkn : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "go" false (some "c") none
      (some (.invoke "llinke" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.bin .concat (.lit (.str ",\"binding_type\":\"branch_payload\",\"condition\":null,\"step\":{\"type\":\"invocation\",\"invocation\":{\"event\":[")) (.cond (.bin .eq (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 1))) (qint 3)) (.lit (.str "\"@")) (.lit (.str "\"")))))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLlinke : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("hi", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("out", (.var "out"))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "linv" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\"],\"args\":[")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.bin .sub (qint 0) (qint 1))), ("q1", (.bin .sub (qint 0) (qint 1))), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.cond (.bin .and (.bin .eq (.var "dp") (qint 1)) (.bin .eq (.var "af") (qint 0))) (qint 1) (.var "hn"))), ("wh", (qint 1)), ("as", (qint 0))])) [] ] }


def kLowLitemc : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "deep" false (some "c") (some (.bin .gt (.var "dp") (qint 1)))
      (some (.invoke "litemd" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "shal" false (some "c") (some (.bin .eq (.var "dp") (qint 1)))
      (some (.invoke "litemp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLitemd : KCallable := .subflow {
  preLabel := none
  head := ("lcls",
    [("dp", (.bin .sub (.var "dp") (qint 1))), ("mod", (.var "mod")), ("fln", (.var "fln")), ("nmod", (.builtin "len" [(.var "mod")])), ("out", (.var "out"))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "litemp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "v")), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (qint 1)), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLitemp : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "src")), ("i", (.var "pr0")), ("n", (.builtin "len" [(.var "src")]))])
  arms := [
    .mk "f4" false (some "c") (some (.bin .eq (.var "k4") (qint 1)))
      (some (.invoke "liteml" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"pre_label\":null,\"impl_of\":null")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "hp" false (some "c") (some (.bin .and (.bin .eq (.var "k4") (qint 0)) (.bin .ge (.var "pr0") (qint 0))))
      (some (.invoke "litem3p" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"pre_label\":\"")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) []
  ,     .mk "np" false (some "c") (some (.bin .and (.bin .eq (.var "k4") (qint 0)) (.bin .lt (.var "pr0") (qint 0))))
      (some (.invoke "litem3i" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "out") (.lit (.str "],\"pre_label\":null,\"impl_of\":[\"")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLitem3p : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.var "pr0")), ("hi", (.var "pr1")), ("out", (.var "out"))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "litem3i" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\",\"impl_of\":[\"")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLitem3i : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "src")), ("i", (.var "f0")), ("hi", (.var "f1")), ("out", (.var "out"))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "liteml" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.lit (.str "\"]")))), ("f0", (.var "f0")), ("f1", (.var "f1")), ("fln", (.var "fln")), ("k4", (.var "k4")), ("pr0", (.var "pr0")), ("pr1", (.var "pr1")), ("q0", (.var "q0")), ("q1", (.var "q1")), ("dp", (.var "dp")), ("af", (.var "af")), ("cs", (.var "cs")), ("hn", (.var "hn"))])) [] ] }


def kLowLiteml : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.builtin "len" [(.var "mod")])), ("out", (.bin .concat (.var "out") (.lit (.str ",\"location\":{\"file\":\""))))])
  arms := [
    .mk "e" false (some "v") none
      (some (.invoke "ltop" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "v") (.bin .concat (.lit (.str "\",\"line\":")) (.bin .concat (.builtin "intToString" [(.var "fln")]) (.lit (.str ",\"col\":0}}}")))))), ("p0", (.bin .sub (qint 0) (qint 1))), ("p1", (.bin .sub (qint 0) (qint 1))), ("q0", (.var "q0"))])) [] ] }


def kLowLtop : KCallable := .subflow {
  preLabel := none
  head := ("pkb",
    [("t", (.var "rows")), ("i", (.bin .mul (.var "i") (qint 6))), ("n", (.var "n"))])
  arms := [
    .mk "fin" false (some "c") (some (.bin .and (.bin .ge (.bin .mul (.var "i") (qint 6)) (.var "n")) (.bin .lt (.var "q0") (qint 0))))
      (some (.invoke "ltail" [("mod", (.var "mod")), ("nmod", (.builtin "len" [(.var "mod")])), ("out", (.var "out"))])) []
  ,     .mk "ev" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "k") (qint 1)) (.bin .lt (.var "q0") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "levo" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "im" false (some "k") (some (.bin .and (.bin .and (.bin .and (.bin .eq (.var "k") (qint 5)) (.bin .lt (.var "q0") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 4)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 5))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "limpl" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "lb" false (some "k") (some (.bin .and (.bin .eq (.var "k") (qint 6)) (.bin .and (.bin .and (.bin .lt (.var "q0") (qint 0)) (.bin .lt (.var "p0") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")])))))))
      (some (.invoke "ltop" [("rows", (.var "rows")), ("i", (.bin .add (.var "i") (qint 1))), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("p0", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))), ("p1", (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3)))), ("q0", (.var "q0"))])) []
  ,     .mk "fw" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "k") (qint 7)) (.bin .lt (.var "q0") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "lflw" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) []
  ,     .mk "ip" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "k") (qint 16)) (.bin .lt (.var "q0") (qint 0))) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2))) (qint 0)) (.bin .and (.bin .ge (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 2)))) (.bin .le (.index (.var "rows") (.bin .add (.bin .mul (.var "i") (qint 6)) (qint 3))) (.builtin "len" [(.var "src")]))))))
      (some (.invoke "limp" [("rows", (.var "rows")), ("i", (.var "i")), ("n", (.var "n")), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.var "out")), ("p0", (.var "p0")), ("p1", (.var "p1"))])) [] ] }


def kLowMain : KCallable := .subflow {
  preLabel := none
  head := ("escl",
    [("src", (.var "mod")), ("i", (qint 0)), ("hi", (.builtin "len" [(.var "mod")])), ("out", (.lit (.str "{\"module_annotations\":[],\"items\":[{\"import_decl\":{\"path\":\"std/compiler\",\"local_name\":\"std.compiler\",\"module\":\"")))])
  arms := [
    .mk "m" false (some "e") none
      (some (.invoke "ltop" [("rows", (.var "rows")), ("i", (qint 0)), ("n", (.builtin "len" [(.var "rows")])), ("src", (.var "src")), ("mod", (.var "mod")), ("out", (.bin .concat (.var "e") (.lit (.str "\"}}")))), ("p0", (.bin .sub (qint 0) (qint 1))), ("p1", (.bin .sub (qint 0) (qint 1))), ("q0", (.bin .sub (qint 0) (qint 1)))])) [] ] }


def kLow : KProg := {
  graph := [("pkb", kLowPkb), ("lxt", kLowLxt), ("ltma", kLowLtma), ("ltmb", kLowLtmb), ("ltk1", kLowLtk1), ("lty1", kLowLty1), ("ltm2", kLowLtm2), ("lln", kLowLln), ("lbs", kLowLbs), ("lpb", kLowLpb), ("lpub", kLowLpub), ("lhx", kLowLhx), ("escl", kLowEscl), ("esca", kLowEsca), ("escb", kLowEscb), ("escx", kLowEscx), ("escx1", kLowEscx1), ("escx2", kLowEscx2), ("esct", kLowEsct), ("esct1", kLowEsct1), ("escty", kLowEscty), ("escty1", kLowEscty1), ("escty2", kLowEscty2), ("lcls", kLowLcls), ("lclsm", kLowLclsm), ("lclsn", kLowLclsn), ("ltail", kLowLtail), ("limp", kLowLimp), ("limp2", kLowLimp2), ("limpm", kLowLimpm), ("limpl", kLowLimpl), ("limpl2", kLowLimpl2), ("limplm", kLowLimplm), ("levo", kLowLevo), ("levoe", kLowLevoe), ("levf", kLowLevf), ("lfld", kLowLfld), ("lfldn", kLowLfldn), ("lbrdf", kLowLbrdf), ("lbrdn", kLowLbrdn), ("levcc", kLowLevcc), ("levcc2", kLowLevcc2), ("levc1", kLowLevc1), ("levcm", kLowLevcm), ("lflw", kLowLflw), ("lhead", kLowLhead), ("lcall", kLowLcall), ("linv", kLowLinv), ("larg", kLowLarg), ("largn", kLowLargn), ("largp", kLowLargp), ("largm", kLowLargm), ("lrb", kLowLrb), ("lbind", kLowLbind), ("lbd", kLowLbd), ("lcond", kLowLcond), ("lcd", kLowLcd), ("lstep", kLowLstep), ("lsxp", kLowLsxp), ("lsiv", kLowLsiv), ("lctor", kLowLctor), ("lctor1", kLowLctor1), ("lctor2", kLowLctor2), ("lctor3", kLowLctor3), ("lctor4", kLowLctor4), ("lctor5", kLowLctor5), ("lconts", kLowLconts), ("larmc", kLowLarmc), ("larmd", kLowLarmd), ("lcarmp", kLowLcarmp), ("llink", kLowLlink), ("llinkb", kLowLlinkb), ("llinkn", kLowLlinkn), ("llinke", kLowLlinke), ("litemc", kLowLitemc), ("litemd", kLowLitemd), ("litemp", kLowLitemp), ("litem3p", kLowLitem3p), ("litem3i", kLowLitem3i), ("liteml", kLowLiteml), ("ltop", kLowLtop), ("main", kLowMain)]
  entry := "main"
  args := [] }

def kLowDecls : List (String × KDecl) :=
  [ ("pkb", { params := [("t", "[]const i64"), ("i", "i64"), ("n", "i64")], ret := some "i64" }),
  ("lxt", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64")], ret := some "i64" }),
  ("ltma", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" }),
  ("ltmb", { params := [("src", "[]const i64"), ("lo", "i64"), ("j", "i64"), ("n", "i64")], ret := some "i64" }),
  ("ltk1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" }),
  ("lty1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" }),
  ("ltm2", { params := [("src", "[]const i64"), ("lo", "i64"), ("j", "i64"), ("n", "i64")], ret := some "i64" }),
  ("lln", { params := [("src", "[]const i64"), ("i", "i64"), ("off", "i64"), ("n", "i64"), ("l", "i64")], ret := some "i64" }),
  ("lbs", { params := [("src", "[]const i64"), ("i", "i64"), ("n", "i64")], ret := some "i64" }),
  ("lpb", { params := [("src", "[]const i64"), ("i", "i64"), ("ls", "i64"), ("j", "i64"), ("n", "i64")], ret := some "i64" }),
  ("lpub", { params := [("src", "[]const i64"), ("j", "i64"), ("n", "i64")], ret := some "i64" }),
  ("lhx", { params := [("d", "i64")], ret := some "string" }),
  ("escl", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string")], ret := some "string" }),
  ("esca", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("c", "i64")], ret := some "string" }),
  ("escb", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("c", "i64"), ("a", "string")], ret := some "string" }),
  ("escx", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("escx1", { params := [("src", "[]const i64"), ("lo", "i64"), ("xt", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("escx2", { params := [("src", "[]const i64"), ("a", "i64"), ("xt", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("esct", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("esct1", { params := [("src", "[]const i64"), ("lo", "i64"), ("b", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("escty", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("escty1", { params := [("src", "[]const i64"), ("lo", "i64"), ("b", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("escty2", { params := [("src", "[]const i64"), ("lo", "i64"), ("c", "i64"), ("n", "i64"), ("out", "string")], ret := some "string" }),
  ("lcls", { params := [("dp", "i64"), ("mod", "[]const i64"), ("fln", "i64"), ("nmod", "i64"), ("out", "string")], ret := some "string" }),
  ("lclsm", { params := [("dp", "i64"), ("mod", "[]const i64"), ("fln", "i64"), ("nmod", "i64"), ("out", "string")], ret := some "string" }),
  ("lclsn", { params := [("dp", "i64"), ("mod", "[]const i64"), ("fln", "i64"), ("nmod", "i64"), ("out", "string")], ret := some "string" }),
  ("ltail", { params := [("mod", "[]const i64"), ("nmod", "i64"), ("out", "string")], ret := some "string" }),
  ("limp", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("limp2", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("limpm", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("limpl", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("limpl2", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("limplm", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levo", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levoe", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levf", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("ff", "i64"), ("bf", "i64"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("lfld", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("ff", "i64"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("lfldn", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("lbrdf", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("lbrdn", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levcc", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levcc2", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levc1", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("r0", "i64"), ("r1", "i64"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("levcm", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("evp", "i64"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("lflw", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64")], ret := some "string" }),
  ("lhead", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lcall", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("linv", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("wh", "i64"), ("as", "i64")], ret := some "string" }),
  ("larg", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("wh", "i64"), ("as", "i64")], ret := some "string" }),
  ("largn", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("wh", "i64"), ("as", "i64")], ret := some "string" }),
  ("largp", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("wh", "i64"), ("as", "i64")], ret := some "string" }),
  ("largm", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("wh", "i64")], ret := some "string" }),
  ("lrb", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("wh", "i64")], ret := some "string" }),
  ("lbind", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lbd", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lcond", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lcd", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lstep", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lsxp", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lsiv", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lctor", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lctor1", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lctor2", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("xt", "i64")], ret := some "string" }),
  ("lctor3", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("xt", "i64"), ("a", "i64")], ret := some "string" }),
  ("lctor4", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("xt", "i64"), ("a", "i64"), ("b", "i64")], ret := some "string" }),
  ("lctor5", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64"), ("a", "i64"), ("b", "i64")], ret := some "string" }),
  ("lconts", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("larmc", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("larmd", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("lcarmp", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("llink", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("llinkb", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("llinkn", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("llinke", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("litemc", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("litemd", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("litemp", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("litem3p", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("litem3i", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("liteml", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("f0", "i64"), ("f1", "i64"), ("fln", "i64"), ("k4", "i64"), ("pr0", "i64"), ("pr1", "i64"), ("q0", "i64"), ("q1", "i64"), ("dp", "i64"), ("af", "i64"), ("cs", "i64"), ("hn", "i64")], ret := some "string" }),
  ("ltop", { params := [("rows", "[]const i64"), ("i", "i64"), ("n", "i64"), ("src", "[]const i64"), ("mod", "[]const i64"), ("out", "string"), ("p0", "i64"), ("p1", "i64"), ("q0", "i64")], ret := some "string" }),
  ("main", { params := [("src", "[]const i64"), ("rows", "[]const i64"), ("mod", "[]const i64")], ret := some "string" }) ]

/-! ## `kWir` — the koru-spelled lowerer — the koru-spelled lowerer (rows → claim sexp)

Mirrors `host2/src/korufe/lower.c` as a surface program: the
same six-int row projection `klow` consumes plus the token
tables a producer hands across the boundary (ident text keyed
by span start in `names`/`nsp`, claim-side string payloads
keyed by quote position in `strs`/`ssp` — koru cannot slice
strings, so name/string text arrives AS DATA).  `nsp` rides
as a packed table — `pix | pairs | eix | hix | xix` — so
name lookup, decl-of-name, dup-tor, and has-impl are O(1)
probes of declared input data rather than O(n) row scans.
Emits the
`(graph …)` document `lower.c` writes; refusal states ride
in-band as `(bad axis)` markers the evaluator refuses.
Generated from `wir.k`'s authority parse — see
_scratch/wir_to_lean.py; the wi/wii races compare the
emitted graph slice against `korufe --lower` byte-for-byte.
-/

/-- Rename invoke/head targets (NOT `jump` — label-local). -/
def renameNode (f : String → String) : KArmNode → KArmNode
  | .terminal => .terminal
  | .jump t a => .jump t a
  | .invoke t a => .invoke (f t) a
  | .produce e => .produce e
  | .retCtor c e => .retCtor c e

def renameArm (f : String → String) : KArm → KArm
  | .mk br anon bind g node kids =>
      .mk br anon bind g (node.map (renameNode f))
        (kids.map (renameArm f))

def renameCallable (f : String → String) : KCallable → KCallable
  | .bare e => .bare e
  | .thunk => .thunk
  | .subflow fl =>
      .subflow { fl with head := (f fl.head.1, fl.head.2)
                         arms := fl.arms.map (renameArm f) }

def prefixGraph (pre : String) (g : List (String × KCallable)) :
    List (String × KCallable) :=
  g.map fun (n, c) => (pre ++ n, renameCallable (pre ++ ·) c)

def kWirPkb : KCallable := .bare
  (.cond (.bin .or (.bin .lt (.var "i") (.lit (.int 0))) (.bin .ge (.var "i") (.var "n"))) (.bin .sub (.lit (.int 0)) (.lit (.int 1))) (.index (.var "t") (.var "i")))

def kWirWn0 : KCallable := .bare
  (.lit (.int 0))

def kWirWc2 : KCallable := .bare
  (.bin .concat (.var "a") (.var "b"))

def kWirWc3 : KCallable := .bare
  (.bin .concat (.var "a") (.bin .concat (.var "b") (.var "c")))

def kWirWc5 : KCallable := .bare
  (.bin .concat (.var "a") (.bin .concat (.var "b") (.bin .concat (.var "c") (.bin .concat (.var "d") (.var "e")))))

def kWirWc7 : KCallable := .bare
  (.bin .concat (.var "a") (.bin .concat (.var "b") (.bin .concat (.var "c") (.bin .concat (.var "d") (.bin .concat (.var "e") (.bin .concat (.var "f") (.var "g")))))))

def kWirWsk : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "ws" false (some "c") (some (.bin .or (.bin .eq (.var "c") (.lit (.int 32))) (.bin .or (.bin .eq (.var "c") (.lit (.int 9))) (.bin .or (.bin .eq (.var "c") (.lit (.int 10))) (.bin .eq (.var "c") (.lit (.int 13))))))) (some (.invoke "wsk" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi"))])) [], .mk "dn" false (some "_") none (some (.produce (.var "i"))) []] }

def kWirWtb : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "j")), ("n", (.var "n"))])
  arms := [.mk "ws" false (some "c") (some (.bin .and (.bin .ge (.var "j") (.var "lo")) (.bin .or (.bin .eq (.var "c") (.lit (.int 32))) (.bin .or (.bin .eq (.var "c") (.lit (.int 9))) (.bin .or (.bin .eq (.var "c") (.lit (.int 10))) (.bin .eq (.var "c") (.lit (.int 13)))))))) (some (.invoke "wtb" [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "j") (.lit (.int 1)))), ("n", (.var "n"))])) [], .mk "dn" false (some "_") none (some (.produce (.bin .add (.var "j") (.lit (.int 1))))) []] }

def kWirWid : KCallable := .bare
  (.cond (.bin .or (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 97))) (.bin .le (.var "c") (.lit (.int 122)))) (.bin .and (.bin .ge (.var "c") (.lit (.int 65))) (.bin .le (.var "c") (.lit (.int 90))))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57)))) (.bin .eq (.var "c") (.lit (.int 95))))) (.lit (.int 1)) (.lit (.int 0)))

def kWirWpe : KCallable := .subflow {
  preLabel := none
  head := ("wid", [("c", (.var "c"))])
  arms := [.mk "ok" false (some "r") (some (.bin .eq (.var "r") (.lit (.int 1)))) (some (.produce (.lit (.int 1)))) [], .mk "mo" false (some "_") none (some (.produce (.cond (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 41))) (.bin .eq (.var "c") (.lit (.int 93)))) (.bin .or (.bin .eq (.var "c") (.lit (.int 125))) (.bin .eq (.var "c") (.lit (.int 34))))) (.lit (.int 1)) (.lit (.int 0))))) []] }

def kWirWnat : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "nsp")), ("i", (.bin .mul (.lit (.int 2)) (.var "i"))), ("n", (.bin .mul (.lit (.int 2)) (.var "nn")))])
  arms := [.mk "hit" false (some "v") (some (.bin .and (.bin .eq (.var "v") (.var "p")) (.bin .lt (.var "i") (.var "nn")))) (some (.produce (.var "i"))) [], .mk "nx" false (some "_") (some (.bin .lt (.var "i") (.var "nn"))) (some (.invoke "wnat" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("p", (.var "p"))])) [], .mk "no" false (some "_") none (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) []] }

def kWirWpix : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "nsp")), ("i", (.var "p")), ("n", (.bin .sub (.builtin "len" [(.var "nsp")]) (.bin .mul (.lit (.int 5)) (.var "nn"))))])
  arms := [.mk "k" false (some "k") none (some (.produce (.var "k"))) []] }

def kWirWnm : KCallable := .subflow {
  preLabel := none
  head := ("wpix", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "p"))])
  arms := [.mk "ok" false (some "k") (some (.bin .ge (.var "k") (.lit (.int 0)))) (some (.produce (.index (.var "names") (.var "k")))) [], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad names)")))) []] }

def kWirWne : KCallable := .subflow {
  preLabel := none
  head := ("wpix", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "p"))])
  arms := [.mk "ok" false (some "k") (some (.bin .ge (.var "k") (.lit (.int 0)))) (some (.produce (.index (.var "nsp") (.bin .add (.bin .add (.bin .sub (.builtin "len" [(.var "nsp")]) (.bin .mul (.lit (.int 5)) (.var "nn"))) (.bin .mul (.lit (.int 2)) (.var "k"))) (.lit (.int 1)))))) [], .mk "no" false (some "_") none (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) []] }

def kWirWst : KCallable := .subflow {
  preLabel := none
  head := ("wnat", [("nsp", (.var "ssp")), ("nn", (.var "ns")), ("i", (.lit (.int 0))), ("p", (.var "p"))])
  arms := [.mk "ok" false (some "k") (some (.bin .ge (.var "k") (.lit (.int 0)))) (some (.produce (.index (.var "strs") (.var "k")))) [], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad strs)")))) []] }

def kWirWeq : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "ln" false (some "_") (some (.bin .ne (.bin .sub (.var "b") (.var "a")) (.bin .sub (.var "y") (.var "x")))) (some (.produce (.lit (.int 0)))) [], .mk "ok" false (some "_") none (some (.invoke "weql" [("src", (.var "src")), ("a", (.var "a")), ("b", (.var "b")), ("x", (.var "x")), ("y", (.var "y")), ("i", (.lit (.int 0)))])) []] }

def kWirWeql : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "a") (.var "i"))), ("n", (.var "b"))])
  arms := [.mk "dn" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.lit (.int 1)))) [], .mk "mm" false (some "c") (some (.cond (.bin .lt (.bin .add (.var "x") (.var "i")) (.var "y")) (.bin .ne (.var "c") (.index (.var "src") (.bin .add (.var "x") (.var "i")))) (.lit (.bool true)))) (some (.produce (.lit (.int 0)))) [], .mk "mo" false (some "_") none (some (.invoke "weql" [("src", (.var "src")), ("a", (.var "a")), ("b", (.var "b")), ("x", (.var "x")), ("y", (.var "y")), ("i", (.bin .add (.var "i") (.lit (.int 1))))])) []] }

def kWirWnv : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "dg" false (some "c") (some (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57))))) (some (.invoke "wnv" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("v", (.bin .add (.bin .mul (.var "v") (.lit (.int 10))) (.bin .sub (.var "c") (.lit (.int 48)))))])) [], .mk "dn" false (some "_") none (some (.produce (.var "v"))) []] }

def kWirWp10 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "z" false (some "_") (some (.bin .le (.var "n") (.lit (.int 0)))) (some (.produce (.lit (.int 1)))) [], .mk "mo" false (some "_") none (some (.invoke "wp10m" [("n", (.var "n"))])) []] }

def kWirWp10m : KCallable := .subflow {
  preLabel := none
  head := ("wp10", [("n", (.bin .sub (.var "n") (.lit (.int 1))))])
  arms := [.mk "t" false (some "t") none (some (.produce (.bin .mul (.var "t") (.lit (.int 10))))) []] }

def kWirWgcd : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "z" false (some "_") (some (.bin .eq (.var "b") (.lit (.int 0)))) (some (.produce (.var "a"))) [], .mk "mo" false (some "_") none (some (.invoke "wgcd" [("a", (.var "b")), ("b", (.bin .mod (.var "a") (.var "b")))])) []] }

def kWirWpb : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .sub (.var "i") (.lit (.int 1)))), ("n", (.var "i"))])
  arms := [.mk "nd" false (some "_") (some (.bin .le (.var "i") (.var "lo"))) (some (.produce (.lit (.int 0)))) [], .mk "ws" false (some "c") (some (.bin .or (.bin .eq (.var "c") (.lit (.int 32))) (.bin .or (.bin .eq (.var "c") (.lit (.int 9))) (.bin .or (.bin .eq (.var "c") (.lit (.int 10))) (.bin .eq (.var "c") (.lit (.int 13))))))) (some (.invoke "wpb" [("src", (.var "src")), ("lo", (.var "lo")), ("i", (.bin .sub (.var "i") (.lit (.int 1))))])) [], .mk "ch" false (some "c") none (some (.produce (.var "c"))) []] }

def kWirWopa : KCallable := .subflow {
  preLabel := none
  head := ("wpb", [("src", (.var "src")), ("lo", (.var "lo")), ("i", (.var "i"))])
  arms := [.mk "op" false (some "p") (some (.bin .and (.bin .and (.bin .eq (.var "d") (.lit (.int 0))) (.bin .eq (.var "ins") (.lit (.int 0)))) (.bin .lt (.var "i") (.var "hi")))) (some (.invoke "wopb" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWopb : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "cm" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 47))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 47))) (.lit (.bool false))))) (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 2))))) [], .mk "oo" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 124))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 124))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 12)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "aa" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 38))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 38))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 11)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "ee" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 61))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 61))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 5)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "ne" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 33))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 61))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 6)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "le" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 60))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 61))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 8)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "ge" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 62))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 61))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 10)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "cc" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 43))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 43))) (.lit (.bool false))))) (some (.produce (.bin .add (.bin .mul (.lit (.int 13)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "lt" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 60)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 7)) (.lit (.int 8))) (.lit (.int 1))))) [], .mk "gt" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 62)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 9)) (.lit (.int 8))) (.lit (.int 1))))) [], .mk "mu" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 42)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 2)) (.lit (.int 8))) (.lit (.int 1))))) [], .mk "dv" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 47)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 3)) (.lit (.int 8))) (.lit (.int 1))))) [], .mk "rm" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 37)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 4)) (.lit (.int 8))) (.lit (.int 1))))) [], .mk "ad" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 43)))) (some (.invoke "wope" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p")), ("op", (.lit (.int 0)))])) [], .mk "sb" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 45)))) (some (.invoke "wops" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p"))])) [], .mk "wo" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 111)))) (some (.invoke "wopo" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p"))])) [], .mk "wa" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 97)))) (some (.invoke "wopd" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWope : KCallable := .subflow {
  preLabel := none
  head := ("wpe", [("c", (.var "p"))])
  arms := [.mk "ok" false (some "v") (some (.bin .eq (.var "v") (.lit (.int 1)))) (some (.produce (.bin .add (.bin .mul (.var "op") (.lit (.int 8))) (.lit (.int 1))))) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWops : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "gl" false (some "n") (some (.bin .and (.bin .or (.bin .and (.bin .ge (.var "p") (.lit (.int 97))) (.bin .le (.var "p") (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.var "p") (.lit (.int 65))) (.bin .le (.var "p") (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.var "p") (.lit (.int 48))) (.bin .le (.var "p") (.lit (.int 57)))) (.bin .eq (.var "p") (.lit (.int 95)))))) (.bin .or (.bin .or (.bin .and (.bin .ge (.var "n") (.lit (.int 97))) (.bin .le (.var "n") (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.var "n") (.lit (.int 65))) (.bin .le (.var "n") (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.var "n") (.lit (.int 48))) (.bin .le (.var "n") (.lit (.int 57)))) (.bin .eq (.var "n") (.lit (.int 95)))))) (.bin .eq (.var "n") (.lit (.int 45)))))) (some (.produce (.lit (.int 0)))) [], .mk "op" false (some "_") none (some (.invoke "wope" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p")), ("op", (.lit (.int 1)))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWopo : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "rr" false (some "n") (some (.bin .eq (.var "n") (.lit (.int 114)))) (some (.invoke "wopo2" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWopo2 : KCallable := .subflow {
  preLabel := none
  head := ("wpe", [("c", (.var "p"))])
  arms := [.mk "pe" false (some "v") (some (.bin .eq (.var "v") (.lit (.int 1)))) (some (.invoke "wopob" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWopob : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 2)))), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 12)) (.lit (.int 8))) (.lit (.int 2))))) [], .mk "ic" false (some "c") (some (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 97))) (.bin .le (.var "c") (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 65))) (.bin .le (.var "c") (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57)))) (.bin .eq (.var "c") (.lit (.int 95))))))) (some (.produce (.lit (.int 0)))) [], .mk "gl" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 45))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 3))) (.var "hi")) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 97))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 65))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 48))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 57)))) (.bin .or (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 95))) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 45))))))) (.lit (.bool false))))) (some (.produce (.lit (.int 0)))) [], .mk "ok" false (some "_") none (some (.produce (.bin .add (.bin .mul (.lit (.int 12)) (.lit (.int 8))) (.lit (.int 2))))) []] }

def kWirWopd : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "rr" false (some "n") (some (.bin .and (.bin .eq (.var "n") (.lit (.int 110))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 2))) (.var "hi")) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 2)))) (.lit (.int 100))) (.lit (.bool false))))) (some (.invoke "wopd2" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("p", (.var "p"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWopd2 : KCallable := .subflow {
  preLabel := none
  head := ("wpe", [("c", (.var "p"))])
  arms := [.mk "pe" false (some "v") (some (.bin .eq (.var "v") (.lit (.int 1)))) (some (.invoke "wopdb" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWopdb : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 3)))), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.bin .add (.bin .mul (.lit (.int 11)) (.lit (.int 8))) (.lit (.int 3))))) [], .mk "ic" false (some "c") (some (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 97))) (.bin .le (.var "c") (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 65))) (.bin .le (.var "c") (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57)))) (.bin .eq (.var "c") (.lit (.int 95))))))) (some (.produce (.lit (.int 0)))) [], .mk "gl" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 45))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 4))) (.var "hi")) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 97))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 65))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 48))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 57)))) (.bin .or (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 95))) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 4)))) (.lit (.int 45))))))) (.lit (.bool false))))) (some (.produce (.lit (.int 0)))) [], .mk "ok" false (some "_") none (some (.produce (.bin .add (.bin .mul (.lit (.int 11)) (.lit (.int 8))) (.lit (.int 3))))) []] }

def kWirWprc : KCallable := .bare
  (.cond (.bin .eq (.var "o") (.lit (.int 12))) (.lit (.int 1)) (.cond (.bin .eq (.var "o") (.lit (.int 11))) (.lit (.int 2)) (.cond (.bin .or (.bin .eq (.var "o") (.lit (.int 5))) (.bin .eq (.var "o") (.lit (.int 6)))) (.lit (.int 3)) (.cond (.bin .and (.bin .ge (.var "o") (.lit (.int 7))) (.bin .le (.var "o") (.lit (.int 10)))) (.lit (.int 4)) (.cond (.bin .eq (.var "o") (.lit (.int 13))) (.lit (.int 5)) (.cond (.bin .or (.bin .eq (.var "o") (.lit (.int 0))) (.bin .eq (.var "o") (.lit (.int 1)))) (.lit (.int 6)) (.lit (.int 7))))))))

def kWirWopn : KCallable := .bare
  (.cond (.bin .eq (.var "o") (.lit (.int 0))) (.lit (.str "add")) (.cond (.bin .eq (.var "o") (.lit (.int 1))) (.lit (.str "sub")) (.cond (.bin .eq (.var "o") (.lit (.int 2))) (.lit (.str "mul")) (.cond (.bin .eq (.var "o") (.lit (.int 3))) (.lit (.str "div")) (.cond (.bin .eq (.var "o") (.lit (.int 4))) (.lit (.str "mod")) (.cond (.bin .eq (.var "o") (.lit (.int 5))) (.lit (.str "eq")) (.cond (.bin .eq (.var "o") (.lit (.int 6))) (.lit (.str "ne")) (.cond (.bin .eq (.var "o") (.lit (.int 7))) (.lit (.str "lt")) (.cond (.bin .eq (.var "o") (.lit (.int 8))) (.lit (.str "le")) (.cond (.bin .eq (.var "o") (.lit (.int 9))) (.lit (.str "gt")) (.cond (.bin .eq (.var "o") (.lit (.int 10))) (.lit (.str "ge")) (.cond (.bin .eq (.var "o") (.lit (.int 11))) (.lit (.str "and")) (.cond (.bin .eq (.var "o") (.lit (.int 12))) (.lit (.str "or")) (.lit (.str "concat")))))))))))))))

def kWirWfp : KCallable := .subflow {
  preLabel := none
  head := ("wopa", [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("d", (.var "d")), ("ins", (.var "ins"))])
  arms := [.mk "fin" false (some "o") (some (.bin .or (.bin .ge (.var "i") (.var "hi")) (.bin .eq (.var "o") (.bin .sub (.lit (.int 0)) (.lit (.int 2)))))) (some (.produce (.var "last"))) [], .mk "hit" false (some "o") (some (.bin .ne (.var "o") (.lit (.int 0)))) (some (.invoke "wfp1" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "last")), ("prec", (.var "prec")), ("o", (.var "o"))])) [], .mk "mo" false (some "_") none (some (.invoke "wfpn" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "last")), ("prec", (.var "prec"))])) []] }

def kWirWfp1 : KCallable := .subflow {
  preLabel := none
  head := ("wprc", [("o", (.bin .div (.var "o") (.lit (.int 8))))])
  arms := [.mk "hit" false (some "q") (some (.bin .eq (.var "q") (.var "prec"))) (some (.invoke "wfpn" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "i")), ("prec", (.var "prec"))])) [], .mk "no" false (some "_") none (some (.invoke "wfpn" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "last")), ("prec", (.var "prec"))])) []] }

def kWirWfpn : KCallable := .subflow {
  preLabel := none
  head := ("wfp", [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.bin .add (.var "i") (.cond (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 92)))) (.lit (.int 2)) (.lit (.int 1))))), ("d", (.cond (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 40))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 91)))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 123))))) (.bin .add (.var "d") (.lit (.int 1))) (.cond (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 41))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 93)))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 125))))) (.bin .sub (.var "d") (.lit (.int 1))) (.var "d")))), ("ins", (.cond (.bin .and (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.bin .eq (.var "ins") (.lit (.int 0)))) (.lit (.int 1)) (.cond (.bin .and (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.bin .eq (.var "ins") (.lit (.int 1)))) (.lit (.int 0)) (.var "ins")))), ("last", (.var "last")), ("prec", (.var "prec"))])
  arms := [.mk "r" false (some "r") none (some (.produce (.var "r"))) []] }

def kWirWmb : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "st" false (some "_") none (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.lit (.int 1))), ("ins", (.lit (.int 0)))])) []] }

def kWirWmb1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.var "hi"))) [], .mk "qo" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .eq (.var "c") (.lit (.int 34))))) (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.lit (.int 1)))])) [], .mk "qc" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.var "c") (.lit (.int 34))))) (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.lit (.int 0)))])) [], .mk "bs" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.var "c") (.lit (.int 92))))) (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 2)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) [], .mk "oo" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 40))) (.bin .eq (.var "c") (.lit (.int 91)))) (.bin .eq (.var "c") (.lit (.int 123)))))) (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.bin .add (.var "d") (.lit (.int 1)))), ("ins", (.var "ins"))])) [], .mk "xc" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 41))) (.bin .eq (.var "c") (.lit (.int 93)))) (.bin .eq (.var "c") (.lit (.int 125)))))) (some (.invoke "wmbx" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("d", (.var "d"))])) [], .mk "mo" false (some "_") none (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])) []] }

def kWirWmbx : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "z" false (some "_") (some (.bin .eq (.bin .sub (.var "d") (.lit (.int 1))) (.lit (.int 0)))) (some (.produce (.var "i"))) [], .mk "mo" false (some "_") none (some (.invoke "wmb1" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.bin .sub (.var "d") (.lit (.int 1)))), ("ins", (.lit (.int 0)))])) []] }

def kWirWss : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.var "hi"))) [], .mk "qt" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 34)))) (some (.produce (.bin .add (.var "i") (.lit (.int 2))))) [], .mk "bs" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 92)))) (some (.invoke "wss" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 2)))), ("hi", (.var "hi"))])) [], .mk "mo" false (some "_") none (some (.invoke "wss" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi"))])) []] }

def kWirWen : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "dg" false (some "c") (some (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57))))) (some (.invoke "wen" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi"))])) [], .mk "dt" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 46))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 48))) (.bin .le (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 57)))) (.lit (.bool false))))) (some (.invoke "wen" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi"))])) [], .mk "dn" false (some "_") none (some (.produce (.var "i"))) []] }

def kWirWcmx : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.var "i"))) [], .mk "cm" false (some "c") (some (.bin .and (.bin .eq (.var "d") (.lit (.int 0))) (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .eq (.var "c") (.var "w"))))) (some (.produce (.var "i"))) [], .mk "qo" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .eq (.var "c") (.lit (.int 34))))) (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.lit (.int 1))), ("w", (.var "w"))])) [], .mk "qc" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.var "c") (.lit (.int 34))))) (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.lit (.int 0))), ("w", (.var "w"))])) [], .mk "bs" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.var "c") (.lit (.int 92))))) (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 2)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("w", (.var "w"))])) [], .mk "oo" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 40))) (.bin .eq (.var "c") (.lit (.int 91)))) (.bin .eq (.var "c") (.lit (.int 123)))))) (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.bin .add (.var "d") (.lit (.int 1)))), ("ins", (.var "ins")), ("w", (.var "w"))])) [], .mk "xc" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 41))) (.bin .eq (.var "c") (.lit (.int 93)))) (.bin .eq (.var "c") (.lit (.int 125)))))) (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.bin .sub (.var "d") (.lit (.int 1)))), ("ins", (.var "ins")), ("w", (.var "w"))])) [], .mk "mo" false (some "_") none (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("w", (.var "w"))])) []] }

def kWirWfd : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.var "last"))) [], .mk "dt" false (some "c") (some (.bin .and (.bin .eq (.var "d") (.lit (.int 0))) (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .eq (.var "c") (.lit (.int 46)))))) (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "i"))])) [], .mk "qo" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .eq (.var "c") (.lit (.int 34))))) (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.lit (.int 1))), ("last", (.var "last"))])) [], .mk "qc" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.var "c") (.lit (.int 34))))) (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.lit (.int 0))), ("last", (.var "last"))])) [], .mk "bs" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.var "c") (.lit (.int 92))))) (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 2)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "last"))])) [], .mk "oo" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 40))) (.bin .eq (.var "c") (.lit (.int 91)))) (.bin .eq (.var "c") (.lit (.int 123)))))) (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.bin .add (.var "d") (.lit (.int 1)))), ("ins", (.var "ins")), ("last", (.var "last"))])) [], .mk "xc" false (some "c") (some (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.var "c") (.lit (.int 41))) (.bin .eq (.var "c") (.lit (.int 93)))) (.bin .eq (.var "c") (.lit (.int 125)))))) (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.bin .sub (.var "d") (.lit (.int 1)))), ("ins", (.var "ins")), ("last", (.var "last"))])) [], .mk "mo" false (some "_") none (some (.invoke "wfd" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("last", (.var "last"))])) []] }

def kWirWty : KCallable := .bare
  (.cond (.bin .or (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "i64"))) (.bin .eq (.var "nm") (.lit (.str "i32")))) (.bin .or (.bin .eq (.var "nm") (.lit (.str "i16"))) (.bin .eq (.var "nm") (.lit (.str "i8"))))) (.bin .or (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "u64"))) (.bin .eq (.var "nm") (.lit (.str "u32")))) (.bin .or (.bin .eq (.var "nm") (.lit (.str "u16"))) (.bin .eq (.var "nm") (.lit (.str "u8"))))) (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "f64"))) (.bin .eq (.var "nm") (.lit (.str "f32")))) (.bin .or (.bin .eq (.var "nm") (.lit (.str "bool"))) (.bin .eq (.var "nm") (.lit (.str "string"))))))) (.lit (.int 1)) (.cond (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "program"))) (.bin .eq (.var "nm") (.lit (.str "void")))) (.bin .eq (.var "nm") (.lit (.str "unit")))) (.lit (.int 1)) (.lit (.int 0))))

def kWirWbl : KCallable := .bare
  (.cond (.bin .or (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "as"))) (.bin .eq (.var "nm") (.lit (.str "intCast")))) (.bin .or (.bin .eq (.var "nm") (.lit (.str "truncate"))) (.bin .eq (.var "nm") (.lit (.str "divTrunc"))))) (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "rem"))) (.bin .eq (.var "nm") (.lit (.str "mod")))) (.bin .or (.bin .eq (.var "nm") (.lit (.str "len"))) (.bin .eq (.var "nm") (.lit (.str "intToString")))))) (.lit (.int 1)) (.lit (.int 0)))

def kWirWev : KCallable := .subflow {
  preLabel := none
  head := ("wfp", [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "lo")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("last", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("prec", (.var "lv"))])
  arms := [.mk "hit" false (some "t") (some (.bin .ge (.var "t") (.lit (.int 0)))) (some (.invoke "wspl" [("lv", (.var "lv")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("t", (.var "t")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "dn" false (some "_") none (some (.invoke "wenx" [("lv", (.var "lv")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWenx : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "nx" false (some "_") (some (.bin .lt (.var "lv") (.lit (.int 7)))) (some (.invoke "wev" [("lv", (.bin .add (.var "lv") (.lit (.int 1)))), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "bt" false (some "_") none (some (.invoke "weu" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWspl : KCallable := .subflow {
  preLabel := none
  head := ("wopa", [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "t")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0)))])
  arms := [.mk "oi" false (some "o") (some (.bin .gt (.var "o") (.lit (.int 0)))) (some (.invoke "wev" [("lv", (.var "lv")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "t")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "l") none (some (.invoke "wsplr" [("lv", (.var "lv")), ("src", (.var "src")), ("lo", (.bin .add (.var "t") (.bin .sub (.var "o") (.bin .mul (.bin .div (.var "o") (.lit (.int 8))) (.lit (.int 8)))))), ("hi", (.var "hi")), ("op", (.bin .div (.var "o") (.lit (.int 8)))), ("l", (.var "l")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad expr)")))) []] }

def kWirWsplr : KCallable := .subflow {
  preLabel := none
  head := ("wev", [("lv", (.var "lv")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "r" false (some "r") none (some (.invoke "wc7" [("a", (.lit (.str "(bin "))), ("b", (.cond (.bin .eq (.var "op") (.lit (.int 0))) (.lit (.str "add")) (.cond (.bin .eq (.var "op") (.lit (.int 1))) (.lit (.str "sub")) (.cond (.bin .eq (.var "op") (.lit (.int 2))) (.lit (.str "mul")) (.cond (.bin .eq (.var "op") (.lit (.int 3))) (.lit (.str "div")) (.cond (.bin .eq (.var "op") (.lit (.int 4))) (.lit (.str "mod")) (.cond (.bin .eq (.var "op") (.lit (.int 5))) (.lit (.str "eq")) (.cond (.bin .eq (.var "op") (.lit (.int 6))) (.lit (.str "ne")) (.cond (.bin .eq (.var "op") (.lit (.int 7))) (.lit (.str "lt")) (.cond (.bin .eq (.var "op") (.lit (.int 8))) (.lit (.str "le")) (.cond (.bin .eq (.var "op") (.lit (.int 9))) (.lit (.str "gt")) (.cond (.bin .eq (.var "op") (.lit (.int 10))) (.lit (.str "ge")) (.cond (.bin .eq (.var "op") (.lit (.int 11))) (.lit (.str "and")) (.cond (.bin .eq (.var "op") (.lit (.int 12))) (.lit (.str "or")) (.lit (.str "concat")))))))))))))))), ("c", (.lit (.str " "))), ("d", (.var "l")), ("e", (.lit (.str " "))), ("f", (.var "r")), ("g", (.lit (.str ")")))])) []] }

def kWirWeu : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "hi"))])
  arms := [.mk "nt" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 33))) (.lit (.bool false)))) (some (.invoke "weu1" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("op", (.lit (.int 1))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "ng" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 45))) (.lit (.bool false)))) (some (.invoke "weu1" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("op", (.lit (.int 0))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "dn" false (some "_") none (some (.invoke "wep" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWeu1 : KCallable := .subflow {
  preLabel := none
  head := ("weu", [("src", (.var "src")), ("lo", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "e" false (some "e") none (some (.produce (.cond (.bin .eq (.var "op") (.lit (.int 1))) (.bin .concat (.lit (.str "(un not ")) (.bin .concat (.var "e") (.lit (.str ")")))) (.bin .concat (.lit (.str "(un neg ")) (.bin .concat (.var "e") (.lit (.str ")"))))))) []] }

def kWirWpm : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "hi"))])
  arms := [.mk "lp" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 40))) (.lit (.bool false)))) (some (.invoke "wpmc" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "lb" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 91))) (.lit (.bool false)))) (some (.invoke "wpmc" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "lc" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 123))) (.lit (.bool false)))) (some (.invoke "wpmc" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "st" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.lit (.bool false)))) (some (.invoke "wss" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "at" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 64))) (.lit (.bool false)))) (some (.produce (.var "hi"))) [], .mk "dg" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 48))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 57)))) (.lit (.bool false)))) (some (.invoke "wen" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "id" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 97))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 65))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 90)))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 95))))) (.lit (.bool false)))) (some (.invoke "wpmv" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) [], .mk "no" false (some "_") none (some (.produce (.var "hi"))) []] }

def kWirWpmc : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.produce (.cond (.bin .lt (.var "m") (.var "hi")) (.bin .add (.var "m") (.lit (.int 1))) (.var "hi")))) []] }

def kWirWpmv : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "i"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wpmv1" [("src", (.var "src")), ("i", (.var "i")), ("e", (.var "e")), ("hi", (.var "hi"))])) []] }

def kWirWpmv1 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "iff" false (some "_") (some (.bin .and (.bin .eq (.var "e") (.bin .add (.var "i") (.lit (.int 2)))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 1))) (.var "hi")) (.bin .and (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 105))) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 102)))) (.lit (.bool false))))) (some (.produce (.var "hi"))) [], .mk "nm" false (some "_") none (some (.invoke "wpmv2" [("src", (.var "src")), ("e", (.var "e")), ("hi", (.var "hi"))])) []] }

def kWirWpmv2 : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "e")), ("hi", (.var "hi"))])
  arms := [.mk "ca" false (some "j") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 40))) (.lit (.bool false)))) (some (.invoke "wpmc" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi"))])) [], .mk "dn" false (some "_") none (some (.produce (.var "e"))) []] }

def kWirWep : KCallable := .subflow {
  preLabel := none
  head := ("wpm", [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])
  arms := [.mk "pe" false (some "p") none (some (.invoke "wem" [("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "p")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "a") none (some (.invoke "wep1" [("src", (.var "src")), ("i", (.var "p")), ("hi", (.var "hi")), ("acc", (.var "a")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWep1 : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "dt" false (some "j") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 46))) (.lit (.bool false)))) (some (.invoke "wep1f" [("src", (.var "src")), ("j", (.var "j")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "ix" false (some "j") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 91))) (.lit (.bool false)))) (some (.invoke "wep1i" [("src", (.var "src")), ("j", (.var "j")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "ca" false (some "j") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 40))) (.lit (.bool false)))) (some (.produce (.lit (.str "(bad expr-call)")))) [], .mk "ws" false (some "j") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .or (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 32))) (.bin .or (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 9))) (.bin .or (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 10))) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 13)))))) (.lit (.bool false)))) (some (.invoke "wep1" [("src", (.var "src")), ("i", (.bin .add (.var "j") (.lit (.int 1)))), ("hi", (.var "hi")), ("acc", (.var "acc")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "dn" false (some "_") none (some (.produce (.var "acc"))) []] }

def kWirWep1f : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.bin .add (.var "j") (.lit (.int 1))))])
  arms := [.mk "ok" false (some "e") (some (.bin .gt (.var "e") (.bin .add (.var "j") (.lit (.int 1))))) (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.bin .add (.var "j") (.lit (.int 1))))])) [.mk "_chain" false (some "nm") none (some (.invoke "wep1" [("src", (.var "src")), ("i", (.var "e")), ("hi", (.var "hi")), ("acc", (.bin .concat (.lit (.str "(field ")) (.bin .concat (.var "acc") (.bin .concat (.lit (.str " ")) (.bin .concat (.var "nm") (.lit (.str ")"))))))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad expr)")))) []] }

def kWirWep1i : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.bin .add (.var "j") (.lit (.int 1)))), ("hi", (.var "hi"))])
  arms := [.mk "ty" false (some "k") none (some (.invoke "wep1t" [("src", (.var "src")), ("j", (.var "j")), ("k", (.var "k")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWep1t : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "k"))])
  arms := [.mk "an" false (some "nm") none (some (.invoke "wty" [("nm", (.var "nm"))])) [.mk "_chain" false (some "t") none (some (.invoke "wep1u" [("src", (.var "src")), ("j", (.var "j")), ("k", (.var "k")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("t", (.var "t")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWep1u : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "k"))])
  arms := [.mk "sk" false (some "e") (some (.bin .and (.bin .eq (.var "t") (.lit (.int 1))) (.bin .gt (.var "e") (.var "k")))) (some (.invoke "wep1v" [("src", (.var "src")), ("j", (.var "j")), ("e", (.var "e")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "ix" false (some "_") none (some (.invoke "wmb" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi"))])) [.mk "_chain" false (some "m") none (some (.invoke "wev" [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.bin .add (.var "j") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "wep1w" [("src", (.var "src")), ("m", (.var "m")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("x", (.var "x")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]]] }

def kWirWep1v : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "e")), ("hi", (.var "hi"))])
  arms := [.mk "rb" false (some "q") (some (.cond (.bin .lt (.var "q") (.var "hi")) (.bin .eq (.index (.var "src") (.var "q")) (.lit (.int 93))) (.lit (.bool false)))) (some (.invoke "wep1" [("src", (.var "src")), ("i", (.bin .add (.var "q") (.lit (.int 1)))), ("hi", (.var "hi")), ("acc", (.var "acc")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "ix" false (some "_") none (some (.invoke "wmb" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi"))])) [.mk "_chain" false (some "m") none (some (.invoke "wev" [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.bin .add (.var "j") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "wep1w" [("src", (.var "src")), ("m", (.var "m")), ("hi", (.var "hi")), ("acc", (.var "acc")), ("x", (.var "x")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]]] }

def kWirWep1w : KCallable := .subflow {
  preLabel := none
  head := ("wc5", [("a", (.lit (.str "(index "))), ("b", (.var "acc")), ("c", (.lit (.str " "))), ("d", (.var "x")), ("e", (.lit (.str ")")))])
  arms := [.mk "a" false (some "a") none (some (.invoke "wep1" [("src", (.var "src")), ("i", (.bin .add (.var "m") (.lit (.int 1)))), ("hi", (.var "hi")), ("acc", (.var "a")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWem : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "hi"))])
  arms := [.mk "lp" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 40))) (.lit (.bool false)))) (some (.invoke "wemg" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "lb" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 91))) (.lit (.bool false)))) (some (.invoke "wema" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "lc" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 123))) (.lit (.bool false)))) (some (.invoke "wemc" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "at" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 64))) (.lit (.bool false)))) (some (.invoke "wemb" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "st" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.lit (.bool false)))) (some (.invoke "wems" [("src", (.var "src")), ("i", (.var "i")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "dg" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 48))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 57)))) (.lit (.bool false)))) (some (.invoke "wnum" [("src", (.var "src")), ("lo", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "wc3" [("a", (.lit (.str "(lit "))), ("b", (.var "x")), ("c", (.lit (.str ")")))])) []], .mk "id" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 97))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 65))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 90)))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 95))))) (.lit (.bool false)))) (some (.invoke "wemv" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad expr)")))) []] }

def kWirWems : KCallable := .subflow {
  preLabel := none
  head := ("wst", [("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("p", (.var "i"))])
  arms := [.mk "s" false (some "s") none (some (.invoke "wc5" [("a", (.lit (.str "(lit (str "))), ("b", (.lit (.str "\""))), ("c", (.var "s")), ("d", (.lit (.str "\""))), ("e", (.lit (.str "))")))])) []] }

def kWirWemg : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.invoke "wev" [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWema : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.invoke "weal" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "m")), ("out", (.lit (.str "(lit (arr"))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "t") none (some (.invoke "wc3" [("a", (.var "t")), ("b", (.lit (.str ")"))), ("c", (.lit (.str ")")))])) []]] }

def kWirWeal : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "dn" false (some "j") (some (.bin .ge (.var "j") (.var "hi"))) (some (.produce (.var "out"))) [], .mk "el" false (some "j") none (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 44)))])) [.mk "_chain" false (some "c") none (some (.invoke "weal1" [("src", (.var "src")), ("j", (.var "j")), ("c", (.var "c")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWeal1 : KCallable := .subflow {
  preLabel := none
  head := ("wel", [("src", (.var "src")), ("lo", (.var "j")), ("hi", (.var "c")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "x" false (some "x") none (some (.invoke "wc3" [("a", (.var "out")), ("b", (.lit (.str " "))), ("c", (.var "x"))])) [.mk "_chain" false (some "o") none (some (.invoke "weal" [("src", (.var "src")), ("i", (.bin .add (.var "c") (.lit (.int 1)))), ("hi", (.var "hi")), ("out", (.var "o")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWemc : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.invoke "wecl" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "m")), ("out", (.lit (.str "(lit (cell"))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "t") none (some (.invoke "wc3" [("a", (.var "t")), ("b", (.lit (.str ")"))), ("c", (.lit (.str ")")))])) []]] }

def kWirWecl : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "dn" false (some "j") (some (.bin .ge (.var "j") (.var "hi"))) (some (.produce (.var "out"))) [], .mk "f" false (some "j") none (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 58)))])) [.mk "_chain" false (some "c") none (some (.invoke "wecl1" [("src", (.var "src")), ("j", (.var "j")), ("c", (.var "c")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWecl1 : KCallable := .subflow {
  preLabel := none
  head := ("wcmx", [("src", (.var "src")), ("i", (.bin .add (.var "c") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 44)))])
  arms := [.mk "m" false (some "m") none (some (.invoke "wecl2" [("src", (.var "src")), ("j", (.var "j")), ("c", (.var "c")), ("m", (.var "m")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWecl2 : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "j"))])
  arms := [.mk "fn" false (some "nm") none (some (.invoke "wel" [("src", (.var "src")), ("lo", (.bin .add (.var "c") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "wecl3" [("src", (.var "src")), ("m", (.var "m")), ("hi", (.var "hi")), ("out", (.var "out")), ("nm", (.var "nm")), ("x", (.var "x")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWecl3 : KCallable := .subflow {
  preLabel := none
  head := ("wc5", [("a", (.var "out")), ("b", (.lit (.str " ("))), ("c", (.var "nm")), ("d", (.lit (.str " "))), ("e", (.var "x"))])
  arms := [.mk "o" false (some "o") none (some (.invoke "wc3" [("a", (.var "o")), ("b", (.lit (.str ")"))), ("c", (.lit (.str "")))])) [.mk "_chain" false (some "p") none (some (.invoke "wecl" [("src", (.var "src")), ("i", (.bin .add (.var "m") (.lit (.int 1)))), ("hi", (.var "hi")), ("out", (.var "p")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWemb : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.bin .add (.var "i") (.lit (.int 1))))])
  arms := [.mk "bn" false (some "nm") none (some (.invoke "wbl" [("nm", (.var "nm"))])) [.mk "_chain" false (some "b") none (some (.invoke "wemb1" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("nm", (.var "nm")), ("b", (.var "b")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWemb1 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "no" false (some "_") (some (.bin .eq (.var "b") (.lit (.int 0)))) (some (.produce (.lit (.str "(bad builtin)")))) [], .mk "ok" false (some "_") none (some (.invoke "wne" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.bin .add (.var "i") (.lit (.int 1))))])) [.mk "_chain" false (some "e") none (some (.invoke "wemb2" [("src", (.var "src")), ("e", (.var "e")), ("hi", (.var "hi")), ("nm", (.var "nm")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWemb2 : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "e")), ("hi", (.var "hi"))])
  arms := [.mk "lp" false (some "j") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 40))) (.lit (.bool false)))) (some (.invoke "wmb" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi"))])) [.mk "_chain" false (some "m") none (some (.invoke "wc3" [("a", (.lit (.str "(builtin "))), ("b", (.var "nm")), ("c", (.lit (.str "")))])) [.mk "_chain" false (some "p") none (some (.invoke "webal" [("src", (.var "src")), ("i", (.bin .add (.var "j") (.lit (.int 1)))), ("hi", (.var "m")), ("out", (.var "p")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "t") none (some (.invoke "wc2" [("a", (.var "t")), ("b", (.lit (.str ")")))])) []]]], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad builtin)")))) []] }

def kWirWebal : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "dn" false (some "j") (some (.bin .ge (.var "j") (.var "hi"))) (some (.produce (.var "out"))) [], .mk "el" false (some "j") none (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 44)))])) [.mk "_chain" false (some "v") none (some (.invoke "webal1" [("src", (.var "src")), ("j", (.var "j")), ("v", (.var "v")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWebal1 : KCallable := .subflow {
  preLabel := none
  head := ("wcmx", [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 58)))])
  arms := [.mk "na" false (some "c") (some (.bin .lt (.var "c") (.var "v"))) (some (.invoke "wc3" [("a", (.var "out")), ("b", (.lit (.str " "))), ("c", (.lit (.str "(bad builtin-arg)")))])) [.mk "_chain" false (some "o") none (some (.invoke "webal" [("src", (.var "src")), ("i", (.bin .add (.var "v") (.lit (.int 1)))), ("hi", (.var "hi")), ("out", (.var "o")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []], .mk "ok" false (some "_") none (some (.invoke "wev" [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.var "j")), ("hi", (.var "v")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "wc3" [("a", (.var "out")), ("b", (.lit (.str " "))), ("c", (.var "x"))])) [.mk "_chain" false (some "o") none (some (.invoke "webal" [("src", (.var "src")), ("i", (.bin .add (.var "v") (.lit (.int 1)))), ("hi", (.var "hi")), ("out", (.var "o")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]]] }

def kWirWemv : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "i"))])
  arms := [.mk "iff" false (some "nm") (some (.bin .eq (.var "nm") (.lit (.str "if")))) (some (.invoke "wemi" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "tru" false (some "nm") (some (.bin .eq (.var "nm") (.lit (.str "true")))) (some (.produce (.lit (.str "(lit (bool true))")))) [], .mk "fls" false (some "nm") (some (.bin .eq (.var "nm") (.lit (.str "false")))) (some (.produce (.lit (.str "(lit (bool false))")))) [], .mk "kwd" false (some "nm") (some (.bin .or (.bin .or (.bin .eq (.var "nm") (.lit (.str "else"))) (.bin .eq (.var "nm") (.lit (.str "when")))) (.bin .or (.bin .eq (.var "nm") (.lit (.str "or"))) (.bin .eq (.var "nm") (.lit (.str "and")))))) (some (.produce (.lit (.str "(bad expr)")))) [], .mk "var" false (some "nm") none (some (.invoke "wemvd" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("nm", (.var "nm")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWemvd : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "i"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wsk" [("src", (.var "src")), ("i", (.var "e")), ("hi", (.var "hi"))])) [.mk "_chain" false (some "j") none (some (.invoke "wemve" [("src", (.var "src")), ("j", (.var "j")), ("hi", (.var "hi")), ("nm", (.var "nm"))])) []]] }

def kWirWemve : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "ca" false (some "_") (some (.cond (.bin .lt (.var "j") (.var "hi")) (.bin .eq (.index (.var "src") (.var "j")) (.lit (.int 40))) (.lit (.bool false)))) (some (.produce (.lit (.str "(bad expr-call)")))) [], .mk "dn" false (some "_") none (some (.invoke "wc3" [("a", (.lit (.str "(var "))), ("b", (.var "nm")), ("c", (.lit (.str ")")))])) []] }

def kWirWemi : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "i"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wsk" [("src", (.var "src")), ("i", (.var "e")), ("hi", (.var "hi"))])) [.mk "_chain" false (some "j") none (some (.invoke "wemi1" [("src", (.var "src")), ("j", (.var "j")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWemi1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "j")), ("n", (.var "hi"))])
  arms := [.mk "lp" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 40)))) (some (.invoke "wmb" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi"))])) [.mk "_chain" false (some "m") none (some (.invoke "wemi2" [("src", (.var "src")), ("j", (.var "j")), ("m", (.var "m")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad if)")))) []] }

def kWirWemi2 : KCallable := .subflow {
  preLabel := none
  head := ("wev", [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.bin .add (.var "j") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "c" false (some "c") none (some (.invoke "wfel" [("src", (.var "src")), ("i", (.bin .add (.var "m") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("ifd", (.lit (.int 0)))])) [.mk "_chain" false (some "el") none (some (.invoke "wemi3" [("src", (.var "src")), ("m", (.var "m")), ("el", (.var "el")), ("c", (.var "c")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWemi3 : KCallable := .subflow {
  preLabel := none
  head := ("wev", [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.bin .add (.var "m") (.lit (.int 1)))), ("hi", (.var "el")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "t" false (some "t") none (some (.invoke "wev" [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.bin .add (.var "el") (.lit (.int 4)))), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "fv") none (some (.invoke "wc7" [("a", (.lit (.str "(cond "))), ("b", (.var "c")), ("c", (.lit (.str " "))), ("d", (.var "t")), ("e", (.lit (.str " "))), ("f", (.var "fv")), ("g", (.lit (.str ")")))])) []]] }

def kWirWtek : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "i")), ("n", (.var "hi"))])
  arms := [.mk "fin" false (some "c") (some (.bin .lt (.var "c") (.lit (.int 0)))) (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) [], .mk "top" false (some "_") (some (.bin .or (.bin .ne (.var "d") (.lit (.int 0))) (.bin .ne (.var "ins") (.lit (.int 0))))) (some (.produce (.lit (.int 0)))) [], .mk "el" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 101)))) (some (.invoke "wtek1" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "fi" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 105)))) (some (.invoke "wtek2" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) [], .mk "mo" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWtek1 : KCallable := .subflow {
  preLabel := none
  head := ("wbd", [("src", (.var "src")), ("pv", (.bin .sub (.var "i") (.lit (.int 1)))), ("nx", (.bin .add (.var "i") (.lit (.int 4)))), ("hi", (.var "hi"))])
  arms := [.mk "nb" false (some "b") (some (.bin .eq (.var "b") (.lit (.int 0)))) (some (.produce (.lit (.int 0)))) [], .mk "ls" false (some "_") none (some (.invoke "wtek1b" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) []] }

def kWirWtek1b : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "ls" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 108))) (.cond (.bin .lt (.bin .add (.var "i") (.lit (.int 3))) (.var "hi")) (.bin .and (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 2)))) (.lit (.int 115))) (.bin .eq (.index (.var "src") (.bin .add (.var "i") (.lit (.int 3)))) (.lit (.int 101)))) (.lit (.bool false))))) (some (.produce (.lit (.int 1)))) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWtek2 : KCallable := .subflow {
  preLabel := none
  head := ("wbd", [("src", (.var "src")), ("pv", (.bin .sub (.var "i") (.lit (.int 1)))), ("nx", (.bin .add (.var "i") (.lit (.int 2)))), ("hi", (.var "hi"))])
  arms := [.mk "nb" false (some "b") (some (.bin .eq (.var "b") (.lit (.int 0)))) (some (.produce (.lit (.int 0)))) [], .mk "ff" false (some "_") none (some (.invoke "wtek2b" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])) []] }

def kWirWtek2b : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "ff" false (some "c") (some (.bin .eq (.var "c") (.lit (.int 102)))) (some (.produce (.lit (.int 2)))) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWbd : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "pv")), ("n", (.var "hi"))])
  arms := [.mk "pi" false (some "c") (some (.bin .or (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 97))) (.bin .le (.var "c") (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 65))) (.bin .le (.var "c") (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57)))) (.bin .eq (.var "c") (.lit (.int 95)))))) (.bin .eq (.var "c") (.lit (.int 45))))) (some (.produce (.lit (.int 0)))) [], .mk "po" false (some "_") none (some (.invoke "wbd1" [("src", (.var "src")), ("nx", (.var "nx")), ("hi", (.var "hi"))])) []] }

def kWirWbd1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.var "nx")), ("n", (.var "hi"))])
  arms := [.mk "ni" false (some "c") (some (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 97))) (.bin .le (.var "c") (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 65))) (.bin .le (.var "c") (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.var "c") (.lit (.int 48))) (.bin .le (.var "c") (.lit (.int 57)))) (.bin .eq (.var "c") (.lit (.int 95))))))) (some (.produce (.lit (.int 0)))) [], .mk "gl" false (some "c") (some (.bin .and (.bin .eq (.var "c") (.lit (.int 45))) (.cond (.bin .lt (.bin .add (.var "nx") (.lit (.int 1))) (.var "hi")) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 97))) (.bin .le (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 122)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 65))) (.bin .le (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 90)))) (.bin .or (.bin .and (.bin .ge (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 48))) (.bin .le (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 57)))) (.bin .or (.bin .eq (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 95))) (.bin .eq (.index (.var "src") (.bin .add (.var "nx") (.lit (.int 1)))) (.lit (.int 45))))))) (.lit (.bool false))))) (some (.produce (.lit (.int 0)))) [], .mk "ok" false (some "_") none (some (.produce (.lit (.int 1)))) []] }

def kWirWfel : KCallable := .subflow {
  preLabel := none
  head := ("wtek", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins"))])
  arms := [.mk "fin" false (some "r") (some (.bin .lt (.var "r") (.lit (.int 0)))) (some (.produce (.var "hi"))) [], .mk "el" false (some "r") (some (.bin .and (.bin .eq (.var "r") (.lit (.int 1))) (.bin .eq (.var "ifd") (.lit (.int 0))))) (some (.produce (.var "i"))) [], .mk "es" false (some "r") (some (.bin .eq (.var "r") (.lit (.int 1)))) (some (.invoke "wfel" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 4)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("ifd", (.bin .sub (.var "ifd") (.lit (.int 1))))])) [], .mk "fi" false (some "r") (some (.bin .eq (.var "r") (.lit (.int 2)))) (some (.invoke "wfel" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 2)))), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("ifd", (.bin .add (.var "ifd") (.lit (.int 1))))])) [], .mk "mo" false (some "_") none (some (.invoke "wfeln" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("d", (.var "d")), ("ins", (.var "ins")), ("ifd", (.var "ifd"))])) []] }

def kWirWfeln : KCallable := .subflow {
  preLabel := none
  head := ("wfel", [("src", (.var "src")), ("i", (.bin .add (.var "i") (.cond (.bin .and (.bin .eq (.var "ins") (.lit (.int 1))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 92)))) (.lit (.int 2)) (.lit (.int 1))))), ("hi", (.var "hi")), ("d", (.cond (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 40))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 91)))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 123))))) (.bin .add (.var "d") (.lit (.int 1))) (.cond (.bin .and (.bin .eq (.var "ins") (.lit (.int 0))) (.bin .or (.bin .or (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 41))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 93)))) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 125))))) (.bin .sub (.var "d") (.lit (.int 1))) (.var "d")))), ("ins", (.cond (.bin .and (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.bin .eq (.var "ins") (.lit (.int 0)))) (.lit (.int 1)) (.cond (.bin .and (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.bin .eq (.var "ins") (.lit (.int 1)))) (.lit (.int 0)) (.var "ins")))), ("ifd", (.var "ifd"))])
  arms := [.mk "r" false (some "r") none (some (.produce (.var "r"))) []] }

def kWirWnum : KCallable := .subflow {
  preLabel := none
  head := ("wen", [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "hi"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wfd" [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "e")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("last", (.bin .sub (.lit (.int 0)) (.lit (.int 1))))])) [.mk "_chain" false (some "d") none (some (.invoke "wnum1" [("src", (.var "src")), ("lo", (.var "lo")), ("e", (.var "e")), ("d", (.var "d"))])) []]] }

def kWirWnum1 : KCallable := .subflow {
  preLabel := none
  head := ("wnv", [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "e")), ("v", (.lit (.int 0)))])
  arms := [.mk "w" false (some "v") (some (.bin .lt (.var "d") (.lit (.int 0)))) (some (.invoke "wc3" [("a", (.lit (.str "(int "))), ("b", (.builtin "intToString" [(.var "v")])), ("c", (.lit (.str ")")))])) [], .mk "fw" false (some "v") none (some (.invoke "wnum2" [("src", (.var "src")), ("e", (.var "e")), ("d", (.var "d")), ("w", (.var "v"))])) []] }

def kWirWnum2 : KCallable := .subflow {
  preLabel := none
  head := ("wnv", [("src", (.var "src")), ("i", (.bin .add (.var "d") (.lit (.int 1)))), ("hi", (.var "e")), ("v", (.lit (.int 0)))])
  arms := [.mk "f" false (some "f") none (some (.invoke "wp10" [("n", (.bin .sub (.var "e") (.bin .add (.var "d") (.lit (.int 1)))))])) [.mk "_chain" false (some "dn") none (some (.invoke "wnum3" [("e", (.var "e")), ("d", (.var "d")), ("w", (.var "w")), ("f", (.var "f")), ("dn", (.var "dn"))])) []]] }

def kWirWnum3 : KCallable := .subflow {
  preLabel := none
  head := ("wgcd", [("a", (.var "f")), ("b", (.var "dn"))])
  arms := [.mk "g" false (some "g") (some (.bin .gt (.var "g") (.lit (.int 0)))) (some (.invoke "wc5" [("a", (.lit (.str "(float "))), ("b", (.builtin "intToString" [(.bin .add (.bin .mul (.var "w") (.bin .div (.var "dn") (.var "g"))) (.bin .div (.var "f") (.var "g")))])), ("c", (.lit (.str " "))), ("d", (.builtin "intToString" [(.bin .div (.var "dn") (.var "g"))])), ("e", (.lit (.str ")")))])) [], .mk "z" false (some "_") none (some (.produce (.lit (.str "(bad float)")))) []] }

def kWirWel : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "hi"))])
  arms := [.mk "lp" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 40))) (.lit (.bool false)))) (some (.invoke "welg" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "lb" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 91))) (.lit (.bool false)))) (some (.invoke "wela" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "lc" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 123))) (.lit (.bool false)))) (some (.invoke "welc" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "st" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 34))) (.lit (.bool false)))) (some (.invoke "wst" [("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("p", (.var "i"))])) [.mk "_chain" false (some "s") none (some (.invoke "wc5" [("a", (.lit (.str "(str "))), ("b", (.lit (.str "\""))), ("c", (.var "s")), ("d", (.lit (.str "\""))), ("e", (.lit (.str ")")))])) []], .mk "dg" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .and (.bin .ge (.index (.var "src") (.var "i")) (.lit (.int 48))) (.bin .le (.index (.var "src") (.var "i")) (.lit (.int 57)))) (.lit (.bool false)))) (some (.invoke "wnum" [("src", (.var "src")), ("lo", (.var "i")), ("hi", (.var "hi")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [], .mk "tr" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 116))) (.lit (.bool false)))) (some (.invoke "wel1" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("nm", (.lit (.str "true"))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) [], .mk "fa" false (some "i") (some (.cond (.bin .lt (.var "i") (.var "hi")) (.bin .eq (.index (.var "src") (.var "i")) (.lit (.int 102))) (.lit (.bool false)))) (some (.invoke "wel1" [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi")), ("nm", (.lit (.str "false"))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad lit)")))) []] }

def kWirWel1 : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "i"))])
  arms := [.mk "t" false (some "v") (some (.bin .eq (.var "v") (.var "nm"))) (some (.invoke "wc3" [("a", (.lit (.str "(bool "))), ("b", (.var "nm")), ("c", (.lit (.str ")")))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad lit)")))) []] }

def kWirWelg : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.invoke "wel" [("src", (.var "src")), ("lo", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWela : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.invoke "well" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "m")), ("out", (.lit (.str "(arr"))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "t") none (some (.invoke "wc2" [("a", (.var "t")), ("b", (.lit (.str ")")))])) []]] }

def kWirWell : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "dn" false (some "j") (some (.bin .ge (.var "j") (.var "hi"))) (some (.produce (.var "out"))) [], .mk "el" false (some "j") none (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 44)))])) [.mk "_chain" false (some "c") none (some (.invoke "well1" [("src", (.var "src")), ("j", (.var "j")), ("c", (.var "c")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWell1 : KCallable := .subflow {
  preLabel := none
  head := ("wel", [("src", (.var "src")), ("lo", (.var "j")), ("hi", (.var "c")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "x" false (some "x") none (some (.invoke "wc3" [("a", (.var "out")), ("b", (.lit (.str " "))), ("c", (.var "x"))])) [.mk "_chain" false (some "o") none (some (.invoke "well" [("src", (.var "src")), ("i", (.bin .add (.var "c") (.lit (.int 1)))), ("hi", (.var "hi")), ("out", (.var "o")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWelc : KCallable := .subflow {
  preLabel := none
  head := ("wmb", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "m" false (some "m") none (some (.invoke "welcl" [("src", (.var "src")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("hi", (.var "m")), ("out", (.lit (.str "(cell"))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "t") none (some (.invoke "wc2" [("a", (.var "t")), ("b", (.lit (.str ")")))])) []]] }

def kWirWelcl : KCallable := .subflow {
  preLabel := none
  head := ("wsk", [("src", (.var "src")), ("i", (.var "i")), ("hi", (.var "hi"))])
  arms := [.mk "dn" false (some "j") (some (.bin .ge (.var "j") (.var "hi"))) (some (.produce (.var "out"))) [], .mk "f" false (some "j") none (some (.invoke "wcmx" [("src", (.var "src")), ("i", (.var "j")), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 58)))])) [.mk "_chain" false (some "c") none (some (.invoke "welcl1" [("src", (.var "src")), ("j", (.var "j")), ("c", (.var "c")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWelcl1 : KCallable := .subflow {
  preLabel := none
  head := ("wcmx", [("src", (.var "src")), ("i", (.bin .add (.var "c") (.lit (.int 1)))), ("hi", (.var "hi")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("w", (.lit (.int 44)))])
  arms := [.mk "m" false (some "m") none (some (.invoke "welcl2" [("src", (.var "src")), ("j", (.var "j")), ("c", (.var "c")), ("m", (.var "m")), ("hi", (.var "hi")), ("out", (.var "out")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []] }

def kWirWelcl2 : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "j"))])
  arms := [.mk "fn" false (some "nm") none (some (.invoke "wel" [("src", (.var "src")), ("lo", (.bin .add (.var "c") (.lit (.int 1)))), ("hi", (.var "m")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "welcl3" [("src", (.var "src")), ("m", (.var "m")), ("hi", (.var "hi")), ("out", (.var "out")), ("nm", (.var "nm")), ("x", (.var "x")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWelcl3 : KCallable := .subflow {
  preLabel := none
  head := ("wc5", [("a", (.var "out")), ("b", (.lit (.str " ("))), ("c", (.var "nm")), ("d", (.lit (.str " "))), ("e", (.var "x"))])
  arms := [.mk "o" false (some "o") none (some (.invoke "wc3" [("a", (.var "o")), ("b", (.lit (.str ")"))), ("c", (.lit (.str "")))])) [.mk "_chain" false (some "p") none (some (.invoke "welcl" [("src", (.var "src")), ("i", (.bin .add (.var "m") (.lit (.int 1)))), ("hi", (.var "hi")), ("out", (.var "p")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWrk : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "rows")), ("i", (.var "i")), ("n", (.bin .mul (.var "nr") (.lit (.int 6))))])
  arms := [.mk "k" false (some "k") none (some (.produce (.var "k"))) []] }

def kWirWevf : KCallable := .subflow {
  preLabel := none
  head := ("wpix", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "lo"))])
  arms := [.mk "ok" false (some "k") (some (.bin .ge (.var "k") (.lit (.int 0)))) (some (.produce (.index (.var "nsp") (.bin .add (.bin .sub (.builtin "len" [(.var "nsp")]) (.bin .mul (.lit (.int 3)) (.var "nn"))) (.var "k"))))) [], .mk "no" false (some "_") none (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) []] }

def kWirWdpe : KCallable := .subflow {
  preLabel := none
  head := ("wpix", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "ok" false (some "k") (some (.bin .ge (.var "k") (.lit (.int 0)))) (some (.produce (.cond (.bin .gt (.index (.var "nsp") (.bin .add (.bin .sub (.builtin "len" [(.var "nsp")]) (.var "nn")) (.var "k"))) (.lit (.int 1))) (.lit (.int 1)) (.lit (.int 0))))) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWhi : KCallable := .subflow {
  preLabel := none
  head := ("wpix", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "lo"))])
  arms := [.mk "ok" false (some "k") (some (.bin .ge (.var "k") (.lit (.int 0)))) (some (.produce (.index (.var "nsp") (.bin .add (.bin .sub (.builtin "len" [(.var "nsp")]) (.bin .mul (.lit (.int 2)) (.var "nn"))) (.var "k"))))) [], .mk "no" false (some "_") none (some (.produce (.lit (.int 0)))) []] }

def kWirWfdn : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "rows")), ("i", (.bin .add (.var "evi") (.bin .mul (.var "i") (.lit (.int 6))))), ("n", (.bin .mul (.var "nr") (.lit (.int 6))))])
  arms := [.mk "fn" false (some "k") (some (.bin .ne (.var "k") (.lit (.int 2)))) (some (.produce (.var "i"))) [], .mk "mo" false (some "_") none (some (.invoke "wfdn" [("rows", (.var "rows")), ("evi", (.var "evi")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("nr", (.var "nr"))])) []] }

def kWirWfdh : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "rows")), ("i", (.bin .add (.var "evi") (.bin .mul (.var "i") (.lit (.int 6))))), ("n", (.bin .mul (.var "nr") (.lit (.int 6))))])
  arms := [.mk "fn" false (some "k") (some (.bin .ne (.var "k") (.lit (.int 2)))) (some (.produce (.lit (.int 0)))) [], .mk "mo" false (some "_") none (some (.invoke "wfdh1" [("rows", (.var "rows")), ("evi", (.var "evi")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("nr", (.var "nr"))])) []] }

def kWirWfdh1 : KCallable := .subflow {
  preLabel := none
  head := ("weq", [("src", (.var "src")), ("a", (.index (.var "rows") (.bin .add (.bin .add (.var "evi") (.bin .mul (.var "i") (.lit (.int 6)))) (.lit (.int 2))))), ("b", (.index (.var "rows") (.bin .add (.bin .add (.var "evi") (.bin .mul (.var "i") (.lit (.int 6)))) (.lit (.int 3))))), ("x", (.var "lo")), ("y", (.var "hi"))])
  arms := [.mk "eq" false (some "v") (some (.bin .eq (.var "v") (.lit (.int 1)))) (some (.produce (.lit (.int 1)))) [], .mk "no" false (some "_") none (some (.invoke "wfdh" [("rows", (.var "rows")), ("evi", (.var "evi")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("nr", (.var "nr"))])) []] }

def kWirWbr0 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "rows")), ("i", (.bin .add (.var "evi") (.bin .mul (.var "i") (.lit (.int 6))))), ("n", (.bin .mul (.var "nr") (.lit (.int 6))))])
  arms := [.mk "sk" false (some "k") (some (.bin .or (.bin .eq (.var "k") (.lit (.int 2))) (.bin .eq (.var "k") (.lit (.int 3))))) (some (.invoke "wbr0" [("rows", (.var "rows")), ("evi", (.var "evi")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("nr", (.var "nr"))])) [], .mk "mo" false (some "_") none (some (.produce (.bin .add (.var "evi") (.bin .mul (.var "i") (.lit (.int 6)))))) []] }

def kWirWbrn : KCallable := .subflow {
  preLabel := none
  head := ("wbr0", [("rows", (.var "rows")), ("evi", (.var "evi")), ("i", (.lit (.int 1))), ("nr", (.var "nr"))])
  arms := [.mk "b" false (some "b") none (some (.invoke "wbrn1" [("rows", (.var "rows")), ("b", (.var "b")), ("i", (.lit (.int 0))), ("nr", (.var "nr"))])) []] }

def kWirWbrn1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "rows")), ("i", (.bin .add (.var "b") (.bin .mul (.var "i") (.lit (.int 6))))), ("n", (.bin .mul (.var "nr") (.lit (.int 6))))])
  arms := [.mk "fn" false (some "k") (some (.bin .ne (.var "k") (.lit (.int 4)))) (some (.produce (.var "i"))) [], .mk "mo" false (some "_") none (some (.invoke "wbrn1" [("rows", (.var "rows")), ("b", (.var "b")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("nr", (.var "nr"))])) []] }

def kWirWbrh : KCallable := .subflow {
  preLabel := none
  head := ("wbr0", [("rows", (.var "rows")), ("evi", (.var "evi")), ("i", (.lit (.int 1))), ("nr", (.var "nr"))])
  arms := [.mk "b" false (some "b") none (some (.invoke "wbrh1" [("rows", (.var "rows")), ("b", (.var "b")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.lit (.int 0))), ("nr", (.var "nr"))])) []] }

def kWirWbrh1 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "rows")), ("i", (.bin .add (.var "b") (.bin .mul (.var "i") (.lit (.int 6))))), ("n", (.bin .mul (.var "nr") (.lit (.int 6))))])
  arms := [.mk "fn" false (some "k") (some (.bin .ne (.var "k") (.lit (.int 4)))) (some (.produce (.lit (.int 0)))) [], .mk "mo" false (some "_") none (some (.invoke "wbrh2" [("rows", (.var "rows")), ("b", (.var "b")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.var "i")), ("nr", (.var "nr"))])) []] }

def kWirWbrh2 : KCallable := .subflow {
  preLabel := none
  head := ("weq", [("src", (.var "src")), ("a", (.index (.var "rows") (.bin .add (.bin .add (.var "b") (.bin .mul (.var "i") (.lit (.int 6)))) (.lit (.int 2))))), ("b", (.index (.var "rows") (.bin .add (.bin .add (.var "b") (.bin .mul (.var "i") (.lit (.int 6)))) (.lit (.int 3))))), ("x", (.var "lo")), ("y", (.var "hi"))])
  arms := [.mk "eq" false (some "v") (some (.bin .eq (.var "v") (.lit (.int 1)))) (some (.produce (.lit (.int 1)))) [], .mk "no" false (some "_") none (some (.invoke "wbrh1" [("rows", (.var "rows")), ("b", (.var "b")), ("src", (.var "src")), ("lo", (.var "lo")), ("hi", (.var "hi")), ("i", (.bin .add (.var "i") (.lit (.int 1)))), ("nr", (.var "nr"))])) []] }

def kWirWrp : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "z" false (some "_") (some (.bin .le (.var "k") (.lit (.int 0)))) (some (.produce (.lit (.str "")))) [], .mk "mo" false (some "_") none (some (.invoke "wrp1" [("k", (.var "k"))])) []] }

def kWirWrp1 : KCallable := .subflow {
  preLabel := none
  head := ("wrp", [("k", (.bin .sub (.var "k") (.lit (.int 1))))])
  arms := [.mk "t" false (some "t") none (some (.invoke "wc2" [("a", (.lit (.str ")"))), ("b", (.var "t"))])) []] }

def kWirWclo : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "z" false (some "_") (some (.bin .eq (.var "inf") (.lit (.int 0)))) (some (.produce (.lit (.str "")))) [], .mk "y" false (some "_") none (some (.invoke "wcloa" [("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) []] }

def kWirWcloa : KCallable := .subflow {
  preLabel := none
  head := ("wrp", [("k", (.bin .add (.var "iopen") (.cond (.bin .ne (.var "curk") (.lit (.int 0))) (.bin .add (.lit (.int 1)) (.bin .mul (.var "dep") (.lit (.int 2)))) (.lit (.int 0)))))])
  arms := [.mk "a" false (some "a") none (some (.invoke "wc3" [("a", (.cond (.bin .eq (.var "curk") (.bin .sub (.lit (.int 0)) (.lit (.int 1)))) (.lit (.str " (node terminal)")) (.lit (.str "")))), ("b", (.var "a")), ("c", (.lit (.str "))")))])) []] }

def kWirWcls : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "z" false (some "_") (some (.bin .eq (.var "curk") (.lit (.int 0)))) (some (.invoke "wrp" [("k", (.var "iopen"))])) [], .mk "tm" false (some "_") (some (.bin .eq (.var "curk") (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) (some (.invoke "wrp" [("k", (.bin .add (.bin .add (.var "iopen") (.lit (.int 1))) (.bin .mul (.var "dep") (.lit (.int 2)))))])) [.mk "_chain" false (some "p") none (some (.invoke "wc2" [("a", (.lit (.str " (node terminal)"))), ("b", (.var "p"))])) []], .mk "y" false (some "_") none (some (.invoke "wrp" [("k", (.bin .add (.bin .add (.var "iopen") (.lit (.int 1))) (.bin .mul (.var "dep") (.lit (.int 2)))))])) []] }

def kWirWex : KCallable := .subflow {
  preLabel := none
  head := ("wtb", [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "hi") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "b" false (some "b") none (some (.invoke "wsk" [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "b"))])) [.mk "_chain" false (some "a") none (some (.invoke "wev" [("lv", (.lit (.int 1))), ("src", (.var "src")), ("lo", (.var "a")), ("hi", (.var "b")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) []]] }

def kWirWpun : KCallable := .subflow {
  preLabel := none
  head := ("wtb", [("src", (.var "src")), ("lo", (.var "lo")), ("j", (.bin .sub (.var "hi") (.lit (.int 1)))), ("n", (.var "hi"))])
  arms := [.mk "b" false (some "b") none (some (.invoke "wsk" [("src", (.var "src")), ("i", (.var "lo")), ("hi", (.var "b"))])) [.mk "_chain" false (some "a") none (some (.invoke "wpun1" [("src", (.var "src")), ("a", (.var "a")), ("b", (.var "b")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) []]] }

def kWirWpun1 : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "a"))])
  arms := [.mk "pu" false (some "e") (some (.bin .eq (.var "e") (.var "b"))) (some (.produce (.var "a"))) [], .mk "fd" false (some "_") none (some (.invoke "wfd" [("src", (.var "src")), ("i", (.var "a")), ("hi", (.var "b")), ("d", (.lit (.int 0))), ("ins", (.lit (.int 0))), ("last", (.bin .sub (.lit (.int 0)) (.lit (.int 1))))])) [.mk "_chain" false (some "f") none (some (.invoke "wpun2" [("src", (.var "src")), ("b", (.var "b")), ("f", (.var "f")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) []]] }

def kWirWpun2 : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.bin .add (.var "f") (.lit (.int 1))))])
  arms := [.mk "ok" false (some "e") (some (.bin .and (.bin .ge (.var "f") (.lit (.int 0))) (.bin .eq (.var "e") (.var "b")))) (some (.invoke "wpun3" [("src", (.var "src")), ("f", (.var "f"))])) [], .mk "no" false (some "_") none (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) []] }

def kWirWpun3 : KCallable := .subflow {
  preLabel := none
  head := ("pkb", [("t", (.var "src")), ("i", (.bin .sub (.var "f") (.lit (.int 1)))), ("n", (.builtin "len" [(.var "src")]))])
  arms := [.mk "a" false (some "c") none (some (.invoke "wpun3b" [("c", (.var "c")), ("f", (.var "f"))])) []] }

def kWirWpun3b : KCallable := .subflow {
  preLabel := none
  head := ("wpe", [("c", (.var "c"))])
  arms := [.mk "ok" false (some "_") none (some (.produce (.bin .add (.var "f") (.lit (.int 1))))) [], .mk "no" false (some "_") none (some (.produce (.bin .sub (.lit (.int 0)) (.lit (.int 1))))) []] }

def kWirWdk : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "iv" false (some "_") (some (.bin .or (.bin .eq (.var "ltk") (.lit (.int 1))) (.bin .eq (.var "ltk") (.lit (.int 2))))) (some (.invoke "wevf" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("lo", (.var "ltl"))])) [], .mk "jp" false (some "_") (some (.bin .eq (.var "ltk") (.lit (.int 3)))) (some (.invoke "wevf" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("lo", (.var "htl"))])) [], .mk "ow" false (some "_") none (some (.produce (.var "fevi"))) []] }

def kWirWarg : KCallable := .subflow {
  preLabel := none
  head := ("wex", [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 4))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 5))))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wdk" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("fevi", (.var "fevi"))])) [.mk "_chain" false (some "d") none (some (.invoke "warg1" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("d", (.var "d")), ("argi", (.var "argi")), ("e", (.var "e"))])) []]] }

def kWirWarg1 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "na" false (some "_") (some (.bin .gt (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))) (.lit (.int 0)))) (some (.invoke "warg2" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("d", (.var "d")), ("e", (.var "e"))])) [], .mk "po" false (some "_") none (some (.invoke "wpun" [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 4))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 5))))), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) [.mk "_chain" false (some "p") none (some (.invoke "warg3" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("d", (.var "d")), ("argi", (.var "argi")), ("e", (.var "e")), ("p", (.var "p"))])) []]] }

def kWirWarg2 : KCallable := .subflow {
  preLabel := none
  head := ("wfdh", [("rows", (.var "rows")), ("evi", (.var "d")), ("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("i", (.lit (.int 1))), ("nr", (.var "nr"))])
  arms := [.mk "h" false (some "h") (some (.bin .or (.bin .lt (.var "d") (.lit (.int 0))) (.bin .eq (.var "h") (.lit (.int 1))))) (some (.invoke "warg2a" [("rows", (.var "rows")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("e", (.var "e"))])) [], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad decl-param)")))) []] }

def kWirWarg2a : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "nm" false (some "nm") none (some (.invoke "wc5" [("a", (.lit (.str " ("))), ("b", (.var "nm")), ("c", (.lit (.str " "))), ("d", (.var "e")), ("e", (.lit (.str ")")))])) []] }

def kWirWarg3 : KCallable := .subflow {
  preLabel := none
  head := ("wne", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "p"))])
  arms := [.mk "pe" false (some "pe") none (some (.invoke "warg3a" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("d", (.var "d")), ("argi", (.var "argi")), ("e", (.var "e")), ("p", (.var "p")), ("pe", (.var "pe"))])) []] }

def kWirWarg3a : KCallable := .subflow {
  preLabel := none
  head := ("wfdh", [("rows", (.var "rows")), ("evi", (.var "d")), ("src", (.var "src")), ("lo", (.var "p")), ("hi", (.var "pe")), ("i", (.lit (.int 1))), ("nr", (.var "nr"))])
  arms := [.mk "h" false (some "h") (some (.bin .and (.bin .ge (.var "p") (.lit (.int 0))) (.bin .or (.bin .lt (.var "d") (.lit (.int 0))) (.bin .eq (.var "h") (.lit (.int 1)))))) (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "p"))])) [.mk "_chain" false (some "nm") none (some (.invoke "wc5" [("a", (.lit (.str " ("))), ("b", (.var "nm")), ("c", (.lit (.str " "))), ("d", (.var "e")), ("e", (.lit (.str ")")))])) []], .mk "ix" false (some "_") none (some (.invoke "warg4" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("d", (.var "d")), ("argi", (.var "argi")), ("e", (.var "e"))])) []] }

def kWirWarg4 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "y" false (some "_") (some (.bin .ge (.var "d") (.lit (.int 0)))) (some (.invoke "warg5" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("d", (.var "d")), ("argi", (.var "argi")), ("e", (.var "e"))])) [], .mk "n" false (some "_") none (some (.produce (.lit (.str "(bad arg-name)")))) []] }

def kWirWarg5 : KCallable := .subflow {
  preLabel := none
  head := ("wfdn", [("rows", (.var "rows")), ("evi", (.var "d")), ("i", (.lit (.int 1))), ("nr", (.var "nr"))])
  arms := [.mk "n" false (some "n") (some (.bin .lt (.bin .add (.var "argi") (.lit (.int 1))) (.var "n"))) (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.bin .add (.var "d") (.bin .mul (.bin .add (.var "argi") (.lit (.int 1))) (.lit (.int 6)))) (.lit (.int 2)))))])) [.mk "_chain" false (some "nm") none (some (.invoke "wc5" [("a", (.lit (.str " ("))), ("b", (.var "nm")), ("c", (.lit (.str " "))), ("d", (.var "e")), ("e", (.lit (.str ")")))])) []], .mk "no" false (some "_") none (some (.produce (.lit (.str "(bad arg-name)")))) []] }

def kWirWhev : KCallable := .subflow {
  preLabel := none
  head := ("wdpe", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("rows", (.var "rows")), ("i", (.var "i"))])
  arms := [.mk "d" false (some "d") none (some (.produce (.cond (.bin .eq (.var "d") (.lit (.int 1))) (.lit (.str " (bad dup-tor)")) (.lit (.str ""))))) []] }

def kWirWhim : KCallable := .subflow {
  preLabel := none
  head := ("wex", [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 4))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 5))))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])) [.mk "_chain" false (some "nm") none (some (.invoke "wc7" [("a", (.lit (.str " (def "))), ("b", (.var "nm")), ("c", (.lit (.str " (bare "))), ("d", (.var "e")), ("e", (.lit (.str "))"))), ("f", (.lit (.str ""))), ("g", (.lit (.str "")))])) []]] }

def kWirWhfw : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "nm" false (some "nm") none (some (.invoke "whfw1" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("plbl", (.var "plbl")), ("nm", (.var "nm"))])) []] }

def kWirWhfw1 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "lb" false (some "_") (some (.bin .ge (.var "plbl") (.lit (.int 0)))) (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "plbl"))])) [.mk "_chain" false (some "lb") none (some (.invoke "wc5" [("a", (.lit (.str " (def "))), ("b", (.var "nm")), ("c", (.lit (.str " (subflow"))), ("d", (.bin .concat (.lit (.str " (label ")) (.bin .concat (.var "lb") (.lit (.str ")"))))), ("e", (.lit (.str "")))])) []], .mk "nl" false (some "_") none (some (.invoke "wc5" [("a", (.lit (.str " (def "))), ("b", (.var "nm")), ("c", (.lit (.str " (subflow"))), ("d", (.lit (.str ""))), ("e", (.lit (.str "")))])) []] }

def kWirWhca : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "nm" false (some "nm") none (some (.invoke "wc3" [("a", (.lit (.str " (head "))), ("b", (.var "nm")), ("c", (.lit (.str "")))])) []] }

def kWirWhco : KCallable := .subflow {
  preLabel := none
  head := ("wbrh", [("rows", (.var "rows")), ("evi", (.var "fevi")), ("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("nr", (.var "nr"))])
  arms := [.mk "b" false (some "b") none (some (.invoke "wbrn" [("rows", (.var "rows")), ("evi", (.var "fevi")), ("nr", (.var "nr"))])) [.mk "_chain" false (some "n") none (some (.invoke "whco1" [("rows", (.var "rows")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("fevi", (.var "fevi")), ("b", (.var "b")), ("n", (.var "n"))])) []]] }

def kWirWhco1 : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "ca" false (some "nm") (some (.bin .eq (.var "nm") (.lit (.str "_")))) (some (.produce (.lit (.str " (arm catchall")))) [], .mk "nm" false (some "nm") none (some (.produce (.cond (.bin .and (.bin .and (.bin .ge (.var "fevi") (.lit (.int 0))) (.bin .gt (.var "n") (.lit (.int 0)))) (.bin .eq (.var "b") (.lit (.int 0)))) (.lit (.str " (bad decl-branch)")) (.bin .concat (.lit (.str " (arm (tag ")) (.bin .concat (.var "nm") (.lit (.str ")"))))))) []] }

def kWirWhbi : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "nm" false (some "nm") none (some (.invoke "wc3" [("a", (.lit (.str " (bind "))), ("b", (.var "nm")), ("c", (.lit (.str ")")))])) []] }

def kWirWhcn : KCallable := .subflow {
  preLabel := none
  head := ("wex", [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])
  arms := [.mk "e" false (some "e") none (some (.invoke "wc3" [("a", (.lit (.str " (when "))), ("b", (.var "e")), ("c", (.lit (.str ")")))])) []] }

def kWirWhct : KCallable := .subflow {
  preLabel := none
  head := ("wbrh", [("rows", (.var "rows")), ("evi", (.var "fevi")), ("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("nr", (.var "nr"))])
  arms := [.mk "b" false (some "b") none (some (.invoke "whct1" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.var "i")), ("fevi", (.var "fevi")), ("b", (.var "b"))])) []] }

def kWirWhct1 : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "nm" false (some "_") (some (.bin .and (.bin .ge (.var "fevi") (.lit (.int 0))) (.bin .eq (.var "b") (.lit (.int 0))))) (some (.produce (.lit (.str "(bad ctor-branch)")))) [], .mk "nm" false (some "nm") none (some (.invoke "whct2" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.var "i")), ("nm", (.var "nm"))])) []] }

def kWirWhct2 : KCallable := .subflow {
  preLabel := none
  head := ("wtb", [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 4))))), ("j", (.bin .sub (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 5)))) (.lit (.int 1)))), ("n", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 5)))))])
  arms := [.mk "e" false (some "be") (some (.bin .lt (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 4)))) (.var "be"))) (some (.invoke "wex" [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 4))))), ("hi", (.var "be")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "x") none (some (.invoke "wc7" [("a", (.lit (.str " (node (ctor "))), ("b", (.var "nm")), ("c", (.lit (.str " "))), ("d", (.var "x")), ("e", (.lit (.str "))"))), ("f", (.lit (.str ""))), ("g", (.lit (.str "")))])) []], .mk "mt" false (some "_") none (some (.invoke "wc7" [("a", (.lit (.str " (node (ctor "))), ("b", (.var "nm")), ("c", (.lit (.str " "))), ("d", (.lit (.str "(lit (cell))"))), ("e", (.lit (.str "))"))), ("f", (.lit (.str ""))), ("g", (.lit (.str "")))])) []] }

def kWirWsti : KCallable := .subflow {
  preLabel := none
  head := ("wnm", [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "nm" false (some "nm") none (some (.invoke "wsti1" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("curk", (.var "curk")), ("pend", (.var "pend")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("jump", (.var "jump")), ("nm", (.var "nm"))])) []] }

def kWirWsti1 : KCallable := .subflow {
  preLabel := none
  head := ("weq", [("src", (.var "src")), ("a", (.var "flbl")), ("b", (.var "flbh")), ("x", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("y", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3)))))])
  arms := [.mk "jl" false (some "j") (some (.bin .and (.bin .eq (.var "jump") (.lit (.int 1))) (.bin .eq (.var "j") (.lit (.int 0))))) (some (.produce (.lit (.str "(bad jump-label)")))) [], .mk "ok" false (some "_") none (some (.invoke "wsti2" [("curk", (.var "curk")), ("pend", (.var "pend")), ("jump", (.var "jump")), ("nm", (.var "nm")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn"))])) []] }

def kWirWsti2 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "bp" false (some "_") (some (.bin .ge (.var "pend") (.lit (.int 0)))) (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.var "pend"))])) [.mk "_chain" false (some "b") none (some (.invoke "wsti3" [("curk", (.var "curk")), ("pend", (.var "pend")), ("jump", (.var "jump")), ("nm", (.var "nm")), ("b", (.var "b"))])) []], .mk "np" false (some "_") none (some (.invoke "wsti3" [("curk", (.var "curk")), ("pend", (.var "pend")), ("jump", (.var "jump")), ("nm", (.var "nm")), ("b", (.lit (.str "")))])) []] }

def kWirWsti3 : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "a0" false (some "_") (some (.bin .and (.bin .eq (.var "curk") (.lit (.int 0))) (.bin .ge (.var "pend") (.lit (.int 0))))) (some (.produce (.bin .concat (.lit (.str " (arm (tag _chain) (bind ")) (.bin .concat (.var "b") (.bin .concat (.lit (.str ") (node (")) (.bin .concat (.cond (.bin .eq (.var "jump") (.lit (.int 1))) (.lit (.str "jump ")) (.lit (.str "invoke "))) (.var "nm"))))))) [], .mk "a1" false (some "_") (some (.bin .eq (.var "curk") (.lit (.int 0)))) (some (.produce (.bin .concat (.lit (.str " (arm (tag _chain) (node (")) (.bin .concat (.cond (.bin .eq (.var "jump") (.lit (.int 1))) (.lit (.str "jump ")) (.lit (.str "invoke "))) (.var "nm"))))) [], .mk "a2" false (some "_") (some (.bin .and (.bin .or (.bin .eq (.var "curk") (.lit (.int 3))) (.bin .eq (.var "curk") (.lit (.int 4)))) (.bin .ge (.var "pend") (.lit (.int 0))))) (some (.produce (.bin .concat (.lit (.str ")) (conts (arm (tag _chain) (bind ")) (.bin .concat (.var "b") (.bin .concat (.lit (.str ") (node (")) (.bin .concat (.cond (.bin .eq (.var "jump") (.lit (.int 1))) (.lit (.str "jump ")) (.lit (.str "invoke "))) (.var "nm"))))))) [], .mk "a3" false (some "_") (some (.bin .or (.bin .eq (.var "curk") (.lit (.int 3))) (.bin .eq (.var "curk") (.lit (.int 4))))) (some (.produce (.bin .concat (.lit (.str ")) (conts (arm (tag _chain) (node (")) (.bin .concat (.cond (.bin .eq (.var "jump") (.lit (.int 1))) (.lit (.str "jump ")) (.lit (.str "invoke "))) (.var "nm"))))) [], .mk "a4" false (some "_") none (some (.produce (.bin .concat (.lit (.str " (node (")) (.bin .concat (.cond (.bin .eq (.var "jump") (.lit (.int 1))) (.lit (.str "jump ")) (.lit (.str "invoke "))) (.var "nm"))))) []] }

def kWirWfin : KCallable := .subflow {
  preLabel := none
  head := ("wn0", [])
  arms := [.mk "bd" false (some "_") (some (.bin .ge (.var "pend") (.lit (.int 0)))) (some (.produce (.bin .concat (.var "out") (.lit (.str "(bad pend)"))))) [], .mk "ok" false (some "_") none (some (.invoke "wclo" [("inf", (.var "inf")), ("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) [.mk "_chain" false (some "c") none (some (.invoke "wfin1" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("out", (.var "out")), ("c", (.var "c"))])) []]] }

def kWirWfin1 : KCallable := .subflow {
  preLabel := none
  head := ("wth", [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.lit (.int 0))), ("out", (.bin .concat (.var "out") (.var "c")))])
  arms := [.mk "t" false (some "t") none (some (.invoke "wc2" [("a", (.var "t")), ("b", (.lit (.str ")")))])) []] }

def kWirWth : KCallable := .subflow {
  preLabel := none
  head := ("wrk", [("rows", (.var "rows")), ("i", (.var "i")), ("nr", (.var "nr"))])
  arms := [.mk "fn" false (some "_") (some (.bin .ge (.var "i") (.bin .mul (.var "nr") (.lit (.int 6))))) (some (.produce (.var "out"))) [], .mk "ev" false (some "k") (some (.bin .eq (.var "k") (.lit (.int 1)))) (some (.invoke "wthi" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("out", (.var "out"))])) [], .mk "mo" false (some "_") none (some (.invoke "wth" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.var "out"))])) []] }

def kWirWthi : KCallable := .subflow {
  preLabel := none
  head := ("whi", [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])
  arms := [.mk "h" false (some "h") none (some (.invoke "wnm" [("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("p", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])) [.mk "_chain" false (some "nm") none (some (.invoke "wthi1" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("out", (.var "out")), ("h", (.var "h")), ("nm", (.var "nm"))])) []]] }

def kWirWthi1 : KCallable := .subflow {
  preLabel := none
  head := ("wc5", [("a", (.var "out")), ("b", (.cond (.bin .eq (.var "h") (.lit (.int 1))) (.lit (.str "")) (.lit (.str " (def ")))), ("c", (.cond (.bin .eq (.var "h") (.lit (.int 1))) (.lit (.str "")) (.var "nm"))), ("d", (.cond (.bin .eq (.var "h") (.lit (.int 1))) (.lit (.str "")) (.lit (.str " thunk)")))), ("e", (.lit (.str "")))])
  arms := [.mk "o" false (some "o") none (some (.invoke "wth" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.var "o"))])) []] }

def kWirWWk : KCallable := .subflow {
  preLabel := none
  head := ("wrk", [("rows", (.var "rows")), ("i", (.var "i")), ("nr", (.var "nr"))])
  arms := [.mk "fin" false (some "_") (some (.bin .ge (.var "i") (.bin .mul (.var "nr") (.lit (.int 6))))) (some (.invoke "wfin" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("out", (.var "out")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep")), ("pend", (.var "pend"))])) [], .mk "bwd" false (some "k") (some (.bin .eq (.var "k") (.lit (.int 17)))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad wire-bad)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "ev" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 1))))) (some (.invoke "wclo" [("inf", (.var "inf")), ("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) [.mk "_chain" false (some "c") none (some (.invoke "whev" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("rows", (.var "rows")), ("i", (.var "i"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.bin .concat (.var "c") (.var "t")))), ("dead", (.cond (.bin .eq (.var "t") (.lit (.str " (bad dup-tor)"))) (.lit (.int 1)) (.var "dead"))), ("inev", (.lit (.int 1))), ("inf", (.lit (.int 0))), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 0))), ("ctk", (.lit (.int 0))), ("dep", (.lit (.int 0))), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ano", (.lit (.int 0)))])) []]], .mk "fl" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 2))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.cond (.bin .eq (.var "inev") (.lit (.int 0))) (.lit (.str "(bad fld-out)")) (.lit (.str ""))))), ("dead", (.cond (.bin .eq (.var "inev") (.lit (.int 0))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "rt" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 3))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.cond (.bin .eq (.var "inev") (.lit (.int 0))) (.lit (.str "(bad ret-out)")) (.lit (.str ""))))), ("dead", (.cond (.bin .eq (.var "inev") (.lit (.int 0))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "br" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 4))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.cond (.bin .eq (.var "inev") (.lit (.int 0))) (.lit (.str "(bad brd-out)")) (.lit (.str ""))))), ("dead", (.cond (.bin .eq (.var "inev") (.lit (.int 0))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "im" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 5))))) (some (.invoke "wclo" [("inf", (.var "inf")), ("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) [.mk "_chain" false (some "c") none (some (.invoke "whim" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.var "i"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.bin .concat (.var "c") (.var "t")))), ("dead", (.var "dead")), ("inev", (.lit (.int 0))), ("inf", (.lit (.int 0))), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 0))), ("ctk", (.lit (.int 0))), ("dep", (.lit (.int 0))), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ano", (.lit (.int 0)))])) []]], .mk "lb" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 6))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.var "out")), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("ple", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "fw0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 7)))) (.bin .ge (.var "pend") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad pend)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "fw" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 7))))) (some (.invoke "wclo" [("inf", (.var "inf")), ("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) [.mk "_chain" false (some "c") none (some (.invoke "whfw" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("plbl", (.var "plbl"))])) [.mk "_chain" false (some "t") none (some (.invoke "wevf" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2)))))])) [.mk "_chain" false (some "f") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.bin .concat (.var "c") (.var "t")))), ("dead", (.var "dead")), ("inev", (.lit (.int 0))), ("inf", (.lit (.int 1))), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 0))), ("ctk", (.lit (.int 0))), ("dep", (.lit (.int 0))), ("pend", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("plbl", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ple", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("flbl", (.var "plbl")), ("flbh", (.var "ple")), ("fevi", (.var "f")), ("ano", (.lit (.int 0)))])) []]]], .mk "ca0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 8)))) (.bin .or (.bin .eq (.var "inf") (.lit (.int 0))) (.bin .ne (.var "ltk") (.lit (.int 0)))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad head)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "ca" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 8))))) (some (.invoke "whca" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.lit (.int 1))), ("ltk", (.lit (.int 1))), ("ltl", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("lth", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("htl", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("hth", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("argi", (.lit (.int 0))), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []], .mk "ar0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 9)))) (.bin .eq (.var "iopen") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad arg)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "ar" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 9))))) (some (.invoke "warg" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.var "i")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("fevi", (.var "fevi"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.bin .add (.var "argi") (.lit (.int 1)))), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []], .mk "rb0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 10)))) (.bin .eq (.var "ltk") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad rbind)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "rb" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 10))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.var "out")), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "co0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 11)))) (.bin .eq (.var "inf") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad cont)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "co1" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 11)))) (.bin .ge (.var "pend") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad pend)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "co2" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 11)))) (.bin .eq (.var "ano") (.lit (.int 1))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad chain-scope)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "co" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 11))))) (some (.invoke "wcls" [("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) [.mk "_chain" false (some "c") none (some (.invoke "wevf" [("nsp", (.var "nsp")), ("nn", (.var "nn")), ("lo", (.var "htl"))])) [.mk "_chain" false (some "d") none (some (.invoke "whco" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("fevi", (.var "d"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.bin .concat (.var "c") (.var "t")))), ("dead", (.cond (.bin .eq (.var "t") (.lit (.str " (bad decl-branch)"))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ctk", (.lit (.int 0))), ("dep", (.lit (.int 0))), ("pend", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []]]], .mk "bi0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 12)))) (.bin .eq (.var "curk") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad bind)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "bi" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 12))))) (some (.invoke "whbi" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []], .mk "cn0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 13)))) (.bin .eq (.var "curk") (.lit (.int 0))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad cond)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "cn" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 13))))) (some (.invoke "whcn" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.var "i"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []], .mk "se0" false (some "k") (some (.bin .and (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 14)))) (.bin .eq (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 1)))) (.bin .or (.bin .ne (.var "curk") (.bin .sub (.lit (.int 0)) (.lit (.int 1)))) (.bin .eq (.var "inf") (.lit (.int 0)))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad step-expr)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "se" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 14)))) (.bin .eq (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 1))))) (some (.invoke "wex" [("src", (.var "src")), ("lo", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("hi", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns"))])) [.mk "_chain" false (some "e") none (some (.invoke "wc5" [("a", (.lit (.str " (node (produce "))), ("b", (.var "e")), ("c", (.lit (.str ")"))), ("d", (.lit (.str ")"))), ("e", (.lit (.str "")))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 1))), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []]], .mk "si0" false (some "k") (some (.bin .and (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 14)))) (.bin .eq (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 2)))) (.bin .or (.bin .or (.bin .eq (.var "curk") (.lit (.int 1))) (.bin .eq (.var "curk") (.lit (.int 2)))) (.bin .eq (.var "curk") (.lit (.int 5)))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad chain-after)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "si" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 14)))) (.bin .eq (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 2))))) (some (.invoke "wsti" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("curk", (.var "curk")), ("pend", (.var "pend")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("jump", (.lit (.int 0)))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.cond (.bin .eq (.var "t") (.lit (.str "(bad jump-label)"))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.lit (.int 2))), ("ltk", (.lit (.int 2))), ("ltl", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("lth", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.cond (.bin .eq (.var "curk") (.lit (.int 0))) (.lit (.int 3)) (.cond (.bin .eq (.var "curk") (.bin .sub (.lit (.int 0)) (.lit (.int 1)))) (.lit (.int 3)) (.var "curk")))), ("ctk", (.lit (.int 3))), ("dep", (.cond (.bin .or (.bin .eq (.var "curk") (.lit (.int 3))) (.bin .eq (.var "curk") (.lit (.int 4)))) (.bin .add (.var "dep") (.lit (.int 1))) (.var "dep"))), ("pend", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.cond (.bin .eq (.var "curk") (.lit (.int 0))) (.lit (.int 1)) (.var "ano")))])) []], .mk "sj0" false (some "k") (some (.bin .and (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 14)))) (.bin .eq (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 3)))) (.bin .or (.bin .or (.bin .eq (.var "curk") (.lit (.int 1))) (.bin .eq (.var "curk") (.lit (.int 2)))) (.bin .eq (.var "curk") (.lit (.int 5)))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad chain-after)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "sj" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 14)))) (.bin .eq (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 1)))) (.lit (.int 3))))) (some (.invoke "wsti" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("i", (.var "i")), ("curk", (.var "curk")), ("pend", (.var "pend")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("jump", (.lit (.int 1)))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.cond (.bin .eq (.var "t") (.lit (.str "(bad jump-label)"))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.lit (.int 2))), ("ltk", (.lit (.int 3))), ("ltl", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 2))))), ("lth", (.index (.var "rows") (.bin .add (.var "i") (.lit (.int 3))))), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.cond (.bin .eq (.var "curk") (.lit (.int 0))) (.lit (.int 4)) (.cond (.bin .eq (.var "curk") (.bin .sub (.lit (.int 0)) (.lit (.int 1)))) (.lit (.int 4)) (.var "curk")))), ("ctk", (.lit (.int 4))), ("dep", (.cond (.bin .or (.bin .eq (.var "curk") (.lit (.int 3))) (.bin .eq (.var "curk") (.lit (.int 4)))) (.bin .add (.var "dep") (.lit (.int 1))) (.var "dep"))), ("pend", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.cond (.bin .eq (.var "curk") (.lit (.int 0))) (.lit (.int 1)) (.var "ano")))])) []], .mk "ct0" false (some "k") (some (.bin .and (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 15)))) (.bin .or (.bin .ne (.var "curk") (.bin .sub (.lit (.int 0)) (.lit (.int 1)))) (.bin .eq (.var "inf") (.lit (.int 0)))))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.lit (.str "(bad ctor)")))), ("dead", (.lit (.int 1))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "ct" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 15))))) (some (.invoke "whct" [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.var "i")), ("fevi", (.var "fevi")), ("nr", (.var "nr"))])) [.mk "_chain" false (some "t") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "t"))), ("dead", (.cond (.bin .eq (.var "t") (.lit (.str "(bad ctor-branch)"))) (.lit (.int 1)) (.var "dead"))), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 2))), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []], .mk "ip" false (some "k") (some (.bin .and (.bin .eq (.var "dead") (.lit (.int 0))) (.bin .eq (.var "k") (.lit (.int 16))))) (some (.invoke "wclo" [("inf", (.var "inf")), ("iopen", (.var "iopen")), ("curk", (.var "curk")), ("dep", (.var "dep"))])) [.mk "_chain" false (some "c") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.bin .concat (.var "out") (.var "c"))), ("dead", (.var "dead")), ("inev", (.lit (.int 0))), ("inf", (.lit (.int 0))), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 0))), ("ctk", (.lit (.int 0))), ("dep", (.lit (.int 0))), ("pend", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ano", (.lit (.int 0)))])) []], .mk "dd" false (some "_") (some (.bin .eq (.var "dead") (.lit (.int 1)))) (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.var "out")), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) [], .mk "mo" false (some "_") none (some (.invoke "w-wk" [("rows", (.var "rows")), ("nr", (.var "nr")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.var "nn")), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.var "ns")), ("i", (.bin .add (.var "i") (.lit (.int 6)))), ("out", (.var "out")), ("dead", (.var "dead")), ("inev", (.var "inev")), ("inf", (.var "inf")), ("iopen", (.var "iopen")), ("ltk", (.var "ltk")), ("ltl", (.var "ltl")), ("lth", (.var "lth")), ("htl", (.var "htl")), ("hth", (.var "hth")), ("argi", (.var "argi")), ("curk", (.var "curk")), ("ctk", (.var "ctk")), ("dep", (.var "dep")), ("pend", (.var "pend")), ("plbl", (.var "plbl")), ("ple", (.var "ple")), ("flbl", (.var "flbl")), ("flbh", (.var "flbh")), ("fevi", (.var "fevi")), ("ano", (.var "ano"))])) []] }

def kWirWMain : KCallable := .subflow {
  preLabel := none
  head := ("w-wk", [("rows", (.var "rows")), ("nr", (.bin .div (.builtin "len" [(.var "rows")]) (.lit (.int 6)))), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("nn", (.builtin "len" [(.var "names")])), ("strs", (.var "strs")), ("ssp", (.var "ssp")), ("ns", (.builtin "len" [(.var "strs")])), ("i", (.lit (.int 0))), ("out", (.lit (.str "(graph"))), ("dead", (.lit (.int 0))), ("inev", (.lit (.int 0))), ("inf", (.lit (.int 0))), ("iopen", (.lit (.int 0))), ("ltk", (.lit (.int 0))), ("ltl", (.lit (.int 0))), ("lth", (.lit (.int 0))), ("htl", (.lit (.int 0))), ("hth", (.lit (.int 0))), ("argi", (.lit (.int 0))), ("curk", (.lit (.int 0))), ("ctk", (.lit (.int 0))), ("dep", (.lit (.int 0))), ("pend", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("plbl", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ple", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("flbl", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("flbh", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("fevi", (.bin .sub (.lit (.int 0)) (.lit (.int 1)))), ("ano", (.lit (.int 0)))])
  arms := [.mk "g" false (some "g") none (some (.produce (.var "g"))) []] }

def kWirMain : KCallable := .subflow {
  preLabel := none
  head := ("w-main", [("rows", (.var "rows")), ("src", (.var "src")), ("names", (.var "names")), ("nsp", (.var "nsp")), ("strs", (.var "strs")), ("ssp", (.var "ssp"))])
  arms := [.mk "r" false (some "r") none (some (.produce (.var "r"))) []] }

def kWir : KProg := {
  graph := [
    ("pkb", kWirPkb),
    ("wn0", kWirWn0),
    ("wc2", kWirWc2),
    ("wc3", kWirWc3),
    ("wc5", kWirWc5),
    ("wc7", kWirWc7),
    ("wsk", kWirWsk),
    ("wtb", kWirWtb),
    ("wid", kWirWid),
    ("wpe", kWirWpe),
    ("wnat", kWirWnat),
    ("wpix", kWirWpix),
    ("wnm", kWirWnm),
    ("wne", kWirWne),
    ("wst", kWirWst),
    ("weq", kWirWeq),
    ("weql", kWirWeql),
    ("wnv", kWirWnv),
    ("wp10", kWirWp10),
    ("wp10m", kWirWp10m),
    ("wgcd", kWirWgcd),
    ("wpb", kWirWpb),
    ("wopa", kWirWopa),
    ("wopb", kWirWopb),
    ("wope", kWirWope),
    ("wops", kWirWops),
    ("wopo", kWirWopo),
    ("wopo2", kWirWopo2),
    ("wopob", kWirWopob),
    ("wopd", kWirWopd),
    ("wopd2", kWirWopd2),
    ("wopdb", kWirWopdb),
    ("wprc", kWirWprc),
    ("wopn", kWirWopn),
    ("wfp", kWirWfp),
    ("wfp1", kWirWfp1),
    ("wfpn", kWirWfpn),
    ("wmb", kWirWmb),
    ("wmb1", kWirWmb1),
    ("wmbx", kWirWmbx),
    ("wss", kWirWss),
    ("wen", kWirWen),
    ("wcmx", kWirWcmx),
    ("wfd", kWirWfd),
    ("wty", kWirWty),
    ("wbl", kWirWbl),
    ("wev", kWirWev),
    ("wenx", kWirWenx),
    ("wspl", kWirWspl),
    ("wsplr", kWirWsplr),
    ("weu", kWirWeu),
    ("weu1", kWirWeu1),
    ("wpm", kWirWpm),
    ("wpmc", kWirWpmc),
    ("wpmv", kWirWpmv),
    ("wpmv1", kWirWpmv1),
    ("wpmv2", kWirWpmv2),
    ("wep", kWirWep),
    ("wep1", kWirWep1),
    ("wep1f", kWirWep1f),
    ("wep1i", kWirWep1i),
    ("wep1t", kWirWep1t),
    ("wep1u", kWirWep1u),
    ("wep1v", kWirWep1v),
    ("wep1w", kWirWep1w),
    ("wem", kWirWem),
    ("wems", kWirWems),
    ("wemg", kWirWemg),
    ("wema", kWirWema),
    ("weal", kWirWeal),
    ("weal1", kWirWeal1),
    ("wemc", kWirWemc),
    ("wecl", kWirWecl),
    ("wecl1", kWirWecl1),
    ("wecl2", kWirWecl2),
    ("wecl3", kWirWecl3),
    ("wemb", kWirWemb),
    ("wemb1", kWirWemb1),
    ("wemb2", kWirWemb2),
    ("webal", kWirWebal),
    ("webal1", kWirWebal1),
    ("wemv", kWirWemv),
    ("wemvd", kWirWemvd),
    ("wemve", kWirWemve),
    ("wemi", kWirWemi),
    ("wemi1", kWirWemi1),
    ("wemi2", kWirWemi2),
    ("wemi3", kWirWemi3),
    ("wtek", kWirWtek),
    ("wtek1", kWirWtek1),
    ("wtek1b", kWirWtek1b),
    ("wtek2", kWirWtek2),
    ("wtek2b", kWirWtek2b),
    ("wbd", kWirWbd),
    ("wbd1", kWirWbd1),
    ("wfel", kWirWfel),
    ("wfeln", kWirWfeln),
    ("wnum", kWirWnum),
    ("wnum1", kWirWnum1),
    ("wnum2", kWirWnum2),
    ("wnum3", kWirWnum3),
    ("wel", kWirWel),
    ("wel1", kWirWel1),
    ("welg", kWirWelg),
    ("wela", kWirWela),
    ("well", kWirWell),
    ("well1", kWirWell1),
    ("welc", kWirWelc),
    ("welcl", kWirWelcl),
    ("welcl1", kWirWelcl1),
    ("welcl2", kWirWelcl2),
    ("welcl3", kWirWelcl3),
    ("wrk", kWirWrk),
    ("wevf", kWirWevf),
    ("wdpe", kWirWdpe),
    ("whi", kWirWhi),
    ("wfdn", kWirWfdn),
    ("wfdh", kWirWfdh),
    ("wfdh1", kWirWfdh1),
    ("wbr0", kWirWbr0),
    ("wbrn", kWirWbrn),
    ("wbrn1", kWirWbrn1),
    ("wbrh", kWirWbrh),
    ("wbrh1", kWirWbrh1),
    ("wbrh2", kWirWbrh2),
    ("wrp", kWirWrp),
    ("wrp1", kWirWrp1),
    ("wclo", kWirWclo),
    ("wcloa", kWirWcloa),
    ("wcls", kWirWcls),
    ("wex", kWirWex),
    ("wpun", kWirWpun),
    ("wpun1", kWirWpun1),
    ("wpun2", kWirWpun2),
    ("wpun3", kWirWpun3),
    ("wpun3b", kWirWpun3b),
    ("wdk", kWirWdk),
    ("warg", kWirWarg),
    ("warg1", kWirWarg1),
    ("warg2", kWirWarg2),
    ("warg2a", kWirWarg2a),
    ("warg3", kWirWarg3),
    ("warg3a", kWirWarg3a),
    ("warg4", kWirWarg4),
    ("warg5", kWirWarg5),
    ("whev", kWirWhev),
    ("whim", kWirWhim),
    ("whfw", kWirWhfw),
    ("whfw1", kWirWhfw1),
    ("whca", kWirWhca),
    ("whco", kWirWhco),
    ("whco1", kWirWhco1),
    ("whbi", kWirWhbi),
    ("whcn", kWirWhcn),
    ("whct", kWirWhct),
    ("whct1", kWirWhct1),
    ("whct2", kWirWhct2),
    ("wsti", kWirWsti),
    ("wsti1", kWirWsti1),
    ("wsti2", kWirWsti2),
    ("wsti3", kWirWsti3),
    ("wfin", kWirWfin),
    ("wfin1", kWirWfin1),
    ("wth", kWirWth),
    ("wthi", kWirWthi),
    ("wthi1", kWirWthi1),
    ("w-wk", kWirWWk),
    ("w-main", kWirWMain),
    ("main", kWirMain)
  ]
  entry := "main"
  args := [] }

def kWirDecls : List (String × KDecl) := [
("pkb", { params := [("t", "[]const i64"), ("i", "i64"), ("n", "i64")], ret := some "i64" })
  , ("wn0", { params := [], ret := some "i64" })
  , ("wc2", { params := [("a", "string"), ("b", "string")], ret := some "string" })
  , ("wc3", { params := [("a", "string"), ("b", "string"), ("c", "string")], ret := some "string" })
  , ("wc5", { params := [("a", "string"), ("b", "string"), ("c", "string"), ("d", "string"), ("e", "string")], ret := some "string" })
  , ("wc7", { params := [("a", "string"), ("b", "string"), ("c", "string"), ("d", "string"), ("e", "string"), ("f", "string"), ("g", "string")], ret := some "string" })
  , ("wsk", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wtb", { params := [("src", "[]const i64"), ("lo", "i64"), ("j", "i64"), ("n", "i64")], ret := some "i64" })
  , ("wid", { params := [("c", "i64")], ret := some "i64" })
  , ("wpe", { params := [("c", "i64")], ret := some "i64" })
  , ("wnat", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wpix", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wnm", { params := [("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("p", "i64")], ret := some "string" })
  , ("wne", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wst", { params := [("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("p", "i64")], ret := some "string" })
  , ("weq", { params := [("src", "[]const i64"), ("a", "i64"), ("b", "i64"), ("x", "i64"), ("y", "i64")], ret := some "i64" })
  , ("weql", { params := [("src", "[]const i64"), ("a", "i64"), ("b", "i64"), ("x", "i64"), ("y", "i64"), ("i", "i64")], ret := some "i64" })
  , ("wnv", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("v", "i64")], ret := some "i64" })
  , ("wp10", { params := [("n", "i64")], ret := some "i64" })
  , ("wp10m", { params := [("n", "i64")], ret := some "i64" })
  , ("wgcd", { params := [("a", "i64"), ("b", "i64")], ret := some "i64" })
  , ("wpb", { params := [("src", "[]const i64"), ("lo", "i64"), ("i", "i64")], ret := some "i64" })
  , ("wopa", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("d", "i64"), ("ins", "i64")], ret := some "i64" })
  , ("wopb", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wope", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64"), ("op", "i64")], ret := some "i64" })
  , ("wops", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wopo", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wopo2", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wopob", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wopd", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wopd2", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("p", "i64")], ret := some "i64" })
  , ("wopdb", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wprc", { params := [("o", "i64")], ret := some "i64" })
  , ("wopn", { params := [("o", "i64")], ret := some "string" })
  , ("wfp", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("d", "i64"), ("ins", "i64"), ("last", "i64"), ("prec", "i64")], ret := some "i64" })
  , ("wfp1", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("d", "i64"), ("ins", "i64"), ("last", "i64"), ("prec", "i64"), ("o", "i64")], ret := some "i64" })
  , ("wfpn", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("d", "i64"), ("ins", "i64"), ("last", "i64"), ("prec", "i64")], ret := some "i64" })
  , ("wmb", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wmb1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64")], ret := some "i64" })
  , ("wmbx", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64")], ret := some "i64" })
  , ("wss", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wen", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wcmx", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64"), ("w", "i64")], ret := some "i64" })
  , ("wfd", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64"), ("last", "i64")], ret := some "i64" })
  , ("wty", { params := [("nm", "string")], ret := some "i64" })
  , ("wbl", { params := [("nm", "string")], ret := some "i64" })
  , ("wev", { params := [("lv", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wenx", { params := [("lv", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wspl", { params := [("lv", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("t", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wsplr", { params := [("lv", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("op", "i64"), ("l", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("weu", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("weu1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("op", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wpm", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "i64" })
  , ("wpmc", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wpmv", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "i64" })
  , ("wpmv1", { params := [("src", "[]const i64"), ("i", "i64"), ("e", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wpmv2", { params := [("src", "[]const i64"), ("e", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wep", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("acc", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1f", { params := [("src", "[]const i64"), ("j", "i64"), ("hi", "i64"), ("acc", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1i", { params := [("src", "[]const i64"), ("j", "i64"), ("hi", "i64"), ("acc", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1t", { params := [("src", "[]const i64"), ("j", "i64"), ("k", "i64"), ("hi", "i64"), ("acc", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1u", { params := [("src", "[]const i64"), ("j", "i64"), ("k", "i64"), ("hi", "i64"), ("acc", "string"), ("t", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1v", { params := [("src", "[]const i64"), ("j", "i64"), ("e", "i64"), ("hi", "i64"), ("acc", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wep1w", { params := [("src", "[]const i64"), ("m", "i64"), ("hi", "i64"), ("acc", "string"), ("x", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wem", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wems", { params := [("src", "[]const i64"), ("i", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemg", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wema", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("weal", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("weal1", { params := [("src", "[]const i64"), ("j", "i64"), ("c", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemc", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wecl", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wecl1", { params := [("src", "[]const i64"), ("j", "i64"), ("c", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wecl2", { params := [("src", "[]const i64"), ("j", "i64"), ("c", "i64"), ("m", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wecl3", { params := [("src", "[]const i64"), ("m", "i64"), ("hi", "i64"), ("out", "string"), ("nm", "string"), ("x", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemb", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemb1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("nm", "string"), ("b", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemb2", { params := [("src", "[]const i64"), ("e", "i64"), ("hi", "i64"), ("nm", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("webal", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("webal1", { params := [("src", "[]const i64"), ("j", "i64"), ("v", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemv", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemvd", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("nm", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemve", { params := [("src", "[]const i64"), ("j", "i64"), ("hi", "i64"), ("nm", "string")], ret := some "string" })
  , ("wemi", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemi1", { params := [("src", "[]const i64"), ("j", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemi2", { params := [("src", "[]const i64"), ("j", "i64"), ("m", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wemi3", { params := [("src", "[]const i64"), ("m", "i64"), ("el", "i64"), ("c", "string"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wtek", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64")], ret := some "i64" })
  , ("wtek1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wtek1b", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wtek2", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wtek2b", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wbd", { params := [("src", "[]const i64"), ("pv", "i64"), ("nx", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wbd1", { params := [("src", "[]const i64"), ("nx", "i64"), ("hi", "i64")], ret := some "i64" })
  , ("wfel", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64"), ("ifd", "i64")], ret := some "i64" })
  , ("wfeln", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("d", "i64"), ("ins", "i64"), ("ifd", "i64")], ret := some "i64" })
  , ("wnum", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wnum1", { params := [("src", "[]const i64"), ("lo", "i64"), ("e", "i64"), ("d", "i64")], ret := some "string" })
  , ("wnum2", { params := [("src", "[]const i64"), ("e", "i64"), ("d", "i64"), ("w", "i64")], ret := some "string" })
  , ("wnum3", { params := [("e", "i64"), ("d", "i64"), ("w", "i64"), ("f", "i64"), ("dn", "i64")], ret := some "string" })
  , ("wel", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wel1", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("nm", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "string" })
  , ("welg", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wela", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("well", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("well1", { params := [("src", "[]const i64"), ("j", "i64"), ("c", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("welc", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("welcl", { params := [("src", "[]const i64"), ("i", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("welcl1", { params := [("src", "[]const i64"), ("j", "i64"), ("c", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("welcl2", { params := [("src", "[]const i64"), ("j", "i64"), ("c", "i64"), ("m", "i64"), ("hi", "i64"), ("out", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("welcl3", { params := [("src", "[]const i64"), ("m", "i64"), ("hi", "i64"), ("out", "string"), ("nm", "string"), ("x", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wrk", { params := [("rows", "[]const i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wevf", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("lo", "i64")], ret := some "i64" })
  , ("wdpe", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("rows", "[]const i64"), ("i", "i64")], ret := some "i64" })
  , ("whi", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("lo", "i64")], ret := some "i64" })
  , ("wfdn", { params := [("rows", "[]const i64"), ("evi", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wfdh", { params := [("rows", "[]const i64"), ("evi", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wfdh1", { params := [("rows", "[]const i64"), ("evi", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wbr0", { params := [("rows", "[]const i64"), ("evi", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wbrn", { params := [("rows", "[]const i64"), ("evi", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wbrn1", { params := [("rows", "[]const i64"), ("b", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wbrh", { params := [("rows", "[]const i64"), ("evi", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wbrh1", { params := [("rows", "[]const i64"), ("b", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wbrh2", { params := [("rows", "[]const i64"), ("b", "i64"), ("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("i", "i64"), ("nr", "i64")], ret := some "i64" })
  , ("wrp", { params := [("k", "i64")], ret := some "string" })
  , ("wrp1", { params := [("k", "i64")], ret := some "string" })
  , ("wclo", { params := [("inf", "i64"), ("iopen", "i64"), ("curk", "i64"), ("dep", "i64")], ret := some "string" })
  , ("wcloa", { params := [("iopen", "i64"), ("curk", "i64"), ("dep", "i64")], ret := some "string" })
  , ("wcls", { params := [("iopen", "i64"), ("curk", "i64"), ("dep", "i64")], ret := some "string" })
  , ("wex", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64")], ret := some "string" })
  , ("wpun", { params := [("src", "[]const i64"), ("lo", "i64"), ("hi", "i64"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "i64" })
  , ("wpun1", { params := [("src", "[]const i64"), ("a", "i64"), ("b", "i64"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "i64" })
  , ("wpun2", { params := [("src", "[]const i64"), ("b", "i64"), ("f", "i64"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "i64" })
  , ("wpun3", { params := [("src", "[]const i64"), ("f", "i64")], ret := some "i64" })
  , ("wpun3b", { params := [("c", "i64"), ("f", "i64")], ret := some "i64" })
  , ("wdk", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("ltk", "i64"), ("ltl", "i64"), ("lth", "i64"), ("htl", "i64"), ("hth", "i64"), ("fevi", "i64")], ret := some "i64" })
  , ("warg", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64"), ("ltk", "i64"), ("ltl", "i64"), ("lth", "i64"), ("htl", "i64"), ("hth", "i64"), ("argi", "i64"), ("fevi", "i64")], ret := some "string" })
  , ("warg1", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("d", "i64"), ("argi", "i64"), ("e", "string")], ret := some "string" })
  , ("warg2", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("d", "i64"), ("e", "string")], ret := some "string" })
  , ("warg2a", { params := [("rows", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("e", "string")], ret := some "string" })
  , ("warg3", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("d", "i64"), ("argi", "i64"), ("e", "string"), ("p", "i64")], ret := some "string" })
  , ("warg3a", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("d", "i64"), ("argi", "i64"), ("e", "string"), ("p", "i64"), ("pe", "i64")], ret := some "string" })
  , ("warg4", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("d", "i64"), ("argi", "i64"), ("e", "string")], ret := some "string" })
  , ("warg5", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("d", "i64"), ("argi", "i64"), ("e", "string")], ret := some "string" })
  , ("whev", { params := [("nsp", "[]const i64"), ("nn", "i64"), ("rows", "[]const i64"), ("i", "i64")], ret := some "string" })
  , ("whim", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64")], ret := some "string" })
  , ("whfw", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("plbl", "i64")], ret := some "string" })
  , ("whfw1", { params := [("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("plbl", "i64"), ("nm", "string")], ret := some "string" })
  , ("whca", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64")], ret := some "string" })
  , ("whco", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("fevi", "i64")], ret := some "string" })
  , ("whco1", { params := [("rows", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("fevi", "i64"), ("b", "i64"), ("n", "i64")], ret := some "string" })
  , ("whbi", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64")], ret := some "string" })
  , ("whcn", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64")], ret := some "string" })
  , ("whct", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64"), ("fevi", "i64"), ("nr", "i64")], ret := some "string" })
  , ("whct1", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64"), ("fevi", "i64"), ("b", "i64")], ret := some "string" })
  , ("whct2", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64"), ("nm", "string")], ret := some "string" })
  , ("wsti", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("curk", "i64"), ("pend", "i64"), ("flbl", "i64"), ("flbh", "i64"), ("jump", "i64")], ret := some "string" })
  , ("wsti1", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("curk", "i64"), ("pend", "i64"), ("flbl", "i64"), ("flbh", "i64"), ("jump", "i64"), ("nm", "string")], ret := some "string" })
  , ("wsti2", { params := [("curk", "i64"), ("pend", "i64"), ("jump", "i64"), ("nm", "string"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64")], ret := some "string" })
  , ("wsti3", { params := [("curk", "i64"), ("pend", "i64"), ("jump", "i64"), ("nm", "string"), ("b", "string")], ret := some "string" })
  , ("wfin", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("out", "string"), ("inf", "i64"), ("iopen", "i64"), ("curk", "i64"), ("dep", "i64"), ("pend", "i64")], ret := some "string" })
  , ("wfin1", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("out", "string"), ("c", "string")], ret := some "string" })
  , ("wth", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("out", "string")], ret := some "string" })
  , ("wthi", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("out", "string")], ret := some "string" })
  , ("wthi1", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("i", "i64"), ("out", "string"), ("h", "i64"), ("nm", "string")], ret := some "string" })
  , ("w-wk", { params := [("rows", "[]const i64"), ("nr", "i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("nn", "i64"), ("strs", "[]const string"), ("ssp", "[]const i64"), ("ns", "i64"), ("i", "i64"), ("out", "string"), ("dead", "i64"), ("inev", "i64"), ("inf", "i64"), ("iopen", "i64"), ("ltk", "i64"), ("ltl", "i64"), ("lth", "i64"), ("htl", "i64"), ("hth", "i64"), ("argi", "i64"), ("curk", "i64"), ("ctk", "i64"), ("dep", "i64"), ("pend", "i64"), ("plbl", "i64"), ("ple", "i64"), ("flbl", "i64"), ("flbh", "i64"), ("fevi", "i64"), ("ano", "i64")], ret := some "string" })
  , ("w-main", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("strs", "[]const string"), ("ssp", "[]const i64")], ret := some "string" })
  , ("main", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("strs", "[]const string"), ("ssp", "[]const i64")], ret := some "string" })
 ]

/-- The unrealized-leg shape: head resolves, no arm matches —
dispatch refuses and the tor NAME is the axis. -/
def kChainStub : KCallable :=
  .subflow ⟨none, ("unrealized", []), []⟩

/-- The `wir` leg realized: the six-arg token-table interface —
the flat rows, source bytes, and name/string tables are the
producer's output crossing the boundary AS DATA (composite values
can't be built inside eval, so the tables arrive as params, not
from `a-main`'s text).  Head hands them to `w-main`; the result is
the `(graph …)` claim text. -/
def kChainWir : KCallable := .subflow {
  preLabel := none
  head := ("w-w-main",
    [("rows", .var "rows"), ("src", .var "src"),
     ("names", .var "names"), ("nsp", .var "nsp"),
     ("strs", .var "strs"), ("ssp", .var "ssp")])
  arms := [ .mk "r" false (some "r") none
      (some (.produce (.var "r"))) [] ] }

/-- The wiring spine: `a-main` row-text → low-txt (mirror doc) and
the arg-supplied tables → `wir` → emt-txt.  `a-main`'s output binds
`rt` — the row-TEXT lane stays the authority-mirror path; `wir`'s
flat `rows` are `chain`'s own param, the same boundary data the
wi/wii legs feed. -/
def kChainMain : KCallable := .subflow {
  preLabel := none
  head := ("a-main", [("chars", .var "src")])
  arms := [ .mk "rows" false (some "rt") none
      (some (.invoke "low-txt"
        [("rows", .var "rt"), ("src", .var "src")]))
      [ .mk "doc" false (some "_") none
          (some (.invoke "wir"
            [("rows", .var "rows"), ("src", .var "src"),
             ("names", .var "names"), ("nsp", .var "nsp"),
             ("strs", .var "strs"), ("ssp", .var "ssp")]))
          [ .mk "claim" false (some "claim") none
              (some (.invoke "emt-txt" [("claim", .var "claim")]))
              [] ] ] ] }

def kChain : KProg := {
  graph :=
    [("unrealized", .bare (.lit (.str "unrealized")))
    ,("low-txt", kChainStub)
    ,("wir", kChainWir)
    ,("emt-txt", kChainStub)
    ,("chain", kChainMain)]
    ++ prefixGraph "a-" kAst.graph
    ++ prefixGraph "l-" kLow.graph
    ++ prefixGraph "w-" kWir.graph
  entry := "chain"
  args := [] }

def kChainDecls : List (String × KDecl) :=
  [ ("chain", { params := [("src", "[]const i64"), ("rows", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("strs", "[]const string"), ("ssp", "[]const i64")], ret := some "string" }),
    ("low-txt", { params := [("rows", "[]const i64"), ("src", "[]const i64")], ret := some "string" }),
    ("wir", { params := [("rows", "[]const i64"), ("src", "[]const i64"), ("names", "[]const string"), ("nsp", "[]const i64"), ("strs", "[]const string"), ("ssp", "[]const i64")], ret := some "string" }),
    ("emt-txt", { params := [("claim", "string")], ret := some "string" }) ]
  ++ (kAstDecls.map fun (n, d) => ("a-" ++ n, d))
  ++ (kLowDecls.map fun (n, d) => ("l-" ++ n, d))
  ++ (kWirDecls.map fun (n, d) => ("w-" ++ n, d))

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
          head := ("classify", [("x", .un .neg (.lit (.int 5)))])
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
