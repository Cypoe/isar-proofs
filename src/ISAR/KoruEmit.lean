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
