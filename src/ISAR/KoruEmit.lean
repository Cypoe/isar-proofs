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
