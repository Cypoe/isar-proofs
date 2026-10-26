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

/-- A navigation that cannot succeed — the refusal arm. `field` on
an int is a type error → `none`. -/
def refused : KExpr := .field (.lit (.int 0)) "x"

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

end ISAR
