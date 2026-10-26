import ISAR.KoruEmit

/-!
# DumpKoruFixtures — the Lean→host2 data crossing

Writes the host2 corpus as **real koru source** `.k` files plus a
`cases.json` spec file:

    lake env lean --run tools/DumpKoruFixtures.lean

writes `host2/specs/tests/<GGG>_<group>/<NNN>_<leaf>/` leaf folders —
`input.k` authored-syntax files in koru's own surface (`tor`, `->`,
`=`, `|`) plus a per-leaf `cases.json` spec row: entry call, fuel,
expected result, expected emit text, oracle.  Groups: `200_emit`
(the emission-fixpoint corpus), `100_flow` (the flow-grammar
corpus), `900_wire` (rows with no surface spelling — the claim is
generated data), `800_forged` (asserted-wrong expectations).

The `.k` files are GENERATED from `koruEmitCorpus` —
one source of truth, no drift.  They are parsed by
`host2/src/korufe/` into the canonical `program.ast.json` shape and
lowered by the same tool into `[flow-eval]` claims — the s-expression
wire is the *lower* layer, never the authored surface.  `cases.json`
rows are the spec: the gate joins file ↔ ast ↔ claim ↔ decided
result ↔ emitted C ↔ runtime.

`800_forged/000_wrong_expect` asserts result 6 where the program
decides 5 — `krun` must DRIFT it, proving claims are re-decided.
-/

def sxName (s : String) : String := s

def sxStrLit (s : String) : String := "\"" ++ s ++ "\""

def binopName : ISAR.KBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .and => "and" | .or => "or" | .concat => "concat"

def unopName : ISAR.KUnOp → String
  | .not => "not" | .neg => "neg"

mutual
def sxVal : ISAR.KVal → String
  | .int i => "(int " ++ toString i ++ ")"
  | .float n d => "(float " ++ toString n ++ " " ++ toString d ++ ")"
  | .bool b => "(bool " ++ (if b then "true" else "false") ++ ")"
  | .str s => "(str " ++ sxStrLit s ++ ")"
  | .arr xs => "(arr" ++ sxVals xs ++ ")"
  | .cell fs => "(cell" ++ sxNamedVals fs ++ ")"

def sxVals : List ISAR.KVal → String
  | [] => ""
  | x :: xs => " " ++ sxVal x ++ sxVals xs

def sxNamedVals : List (String × ISAR.KVal) → String
  | [] => ""
  | (n, v) :: xs => " (" ++ sxName n ++ " " ++ sxVal v ++ ")" ++ sxNamedVals xs

def sxExpr : ISAR.KExpr → String
  | .lit v => "(lit " ++ sxVal v ++ ")"
  | .var n => "(var " ++ sxName n ++ ")"
  | .bin op a b => "(bin " ++ binopName op ++ " " ++ sxExpr a ++ " " ++ sxExpr b ++ ")"
  | .un op e => "(un " ++ unopName op ++ " " ++ sxExpr e ++ ")"
  | .cond c t e => "(cond " ++ sxExpr c ++ " " ++ sxExpr t ++ " " ++ sxExpr e ++ ")"
  | .field o n => "(field " ++ sxExpr o ++ " " ++ sxName n ++ ")"
  | .index o i => "(index " ++ sxExpr o ++ " " ++ sxExpr i ++ ")"
  | .builtin n args => "(builtin " ++ sxName n ++ sxExprs args ++ ")"

def sxExprs : List ISAR.KExpr → String
  | [] => "" | x :: xs => " " ++ sxExpr x ++ sxExprs xs

def sxNamedExprs : List (String × ISAR.KExpr) → String
  | [] => ""
  | (n, e) :: xs => " (" ++ sxName n ++ " " ++ sxExpr e ++ ")" ++ sxNamedExprs xs

def sxArmNode : ISAR.KArmNode → String
  | .terminal => "terminal"
  | .jump t args => "(jump " ++ sxName t ++ sxNamedExprs args ++ ")"
  | .invoke t args => "(invoke " ++ sxName t ++ sxNamedExprs args ++ ")"
  | .produce e => "(produce " ++ sxExpr e ++ ")"
  | .retCtor c e => "(ctor " ++ sxName c ++ " " ++ sxExpr e ++ ")"

def sxArm : ISAR.KArm → String
  | .mk br ca bi co no cs =>
      let tagf := if ca then "catchall" else "(tag " ++ sxName br ++ ")"
      let fields :=
        [tagf]
        ++ (match bi with | none => [] | some b => ["(bind " ++ sxName b ++ ")"])
        ++ (match co with | none => [] | some e => ["(when " ++ sxExpr e ++ ")"])
        ++ (match no with | none => [] | some n => ["(node " ++ sxArmNode n ++ ")"])
        ++ (match cs with
            | [] => []
            | _ => ["(conts" ++ sxArms cs ++ ")"])
      "(arm " ++ String.intercalate " " fields ++ ")"

def sxArms : List ISAR.KArm → String
  | [] => "" | a :: xs => " " ++ sxArm a ++ sxArms xs
end

def sxFlow (f : ISAR.KFlow) : String :=
  let labelf := match f.preLabel with
    | none => [] | some l => ["(label " ++ sxName l ++ ")"]
  let head := "(head " ++ sxName f.head.1 ++ sxNamedExprs f.head.2 ++ ")"
  "(subflow " ++ String.intercalate " " (labelf ++ [head]) ++ sxArms f.arms ++ ")"

def sxDecl (nc : String × ISAR.KCallable) : String :=
  "(def " ++ sxName nc.1 ++ " " ++ (match nc.2 with
    | .bare e => "(bare " ++ sxExpr e ++ ")"
    | .thunk => "thunk"
    | .subflow f => sxFlow f) ++ ")"

def sxDecls : List (String × ISAR.KCallable) → String
  | [] => "" | d :: xs => " " ++ sxDecl d ++ sxDecls xs

def sxResult : ISAR.KResult → String
  | ⟨none, none⟩ => "(void)"
  | ⟨none, some v⟩ => "(bare " ++ sxVal v ++ ")"
  | ⟨some b, none⟩ => "(tag " ++ sxName b ++ ")"
  | ⟨some b, some v⟩ => "(tag " ++ sxName b ++ " " ++ sxVal v ++ ")"

def sxExpected : Option ISAR.KResult → String
  | none => "refuse" | some r => sxResult r

def sxArgs (args : List (String × ISAR.KVal)) : String :=
  String.intercalate "" (args.map fun (n, v) => " (" ++ sxName n ++ " " ++ sxVal v ++ ")")

/-- The `[flow-eval]` claim line for a program — graph, entry call,
fuel, decided result, empty oracle.  Kept for the lower layer only:
generated `.k` files carry real koru syntax; the claim is what
`korufe --lower` produces from the ast, not what gets authored. -/
def claimSx (p : ISAR.KProg) (fuel : Nat) (expected : Option ISAR.KResult) : String :=
  "[flow-eval] ((entry " ++ sxName p.entry ++ sxArgs p.args
    ++ ") (fuel " ++ toString fuel
    ++ ") (result " ++ sxExpected expected
    ++ ") (graph" ++ sxDecls p.graph
    ++ ") (oracle))"

/-- One oracle leaf — `(leaf name ((arg val) ...) result)`. -/
def sxLeaf (leaf : (String × List (String × ISAR.KVal)) × ISAR.KResult)
    : String :=
  "(leaf " ++ sxName leaf.1.1 ++ " ("
    ++ String.intercalate " "
      (leaf.1.2.map fun (n, v) => "(" ++ sxName n ++ " " ++ sxVal v ++ ")")
    ++ ") " ++ sxResult leaf.2 ++ ")"

/-- The claim for a wire row — same `[flow-eval]` shape korufe
produces, authored directly because no `.k` spells the program. -/
def claimSxO (p : ISAR.KProg) (fuel : Nat)
    (expected : Option ISAR.KResult) (o : ISAR.KOracle) : String :=
  "[flow-eval] ((entry " ++ sxName p.entry ++ sxArgs p.args
    ++ ") (fuel " ++ toString fuel
    ++ ") (result " ++ sxExpected expected
    ++ ") (graph" ++ sxDecls p.graph
    ++ ") (oracle" ++ String.intercalate "" (o.map fun l => " " ++ sxLeaf l)
    ++ "))"

/-! ## Koru surface printer — `KProg` → real `.k` syntax

The mirror of `korufe`'s parse: every shape printed here must parse
back through korufe's declared subset.  Anything the subset cannot
express makes the GENERATOR panic — a corpus that cannot be spelled
in the subset is a subset bug, not a silent fallback. -/

/-- Finite-decimal render for wire rationals.  Koru floats are decimal
literals, so only `d = 2^a·5^b` is surface-expressible; anything else
cannot be spelled and panics at generation. -/
def ratDecimal (n d : Int) : Option String :=
  if d <= 0 then none else
  let rec strip (x a b fuel : Nat) : Nat × Nat × Nat :=
    match fuel with
    | 0 => (x, a, b)
    | f + 1 =>
      if x % 2 == 0 && x != 0 then strip (x / 2) (a + 1) b f
      else if x % 5 == 0 && x != 0 then strip (x / 5) a (b + 1) f
      else (x, a, b)
  let (rem, a, b) := strip d.toNat 0 0 64
  if rem != 1 then none else
  let k := max a b
  let scale : Int := (2 : Int) ^ (k - a) * (5 : Int) ^ (k - b)
  let scaled := n * scale
  let neg := scaled < 0
  let an := scaled.natAbs
  let pw := (10 : Nat) ^ k
  let whole := an / pw
  let fracs := toString (an % pw)
  let pad := String.ofList (List.replicate (k - fracs.length) '0')
  some ((if neg then "-" else "") ++ toString whole ++ "." ++ pad ++ fracs)

mutual
def kValSrc : ISAR.KVal → String
  | .int i => toString i
  | .float n d => (ratDecimal n d).get!
  | .bool b => if b then "true" else "false"
  | .str s => "\"" ++ s ++ "\""
  | .arr xs => "[" ++ String.intercalate ", " (kValsSrc xs) ++ "]"
  | .cell fs => "{" ++ String.intercalate ", " (kNamedValsSrc fs) ++ "}"

def kValsSrc : List ISAR.KVal → List String
  | [] => [] | x :: xs => kValSrc x :: kValsSrc xs

def kNamedValsSrc : List (String × ISAR.KVal) → List String
  | [] => []
  | (n, v) :: xs => (sxName n ++ ": " ++ kValSrc v) :: kNamedValsSrc xs
end

def binSym : ISAR.KBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||" | .concat => "++"

mutual
/-- Atom-position print: literals/vars/postfix chains stay bare,
anything compound parenthesizes. -/
def kAtomSrc : ISAR.KExpr → String
  | .lit v => kValSrc v
  | .var n => sxName n
  | .field o n => kPostSrc o ++ "." ++ sxName n
  | .index o i => kPostSrc o ++ "[" ++ kExprSrc i ++ "]"
  | e => "(" ++ kExprSrc e ++ ")"

/-- Postfix-object position: what can take `.field`/`[i]`/`(args)`
without parens. -/
def kPostSrc : ISAR.KExpr → String
  | .var n => sxName n
  | .field o n => kPostSrc o ++ "." ++ sxName n
  | .index o i => kPostSrc o ++ "[" ++ kExprSrc i ++ "]"
  | e => "(" ++ kExprSrc e ++ ")"

def kExprSrc : ISAR.KExpr → String
  | .lit v => kValSrc v
  | .var n => sxName n
  | .bin op a b =>
      "(" ++ kExprSrc a ++ " " ++ binSym op ++ " " ++ kExprSrc b ++ ")"
  | .un .neg e => "-" ++ kAtomSrc e
  | .un .not e => "!" ++ kAtomSrc e
  | .cond c t e =>
      "if(" ++ kExprSrc c ++ ") " ++ kExprSrc t
        ++ " else " ++ kExprSrc e
  | .field o n => kPostSrc o ++ "." ++ sxName n
  | .index o i => kPostSrc o ++ "[" ++ kExprSrc i ++ "]"
  | .builtin n args =>
      "@" ++ sxName n ++ "(" ++ String.intercalate ", " (kExprsSrc args) ++ ")"

def kExprsSrc : List ISAR.KExpr → List String
  | [] => [] | x :: xs => kExprSrc x :: kExprsSrc xs
end

/-- Koru puns: `f(x)` binds param `x` from a bare `x`; the pun name
is the expr's trailing ident (`f(p.x)` puns to `x`).  `n: e` where
`e` puns to `n` is a refused redundancy (PARSE005) — emit the pun. -/
def punName : ISAR.KExpr → Option String
  | .var v => some v
  | .field _ f => some f
  | _ => none

def kNamedExprsSrc (args : List (String × ISAR.KExpr)) : String :=
  String.intercalate ", " (go args) where
  go : List (String × ISAR.KExpr) → List String
    | [] => []
    | (n, e) :: xs =>
        (match punName e with
         | some p => if p == n then kExprSrc e
           else sxName n ++ ": " ++ kExprSrc e
         | none => sxName n ++ ": " ++ kExprSrc e) :: go xs

/-- Guard position: koru's `when <cond>` reads to the next `->`/`|>`/
`=>` delimiter — a parenthesised compound stays correct; a top-level
binop spells bare (`when 0 < i`, koru's own idiom). -/
def kGuardSrc : ISAR.KExpr → String
  | .bin op a b =>
      kExprSrc a ++ " " ++ binSym op ++ " " ++ kExprSrc b
  | e => kExprSrc e

/-- One arm line incl. its `|`/`|*` marker — the residual arm is
glued `|*` in real koru (`| *` is the retired deref spelling). -/
def kArmSrc (a : ISAR.KArm) : String :=
  let head := if a.catchall then
      panic! "residual |* arm has no koru surface in the subset — wire row"
    else if a.branch == "" then
      panic! "bare-dispatch arm has no koru surface in the subset"
    else sxName a.branch
  let bindf := match a.bind with
    | none => ""
    | some b => " " ++ sxName b
  let whenf := match a.cond with
    | none => ""
    | some e => " when " ++ kGuardSrc e
  let nodef := match a.node with
    | none => ""
    | some .terminal => ""
    | some (.produce e) => " -> " ++ kExprSrc e
    | some (.retCtor c e) =>
        match e with
        | .lit (.cell []) => " => " ++ sxName c
        | _ => " => " ++ sxName c ++ " " ++ kExprSrc e
    | some (.invoke t args) =>
        " |> " ++ sxName t ++ "(" ++ kNamedExprsSrc args ++ ")"
    | some (.jump l args) =>
        " |> @" ++ sxName l ++ "(" ++ kNamedExprsSrc args ++ ")"
  match a.conts with
  | _ :: _ => panic! "nested continuation arms have no koru surface in the subset"
  | [] => (if a.catchall then "|*" else "| ") ++ head ++ bindf ++ whenf ++ nodef

def kFlowSrc (f : ISAR.KFlow) : String :=
  (match f.preLabel with | none => "" | some l => "#" ++ sxName l ++ " ")
    ++ sxName f.head.1 ++ "(" ++ kNamedExprsSrc f.head.2 ++ ")"
    ++ String.intercalate "" (f.arms.map fun a => "\n" ++ kArmSrc a)

/-- Field declarations for a `tor` — value-typed from entry args.
`arr`/`cell` args have no koru spelling in the subset; panic. -/
def kArgTy : ISAR.KVal → String
  | .int _ => "i64" | .float _ _ => "f64" | .bool _ => "bool"
  | .str _ => "string"
  | .arr _ => panic! "arr arg type has no koru spelling in the subset"
  | .cell _ => panic! "cell arg type has no koru spelling in the subset"

def kDeclFieldsT (args : List (String × String)) : String :=
  "{" ++ String.intercalate ", "
    (args.map fun (n, t) => sxName n ++ ": " ++ t) ++ "}"

def kDeclFields (args : List (String × ISAR.KVal)) : String :=
  kDeclFieldsT (args.map fun (n, v) => (n, kArgTy v))

/-- `| br ty` rows under a `tor` — the branch decls koruc requires
(KORU021). `none` payload type spells `| br`. -/
def kBranchesSrc (bs : List (String × Option String)) : String :=
  String.intercalate "" (bs.map fun (b, ty) =>
    "\n| " ++ b ++ match ty with | some t => " " ++ t | none => "")

/-- Return annotation for literal bare impls — honest koru where the
type is statically obvious; omitted otherwise (koru infers). -/
def kRetTy : ISAR.KExpr → String
  | .lit (.int _) => " -> i64"
  | .lit (.float _ _) => " -> f64"
  | .lit (.bool _) => " -> bool"
  | .lit (.str _) => " -> string"
  | _ => ""

/-- Resolve a callable's declared contract: an explicit decls entry
wins; the entry callable derives params from `p.args`; everything
else declares `{}`. -/
def kDeclOf (decls : List (String × ISAR.KDecl)) (entry : String)
    (eargs : List (String × ISAR.KVal)) (n : String) : ISAR.KDecl :=
  match decls.find? (·.1 == n) with
  | some (_, d) => d
  | none => if n == entry
      then { params := eargs.map fun (a, v) => (a, kArgTy v) } else {}

/-- A `tor` declaration plus its impl, for one graph entry.  Params
and branch rows come from the resolved `KDecl` — the contract real
koru checks at PARSE006/KORU021.  `declared := false` emits no `tor`
line — a legal implicit decl (impl/callable only). -/
def kCallableSrc (name : String) (d : ISAR.KDecl)
    : ISAR.KCallable → String
  | .bare e =>
      (if d.declared then
        "tor " ++ sxName name ++ " " ++ kDeclFieldsT d.params ++ kRetTy e
          ++ kBranchesSrc d.branches ++ "\n" else "")
        ++ sxName name ++ " -> " ++ kExprSrc e
  | .thunk =>
      if d.declared then
        "tor " ++ sxName name ++ " " ++ kDeclFieldsT d.params
          ++ kBranchesSrc d.branches
      else ""
  | .subflow f =>
      (if d.declared then
        "tor " ++ sxName name ++ " " ++ kDeclFieldsT d.params
          ++ kBranchesSrc d.branches ++ "\n" else "")
        ++ sxName name ++ " = " ++ kFlowSrc f

/-- A whole corpus `.k` file: `tor` decls + impls in graph order.
Decl contracts come from the row's `decls`; the entry callable falls
back to `p.args`; others default to `{}`. -/
def kProgSrc (name : String) (p : ISAR.KProg)
    (decls : List (String × ISAR.KDecl) := []) : String :=
  "// " ++ name ++ " — generated by tools/DumpKoruFixtures.lean, do not edit\n"
    ++ String.intercalate "\n\n" (p.graph.map fun (n, c) =>
        kCallableSrc n (kDeclOf decls p.entry p.args n) c)
    ++ "\n"

/-- `kemit.k`: the compiler program spelled in koru.  `emit` takes a
quoted program `src` — declared `program`-typed; arg-less invoke
refuses (`src` unbound), the emit leg supplies it via `--emit`. -/
def kemitFile : String :=
  "// kemit.k — the C99 compiler as a koru program (generated)\n"
    ++ "// arg-less invoke refuses: `src` unbound; the emit leg\n"
    ++ "// supplies it via --emit (quote of the source program)\n"
    ++ "tor emit { src: program } -> string\n"
    ++ "emit -> " ++ kExprSrc ISAR.kEmitExpr ++ "\n"

/-! ## cases.json — the spec rows

One row per corpus file: entry call, fuel, expected result, expected
emit text, oracle leaves.  `korufe --lower FILE.ast.json cases.json
KEY` joins a program's ast with its row into the `[flow-eval]` claim.
-/

def jsonEsc (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _ => acc.push c) ""

mutual
def kValJson : ISAR.KVal → String
  | .int i => "{\"int\":" ++ toString i ++ "}"
  | .float n d => "{\"float\":[" ++ toString n ++ "," ++ toString d ++ "]}"
  | .bool b => "{\"bool\":" ++ (if b then "true" else "false") ++ "}"
  | .str s => "{\"str\":\"" ++ jsonEsc s ++ "\"}"
  | .arr xs => "{\"arr\":[" ++ String.intercalate "," (kValsJson xs) ++ "]}"
  | .cell fs =>
      "{\"cell\":{" ++ String.intercalate "," (kNamedValsJson fs) ++ "}}"

def kValsJson : List ISAR.KVal → List String
  | [] => [] | x :: xs => kValJson x :: kValsJson xs

def kNamedValsJson : List (String × ISAR.KVal) → List String
  | [] => []
  | (n, v) :: xs => ("\"" ++ jsonEsc n ++ "\":" ++ kValJson v) :: kNamedValsJson xs
end

def kResultJson : ISAR.KResult → String
  | ⟨none, none⟩ => "{\"void\":true}"
  | ⟨none, some v⟩ => "{\"bare\":" ++ kValJson v ++ "}"
  | ⟨some b, none⟩ => "{\"tag\":\"" ++ jsonEsc b ++ "\"}"
  | ⟨some b, some v⟩ =>
      "{\"tag\":\"" ++ jsonEsc b ++ "\",\"payload\":" ++ kValJson v ++ "}"

def kExpectJson : Option ISAR.KResult → String
  | none => "\"refuse\""
  | some r => kResultJson r

def kArgsJson (args : List (String × ISAR.KVal)) : String :=
  "{" ++ String.intercalate ","
    (args.map fun (n, v) => "\"" ++ jsonEsc n ++ "\":" ++ kValJson v) ++ "}"

def kEmitJson (p : ISAR.KProg) : String :=
  match ISAR.emitC99 p with
  | some s => "\"" ++ jsonEsc s ++ "\""
  | none => "\"refuse\""

/-- One oracle leaf — asserted-call row `(name,args) → result`. -/
def kLeafJson (leaf : (String × List (String × ISAR.KVal)) × ISAR.KResult)
    : String :=
  "{\"name\":\"" ++ jsonEsc leaf.1.1
    ++ "\",\"args\":" ++ kArgsJson leaf.1.2
    ++ ",\"result\":" ++ kResultJson leaf.2 ++ "}"

def kOracleJson (o : ISAR.KOracle) : String :=
  "[" ++ String.intercalate "," (o.map kLeafJson) ++ "]"

/-- The spec row for one corpus member. `expect` is the kernel's own
decided result under the row's oracle — the claim asserts what `runK`
decides, never a hoped value (case-forged's row is hand-asserted
instead). -/
def caseRow (fuel : Nat) (p : ISAR.KProg) (o : ISAR.KOracle := [])
    (extra : String := "") : String :=
  "{\"entry\":\"" ++ jsonEsc p.entry ++ "\",\"fuel\":" ++ toString fuel
    ++ ",\"args\":" ++ kArgsJson p.args
    ++ (if o.isEmpty then "" else ",\"oracle\":" ++ kOracleJson o)
    ++ ",\"expect\":" ++ kExpectJson (ISAR.evalKProg p o fuel)
    ++ ",\"emit\":" ++ kEmitJson p ++ extra ++ "}"

/-- `i` zero-padded to 3 digits — the `NNN` of the leaf convention. -/
def pad3 (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

/-- Write one leaf folder: `input.k` (surface rows) + `cases.json`
carrying exactly one row keyed by the leaf's bare name.  A wire leaf
passes `file := false` — the row carries the generated `claim`
instead and no surface file is written. -/
def writeLeaf (group leaf row : String) (src : Option String)
    : IO Unit := do
  let dir := "host2/specs/tests/" ++ group ++ "/" ++ leaf
  IO.FS.createDirAll dir
  match src with
  | some s => IO.FS.writeFile (dir ++ "/input.k") s
  | none => pure ()
  IO.FS.writeFile (dir ++ "/cases.json")
    ("{\"cases\":{\"" ++ leaf ++ "\":" ++ row ++ "}}\n")

def main : IO Unit := do
  let fuel := 64
  -- 200_emit — the emission-fixpoint corpus: accept + every refusal
  -- shape kEmit owns, each as a named leaf
  let emitNames := ["accept_int", "accept_neg", "refuse_entry",
    "refuse_args", "refuse_graph", "refuse_expr", "refuse_float",
    "refuse_thunk"]
  for (p, i) in ISAR.koruEmitCorpus.zipIdx do
    let leaf := pad3 i ++ "_" ++ emitNames.getD i "unnamed"
    writeLeaf "200_emit" leaf
      (caseRow fuel p [] ",\"file\":\"input.k\"")
      (some (kProgSrc leaf p))
  -- 100_flow — the flow-grammar corpus: every arm/dispatch shape the
  -- subset spells, oracle leaves riding the row.  Wire-only rows
  -- (no surface spelling) land in 900_wire with their own sequence.
  let mut fi := 0
  let mut wi := 0
  for (key, r) in ISAR.koruFlowCorpus do
    let base := (key.drop 5).toString.map fun c =>
      if c == '-' then '_' else c
    if r.wire then
      let leaf := pad3 wi ++ "_" ++ base
      wi := wi + 1
      writeLeaf "900_wire" leaf
        (caseRow fuel r.prog r.oracle
          (",\"claim\":\"" ++ jsonEsc
            (claimSxO r.prog fuel (ISAR.evalKProg r.prog r.oracle fuel)
              r.oracle) ++ "\""))
        none
    else
      let leaf := pad3 fi ++ "_" ++ base
      fi := fi + 1
      writeLeaf "100_flow" leaf
        (caseRow fuel r.prog r.oracle ",\"file\":\"input.k\"")
        (some (kProgSrc leaf r.prog r.decls))
  -- kemit: the compiler as a koru program — emit_prog marks the row
  -- as the emitter, not an emission target
  writeLeaf "200_emit" "100_kemit"
    ("{\"entry\":\"emit\",\"fuel\":" ++ toString fuel
      ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
      ++ ",\"file\":\"input.k\",\"emit_prog\":true}")
    (some kemitFile)
  -- 800_forged — an asserted-wrong expectation over a deciding
  -- program: krun must DRIFT, proving claims are re-decided
  let forged : ISAR.KProg := ⟨[("main", .bare (.lit (.int 5)))], "main", []⟩
  writeLeaf "800_forged" "000_wrong_expect"
    ("{\"entry\":\"main\",\"fuel\":" ++ toString fuel ++ ",\"args\":{}"
      ++ ",\"expect\":{\"bare\":{\"int\":6}},\"emit\":\"refuse\""
      ++ ",\"file\":\"input.k\",\"forged\":true}")
    (some (kProgSrc "000_wrong_expect" forged))
