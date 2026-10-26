import ISAR.KoruEmit

/-!
# DumpKoruFixtures — the Lean→host2 data crossing

Writes the host2 corpus as **real koru source** `.k` files plus a
`cases.json` spec file:

    lake env lean --run tools/DumpKoruFixtures.lean

writes `host2/specs/corpus/case-*.k`, `kemit.k`, `case-forged.k` —
authored-syntax files in koru's own surface (`tor`, `->`, `=`, `|`),
and `host2/specs/cases.json` carrying the per-case spec rows:
entry call, fuel, expected result, expected emit text, oracle.

The `.k` files are GENERATED from `koruEmitCorpus` — one source of
truth, no drift.  They are parsed by `host2/src/korufe.c` into the
canonical `program.ast.json` shape and lowered by the same tool into
`[flow-eval]` claims — the s-expression wire is the *lower* layer,
never the authored surface.  `cases.json` rows are the spec: the gate
joins file ↔ ast ↔ claim ↔ decided result ↔ emitted C ↔ runtime.

`case-forged.k` has its spec row claim result 6 where the program
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
      sxName n ++ "(" ++ String.intercalate ", " (kExprsSrc args) ++ ")"

def kExprsSrc : List ISAR.KExpr → List String
  | [] => [] | x :: xs => kExprSrc x :: kExprsSrc xs
end

def kNamedExprsSrc (args : List (String × ISAR.KExpr)) : String :=
  String.intercalate ", " (go args) where
  go : List (String × ISAR.KExpr) → List String
    | [] => []
    | (n, e) :: xs => (sxName n ++ ": " ++ kExprSrc e) :: go xs

def kArmSrc (a : ISAR.KArm) : String :=
  let head := if a.catchall then "*"
    else if a.branch == "" then
      panic! "bare-dispatch arm has no koru surface in the subset"
    else sxName a.branch
  let bindf := match a.bind with
    | none => ""
    | some b => " " ++ sxName b
  let whenf := match a.cond with
    | none => ""
    | some e => " when(" ++ kExprSrc e ++ ")"
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
  | [] => head ++ bindf ++ whenf ++ nodef

def kFlowSrc (f : ISAR.KFlow) : String :=
  (match f.preLabel with | none => "" | some l => "#" ++ sxName l ++ " ")
    ++ sxName f.head.1 ++ "(" ++ kNamedExprsSrc f.head.2 ++ ")"
    ++ String.intercalate "" (f.arms.map fun a => "\n| " ++ kArmSrc a)

/-- Field declarations for a `tor` — value-typed from entry args.
`arr`/`cell` args have no koru spelling in the subset; panic. -/
def kArgTy : ISAR.KVal → String
  | .int _ => "i64" | .float _ _ => "f64" | .bool _ => "bool"
  | .str _ => "string"
  | .arr _ => panic! "arr arg type has no koru spelling in the subset"
  | .cell _ => panic! "cell arg type has no koru spelling in the subset"

def kDeclFields (args : List (String × ISAR.KVal)) : String :=
  "{" ++ String.intercalate ", "
    (args.map fun (n, v) => sxName n ++ ": " ++ kArgTy v) ++ "}"

/-- Return annotation for literal bare impls — honest koru where the
type is statically obvious; omitted otherwise (koru infers). -/
def kRetTy : ISAR.KExpr → String
  | .lit (.int _) => " -> i64"
  | .lit (.float _ _) => " -> f64"
  | .lit (.bool _) => " -> bool"
  | .lit (.str _) => " -> string"
  | _ => ""

/-- A `tor` declaration plus its impl, for one graph entry.  The
entry's arg types come from the program's `args` field; other
callables declare `{}` — wire signatures are untyped, the fields are
descriptive surface. -/
def kCallableSrc (name : String) (args : List (String × ISAR.KVal))
    : ISAR.KCallable → String
  | .bare e =>
      "tor " ++ sxName name ++ " " ++ kDeclFields args ++ kRetTy e
        ++ "\n" ++ sxName name ++ " -> " ++ kExprSrc e
  | .thunk => "tor " ++ sxName name ++ " " ++ kDeclFields args
  | .subflow f =>
      "tor " ++ sxName name ++ " " ++ kDeclFields args
        ++ "\n" ++ sxName name ++ " = " ++ kFlowSrc f

/-- A whole corpus `.k` file: `tor` decls + impls in graph order.
Entry callables get arg fields from `p.args`; others declare `{}`. -/
def kProgSrc (name : String) (p : ISAR.KProg) : String :=
  "// " ++ name ++ " — generated by tools/DumpKoruFixtures.lean, do not edit\n"
    ++ String.intercalate "\n\n" (p.graph.map fun (n, c) =>
        kCallableSrc n (if n == p.entry then p.args else []) c)
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

def kExpectJson : Option ISAR.KResult → String
  | none => "\"refuse\""
  | some ⟨none, none⟩ => "{\"void\":true}"
  | some ⟨none, some v⟩ => "{\"bare\":" ++ kValJson v ++ "}"
  | some ⟨some b, none⟩ => "{\"tag\":\"" ++ jsonEsc b ++ "\"}"
  | some ⟨some b, some v⟩ =>
      "{\"tag\":\"" ++ jsonEsc b ++ "\",\"payload\":" ++ kValJson v ++ "}"

def kArgsJson (args : List (String × ISAR.KVal)) : String :=
  "{" ++ String.intercalate ","
    (args.map fun (n, v) => "\"" ++ jsonEsc n ++ "\":" ++ kValJson v) ++ "}"

def kEmitJson (p : ISAR.KProg) : String :=
  match ISAR.emitC99 p with
  | some s => "\"" ++ jsonEsc s ++ "\""
  | none => "\"refuse\""

/-- The spec row for one corpus member. `expect` is the kernel's own
decided result — the claim asserts what `runK` decides, never a hoped
value (case-forged's row is hand-asserted instead). -/
def caseRow (fuel : Nat) (p : ISAR.KProg) (extra : String := "") : String :=
  "{\"entry\":\"" ++ jsonEsc p.entry ++ "\",\"fuel\":" ++ toString fuel
    ++ ",\"args\":" ++ kArgsJson p.args
    ++ ",\"expect\":" ++ kExpectJson (ISAR.evalKProg p [] fuel)
    ++ ",\"emit\":" ++ kEmitJson p ++ extra ++ "}"

def main : IO Unit := do
  let fuel := 64
  let dir := "host2/specs/corpus"
  let mut rows : List String := []
  for (p, i) in ISAR.koruEmitCorpus.zipIdx do
    let key := "case-" ++ toString i
    IO.FS.writeFile (dir ++ "/" ++ key ++ ".k") (kProgSrc key p)
    rows := rows ++ ["\"" ++ key ++ "\":" ++ caseRow fuel p
      (",\"file\":\"" ++ key ++ ".k\"")]
  IO.FS.writeFile (dir ++ "/kemit.k") kemitFile
  -- kemit's own row: entry emit, no args → `src` unbound → refuse;
  -- emit_prog marks it as the emitter, not an emission target
  rows := rows ++ ["\"kemit\":{\"entry\":\"emit\",\"fuel\":" ++ toString fuel
    ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
    ++ ",\"file\":\"kemit.k\",\"emit_prog\":true}"]
  -- the forged case: case-0's program with an asserted-wrong result —
  -- krun must DRIFT, proving claims are re-decided
  let forged : ISAR.KProg := ⟨[("main", .bare (.lit (.int 5)))], "main", []⟩
  IO.FS.writeFile (dir ++ "/case-forged.k") (kProgSrc "case-forged" forged)
  rows := rows ++ ["\"case-forged\":{\"entry\":\"main\",\"fuel\":"
    ++ toString fuel ++ ",\"args\":{}"
    ++ ",\"expect\":{\"bare\":{\"int\":6}},\"emit\":\"refuse\""
    ++ ",\"file\":\"case-forged.k\",\"forged\":true}"]
  IO.FS.writeFile "host2/specs/cases.json"
    ("{\"cases\":{" ++ String.intercalate "," rows ++ "}}\n")
