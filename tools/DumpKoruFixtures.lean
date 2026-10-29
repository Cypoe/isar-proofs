import ISAR.KoruProgEmit

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

/-- Koru string literal escaping — the inverse of the upstream
decode set (the AST keeps the raw token, the VALUE decodes `\"`→`"`,
`\\`→`\`, `\n`/`\t`/`\r`→controls, unknown keeps both bytes): every
value byte gets its decoding spelling.  The same set serves wire
`(str …)` atoms — krun's `sx` reader decodes the identical escapes. -/
def koruStrEsc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n"
    else if c == '\t' then "\\t"
    else if c == '\r' then "\\r"
    else if c.toNat < 0x20 then "\\u00" ++
      (let h := String.ofList (Nat.toDigits 16 c.toNat)
       "".pushn '0' (2 - h.length) ++ h)
    else c.toString)

def sxStrLit (s : String) : String := "\"" ++ koruStrEsc s ++ "\""

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
  | .int i =>
      -- koru has no negative-literal spelling: `-` is always unary
      -- `negate`.  An `int (-k)` in EXPR position is unspellable —
      -- panic (the corpus row must spell `.un .neg` or ride a wire
      -- leaf) rather than emit `-k` which parses back as `negate k`.
      if i < 0
      then panic! "negative int literal has no koru surface — spell .un .neg"
      else toString i
  | .float n d =>
      if n < 0
      then panic! "negative float literal has no koru surface — spell .un .neg"
      else (ratDecimal n d).get!
  | .bool b => if b then "true" else "false"
  | .str s => "\"" ++ koruStrEsc s ++ "\""
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
      -- `if … else` is greedier than any binary op (`else x`
      -- swallows a trailing `a ++ b`), so a `.cond` operand must
      -- carry its own parens.
      let wrap (x : ISAR.KExpr) (s : String) : String :=
        match x with | .cond _ _ _ => "(" ++ s ++ ")" | _ => s
      "(" ++ wrap a (kExprSrc a) ++ " " ++ binSym op
        ++ " " ++ wrap b (kExprSrc b) ++ ")"
  | .un .neg e => "-(" ++ kExprSrc e ++ ")"
  | .un .not e => "!(" ++ kExprSrc e ++ ")"
  | .cond c t e =>
      -- the then-branch gets the same guard: `if c if … else …`
      -- has no surface reading
      let wrap (x : ISAR.KExpr) (s : String) : String :=
        match x with | .cond _ _ _ => "(" ++ s ++ ")" | _ => s
      "if(" ++ kExprSrc c ++ ") " ++ wrap t (kExprSrc t)
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

/-- Chain-step printing: `conts` under an invoke arm spell koru's
`|>` sequence — each cont is a `_chain`-named arm whose `bind` is
the previous step's retbind (`f(): b` — koru puts the `: b` on the
invocation, the wire carries it on the next arm). Linear only: a
branching cont list, a non-invoke step, or a guarded/tagged step
has no surface — panic, don't guess. -/
def kContsSrc : List ISAR.KArm → String
  | [] => ""
  | [.mk _b ca bind cond node conts] =>
      let bindf := match bind with
        | none => ""
        | some b => " : " ++ sxName b
      let stepf := match node with
        | some (.invoke t args) =>
            " |> " ++ sxName t ++ "(" ++ kNamedExprsSrc args ++ ")"
        | _ => panic! "koru chain step must invoke a callable"
      (if ca || cond.isSome then
        panic! "tagged/guarded chain step has no koru surface"
       else "") ++ bindf ++ stepf ++ kContsSrc conts
  | _ => panic! "branching cont list has no koru surface — wire row"
termination_by l => sizeOf l
decreasing_by
  all_goals (simp_wf <;> omega)

mutual
/-- Free-var check for the `_` discard the authority demands on
unreferenced arm bindings (KORU100).  Cont arms get a fresh env —
only the guard and node can see the bind. -/
def kExprUsesVar (x : String) : ISAR.KExpr → Bool
  | .lit _ => false
  | .var n => n == x
  | .bin _ a b => kExprUsesVar x a || kExprUsesVar x b
  | .un _ e => kExprUsesVar x e
  | .cond c t e => kExprUsesVar x c || kExprUsesVar x t
                   || kExprUsesVar x e
  | .field o _ => kExprUsesVar x o
  | .index o i => kExprUsesVar x o || kExprUsesVar x i
  | .builtin _ args => kExprArgsUseVar x args

def kExprArgsUseVar (x : String) : List ISAR.KExpr → Bool
  | [] => false
  | e :: es => kExprUsesVar x e || kExprArgsUseVar x es
end

def kArmNodeUsesVar (x : String) : ISAR.KArmNode → Bool
  | .terminal => false
  | .jump _ args => args.any (fun (_, e) => kExprUsesVar x e)
  | .invoke _ args => args.any (fun (_, e) => kExprUsesVar x e)
  | .produce e => kExprUsesVar x e
  | .retCtor _ e => kExprUsesVar x e

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
    | some b =>
        let used :=
          (a.cond.map (kExprUsesVar b)).getD false
          || (a.node.map (kArmNodeUsesVar b)).getD false
        " " ++ (if used then sxName b else "_")
  let whenf := match a.cond with
    | none => ""
    | some e => " when " ++ kGuardSrc e
  let nodef := match a.node with
    | none =>
        (if a.conts.isEmpty then ""
         else panic! "conts under a bare arm have no koru surface")
    | some .terminal =>
        (if a.conts.isEmpty then ""
         else panic! "conts under a terminal arm have no koru surface")
    | some (.produce e) =>
        (if a.conts.isEmpty then ""
         else panic! "conts under a produce arm have no koru surface")
        ++ " -> " ++ kExprSrc e
    | some (.retCtor c e) =>
        (if a.conts.isEmpty then ""
         else panic! "conts under a ctor arm have no koru surface")
        ++ match e with
          | .lit (.cell []) => " => " ++ sxName c
          | _ => " => " ++ sxName c ++ " " ++ kExprSrc e
    | some (.invoke t args) =>
        " |> " ++ sxName t ++ "(" ++ kNamedExprsSrc args ++ ")"
          ++ kContsSrc a.conts
    | some (.jump l args) =>
        (if a.conts.isEmpty then ""
         else panic! "conts under a jump arm have no koru surface")
        ++ " |> @" ++ sxName l ++ "(" ++ kNamedExprsSrc args ++ ")"
  (if a.catchall then "|*" else "| ") ++ head ++ bindf ++ whenf ++ nodef

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

/-- The `-> ty` annotation on a `tor` line — the declared return,
or the literal-inferred one for bare impls when none is declared. -/
def kRetAnn (d : ISAR.KDecl) (e : ISAR.KExpr) : String :=
  match d.ret with
  | some t => " -> " ++ t
  | none => kRetTy e

/-- A `tor` declaration plus its impl, for one graph entry.  Params
and branch rows come from the resolved `KDecl` — the contract real
koru checks at PARSE006/KORU021.  `declared := false` emits no `tor`
line — a legal implicit decl (impl/callable only). -/
def kCallableSrc (name : String) (d : ISAR.KDecl)
    : ISAR.KCallable → String
  | .bare e =>
      (if d.declared then
        "tor " ++ sxName name ++ " " ++ kDeclFieldsT d.params
          ++ kRetAnn d e ++ kBranchesSrc d.branches ++ "\n" else "")
        ++ sxName name ++ " -> " ++ kExprSrc e
  | .thunk =>
      if d.declared then
        "tor " ++ sxName name ++ " " ++ kDeclFieldsT d.params
          ++ (d.ret.map (" -> " ++ ·)).getD ""
          ++ kBranchesSrc d.branches
      else ""
  | .subflow f =>
      (if d.declared then
        "tor " ++ sxName name ++ " " ++ kDeclFieldsT d.params
          ++ (d.ret.map (" -> " ++ ·)).getD ""
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

/-- `kemit.k`: the compiler program spelled in koru — a real
multi-callable program (`emit`'s gate → `render`'s recursive walk →
assembler legs), not a bare-expr stub.  `emit` takes a quoted
program `src` — declared `program`-typed; arg-less invoke refuses
(`src` unbound), the emit leg supplies it via `--emit`. -/
def kemitFile : String :=
  "// kemit.k — the C99 compiler as a koru program (generated)\n"
    ++ "// arg-less invoke refuses: `src` unbound; the emit leg\n"
    ++ "// supplies it via --emit (quote of the source program)\n"
    ++ String.intercalate "\n\n" (ISAR.kEmit.graph.map fun (n, c) =>
        kCallableSrc n (ISAR.kEmitDecls.find? (·.1 == n)
          |>.map (·.2) |>.getD {}) c)
    ++ "\n"

/-- `klex.k`: the sexpr lexer spelled in koru — jump-loop scan over
`(arr int)` char codes, sexpr tokens as `out` text.  `chars` is
`[]const i64` — koru's own slice spelling, documentary in the
untyped subset. -/
def klexFile : String :=
  "// klex.k — a koru-spelled sexpr lexer over char codes (generated)\n"
    ++ "// chars arrives as (arr int) on the wire; the host does\n"
    ++ "// bytes->codes.  arg-less invoke refuses: `chars` unbound.\n"
    ++ String.intercalate "\n\n" (ISAR.kLex.graph.map fun (n, c) =>
        kCallableSrc n (ISAR.kLexDecls.find? (·.1 == n)
          |>.map (·.2) |>.getD {}) c)
    ++ "\n"

/-- `ksexp.k`: the sexpr parser spelled in koru — explicit-stack
scan over `(arr int)` char codes, span-tagged tree as `out` text. -/
def ksexpFile : String :=
  "// ksexp.k — a koru-spelled sexpr parser over char codes (generated)\n"
    ++ "// explicit-stack parse: depth is the stack register;\n"
    ++ "// nodes print as (kind start end) spans — no chr/slice.\n"
    ++ "// arg-less invoke refuses: `chars` unbound.\n"
    ++ String.intercalate "\n\n" (ISAR.kSexp.graph.map fun (n, c) =>
        kCallableSrc n (ISAR.kSexpDecls.find? (·.1 == n)
          |>.map (·.2) |>.getD {}) c)
    ++ "\n"

/-- `kast.k`: the koru surface parser spelled in koru — explicit
rule-chain state machine over `(arr int)` char codes; flat
`(kind span…)` rows as `out` text, raced against `koruc
--ast-json` in the gate. -/
def kastFile : String :=
  "// kast.k — a koru-spelled surface parser → flat AST rows (generated)\n"
    ++ "// item-level grammar: import/tor/impl/flow + arm bars;\n"
    ++ "// names, types, exprs ride source spans — the authority's\n"
    ++ "// own ast keeps them as text too.  arg-less invoke\n"
    ++ "// refuses: `chars` unbound.\n"
    ++ String.intercalate "\n\n" (ISAR.kAst.graph.map fun (n, c) =>
        kCallableSrc n (ISAR.kAstDecls.find? (·.1 == n)
          |>.map (·.2) |>.getD {}) c)
    ++ "\n"

/-- `klow.k`: the koru-spelled reifier — flat six-int rows + the
source byte array → the `program.ast.json` document as a string.
Mirrors `reify.c`'s state machine and `write_ast_json`'s shape;
the gate races parsed-JSON equality against `korufe --reify`.
arg-less invoke refuses: `src`/`rows`/`mod` unbound. -/
def klowFile : String :=
  "// klow.k — a koru-spelled reifier → program.ast.json (generated)\n"
    ++ "// flat six-int rows + source bytes in; escaped JSON text\n"
    ++ "// out (span bytes as \\u00xx).  arg-less invoke refuses:\n"
    ++ "// `src`/`rows`/`mod` unbound.\n"
    ++ String.intercalate "\n\n" (ISAR.kLow.graph.map fun (n, c) =>
        kCallableSrc n (ISAR.kLowDecls.find? (·.1 == n)
          |>.map (·.2) |>.getD {}) c)
    ++ "\n"

/-- A test input as the wire value: chars → `(arr int)` codes. -/
def klexChars (s : String) : ISAR.KVal :=
  .arr (s.toList.map fun c => .int (Int.ofNat c.toNat))

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

/-- A leaf whose cases.json carries several rows — the klex leaf:
one `emit_prog` program row plus per-input rows over the same
`input.k`. -/
def writeLeafRows (group leaf : String) (rows : List (String × String))
    (src : Option String) : IO Unit := do
  let dir := "host2/specs/tests/" ++ group ++ "/" ++ leaf
  IO.FS.createDirAll dir
  match src with
  | some s => IO.FS.writeFile (dir ++ "/input.k") s
  | none => pure ()
  IO.FS.writeFile (dir ++ "/cases.json")
    ("{\"cases\":{" ++ String.intercalate ","
      (rows.map fun (n, r) => "\"" ++ n ++ "\":" ++ r) ++ "}}\n")

/-- FNV-1a-64 over UTF-8 — the generated-artifact freshness stamp.
Not crypto; a content hash is enough to catch `kemit.c` drifting
from `input.k` when someone regenerates one side only. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3)
    0xcbf29ce484222325

def main : IO Unit := do
  let fuel := 64
  -- 200_emit — the emission-fixpoint corpus: accepts across the
  -- expr subset + every refusal shape kEmit owns, each a named leaf
  let emitNames := ["accept_int", "emit_neg_lit", "accept_bin",
    "accept_nested", "accept_div", "accept_mod", "accept_uneg",
    "accept_unested",
    -- H2 changed input: boundary + trunc-division witnesses
    "accept_intmax", "accept_mixops", "accept_deep",
    "accept_negdiv", "accept_negmod", "accept_negnest",
    "refuse_entry", "refuse_args", "refuse_graph",
    "refuse_var", "refuse_op", "refuse_unop", "refuse_cond",
    "refuse_child", "refuse_float", "refuse_str", "refuse_thunk",
    "refuse_bool", "refuse_arrlit", "refuse_celllit",
    "refuse_field", "refuse_index", "refuse_builtin"]
  let mut wi := 0
  for (p, i) in ISAR.koruEmitCorpus.zipIdx do
    if i == 1 then
      -- `.lit (.int (-3))`: koru has no negative-literal spelling —
      -- the member stays in the fixpoint corpus but rides a wire
      -- leaf (claim declared, no surface file).
      let leaf := pad3 wi ++ "_emit_neg_lit"
      wi := wi + 1
      writeLeaf "900_wire" leaf
        (caseRow fuel p [] (",\"claim\":\"" ++ jsonEsc
          (claimSxO p fuel (ISAR.evalKProg p [] fuel) []) ++ "\""))
        none
    else
      let leaf := pad3 i ++ "_" ++ emitNames.getD i "unnamed"
      writeLeaf "200_emit" leaf
        (caseRow fuel p [] ",\"file\":\"input.k\"")
        (some (kProgSrc leaf p))
  -- 100_flow — the flow-grammar corpus: every arm/dispatch shape the
  -- subset spells, oracle leaves riding the row.  Wire-only rows
  -- (no surface spelling) land in 900_wire with their own sequence.
  let mut fi := 0
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
  -- as the emitter, not an emission target.  Fuel sized for the
  -- recursive render walk the --emit leg drives.
  writeLeaf "200_emit" "900_kemit"
    ("{\"entry\":\"emit\",\"fuel\":1024"
      ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
      ++ ",\"file\":\"input.k\",\"emit_prog\":true}")
    (some kemitFile)
  -- klex: the lexer as a koru program — the emit_prog row marks
  -- the program for gen/klex.c; sibling rows are the inputs the
  -- compiled artifact re-decides via `krun --args` cells.  Fuel
  -- sized for the per-char scan loop over the longest input.
  writeLeafRows "200_emit" "901_klex"
    ([("901_klex",
       "{\"entry\":\"main\",\"fuel\":512"
       ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
       ++ ",\"file\":\"input.k\",\"emit_prog\":true"
       ++ ",\"emit_args\":true,\"gen\":\"klex\"}")]
     ++ ([("(1 + 22)", "paren"), ("main", "atom"),
          ("(flow-eval)", "flowkw"), ("x$", "bad"), ("", "empty"),
          ("42", "num"), ("(1 + 22) main", "mix")].map fun (s, tag) =>
        ("901_klex_" ++ tag,
         caseRow 512
           { ISAR.kLex with
             args := [("chars", klexChars s)] }
           [] ",\"file\":\"input.k\"")))
    (some klexFile)
  -- ksexp: the sexpr parser as a koru program — same emit_args wire
  -- as klex, structural rows: nesting, ws-normalization, spans, and
  -- the four structural refusal shapes.  `gen` names the artifact.
  writeLeafRows "200_emit" "902_ksexp"
    ([("902_ksexp",
       "{\"entry\":\"main\",\"fuel\":1024"
       ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
       ++ ",\"file\":\"input.k\",\"emit_prog\":true"
       ++ ",\"emit_args\":true,\"gen\":\"ksexp\"}")]
     ++ ([("(a b c)", "list"), ("(a (b c) d)", "nest"),
          ("  ( 1 + 22 )", "ws"), ("((x))", "deep"),
          ("(a b", "unclosed"), ("(a) (b)", "twofold"),
          ("x", "toplevel"), (")", "underflow")].map fun (s, tag) =>
        ("902_ksexp_" ++ tag,
         caseRow 1024
           { ISAR.kSexp with
             args := [("chars", klexChars s)] }
           [] ",\"file\":\"input.k\"")))
    (some ksexpFile)
  -- kast: the surface parser as a koru program — real koru
  -- sources in as `(arr int)` args, flat `(kind span…)` rows out.
  -- `src` carries the same text the chars encode so the gate can
  -- hand it to `koruc --ast-json` and race the normalized
  -- authority AST against the decided row text.
  writeLeafRows "200_emit" "903_kast"
    ([("903_kast",
       "{\"entry\":\"main\",\"fuel\":8192"
       ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
       ++ ",\"file\":\"input.k\",\"emit_prog\":true"
       ++ ",\"emit_args\":true,\"gen\":\"kast\"}")]
     ++ ([("tor sign {x: i64} -> bool\nsign -> (x < 0)\n", "decl"),
          ("tor tick {i: i64}\n| next i64\n| stop\n\ntor count {i: i64}\ncount = #loop tick(i)\n| next i when 0 < i |> @loop(i: (i - 1))\n| next i -> i\n",
           "flow"),
          ("tor classify {x: i64}\n| pos i64\n| neg i64\nclassify = sign(x)\n| ok p when p => pos x\n| ok _ => neg x\n",
           "ctor"),
          ("import std/compiler\ntor main {}\nmain -> 1\n", "imp"),
          ("tor main {}\nmain = tick()\n| go\n\ntor tick {}\n| go i64\n| stop\n",
           "term"),
          ("", "empty"),
          ("tor broken {\n", "bad")].map fun (s, tag) =>
        ("903_kast_" ++ tag,
         caseRow 8192
           { ISAR.kAst with
             args := [("chars", klexChars s)] }
           [] (",\"file\":\"input.k\",\"src\":\""
             ++ jsonEsc s ++ "\",\"race\":true"))))
    (some kastFile)
  -- 904_klow — the koru-spelled reifier: flat six-int rows + the
  -- source bytes -> the ast.json document as an escaped string.
  -- The leaf carries only the emit_prog row: per-input rows+src are
  -- derived at check time from the kast binary's own wire (the kl
  -- leg), so no second hand-encoded row set can drift from it.
  writeLeaf "200_emit" "904_klow"
    ("{\"entry\":\"main\",\"fuel\":4000000"
      ++ ",\"args\":{},\"expect\":\"refuse\",\"emit\":\"refuse\""
      ++ ",\"file\":\"input.k\",\"emit_prog\":true"
      ++ ",\"emit_args\":true,\"gen\":\"klow\"}")
    (some klowFile)
  -- 800_forged — an asserted-wrong expectation over a deciding
  -- program: krun must DRIFT, proving claims are re-decided
  let forged : ISAR.KProg := ⟨[("main", .bare (.lit (.int 5)))], "main", []⟩
  writeLeaf "800_forged" "000_wrong_expect"
    ("{\"entry\":\"main\",\"fuel\":" ++ toString fuel ++ ",\"args\":{}"
      ++ ",\"expect\":{\"bare\":{\"int\":6}},\"emit\":\"refuse\""
      ++ ",\"file\":\"input.k\",\"forged\":true}")
    (some (kProgSrc "000_wrong_expect" forged))
  -- specs/gen — the compiler as COMPILED CODE: emitProgC lowers the
  -- whole kEmit program (callables, dispatch, chains, exprs) to C99
  -- plus the declared runtime prelude.  The gate compiles it through
  -- clang AND the CompCert row and runs it on every corpus quote —
  -- the H1 leg: a koru-spelled compiler executing as an artifact.
  match ISAR.emitProgC ISAR.kEmit 1024 with
  | .ok c =>
      IO.FS.createDirAll "host2/specs/gen"
      -- stamp binds the artifact to its input: `input.fnv1a64` of the
      -- 900_kemit/input.k text this run wrote — check.py's gen.stamp
      -- leg fails if either side was regenerated without the other
      IO.FS.writeFile "host2/specs/gen/kemit.c"
        ("/* input.fnv1a64:" ++ toString (fnv1a64 kemitFile)
          ++ " */\n" ++ c)
  | .error ax => throw (IO.userError s!"emitProgC refused: {ax}")
  -- klex.c — the lexer as compiled code: emitProgC lowers kLex's
  -- callables (jump loops, ordered dispatch, invoke tails) to C99.
  -- Same stamp contract as kemit.c.
  match ISAR.emitProgC ISAR.kLex 1024 with
  | .ok c =>
      IO.FS.createDirAll "host2/specs/gen"
      IO.FS.writeFile "host2/specs/gen/klex.c"
        ("/* input.fnv1a64:" ++ toString (fnv1a64 klexFile)
          ++ " */\n" ++ c)
  | .error ax => throw (IO.userError s!"emitProgC(kLex) refused: {ax}")
  -- ksexp.c — the parser as compiled code: the explicit-stack scan
  -- lowered by the same emitProgC path.  Same stamp contract.
  match ISAR.emitProgC ISAR.kSexp 1024 with
  | .ok c =>
      IO.FS.createDirAll "host2/specs/gen"
      IO.FS.writeFile "host2/specs/gen/ksexp.c"
        ("/* input.fnv1a64:" ++ toString (fnv1a64 ksexpFile)
          ++ " */\n" ++ c)
  | .error ax => throw (IO.userError s!"emitProgC(kSexp) refused: {ax}")
  -- kast.c — the surface parser as compiled code: the largest
  -- koru program lowered so far (76 callables: int scanners,
  -- rule chains, row emission).  Same stamp contract; fuel sized
  -- for the longest corpus source.
  match ISAR.emitProgC ISAR.kAst 8192 with
  | .ok c =>
      IO.FS.createDirAll "host2/specs/gen"
      IO.FS.writeFile "host2/specs/gen/kast.c"
        ("/* input.fnv1a64:" ++ toString (fnv1a64 kastFile)
          ++ " */\n" ++ c)
  | .error ax => throw (IO.userError s!"emitProgC(kAst) refused: {ax}")
  -- klow.c — the reifier as compiled code: emitProgC lowers kLow's
  -- 84 callables (byte scanners, escapers, the row state machine) to
  -- C99.  Same stamp contract; the kl leg races it against `korufe
  -- --reify` and the interpreted krun lane.
  match ISAR.emitProgC ISAR.kLow 8192 with
  | .ok c =>
      IO.FS.createDirAll "host2/specs/gen"
      IO.FS.writeFile "host2/specs/gen/klow.c"
        ("/* input.fnv1a64:" ++ toString (fnv1a64 klowFile)
          ++ " */\n" ++ c)
  | .error ax => throw (IO.userError s!"emitProgC(kLow) refused: {ax}")
