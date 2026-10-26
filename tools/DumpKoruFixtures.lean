import ISAR.KoruEmit

/-!
# DumpKoruFixtures — the Lean→host2 data crossing

Writes the host2 corpus as `.k` files in the verification-lane claim
format — the `[flow-eval]` s-expression wire that `w:/src/koru`'s
golden corpus and `FlowCheck.lean` declare:

    lake env lean --run tools/DumpKoruFixtures.lean

writes `host2/specs/corpus/case-*.k`, `kemit.k`, `case-forged.k`.

    [flow-eval] ((entry NAME (ARGV*)) (fuel N) (result R)
                 (graph DECL*) (oracle LEAF*))

These writers are the emit half of that format; the decoders are
FlowCheck (Lean, koru repo) and `host2/src/krun.c` (C, this repo).
The corpus files are GENERATED from `koruEmitCorpus` — one source of
truth, no drift.  Each file's expected emit text rides as a
`# emit:` comment — non-claim lines are inert to claim readers
(golden.txt discipline), so the marker is metadata the gate greps.

The kernel's *decided* result is embedded in the claim: `krun` does
not get to refuse a decidable claim, and a `refuse` claim must
actually refuse.  `case-forged.k` claims a wrong result — the C
checker must DRIFT it.
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
  | { branch := none, payload := none } => "(void)"
  | { branch := none, payload := some v } => "(bare " ++ sxVal v ++ ")"
  | { branch := some b, payload := none } => "(tag " ++ sxName b ++ ")"
  | { branch := some b, payload := some v } => "(tag " ++ sxName b ++ " " ++ sxVal v ++ ")"

def sxExpected : Option ISAR.KResult → String
  | none => "refuse" | some r => sxResult r

def sxArgs (args : List (String × ISAR.KVal)) : String :=
  String.intercalate "" (args.map fun (n, v) => " (" ++ sxName n ++ " " ++ sxVal v ++ ")")

/-- The `[flow-eval]` claim line for a program — graph, entry call,
fuel, decided result, empty oracle. -/
def claimSx (p : ISAR.KProg) (fuel : Nat) (expected : Option ISAR.KResult) : String :=
  "[flow-eval] ((entry " ++ sxName p.entry ++ sxArgs p.args
    ++ ") (fuel " ++ toString fuel
    ++ ") (result " ++ sxExpected expected
    ++ ") (graph" ++ sxDecls p.graph
    ++ ") (oracle))"

/-- A corpus `.k` file: comment header + emit expectation marker +
the claim line. `#` lines are inert to claim readers. -/
def corpusFile (name : String) (p : ISAR.KProg) (fuel : Nat) : String :=
  let emitLine := match ISAR.emitC99 p with
    | some s => "# emit: " ++ s
    | none => "# emit: refuse"
  "# " ++ name ++ " — generated by tools/DumpKoruFixtures.lean, do not edit\n"
    ++ emitLine ++ "\n" ++ claimSx p fuel (ISAR.evalKProg p [] fuel) ++ "\n"

/-- The compiler program's own file: arg-less `emit` refuses (var src
unbound) — the claim `(result refuse)` is what `krun kemit.k` must
reproduce. -/
def kemitFile (fuel : Nat) : String :=
  "# kemit.k — the C99 compiler as a koru program (generated)\n"
    ++ "# arg-less invoke refuses: `src` is unbound; the emit leg\n"
    ++ "# supplies it via --emit (quote of the source program)\n"
    ++ "# emit: refuse\n"
    ++ claimSx ISAR.kEmit fuel (ISAR.evalKProg ISAR.kEmit [] fuel) ++ "\n"

def main : IO Unit := do
  let fuel := 64
  let dir := "host2/specs/corpus"
  for (p, i) in ISAR.koruEmitCorpus.zipIdx do
    IO.FS.writeFile (dir ++ "/case-" ++ toString i ++ ".k")
      (corpusFile ("case-" ++ toString i) p fuel)
  IO.FS.writeFile (dir ++ "/kemit.k") (kemitFile fuel)
  -- a forged claim: case-0's graph claiming result 6 (decides 5) —
  -- the C checker must DRIFT it, proving claims are re-decided
  let forged : ISAR.KProg := ⟨[("main", .bare (.lit (.int 5)))], "main", []⟩
  IO.FS.writeFile (dir ++ "/case-forged.k")
    ("# case-forged — claims result 6, program decides 5; must DRIFT\n"
      ++ "# emit: refuse\n"
      ++ claimSx forged fuel (some ⟨none, some (.int 6)⟩) ++ "\n")
