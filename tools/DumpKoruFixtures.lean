import ISAR.KoruEmit

/-!
# DumpKoruFixtures — the Lean→host2 data crossing

Prints the koru fixture file as JSON on stdout:

    lake env lean --run tools/DumpKoruFixtures.lean > host2/specs/koru-fixtures.json

The file is GENERATED — never hand-edit. It carries, for every member
of `koruEmitCorpus`: the program in the `.kv` wire form (one object per
grammar node: `{"<ctor>": payload}`), its quotation `quoteProg prog`,
`evalKProg`'s decision, `emitC99`'s output, and `kEmit`'s decision under
`runK`. `host2` must reproduce every field independently — that is the
witness discipline: data crosses, logic never does.

The `.kv` format is declared here (canonical writer) and in
`host2/kwire.py` (reader + validator).
-/

def jstr (s : String) : String :=
  let esc (c : Char) : String :=
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c => if c.toNat < 32
           then "\\u00" ++ String.singleton (Char.ofNat (48 + c.toNat / 16))
                  ++ String.singleton (Char.ofNat (48 + c.toNat % 16))
           else c.toString
  "\"" ++ String.intercalate "" (s.toList.map esc) ++ "\""

def jbool : Bool → String | true => "true" | false => "false"

def jlist (f : α → String) (xs : List α) : String :=
  "[" ++ String.intercalate "," (xs.map f) ++ "]"

def jopt (f : α → String) : Option α → String
  | none => "null" | some x => f x

def binopName : ISAR.KBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .and => "and" | .or => "or" | .concat => "concat"

def unopName : ISAR.KUnOp → String
  | .not => "not" | .neg => "neg"

mutual
def kvalJ : ISAR.KVal → String
  | .int i => "{\"int\":" ++ toString i ++ "}"
  | .float n d => "{\"float\":[" ++ toString n ++ "," ++ toString d ++ "]}"
  | .bool b => "{\"bool\":" ++ jbool b ++ "}"
  | .str s => "{\"str\":" ++ jstr s ++ "}"
  | .arr xs => "{\"arr\":[" ++ String.intercalate "," (kvalListJ xs) ++ "]}"
  | .cell fs => "{\"cell\":[" ++ String.intercalate "," (kcellListJ fs) ++ "]}"

def kvalListJ : List ISAR.KVal → List String
  | [] => []
  | x :: xs => kvalJ x :: kvalListJ xs

def kcellListJ : List (String × ISAR.KVal) → List String
  | [] => []
  | (n, v) :: xs => ("[" ++ jstr n ++ "," ++ kvalJ v ++ "]") :: kcellListJ xs

def kexprJ : ISAR.KExpr → String
  | .lit v => "{\"lit\":" ++ kvalJ v ++ "}"
  | .var n => "{\"var\":" ++ jstr n ++ "}"
  | .bin op a b =>
      "{\"bin\":[" ++ jstr (binopName op) ++ "," ++ kexprJ a ++ "," ++ kexprJ b ++ "]}"
  | .un op e => "{\"un\":[" ++ jstr (unopName op) ++ "," ++ kexprJ e ++ "]}"
  | .cond c t e =>
      "{\"cond\":[" ++ kexprJ c ++ "," ++ kexprJ t ++ "," ++ kexprJ e ++ "]}"
  | .field o n => "{\"field\":[" ++ kexprJ o ++ "," ++ jstr n ++ "]}"
  | .index o i => "{\"index\":[" ++ kexprJ o ++ "," ++ kexprJ i ++ "]}"
  | .builtin n args =>
      "{\"builtin\":[" ++ jstr n ++ ",[" ++ String.intercalate "," (kexprListJ args) ++ "]]}"

def kexprListJ : List ISAR.KExpr → List String
  | [] => []
  | x :: xs => kexprJ x :: kexprListJ xs

def kNamedExprsJ : List (String × ISAR.KExpr) → List String
  | [] => []
  | (n, e) :: xs => ("[" ++ jstr n ++ "," ++ kexprJ e ++ "]") :: kNamedExprsJ xs

def karmNodeJ : ISAR.KArmNode → String
  | .terminal => "{\"terminal\":[]}"
  | .jump t args => "{\"jump\":[" ++ jstr t ++ ",[" ++ String.intercalate "," (kNamedExprsJ args) ++ "]]}"
  | .invoke t args => "{\"invoke\":[" ++ jstr t ++ ",[" ++ String.intercalate "," (kNamedExprsJ args) ++ "]]}"
  | .produce e => "{\"produce\":" ++ kexprJ e ++ "}"
  | .retCtor c e => "{\"retCtor\":[" ++ jstr c ++ "," ++ kexprJ e ++ "]}"

def joptE : Option ISAR.KExpr → String
  | none => "null" | some e => kexprJ e

def joptN : Option ISAR.KArmNode → String
  | none => "null" | some a => karmNodeJ a

def karmJ : ISAR.KArm → String
  | .mk br ca bi co no cs =>
      "{\"arm\":{\"branch\":" ++ jstr br
        ++ ",\"catchall\":" ++ jbool ca
        ++ ",\"bind\":" ++ jopt jstr bi
        ++ ",\"cond\":" ++ joptE co
        ++ ",\"node\":" ++ joptN no
        ++ ",\"conts\":[" ++ String.intercalate "," (karmListJ cs) ++ "]}}"

def karmListJ : List ISAR.KArm → List String
  | [] => []
  | a :: xs => karmJ a :: karmListJ xs
end

def kflowJ (f : ISAR.KFlow) : String :=
  "{\"flow\":{\"preLabel\":" ++ jopt jstr f.preLabel
    ++ ",\"head\":[" ++ jstr f.head.1 ++ ",[" ++ String.intercalate "," (kNamedExprsJ f.head.2) ++ "]]"
    ++ ",\"arms\":[" ++ String.intercalate "," (karmListJ f.arms) ++ "]}}"

def kcallableJ : ISAR.KCallable → String
  | .bare e => "{\"bare\":" ++ kexprJ e ++ "}"
  | .thunk => "{\"thunk\":[]}"
  | .subflow f => "{\"subflow\":" ++ kflowJ f ++ "}"

def kprogJ (p : ISAR.KProg) : String :=
  "{\"graph\":" ++ jlist (fun (n, c) => "[" ++ jstr n ++ "," ++ kcallableJ c ++ "]") p.graph
    ++ ",\"entry\":" ++ jstr p.entry
    ++ ",\"args\":" ++ jlist (fun (n, v) =>
        "[" ++ jstr n ++ "," ++ kvalJ v ++ "]") p.args ++ "}"

def kresultJ (r : ISAR.KResult) : String :=
  "{\"branch\":" ++ jopt jstr r.branch
    ++ ",\"payload\":" ++ jopt kvalJ r.payload ++ "}"

/-- One fixture row for a corpus program. -/
def caseJ (i : Nat) (fuel : Nat) (src : ISAR.KProg) : String :=
  let quoted := ISAR.quoteProg src
  let kemitRes := ISAR.asKResult
    (ISAR.runK ISAR.kEmit.graph [] fuel
      (.invoke "emit" [("src", quoted)]))
  "{\"id\":" ++ toString i
    ++ ",\"prog\":" ++ kprogJ src
    ++ ",\"quoted_src\":" ++ kvalJ quoted
    ++ ",\"eval\":" ++ jopt kresultJ (ISAR.evalKProg src [] fuel)
    ++ ",\"emit\":" ++ jopt jstr (ISAR.emitC99 src)
    ++ ",\"kemit\":" ++ jopt kresultJ kemitRes
    ++ "}"

def fixtureJ (fuel : Nat) : String :=
  "{\"generated\":\"lake env lean --run tools/DumpKoruFixtures.lean -- do not hand-edit\""
    ++ ",\"wire\":\"kv-json v1: one object per grammar node, {\\\"<ctor>\\\": payload}\""
    ++ ",\"fuel\":" ++ toString fuel
    ++ ",\"programs\":{\"kemit\":" ++ kprogJ ISAR.kEmit ++ "}"
    ++ ",\"cases\":" ++ jlist (fun (p, i) => caseJ i fuel p)
        (ISAR.koruEmitCorpus.zipIdx) ++ "}"

def main : IO Unit := do
  IO.println (fixtureJ 64)
