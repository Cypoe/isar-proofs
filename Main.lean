import ISAR.Kernel
import ISAR.Reduce

/-!
# isar-reduce — thin CLI for ISAR term reduction

Usage: `lake exe isar-reduce`           — run golden suite
       `lake exe isar-reduce --term "((S K) K) I"` — reduce a term

Prints NF and step count using both `cd` (parallel) and `step?` (LO) strategies.
-/

open ISAR

/-- Iterate `cd` on raw ITerm until fixpoint or fuel exhaustion. -/
private def cdLoop (fuel : Nat) (t : ITerm) : ITerm :=
  match fuel with
  | 0 => t
  | n + 1 =>
    let t' := cd t
    if t == t' then t else cdLoop n t'

private def showTerm : ITerm → String
  | .var n => s!"v{n}"
  | .norm => "I"
  | .konst => "K"
  | .dup => "D"
  | .swap => "C"
  | .comp => "B"
  | .sₛ => "S"
  | .app f x => s!"({showTerm f} {showTerm x})"

/-- Minimal parser: atoms I K S B C D, application via `(f x)`. -/
private partial def parseOne (cs : List Char) : Option (ITerm × List Char) :=
  match cs with
  | [] => none
  | '(' :: rest =>
    let rest := rest.dropWhile (· == ' ')
    match parseOne rest with
    | none => none
    | some (f, rest) =>
      let rest := rest.dropWhile (· == ' ')
      match parseOne rest with
      | none => none
      | some (x, rest) =>
        let rest := rest.dropWhile (· == ' ')
        match rest with
        | ')' :: rest => some (.app f x, rest)
        | _ => none
  | 'I' :: rest => some (.norm, rest)
  | 'K' :: rest => some (.konst, rest)
  | 'S' :: rest => some (.sₛ, rest)
  | 'B' :: rest => some (.comp, rest)
  | 'C' :: rest => some (.swap, rest)
  | 'D' :: rest => some (.dup, rest)
  | _ => none

private def parseTerm (s : String) : Option ITerm :=
  match parseOne s.trimAscii.toString.toList with
  | some (t, rest) => if rest.all (· == ' ') then some t else none
  | none => none

structure Golden where
  label : String
  term : ITerm
  expectedNF : ITerm

open ITerm in
private def goldens : List Golden := [
  { label := "I K → K",
    term := app norm konst,
    expectedNF := konst },
  { label := "K S I → S",
    term := app (app konst sₛ) norm,
    expectedNF := sₛ },
  { label := "S K K I → I",
    term := app (app (app sₛ konst) konst) norm,
    expectedNF := norm },
  { label := "B f g x = f(gx): B K I S → K S",
    term := app (app (app (app (app sₛ (app konst sₛ)) konst) konst) norm) sₛ,
    expectedNF := app konst sₛ }
]

private def runGolden (g : Golden) : IO Bool := do
  let fuel := 200
  let (steps, nf_step) := reduceCount fuel g.term
  let nf_cd := cdLoop fuel g.term
  let pass := nf_step == g.expectedNF
  let tag := if pass then "✓" else "✗"
  IO.println s!"{tag} {g.label}"
  IO.println s!"  step? ({steps} steps): {showTerm nf_step}"
  IO.println s!"  cd    (fuel {fuel}):   {showTerm nf_cd}"
  if !pass then
    IO.println s!"  EXPECTED: {showTerm g.expectedNF}"
  return pass

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--term", s] =>
    match parseTerm s with
    | none => IO.eprintln s!"parse error: {s}"; return 1
    | some t =>
      let (steps, nf) := reduceCount 1000 t
      IO.println s!"{showTerm nf}  ({steps} steps)"
      return 0
  | _ =>
    IO.println "isar-reduce golden suite"
    IO.println "========================"
    let mut allPass := true
    for g in goldens do
      let pass ← runGolden g
      if !pass then allPass := false
    return if allPass then 0 else 1
