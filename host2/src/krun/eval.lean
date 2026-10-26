import ISAR.FlowDialect

/-! # krun/eval.c — the runK twin, pinned

The C evaluator is a mechanical port of `runK` (ISAR.FlowDialect):
one function `run_k` over a `Call` union, recursion at strictly
smaller fuel, `none` = refusal everywhere Lean returns `none`.
This file pins the correspondence where it is checkable and names
the places where it is only declared.

## Call.tag ↔ KCall constructor order (declared, read off both)

| C tag | KCall constructor |
|-------|-------------------|
| 0     | invoke            |
| 1     | flow              |
| 2     | loop              |
| 3     | dispatchTag       |
| 4     | dispatchBare      |
| 5     | armTry            |
| 6     | armWalk           |

## Outc.t ↔ KOutcome (+ refusal)

| C tag | meaning  | Lean side        |
|-------|----------|------------------|
| 0     | refuse   | `none`           |
| 1     | result   | `some (.result)` |
| 2     | jump     | `some (.jump)`   |
| 3     | done     | `some (.done)`   |
| 4     | skip     | `some (.skip)`   |

## Declared divergence

int64 arithmetic is CHECKED in C: overflow refuses where Lean's
`Int` would still decide.  The corpus never exercises it; named in
realizations.json (`flow-eval` row). -/

namespace Host2.KRun

/-- The `_chain` contract korufe emits for `|>` continuation steps:
an unnamed koru chain arm is lowered to a decorated-name arm, and
under a BARE result `dispatchBare` admits it — binds the payload,
walks the node.  This pin is the semantic the ported corpus relies
on (`|> a() |> b()` chains); if the wire ever refuses decorated
names under bare dispatch the ported legs break here first. -/
def chainProg : ISAR.KProg := {
  graph := [
    ("a", .bare (.lit (.int 5)))
  , ("main", .subflow {
      preLabel := none
      head := ("a", [])
      arms := [ .mk "_chain" false (some "x") none
                  (some (.produce (.var "x"))) [] ] }) ]
  entry := "main"
  args := [] }

theorem evalK_chain :
    ISAR.evalKProg chainProg [] 64
    == some { branch := none, payload := some (.int 5) } := by
  native_decide

end Host2.KRun
