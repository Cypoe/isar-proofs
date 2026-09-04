import ISAR.Kernel
import ISAR.LambdaFragment
import ISAR.Reduce

/-!
# LambdaEval — λ dialect column against the gold reduce

`compile` (Lean `LambdaFragment`) then `reduceFuel` (Lean `IStep`).
Host twin: `host/lambda_dialect.py` (same `abstract0` / `compile`, familiar `\x. e` sugar).
-/

namespace ISAR

open LTerm

/-- de Bruijn: λx. x -/
private def idL : LTerm := .abs (.var 0)

/-- de Bruijn: λx. λy. x -/
private def constL : LTerm := .abs (.abs (.var 1))

/-- de Bruijn: λx. λy. λz. (x z) (y z) -/
private def sL : LTerm :=
  .abs (.abs (.abs (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

#eval compile idL
#eval compile constL
#eval reduceFuel 20 (.app (compile idL) .konst)
#eval reduceFuel 40 (.app (.app (compile constL) .sₛ) .norm)
#eval reduceFuel 80 (.app (.app (.app (compile sL) .konst) .konst) .norm)

#guard compile idL == .norm
#guard compile constL == .app (.app .comp .konst) .norm
#guard reduceFuel 20 (.app (compile idL) .konst) == .konst
#guard reduceFuel 40 (.app (.app (compile constL) .sₛ) .norm) == .sₛ
#guard reduceFuel 80 (.app (.app (.app (compile sL) .konst) .konst) .norm) == .norm

end ISAR
