import ISAR.InvariantLayer
import ISAR.KernelCategory

namespace ISAR

/--
An abstract Dialect represents a semantic view over the representation-free substrate.
For a given dialect, we have:
1. `Object`: The type of dialect objects/terms.
2. `Obs`: The type of observations or results of evaluation.
3. `ObsEq`: The observational equivalence relation on observations.
4. `eval`: The dialect's evaluation function.
5. `encode`: A compiler/encoder mapping dialect objects to substrate terms (`ISKSubtype`).
6. `decode`: A decoder mapping substrate quotient classes (`InvariantLayer`) to observations.
7. `preserves`: The main coherence/preservation law, showing that decoding the quotient class
   of an encoded object is observationally equivalent to evaluating the object in the dialect.
-/
structure Dialect where
  Object : Type
  Obs : Type
  ObsEq : Obs → Obs → Prop
  is_equiv : Equivalence ObsEq
  eval : Object → Obs
  encode : Object → ISKSubtype
  decode : InvariantLayer → Obs
  preserves : ∀ (x : Object), ObsEq (decode (Quotient.mk operEqSetoid (encode x))) (eval x)

/-- The equivalence relation setoid on a Dialect's observations. -/
def Dialect.setoid (D : Dialect) : Setoid D.Obs where
  r := D.ObsEq
  iseqv := D.is_equiv

end ISAR
