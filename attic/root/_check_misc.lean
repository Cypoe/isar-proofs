import ISAR.SpecVocabulary
open ISAR
#check @Bool.and_eq_true
#check @closed_app
#check @LTerm.var
example (f x : LTerm) (hf : closed 0 f = true) (hx : closed 0 x = true) :
    closed 0 (.app f x) = true :=
  Bool.and_eq_true.mpr ⟨hf, hx⟩
example (b : LTerm) (hb : closed 1 b = true) :
    closed 0 (.abs b) = true := hb
example : DecidableEq LTerm := inferInstance
