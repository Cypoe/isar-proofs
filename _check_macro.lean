import ISAR.SpecVocabulary
open ISAR
example (v : LTerm) (hv : closed 0 v = true) :
    closed 0 (shift 1 0 v) = true := by
  simp only [shift_of_closed0 hv]
example (v : LTerm) (hv : closed 0 v = true) :
    closed 0 (shift 1 0 v) = true := by
  simp [shift_of_closed0]
example (v : LTerm) (hv : closed 0 v = true) :
    closed 0 (shift 1 0 v) = true := by
  simp [*]
