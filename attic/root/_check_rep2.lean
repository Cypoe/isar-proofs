import ISAR.SpecVocabulary
open ISAR
-- mimic: conjunction of True-leaves + closed-leaves + forall-leaves
example (rbbT : LTerm) (hr : closed 0 rbbT = true) :
    (True ∧ (True ∧ True) ∧ True) ∧
    ((True ∧ closed 0 rbbT = true) ∧ True) ∧
    (True ∧ (∀ x ∈ ([] : List LTerm), x = x) ∧ True) ∧
    (∀ v : LTerm, closed 0 v = true → closed 0 v = true) := by
  repeat' first
    | (intro x hx; cases hx)
    | (try simp only [closed]) <;> repeat' constructor <;>
      first | assumption | decide
    | (intro v hv; assumption)
    | constructor
