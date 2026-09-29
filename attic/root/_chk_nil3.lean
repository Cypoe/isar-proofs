import ISAR.SpecVocabulary
open ISAR
-- simulate: predicate on items, forall_mem_cons chain with metavar tail
variable (P : LTerm → Prop) (a : LTerm)
example : ∀ x ∈ [a, a], P x :=
  List.forall_mem_cons.mpr ⟨sorry,
    List.forall_mem_cons.mpr ⟨sorry,
      fun x hx => False.elim (List.not_mem_nil hx)⟩⟩
