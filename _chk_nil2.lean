import ISAR.SpecVocabulary
open ISAR
variable (P : LTerm → Prop)
example : ∀ x ∈ ([] : List LTerm), P x := fun x hx => False.elim (List.not_mem_nil hx)
example : ∀ x ∈ ([] : List LTerm), P x := fun x hx => absurd hx List.not_mem_nil
example : ∀ x ∈ ([] : List LTerm), P x := List.forall_mem_nil P
example : ∀ x ∈ ([] : List LTerm), P x := fun x hx => nomatch hx
