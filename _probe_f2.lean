import ISAR.SpecVocabulary
namespace ISAR
example {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    {a : α} {b : β} (h : List.Forall₂ R xs ys) (h2 : R a b) :
    List.Forall₂ R (xs ++ [a]) (ys ++ [b]) :=
  List.Forall₂.append h (List.Forall₂.cons h2 List.Forall₂.nil)
example {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    List.Forall₂ R xs.reverse ys.reverse := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    rw [List.reverse_cons, List.reverse_cons]
    exact List.Forall₂.append ih (List.Forall₂.cons hr List.Forall₂.nil)
-- klL vs nilL shape check
#eval (klL == nilL)
#eval decide (klL = nilL)
end ISAR
