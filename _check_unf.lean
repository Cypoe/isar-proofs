import ISAR.SpecVocabulary
namespace ISAR
inductive PSeg where
  | cell : LTerm → PSeg
  | fuse : List LTerm → List LTerm → PSeg
  | fuelR : List LTerm → PSeg
inductive OSeg where
  | frag : List PSeg → OSeg
  | stS : List LTerm → OSeg
  | bDS : List LTerm → OSeg
def psegClosed (s : PSeg) : Prop :=
  match s with
  | .cell it => closed 0 it = true
  | .fuse a b => (∀ c ∈ a, closed 0 c = true) ∧
      (∀ c ∈ b, closed 0 c = true)
  | .fuelR a => ∀ c ∈ a, closed 2 c = true ∧
      (∀ v : LTerm, closed 0 v = true →
        closed 0 (subst v 1 c) = true)
def osegClosed (s : OSeg) : Prop :=
  match s with
  | .frag segs => ∀ s ∈ segs, psegClosed s
  | .stS items | .bDS items => ∀ c ∈ items, closed 0 c = true

example : osegClosed (.frag [.cell klL]) := by
  simp only [osegClosed, psegClosed, List.forall_mem_cons,
    List.forall_mem_nil, and_true]
  exact closed_klL
example : osegClosed (.frag [.fuelR [klL]]) := by
  simp only [osegClosed, psegClosed, List.forall_mem_cons,
    List.forall_mem_nil, and_true]
  exact ⟨closed_klL, fun v hv => by
    simp [subst, shift_of_closed0 hv, subst_of_closed0 closed_klL]⟩
end ISAR
