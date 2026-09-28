example : (True ∧ True) ∧ (True ∧ (True ∧ True)) := by
  repeat' first | trivial | constructor
example (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (P ∧ (Q ∧ True)) := by
  repeat' first | assumption | constructor
