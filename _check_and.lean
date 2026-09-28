example : (True ∧ True) ∧ (True ∧ True) ∧ True := by
  and_intros
example : (True ∧ True) ∧ True ∧ (True ∧ True) := by
  and_intros
example : True ∧ (1 = 1 ∧ True) := by
  and_intros
  · trivial
  · rfl
  · trivial
