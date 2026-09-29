import ISAR.SpecVocabulary
open ISAR
def citem : LTerm := aps conssL
  [aps conssL [nibLit 6, aps conssL [nibLit 12, klL]],
   aps conssL [aps pairSrcL [nibLit 5, nibLit 15], klL]]
example : closed 0 citem = true := by decide
example : closed 2 (aps conssL [nibLit 6, .var 1]) = true := by decide
-- and-tree term check
theorem closed_appD (d : Nat) (f x : LTerm)
    (hf : closed d f = true) (hx : closed d x = true) :
    closed d (.app f x) = true := by
  simp only [closed, Bool.and_eq_true]; exact ⟨hf, hx⟩
example (rbbT : LTerm) (hr : closed 0 rbbT = true) :
    closed 0 (aps conssL [nibLit 6, rbbT]) = true :=
  closed_appD 0 _ _
    (closed_appD 0 _ _
      (closed_conssL_any 0)
      (closed_nibLit_any 6 0))
    (closed_mono hr (Nat.zero_le 0))
