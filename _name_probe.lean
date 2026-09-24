import ISAR.LambdaFragment
open List
example (l : List Nat) (f : Nat → Nat) : (l.map f).reverse = l.reverse.map f := by
  exact?
