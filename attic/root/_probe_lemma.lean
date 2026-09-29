import ISAR.SpecVocabulary
open Relation ISAR
example (c : Bool) (a : LTerm) : (if c then a else a) = a := by simp only [ite_self]
example (c : Bool) (a : LTerm) : (if c then a else a) = a := by simp
