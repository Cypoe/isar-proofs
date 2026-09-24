import ISAR.LambdaFragment
import ISAR.BasisDev
import ISAR.HeapDev

namespace ISAR
open Relation LTerm

def hstep : LTerm → LTerm
  | .app f x =>
      match f with
      | .abs b => subst x 0 b
      | _ => .app (hstep f) x
  | t => t

def hsteps : Nat → LTerm → LTerm
  | 0, t => t
  | n + 1, t => hsteps n (hstep t)

def absN : Nat → LTerm → LTerm
  | 0, t => t
  | n + 1, t => .abs (absN n t)

def aps : LTerm → List LTerm → LTerm := List.foldl .app

def nibLit : Fin 16 → LTerm := fun i => absN 16 (.var (15 - i.val))
def klL : LTerm := .abs (.abs (.var 1))
def kilL : LTerm := .abs (.abs (.var 0))
def boolLit : Bool → LTerm := fun b => if b then klL else kilL
def nibAddL : LTerm :=
  .abs (.abs (aps (.var 1) (List.ofFn fun i : Fin 16 =>
    aps (.var 0) (List.ofFn fun j : Fin 16 =>
      nibLit ⟨(i.val + j.val) % 16, by omega⟩))))

/-- `_NIBCARRY = (\a. \b. a C_0 … C_15)` where `C_i`'s j-th is BT iff
    i + j ≥ 16. -/
def nibCarryL : LTerm :=
  .abs (.abs (aps (.var 1) (List.ofFn fun i : Fin 16 =>
    aps (.var 0) (List.ofFn fun j : Fin 16 =>
      boolLit (decide (16 ≤ i.val + j.val))))))

theorem nibadd_table_decide : ∀ i j : Fin 16,
    hsteps 64 (aps nibAddL [nibLit i, nibLit j])
      = nibLit ⟨(i.val + j.val) % 16, by omega⟩ := by
  decide

theorem nibcarry_table_decide : ∀ i j : Fin 16,
    hsteps 64 (aps nibCarryL [nibLit i, nibLit j])
      = boolLit (decide (16 ≤ i.val + j.val)) := by
  decide
