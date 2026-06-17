import ISAR

open ISAR

inductive LTerm : Type where
  | var : Nat → LTerm
  | abs : LTerm → LTerm
  | app : LTerm → LTerm → LTerm
deriving DecidableEq, Repr

def shift (d : Nat) (c : Nat) : LTerm → LTerm
  | .var n => if n < c then .var n else .var (n + d)
  | .abs body => .abs (shift d (c + 1) body)
  | .app f x => .app (shift d c f) (shift d c x)

def subst (s : LTerm) (c : Nat) : LTerm → LTerm
  | .var n =>
      if n < c then .var n
      else if n = c then shift c 0 s
      else .var (n - 1)
  | .abs body => .abs (subst s (c + 1) body)
  | .app f x => .app (subst s c f) (subst s c x)

inductive LStep : LTerm → LTerm → Prop where
  | beta (body s : LTerm) :
      LStep (.app (.abs body) s) (subst s 0 body)
  | appL {f f' x : LTerm} :
      LStep f f' → LStep (.app f x) (.app f' x)
  | appR {f x x' : LTerm} :
      LStep x x' → LStep (.app f x) (.app f x')
  | abs {body body' : LTerm} :
      LStep body body' → LStep (.abs body) (.abs body')

abbrev LRed := Relation.ReflTransGen LStep

-- Helper for LRed congruence
theorem LRed_app_left {f f' x : LTerm} (h : LRed f f') :
    LRed (.app f x) (.app f' x) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (LStep.appL hstep)

theorem LRed_app_right {f x x' : LTerm} (h : LRed x x') :
    LRed (.app f x) (.app f x') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (LStep.appR hstep)

theorem LRed_app {f f' x x' : LTerm} (hf : LRed f f') (hx : LRed x x') :
    LRed (.app f x) (.app f' x') :=
  Relation.ReflTransGen.trans (LRed_app_left hf) (LRed_app_right hx)

theorem LRed_abs {body body' : LTerm} (h : LRed body body') :
    LRed (.abs body) (.abs body') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (LStep.abs hstep)
