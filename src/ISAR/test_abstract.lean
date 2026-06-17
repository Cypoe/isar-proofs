namespace Relation

inductive ReflTransGen {α : Type _} (r : α → α → Prop) (a : α) : α → Prop where
  | refl : ReflTransGen r a a
  | tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace ReflTransGen

theorem trans {α : Type _} {r : α → α → Prop} {a b c : α}
    (h1 : ReflTransGen r a b) (h2 : ReflTransGen r b c) : ReflTransGen r a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact ReflTransGen.tail ih hstep

theorem single {α : Type _} {r : α → α → Prop} {a b : α} (h : r a b) : ReflTransGen r a b :=
  ReflTransGen.tail ReflTransGen.refl h

end ReflTransGen

end Relation

open Relation

inductive ITerm : Type where
  | var   : Nat → ITerm
  | norm  : ITerm
  | konst : ITerm
  | dup   : ITerm
  | swap  : ITerm
  | comp  : ITerm
  | sₛ    : ITerm
  | app   : ITerm → ITerm → ITerm
deriving DecidableEq, Repr

inductive IStep : ITerm → ITerm → Prop where
  | normβ (x : ITerm) :
      IStep (ITerm.app ITerm.norm x) x
  | konstβ (x y : ITerm) :
      IStep (ITerm.app (ITerm.app ITerm.konst x) y) x
  | compβ (f g x : ITerm) :
      IStep (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x)
             (ITerm.app f (ITerm.app g x))
  | sβ (x y z : ITerm) :
      IStep (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ x) y) z)
             (ITerm.app (ITerm.app x z) (ITerm.app y z))
  | appL {f f' x : ITerm} :
      IStep f f' → IStep (ITerm.app f x) (ITerm.app f' x)
  | appR {f x x' : ITerm} :
      IStep x x' → IStep (ITerm.app f x) (ITerm.app f x')

abbrev IRed  := Relation.ReflTransGen IStep

theorem IRed_app_left {f f' x : ITerm} :
    IRed f f' → IRed (ITerm.app f x) (ITerm.app f' x) := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (IStep.appL hstep)

theorem IRed_app_right {f x x' : ITerm} :
    IRed x x' → IRed (ITerm.app f x) (ITerm.app f x') := by
  intro h
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (IStep.appR hstep)

theorem IRed_app {f f' x x' : ITerm} (hf : IRed f f') (hx : IRed x x') :
    IRed (ITerm.app f x) (ITerm.app f' x') :=
  Relation.ReflTransGen.trans (IRed_app_left hf) (IRed_app_right hx)

def occurs0 : ITerm → Bool
  | .var 0 => true
  | .var _ => false
  | .norm => false
  | .konst => false
  | .dup => false
  | .swap => false
  | .comp => false
  | .sₛ => false
  | .app f x => occurs0 f || occurs0 x

def shift_down : ITerm → ITerm
  | .var 0 => .var 0
  | .var n => .var (n - 1)
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => .sₛ
  | .app f x => .app (shift_down f) (shift_down x)

def abstract0 (t : ITerm) : ITerm :=
  match occurs0 t with
  | false => .app .konst (shift_down t)
  | true =>
      match t with
      | .var 0 => .norm
      | .app f x =>
          match occurs0 f, occurs0 x with
          | false, true => .app (.app .comp (shift_down f)) (abstract0 x)
          | true, false => .app (.app .swap (abstract0 f)) (shift_down x)
          | true, true => .app (.app (.app .sₛ (abstract0 f)) (abstract0 x))
      | _ => .norm

def subst_isar (x : ITerm) : ITerm → ITerm
  | .var 0 => x
  | .var n => .var (n - 1)
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => .sₛ
  | .app f y => .app (subst_isar x f) (subst_isar x y)

theorem abstract_sound (t x : ITerm) :
    IRed (ITerm.app (abstract0 t) x) (subst_isar x t) := by
  induction t with
  | var n =>
      by_cases h0 : n = 0
      · subst h0
        -- t = var 0
        -- occurs0 t = true
        -- abstract0 (var 0) = norm
        -- subst_isar x (var 0) = x
        -- IRed (app norm x) x
        have h_occ : occurs0 (.var 0) = true := rfl
        have h_abs : abstract0 (.var 0) = .norm := rfl
        have h_sub : subst_isar x (.var 0) = x := rfl
        exact Relation.ReflTransGen.single (IStep.normβ x)
      · -- n > 0
        -- occurs0 (var n) = false
        -- abstract0 (var n) = app konst (shift_down (var n)) = app konst (var (n-1))
        -- subst_isar x (var n) = var (n-1)
        -- IRed (app (app konst (var (n-1))) x) (var (n-1))
        have h_occ : occurs0 (.var n) = false := by
          cases n with
          | zero => contradiction
          | succ n => rfl
        have h_abs : abstract0 (.var n) = .app .konst (.var (n - 1)) := by
          simp [abstract0, occurs0, h_occ, shift_down]
          cases n with
          | zero => contradiction
          | succ n => rfl
        have h_sub : subst_isar x (.var n) = .var (n - 1) := by
          cases n with
          | zero => contradiction
          | succ n => rfl
        rw [h_abs, h_sub]
        exact Relation.ReflTransGen.single (IStep.konstβ (.var (n - 1)) x)
  | norm =>
      exact Relation.ReflTransGen.single (IStep.konstβ .norm x)
  | konst =>
      exact Relation.ReflTransGen.single (IStep.konstβ .konst x)
  | dup =>
      exact Relation.ReflTransGen.single (IStep.konstβ .dup x)
  | swap =>
      exact Relation.ReflTransGen.single (IStep.konstβ .swap x)
  | comp =>
      exact Relation.ReflTransGen.single (IStep.konstβ .comp x)
  | sₛ =>
      exact Relation.ReflTransGen.single (IStep.konstβ .sₛ x)
  | app f y ihf ihy =>
      by_cases h_occ : occurs0 (.app f y) = true
      · -- occurs0 (.app f y) = true
        -- occurs0 f || occurs0 y = true
        have h_abs_true : abstract0 (.app f y) =
          match occurs0 f, occurs0 y with
          | false, true => .app (.app .comp (shift_down f)) (abstract0 y)
          | true, false => .app (.app .swap (abstract0 f)) (shift_down y)
          | true, true => .app (.app (.app .sₛ (abstract0 f)) (abstract0 y)) := by
            simp [abstract0, h_occ]
        -- Let's do cases on occurs0 f and occurs0 y
        by_cases hf_occ : occurs0 f = true
        · by_cases hy_occ : occurs0 y = true
          · -- both occurs0 f and occurs0 y are true
            have h_abs : abstract0 (.app f y) = .app (.app (.app .sₛ (abstract0 f)) (abstract0 y)) := by
              simp [abstract0, h_occ, hf_occ, hy_occ]
            rw [h_abs]
            -- We want: IRed (app (app (app (app sₛ (abstract0 f)) (abstract0 y)) x) (app (subst_isar x f) (subst_isar x y))
            -- IStep (app (app (app (app sₛ (abstract0 f)) (abstract0 y)) x) (app (app (abstract0 f) x) (app (abstract0 y) x))
            have h_step : IStep (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ (abstract0 f)) (abstract0 y)) x)
                                (ITerm.app (ITerm.app (abstract0 f) x) (ITerm.app (abstract0 y) x)) :=
              IStep.sβ (abstract0 f) (abstract0 y) x
            have h_ih : IRed (ITerm.app (ITerm.app (abstract0 f) x) (ITerm.app (abstract0 y) x))
                             (ITerm.app (subst_isar x f) (subst_isar x y)) :=
              IRed_app ihf ihy
            exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h_step) h_ih
          · -- occurs0 f = true, occurs0 y = false
            have hy_occ_false : occurs0 y = false := by
              match h : occurs0 y with
              | false => rfl
              | true => contradiction
            have h_abs : abstract0 (.app f y) = .app (.app .swap (abstract0 f)) (shift_down y) := by
              simp [abstract0, h_occ, hf_occ, hy_occ_false]
            rw [h_abs]
            have h_step : IStep (ITerm.app (ITerm.app (ITerm.app ITerm.swap (abstract0 f)) (shift_down y)) x)
                                (ITerm.app (ITerm.app (abstract0 f) x) (shift_down y)) :=
              IStep.swapβ (abstract0 f) (shift_down y) x
            -- Since occurs0 y is false, subst_isar x y = shift_down y
            have h_sub_y : subst_isar x y = shift_down y := by
              induction y with
              | var n =>
                  -- occurs0 y = false means n > 0
                  cases n with
                  | zero => contradiction
                  | succ n => rfl
              | norm => rfl
              | konst => rfl
              | dup => rfl
              | swap => rfl
              | comp => rfl
              | sₛ => rfl
              | app f2 y2 ihf2 ihy2 =>
                  -- occurs0 f2 || occurs0 y2 = false
                  -- occurs0 f2 = false and occurs0 y2 = false
                  have hf2_occ : occurs0 f2 = false := by
                    match h : occurs0 f2 with
                    | false => rfl
                    | true => contradiction
                  have hy2_occ : occurs0 y2 = false := by
                    match h : occurs0 y2 with
                    | false => rfl
                    | true => contradiction
                  simp [subst_isar, shift_down]
                  exact ⟨ihf2 hf2_occ, ihy2 hy2_occ⟩
            rw [h_sub_y]
            have h_ih : IRed (ITerm.app (ITerm.app (abstract0 f) x) (shift_down y))
                             (ITerm.app (subst_isar x f) (shift_down y)) :=
              IRed_app_left ihf
            exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h_step) h_ih
        · -- occurs0 f = false
          have hf_occ_false : occurs0 f = false := by
            match h : occurs0 f with
            | false => rfl
            | true => contradiction
          -- Since occurs0 (app f y) is true, occurs0 y must be true
          have hy_occ : occurs0 y = true := by
            simp [occurs0] at h_occ
            match h : occurs0 f with
            | false => exact h_occ
            | true => contradiction
          have h_abs : abstract0 (.app f y) = .app (.app .comp (shift_down f)) (abstract0 y) := by
            simp [abstract0, h_occ, hf_occ_false, hy_occ]
          rw [h_abs]
          have h_step : IStep (ITerm.app (ITerm.app (ITerm.app ITerm.comp (shift_down f)) (abstract0 y)) x)
                              (ITerm.app (shift_down f) (ITerm.app (abstract0 y) x)) :=
            IStep.compβ (shift_down f) (abstract0 y) x
          have h_sub_f : subst_isar x f = shift_down f := by
            induction f with
            | var n =>
                cases n with
                | zero => contradiction
                | succ n => rfl
            | norm => rfl
            | konst => rfl
            | dup => rfl
            | swap => rfl
            | comp => rfl
            | sₛ => rfl
            | app f2 y2 ihf2 ihy2 =>
                have hf2_occ : occurs0 f2 = false := by
                  match h : occurs0 f2 with
                  | false => rfl
                  | true => contradiction
                have hy2_occ : occurs0 y2 = false := by
                  match h : occurs0 y2 with
                  | false => rfl
                  | true => contradiction
                simp [subst_isar, shift_down]
                exact ⟨ihf2 hf2_occ, ihy2 hy2_occ⟩
          rw [h_sub_f]
          have h_ih : IRed (ITerm.app (shift_down f) (ITerm.app (abstract0 y) x))
                           (ITerm.app (shift_down f) (subst_isar x y)) :=
            IRed_app_right ihy
          exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h_step) h_ih
      · -- occurs0 (.app f y) = false
        -- abstract0 (.app f y) = app konst (shift_down (app f y))
        have h_abs : abstract0 (.app f y) = .app .konst (shift_down (.app f y)) := by
          simp [abstract0, h_occ]
        rw [h_abs]
        have h_sub : subst_isar x (.app f y) = shift_down (.app f y) := by
          induction (.app f y) with
          | var n => contradiction
          | norm => contradiction
          | konst => contradiction
          | dup => contradiction
          | swap => contradiction
          | comp => contradiction
          | sₛ => contradiction
          | app f2 y2 ihf2 ihy2 =>
              have h_occ_fy : occurs0 (app f2 y2) = false := h_occ
              have hf2_occ : occurs0 f2 = false := by
                match h : occurs0 f2 with
                | false => rfl
                | true => contradiction
              have hy2_occ : occurs0 y2 = false := by
                match h : occurs0 y2 with
                | false => rfl
                | true => contradiction
              simp [subst_isar, shift_down]
              exact ⟨ihf2 hf2_occ, ihy2 hy2_occ⟩
        rw [h_sub]
        exact Relation.ReflTransGen.single (IStep.konstβ (shift_down (.app f y)) x)
