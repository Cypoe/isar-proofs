import ISAR

open Relation

namespace ISAR

/- =========================================================
   1. Lambda terms (LTerm) and weak beta-reduction (LStep)
   ========================================================= -/

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

abbrev LRed := Relation.ReflTransGen LStep

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

/- =========================================================
   2. Bracket abstraction compiler functions
   ========================================================= -/

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

def shift_isar (d : Nat) (c : Nat) : ITerm → ITerm
  | .var n => if n < c then .var n else .var (n + d)
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => .sₛ
  | .app f x => .app (shift_isar d c f) (shift_isar d c x)

def abstract0 (t : ITerm) : ITerm :=
  match occurs0 t with
  | false => .app .konst (shift_down t)
  | true =>
      match t with
      | .var 0 => .norm
      | .app f x =>
          match occurs0 f, occurs0 x with
          | false, true => .app (.app .comp (shift_down f)) (abstract0 x)
          | _, _ => .app (.app .sₛ (abstract0 f)) (abstract0 x)
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

def subst_isar_at (c : Nat) (x : ITerm) : ITerm → ITerm
  | .var n =>
      if n < c then .var n
      else if n = c then x
      else .var (n - 1)
  | .norm => .norm
  | .konst => .konst
  | .dup => .dup
  | .swap => .swap
  | .comp => .comp
  | .sₛ => .sₛ
  | .app f y => .app (subst_isar_at c x f) (subst_isar_at c x y)

def compile : LTerm → ITerm
  | .var n => .var n
  | .app f x => .app (compile f) (compile x)
  | .abs body => abstract0 (compile body)

/- =========================================================
   3. Shifting & Substitution Lemmas for compiler
   ========================================================= -/

theorem subst_isar_no_occur {t : ITerm} (h : occurs0 t = false) (x : ITerm) :
    subst_isar x t = shift_down t := by
  induction t with
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
  | app f y ihf ihy =>
      simp [occurs0] at h
      simp [subst_isar, shift_down]
      exact ⟨ihf h.1, ihy h.2⟩

theorem abstract_sound (t x : ITerm) :
    IRed (ITerm.app (abstract0 t) x) (subst_isar x t) := by
  induction t with
  | var n =>
      by_cases h0 : n = 0
      case pos =>
        subst h0
        have h_abs : abstract0 (ITerm.var 0) = .norm := rfl
        have h_sub : subst_isar x (ITerm.var 0) = x := rfl
        rw [h_abs, h_sub]
        exact Relation.ReflTransGen.single (IStep.normβ x)
      case neg =>
        have h_occ : occurs0 (ITerm.var n) = false := by
          cases n with
          | zero => contradiction
          | succ n => rfl
        have h_abs : abstract0 (ITerm.var n) = .app .konst (ITerm.var (n - 1)) := by
          cases n with
          | zero => contradiction
          | succ n => rfl
        have h_sub : subst_isar x (ITerm.var n) = ITerm.var (n - 1) := by
          cases n with
          | zero => contradiction
          | succ n => rfl
        rw [h_abs, h_sub]
        exact Relation.ReflTransGen.single (IStep.konstβ (ITerm.var (n - 1)) x)
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
      case pos =>
        by_cases hf_occ : occurs0 f = false ∧ occurs0 y = true
        case pos =>
          have h_abs : abstract0 (.app f y) = .app (.app .comp (shift_down f)) (abstract0 y) := by
            simp [abstract0, h_occ, hf_occ.1, hf_occ.2]
          rw [h_abs]
          have h_step : IStep (ITerm.app (ITerm.app (ITerm.app ITerm.comp (shift_down f)) (abstract0 y)) x)
                              (ITerm.app (shift_down f) (ITerm.app (abstract0 y) x)) :=
            IStep.compβ (shift_down f) (abstract0 y) x
          have h_sub_f : subst_isar x f = shift_down f := subst_isar_no_occur hf_occ.1 x
          dsimp [subst_isar]
          rw [h_sub_f]
          have h_ih : IRed (ITerm.app (shift_down f) (ITerm.app (abstract0 y) x))
                           (ITerm.app (shift_down f) (subst_isar x y)) :=
            IRed_app_right ihy
          exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h_step) h_ih
        case neg =>
          have h_abs : abstract0 (.app f y) = .app (.app .sₛ (abstract0 f)) (abstract0 y) := by
            simp [abstract0, h_occ]
            split
            { rename_i h1 h2
              exact False.elim (hf_occ ⟨h1, h2⟩) }
            { rfl }
          rw [h_abs]
          have h_step : IStep (ITerm.app (ITerm.app (ITerm.app ITerm.sₛ (abstract0 f)) (abstract0 y)) x)
                              (ITerm.app (ITerm.app (abstract0 f) x) (ITerm.app (abstract0 y) x)) :=
            IStep.sβ (abstract0 f) (abstract0 y) x
          dsimp [subst_isar]
          have h_ih : IRed (ITerm.app (ITerm.app (abstract0 f) x) (ITerm.app (abstract0 y) x))
                           (ITerm.app (subst_isar x f) (subst_isar x y)) :=
            IRed_app ihf ihy
          exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h_step) h_ih
      case neg =>
        have h_occ_false : occurs0 (.app f y) = false := by
          cases h : occurs0 (.app f y) with
          | true =>
              rw [h] at h_occ
              contradiction
          | false => rfl
        have h_abs : abstract0 (.app f y) = .app .konst (shift_down (.app f y)) := by
          simp [abstract0, h_occ_false]
        rw [h_abs]
        have h_sub : subst_isar x (.app f y) = shift_down (.app f y) := subst_isar_no_occur h_occ_false x
        rw [h_sub]
        exact Relation.ReflTransGen.single (IStep.konstβ (shift_down (.app f y)) x)

theorem occurs0_shift_isar (d : Nat) (c : Nat) (t : ITerm) (hc : c > 0) :
    occurs0 (shift_isar d c t) = occurs0 t := by
  induction t with
  | var n =>
      simp only [shift_isar]
      split
      { rfl }
      { rename_i h
        cases n with
        | zero =>
            have h_lt : 0 < c := hc
            exact False.elim (h h_lt)
        | succ m =>
            have h_eq : m + 1 + d = Nat.succ (m + d) := Nat.succ_add m d
            rw [h_eq]
            rfl }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [shift_isar, occurs0, ihf, ihy]

theorem shift_down_shift_isar (d : Nat) (c : Nat) (t : ITerm) (h : occurs0 t = false) :
    shift_down (shift_isar d (c + 1) t) = shift_isar d c (shift_down t) := by
  induction t with
  | var n =>
      unfold occurs0 at h
      cases n with
      | zero => contradiction
      | succ m =>
          simp only [shift_isar]
          split
          { rename_i h1
            simp only [shift_down, shift_isar]
            split
            { rfl }
            { rename_i h2
              have h1' : m < c := Nat.lt_of_succ_lt_succ h1
              have h2' : ¬(m < c) := by
                rw [show Nat.succ m - 1 = m by rfl] at h2
                exact h2
              exact False.elim (h2' h1') } }
          { rename_i h1
            have h_eq : m + 1 + d = Nat.succ (m + d) := Nat.succ_add m d
            rw [h_eq]
            simp only [shift_down, shift_isar]
            split
            { rename_i h2
              have h1' : ¬(m < c) := by
                intro hm
                have : Nat.succ m < Nat.succ c := Nat.succ_lt_succ hm
                exact h1 this
              have h2' : m < c := by
                rw [show Nat.succ m - 1 = m by rfl] at h2
                exact h2
              exact False.elim (h1' h2') }
            { rfl } }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      unfold occurs0 at h
      have hf : occurs0 f = false := by
        cases hf_occ : occurs0 f with
        | true => simp [hf_occ] at h
        | false => rfl
      have hy : occurs0 y = false := by
        cases hy_occ : occurs0 y with
        | true => simp [hy_occ] at h
        | false => rfl
      simp [shift_isar, shift_down]
      exact ⟨ihf hf, ihy hy⟩

theorem abstract0_shift_isar (d : Nat) (c : Nat) (t : ITerm) :
    shift_isar d c (abstract0 t) = abstract0 (shift_isar d (c + 1) t) := by
  have hc : c + 1 > 0 := Nat.succ_pos c
  induction t with
  | var n =>
      by_cases hn0 : n = 0
      { subst hn0
        rfl }
      { have h_occ : occurs0 (ITerm.var n) = false := by
          cases n with
          | zero => contradiction
          | succ m => rfl
        have h_occ' : occurs0 (shift_isar d (c + 1) (ITerm.var n)) = false := by
          rw [occurs0_shift_isar d (c + 1) (ITerm.var n) hc]
          exact h_occ
        unfold abstract0
        rw [h_occ, h_occ']
        rw [shift_down_shift_isar d c (ITerm.var n) h_occ]
        simp [shift_isar] }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      by_cases h_occ : occurs0 (.app f y) = true
      { have h_occ' : occurs0 (shift_isar d (c + 1) (.app f y)) = true := by
          rw [occurs0_shift_isar d (c + 1) (.app f y) hc]
          exact h_occ
        unfold abstract0
        rw [h_occ, h_occ']
        have h_sh : shift_isar d (c + 1) (.app f y) = .app (shift_isar d (c + 1) f) (shift_isar d (c + 1) y) := rfl
        rw [h_sh]
        dsimp only
        have h_f : occurs0 (shift_isar d (c + 1) f) = occurs0 f := occurs0_shift_isar d (c + 1) f hc
        have h_y : occurs0 (shift_isar d (c + 1) y) = occurs0 y := occurs0_shift_isar d (c + 1) y hc
        rw [h_f, h_y]
        split
        { rename_i h1 h2
          simp [shift_down_shift_isar d c f h1, ihy, shift_isar] }
        { rename_i h_match
          simp [ihf, ihy, shift_isar] } }
      { have h_occ_false : occurs0 (.app f y) = false := by
          cases h : occurs0 (.app f y) with
          | true => contradiction
          | false => rfl
        have h_occ' : occurs0 (shift_isar d (c + 1) (.app f y)) = false := by
          rw [occurs0_shift_isar d (c + 1) (.app f y) hc]
          exact h_occ_false
        unfold abstract0
        rw [h_occ_false, h_occ']
        rw [shift_down_shift_isar d c (.app f y) h_occ_false]
        simp [shift_isar] }

theorem compile_shift (d c : Nat) (t : LTerm) :
    compile (shift d c t) = shift_isar d c (compile t) := by
  induction t generalizing c with
  | var n =>
      unfold shift
      split
      { unfold compile shift_isar
        split
        { rfl }
        { rename_i h h2
          exact False.elim (h2 h) } }
      { rename_i h
        unfold compile shift_isar
        split
        { rename_i h2
          exact False.elim (h h2) }
        { rfl } }
  | app f x ihf ihx =>
      simp [shift, compile, shift_isar, ihf, ihx]
  | abs body ih =>
      simp [shift, compile, abstract0_shift_isar, ih]

theorem shift_isar_add (c : Nat) (u : ITerm) :
    shift_isar (c + 1) 0 u = shift_isar 1 c (shift_isar c 0 u) := by
  induction u with
  | var n =>
      have h_lt0 : ¬(n < 0) := Nat.not_lt_zero n
      simp [shift_isar, h_lt0]
      split
      { rename_i h
        have : n + c >= c := Nat.le_add_left c n
        exact False.elim (Nat.not_lt_of_le this h) }
      { rfl }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [shift_isar, ihf, ihy]

theorem shift_down_shift_isar_coincide (c : Nat) (s : ITerm) :
    shift_down (shift_isar 1 c (shift_isar c 0 s)) = shift_isar c 0 s := by
  induction s with
  | var n =>
      have h_lt0 : ¬(n < 0) := Nat.not_lt_zero n
      simp [shift_isar, h_lt0]
      split
      { rename_i h
        have : n + c >= c := Nat.le_add_left c n
        exact False.elim (Nat.not_lt_of_le this h) }
      { simp [shift_down] }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [shift_isar, shift_down, ihf, ihy]

theorem occurs0_subst_isar (c : Nat) (x : ITerm) (hx : occurs0 x = false) (u : ITerm) :
    occurs0 (subst_isar_at (c + 1) x u) = occurs0 u := by
  induction u with
  | var n =>
      unfold subst_isar_at
      split
      { rfl }
      { rename_i h1
        split
        { rename_i h2
          subst h2
          exact hx }
        { rename_i h2
          cases n with
          | zero =>
              have h_lt : 0 < c + 1 := Nat.succ_pos c
              exact False.elim (h1 h_lt)
          | succ m =>
              cases m with
              | zero =>
                  have hc : c = 0 := by
                    cases c with
                    | zero => rfl
                    | succ k =>
                        have h_lt : 1 < Nat.succ (Nat.succ k) := Nat.succ_lt_succ (Nat.succ_pos k)
                        exact False.elim (h1 h_lt)
                  subst hc
                  exact False.elim (h2 rfl)
              | succ k => rfl } }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [subst_isar_at, occurs0, ihf, ihy]

theorem occurs0_special_X (c : Nat) (s : ITerm) :
    occurs0 (shift_isar 1 c (shift_isar c 0 s)) = false := by
  induction s with
  | var n =>
      have h_lt0 : ¬(n < 0) := Nat.not_lt_zero n
      simp only [shift_isar, h_lt0, ↓reduceIte]
      split
      { rename_i h
        have : n + c >= c := Nat.le_add_left c n
        have : ¬(n + c < c) := Nat.not_lt_of_le this
        contradiction }
      { rfl }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [shift_isar, occurs0, ihf, ihy]

theorem shift_down_subst_isar_special (c : Nat) (s : ITerm) (u : ITerm) (hu : occurs0 u = false) :
    shift_down (subst_isar_at (c + 1) (shift_isar 1 c (shift_isar c 0 s)) u) =
    subst_isar_at c (shift_isar c 0 s) (shift_down u) := by
  induction u with
  | var n =>
      unfold occurs0 at hu
      cases n with
      | zero => contradiction
      | succ m =>
          simp [subst_isar_at, shift_down]
          split
          { rfl }
          { rename_i h1
            split
            { exact shift_down_shift_isar_coincide c s }
            { cases m with
              | zero => rfl
              | succ k => rfl } }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      unfold occurs0 at hu
      have hf : occurs0 f = false := by
        cases h : occurs0 f with
        | false => rfl
        | true => simp [h] at hu
      have hy : occurs0 y = false := by
        cases h : occurs0 y with
        | false => rfl
        | true => simp [h] at hu
      simp [subst_isar_at, shift_down, ihf hf, ihy hy]

theorem abstract0_subst_isar_special (c : Nat) (s : ITerm) (u : ITerm) :
    abstract0 (subst_isar_at (c + 1) (shift_isar 1 c (shift_isar c 0 s)) u) =
    subst_isar_at c (shift_isar c 0 s) (abstract0 u) := by
  let X := shift_isar 1 c (shift_isar c 0 s)
  let Y := shift_isar c 0 s
  have hX : occurs0 X = false := occurs0_special_X c s
  induction u with
  | var n =>
      by_cases hn0 : n = 0
      { subst hn0
        have h_lt : 0 < c + 1 := Nat.succ_pos c
        simp only [subst_isar_at, abstract0, occurs0]
        rw [if_pos h_lt]
        rfl }
      { have h_occ : occurs0 (.var n) = false := by
          cases n with
          | zero => contradiction
          | succ m => rfl
        have h_occ' : occurs0 (subst_isar_at (c + 1) X (.var n)) = false := by
          rw [occurs0_subst_isar c X hX (.var n)]
          exact h_occ
        unfold abstract0
        rw [h_occ, h_occ']
        rw [shift_down_subst_isar_special c s (.var n) h_occ]
        simp only [subst_isar_at] }
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      by_cases h_occ : occurs0 (.app f y) = true
      { have h_occ' : occurs0 (subst_isar_at (c + 1) X (.app f y)) = true := by
          rw [occurs0_subst_isar c X hX (.app f y)]
          exact h_occ
        unfold abstract0
        rw [h_occ, h_occ']
        simp only [subst_isar_at]
        have h_f : occurs0 (subst_isar_at (c + 1) X f) = occurs0 f := occurs0_subst_isar c X hX f
        have h_y : occurs0 (subst_isar_at (c + 1) X y) = occurs0 y := occurs0_subst_isar c X hX y
        rw [h_f, h_y]
        split
        { rename_i h1 h2
          simp only [shift_down_subst_isar_special c s f h1, ihy, subst_isar_at] }
        { rename_i h_match
          simp only [ihf, ihy, subst_isar_at] } }
      { have h_occ_false : occurs0 (.app f y) = false := by
          cases h : occurs0 (.app f y) with
          | true => contradiction
          | false => rfl
        have h_occ' : occurs0 (subst_isar_at (c + 1) X (.app f y)) = false := by
          rw [occurs0_subst_isar c X hX (.app f y)]
          exact h_occ_false
        unfold abstract0
        rw [h_occ_false, h_occ']
        rw [shift_down_subst_isar_special c s (.app f y) h_occ_false]
        simp only [subst_isar_at] }

theorem compile_subst (s : LTerm) (c : Nat) (t : LTerm) :
    compile (subst s c t) = subst_isar_at c (shift_isar c 0 (compile s)) (compile t) := by
  induction t generalizing c with
  | var n =>
      dsimp [subst, compile, subst_isar_at]
      split
      { rfl }
      { rename_i h1
        split
        { rename_i h2
          subst h2
          rw [compile_shift] }
        { rfl } }
  | app f x ihf ihx =>
      simp [subst, compile, subst_isar_at, ihf, ihx]
  | abs body ih =>
      simp [subst, compile, shift_isar_add, abstract0_subst_isar_special, ih]

/- =========================================================
   4. Weak Beta Reduction Simulation Theorems
   ========================================================= -/

theorem shift_isar_zero (c : Nat) (s : ITerm) :
    shift_isar 0 c s = s := by
  induction s generalizing c with
  | var n =>
      simp [shift_isar]
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [shift_isar, ihf, ihy]

theorem subst_isar_eq_subst_isar_at_0 (x : ITerm) (t : ITerm) :
    subst_isar x t = subst_isar_at 0 x t := by
  induction t with
  | var n =>
      cases n with
      | zero => rfl
      | succ m => rfl
  | norm => rfl
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f y ihf ihy =>
      simp [subst_isar, subst_isar_at, ihf, ihy]

theorem compile_simulates_step {t u : LTerm} (h : LStep t u) :
    IRed (compile t) (compile u) := by
  induction h with
  | beta body s =>
      dsimp [compile]
      rw [compile_subst]
      rw [shift_isar_zero]
      rw [← subst_isar_eq_subst_isar_at_0]
      exact abstract_sound (compile body) (compile s)
  | appL hstep ih =>
      dsimp [compile]
      exact IRed_app_left ih
  | appR hstep ih =>
      dsimp [compile]
      exact IRed_app_right ih

theorem compile_simulates_red {t u : LTerm} (h : LRed t u) :
    IRed (compile t) (compile u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih (compile_simulates_step hstep)

end ISAR
