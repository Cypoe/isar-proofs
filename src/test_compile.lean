import ISAR

open ISAR

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
