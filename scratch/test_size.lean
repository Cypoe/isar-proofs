import ISAR
import InvariantLayer

namespace ISAR

def term_size : ITerm → Nat
  | .var _ => 1
  | .norm | .konst | .dup | .swap | .comp | .sₛ => 1
  | .app f x => term_size f + term_size x + 1

inductive IKTerm : ITerm → Prop where
  | norm  : IKTerm .norm
  | konst : IKTerm .konst
  | app {f x : ITerm} : IKTerm f → IKTerm x → IKTerm (.app f x)

theorem cd_app_of_not_redex (f x : ITerm) (h1 : f ≠ .norm) (h2 : ∀ y, f ≠ .app .konst y)
    (h3 : ∀ y z, f ≠ .app (.app .comp y) z) (h4 : ∀ y z, f ≠ .app (.app .sₛ y) z) :
    cd (.app f x) = .app (cd f) (cd x) := by
  cases f with
  | var n => rfl
  | norm => contradiction
  | konst => rfl
  | dup => rfl
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f1 x1 =>
      cases f1 with
      | var n => rfl
      | norm => rfl
      | konst =>
          have h_contra := h2 x1
          contradiction
      | dup => rfl
      | swap => rfl
      | comp => rfl
      | sₛ => rfl
      | app f2 x2 =>
          cases f2 with
          | var n => rfl
          | norm => rfl
          | konst => rfl
          | dup => rfl
          | swap => rfl
          | comp =>
              have h_contra := h3 x2 x1
              contradiction
          | sₛ =>
              have h_contra := h4 x2 x1
              contradiction
          | app f3 x3 => rfl

theorem cd_size_le_IK (t : ITerm) (ht : IKTerm t) : term_size (cd t) ≤ term_size t :=
  match t with
  | .norm => Nat.le_refl _
  | .konst => Nat.le_refl _
  | .var _ => by cases ht
  | .dup => by cases ht
  | .swap => by cases ht
  | .comp => by cases ht
  | .sₛ => by cases ht
  | .app f x => by
      cases ht with | @app _ _ hf hx =>
      cases hf with
      | norm =>
          dsimp [cd, term_size]
          have ih := cd_size_le_IK x hx
          omega
      | konst =>
          dsimp [cd, term_size]
          have ih := cd_size_le_IK x hx
          omega
      | @app f1 x1 hf1 hx1 =>
          cases hf1 with
          | konst =>
              dsimp [cd, term_size]
              have ih1 := cd_size_le_IK x1 hx1
              omega
          | norm =>
              dsimp [cd, term_size]
              have ih1 := cd_size_le_IK x1 hx1
              have ih2 := cd_size_le_IK x hx
              omega
          | @app f2 x2 hf2 hx2 =>
              have h_eq : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) =
                          ITerm.app (cd (ITerm.app (ITerm.app f2 x2) x1)) (cd x) := by
                apply cd_app_of_not_redex
                { intro h; cases h }
                { intro y h; cases h }
                { intro y z h
                  injection h with h_left _
                  injection h_left with h_comp _
                  subst h_comp
                  cases hf2 }
                { intro y z h
                  injection h with h_left _
                  injection h_left with h_s _
                  subst h_s
                  cases hf2 }
              rw [h_eq]
              have hf_reconstructed : IKTerm (ITerm.app (ITerm.app f2 x2) x1) := IKTerm.app (IKTerm.app hf2 hx2) hx1
              have ih1 := cd_size_le_IK (ITerm.app (ITerm.app f2 x2) x1) hf_reconstructed
              have ih2 := cd_size_le_IK x hx
              dsimp [term_size] at ih1
              dsimp [term_size]
              omega

theorem cd_size_lt_IK (t : ITerm) (ht : IKTerm t) (h : t ≠ cd t) : term_size (cd t) < term_size t :=
  match t with
  | .norm => by contradiction
  | .konst => by contradiction
  | .var _ => by cases ht
  | .dup => by cases ht
  | .swap => by cases ht
  | .comp => by cases ht
  | .sₛ => by cases ht
  | .app f x => by
      cases ht with | @app _ _ hf hx =>
      cases hf with
      | norm =>
          dsimp [cd, term_size]
          have ih := cd_size_le_IK x hx
          omega
      | konst =>
          dsimp [cd, term_size]
          have h_ne : x ≠ cd x := by
            intro hc
            have hc2 : cd (ITerm.app ITerm.konst x) = ITerm.app ITerm.konst x := by
              dsimp [cd]
              rw [←hc]
            exact h hc2.symm
          have ih := cd_size_lt_IK x hx h_ne
          omega
      | @app f1 x1 hf1 hx1 =>
          cases hf1 with
          | konst =>
              dsimp [cd, term_size]
              have ih1 := cd_size_le_IK x1 hx1
              omega
          | norm =>
              dsimp [cd, term_size]
              have ih1 := cd_size_le_IK x1 hx1
              have ih2 := cd_size_le_IK x hx
              omega
          | @app f2 x2 hf2 hx2 =>
              have h_eq : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) =
                          ITerm.app (cd (ITerm.app (ITerm.app f2 x2) x1)) (cd x) := by
                apply cd_app_of_not_redex
                { intro h; cases h }
                { intro y h; cases h }
                { intro y z h
                  injection h with h_left _
                  injection h_left with h_comp _
                  subst h_comp
                  cases hf2 }
                { intro y z h
                  injection h with h_left _
                  injection h_left with h_s _
                  subst h_s
                  cases hf2 }
              have hf_reconstructed : IKTerm (ITerm.app (ITerm.app f2 x2) x1) := IKTerm.app (IKTerm.app hf2 hx2) hx1
              by_cases hf_eq : (ITerm.app (ITerm.app f2 x2) x1) = cd (ITerm.app (ITerm.app f2 x2) x1)
              { have h_ne : x ≠ cd x := by
                  intro hc
                  have hc2 : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) = ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x := by
                    rw [h_eq, ←hf_eq, ←hc]
                  exact h hc2.symm
                have ih1 := cd_size_le_IK (ITerm.app (ITerm.app f2 x2) x1) hf_reconstructed
                have ih2 := cd_size_lt_IK x hx h_ne
                rw [h_eq]
                dsimp [term_size] at ih1
                dsimp [term_size]
                omega }
              { have ih1 := cd_size_lt_IK (ITerm.app (ITerm.app f2 x2) x1) hf_reconstructed hf_eq
                have ih2 := cd_size_le_IK x hx
                rw [h_eq]
                dsimp [term_size] at ih1
                dsimp [term_size]
                omega }

def cd_loop_fuel (fuel : Nat) (t : ISKSubtype) : ISKSubtype :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
      let t' := cd t.val
      if t.val = t' then
        t
      else
        cd_loop_fuel fuel' ⟨t', ISKTerm_cd t.property⟩

theorem OperEq_cd_loop_fuel (fuel : Nat) (t : ISKSubtype) :
    OperEq (cd_loop_fuel fuel t) t := by
  induction fuel generalizing t with
  | zero =>
      dsimp [cd_loop_fuel]
      exact OperEq.refl t
  | succ fuel' ih =>
      dsimp [cd_loop_fuel]
      split
      { exact OperEq.refl t }
      { have ih_inst := ih ⟨cd t.val, ISKTerm_cd t.property⟩
        have h_ps := ParStep_cd t.val (ParStep.refl t.val)
        have h_ired := ParStep_to_IRed h_ps
        have h_eq : OperEq ⟨cd t.val, ISKTerm_cd t.property⟩ t := by
          exact ⟨cd t.val, Relation.ReflTransGen.refl, h_ired⟩
        exact OperEq.trans ih_inst h_eq }

theorem cd_loop_fuel_quotient_eq (fuel : Nat) (t : ISKSubtype) :
    toInvariantLayer (cd_loop_fuel fuel t) = toInvariantLayer t := by
  unfold toInvariantLayer
  exact Quotient.sound (OperEq_cd_loop_fuel fuel t)

end ISAR
