import ISAR
import InvariantLayer

namespace ISAR

def dupCount : ITerm → Nat
  | .dup         => 1
  | .app .dup _  => 0
  | .app f x     => dupCount f + dupCount x
  | _            => 0

inductive LinearIKTerm : ITerm → Prop where
  | norm  : LinearIKTerm .norm
  | konst : LinearIKTerm .konst
  | app {f x : ITerm} : LinearIKTerm f → LinearIKTerm x →
            dupCount (ITerm.app f x) = 0 →
            LinearIKTerm (ITerm.app f x)
  | app_dup {x : ITerm} :
      LinearIKTerm x →
      LinearIKTerm (ITerm.app .dup x)

theorem dupCount_of_LinearIKTerm {t : ITerm} (ht : LinearIKTerm t) : dupCount t = 0 := by
  induction ht with
  | norm => rfl
  | konst => rfl
  | app _ _ h_dup => exact h_dup
  | app_dup _ => rfl

theorem dupCount_app_of_zero {f x : ITerm} (h : dupCount f = 0) : dupCount (ITerm.app f x) = dupCount f + dupCount x := by
  cases f with
  | var n => rfl
  | norm => rfl
  | konst => rfl
  | dup => contradiction
  | swap => rfl
  | comp => rfl
  | sₛ => rfl
  | app f1 x1 => rfl

theorem dupCount_app {f x : ITerm} (hf : LinearIKTerm f) : dupCount (ITerm.app f x) = dupCount f + dupCount x := by
  cases hf with
  | norm => rfl
  | konst => rfl
  | app => rfl
  | app_dup => rfl

theorem cd_size_le_LinearIK (t : ITerm) (ht : LinearIKTerm t) : term_size (cd t) ≤ term_size t :=
  match t with
  | .norm => Nat.le_refl _
  | .konst => Nat.le_refl _
  | .dup => by cases ht
  | .var _ => by cases ht
  | .swap => by cases ht
  | .comp => by cases ht
  | .sₛ => by cases ht
  | .app f x => by
      cases ht with
      | app_dup hx =>
          dsimp [cd, term_size]
          have ih := cd_size_le_LinearIK x hx
          omega
      | app hf hx h_dup =>
          cases hf with
          | norm =>
              dsimp [cd, term_size]
              have ih := cd_size_le_LinearIK x hx
              omega
          | konst =>
              dsimp [cd, term_size]
              have ih := cd_size_le_LinearIK x hx
              omega
          | @app_dup x1 hx1 =>
              dsimp [cd, term_size]
              have ih1 := cd_size_le_LinearIK x1 hx1
              have ih2 := cd_size_le_LinearIK x hx
              omega
          | @app f1 x1 hf1 hx1 h_dup1 =>
              cases hf1 with
              | konst =>
                  dsimp [cd, term_size]
                  have ih1 := cd_size_le_LinearIK x1 hx1
                  omega
              | norm =>
                  dsimp [cd, term_size]
                  have ih1 := cd_size_le_LinearIK x1 hx1
                  have ih2 := cd_size_le_LinearIK x hx
                  omega
              | @app_dup x2 hx2 =>
                  dsimp [cd, term_size]
                  have ih1 := cd_size_le_LinearIK x2 hx2
                  have ih2 := cd_size_le_LinearIK x1 hx1
                  have ih3 := cd_size_le_LinearIK x hx
                  omega
              | @app f2 x2 hf2 hx2 h_dup2 =>
                  have h_eq : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) =
                              ITerm.app (cd (ITerm.app (ITerm.app f2 x2) x1)) (cd x) := by
                    apply cd_app_of_not_redex
                    { intro h_contra; cases h_contra }
                    { intro y h_contra; cases h_contra }
                    { intro y z h_contra
                      injection h_contra with h_left _
                      cases h_left; cases hf2 }
                    { intro y z h_contra
                      injection h_contra with h_left _
                      cases h_left; cases hf2 }
                  rw [h_eq]
                  have hf_reconstructed : LinearIKTerm (ITerm.app (ITerm.app f2 x2) x1) :=
                    LinearIKTerm.app (LinearIKTerm.app hf2 hx2 h_dup2) hx1 h_dup1
                  have ih1 := cd_size_le_LinearIK (ITerm.app (ITerm.app f2 x2) x1) hf_reconstructed
                  have ih2 := cd_size_le_LinearIK x hx
                  dsimp [term_size] at ih1
                  dsimp [term_size]
                  omega

theorem cd_size_lt_LinearIK (t : ITerm) (ht : LinearIKTerm t) (h : t ≠ cd t) : term_size (cd t) < term_size t :=
  match t with
  | .norm => by contradiction
  | .konst => by contradiction
  | .dup => by cases ht
  | .var _ => by cases ht
  | .swap => by cases ht
  | .comp => by cases ht
  | .sₛ => by cases ht
  | .app f x => by
      cases ht with
      | app_dup hx =>
          dsimp [cd, term_size]
          have h_ne : x ≠ cd x := by
            intro hc
            have hc2 : cd (ITerm.app .dup x) = ITerm.app .dup x := by
              dsimp [cd]
              rw [←hc]
            exact h hc2.symm
          have ih := cd_size_lt_LinearIK x hx h_ne
          omega
      | app hf hx h_dup =>
          cases hf with
          | norm =>
              dsimp [cd, term_size]
              have ih := cd_size_le_LinearIK x hx
              omega
          | konst =>
              dsimp [cd, term_size]
              have h_ne : x ≠ cd x := by
                intro hc
                have hc2 : cd (ITerm.app .konst x) = ITerm.app .konst x := by
                  dsimp [cd]
                  rw [←hc]
                exact h hc2.symm
              have ih := cd_size_lt_LinearIK x hx h_ne
              omega
          | @app_dup x1 hx1 =>
              dsimp [cd, term_size]
              by_cases hx1_eq : x1 = cd x1
              { by_cases hx_eq : x = cd x
                { have hc2 : cd (ITerm.app (ITerm.app .dup x1) x) = ITerm.app (ITerm.app .dup x1) x := by
                    dsimp [cd]
                    rw [←hx1_eq, ←hx_eq]
                  exact False.elim (h hc2.symm) }
                { have ih1 := cd_size_le_LinearIK x1 hx1
                  have ih2 := cd_size_lt_LinearIK x hx hx_eq
                  omega } }
              { have ih1 := cd_size_lt_LinearIK x1 hx1 hx1_eq
                have ih2 := cd_size_le_LinearIK x hx
                omega }
          | @app f1 x1 hf1 hx1 h_dup1 =>
              cases hf1 with
              | konst =>
                  dsimp [cd, term_size]
                  have ih1 := cd_size_le_LinearIK x1 hx1
                  omega
              | norm =>
                  dsimp [cd, term_size]
                  have ih1 := cd_size_le_LinearIK x1 hx1
                  have ih2 := cd_size_le_LinearIK x hx
                  omega
              | @app_dup x2 hx2 =>
                  dsimp [cd, term_size]
                  by_cases hx2_eq : x2 = cd x2
                  { by_cases hx1_eq : x1 = cd x1
                    { by_cases hx_eq : x = cd x
                      { have hc2 : cd (ITerm.app (ITerm.app (ITerm.app .dup x2) x1) x) =
                                  ITerm.app (ITerm.app (ITerm.app .dup x2) x1) x := by
                          dsimp [cd]
                          rw [←hx2_eq, ←hx1_eq, ←hx_eq]
                        exact False.elim (h hc2.symm) }
                      { have ih1 := cd_size_le_LinearIK x2 hx2
                        have ih2 := cd_size_le_LinearIK x1 hx1
                        have ih3 := cd_size_lt_LinearIK x hx hx_eq
                        omega } }
                    { have ih1 := cd_size_le_LinearIK x2 hx2
                      have ih2 := cd_size_lt_LinearIK x1 hx1 hx1_eq
                      have ih3 := cd_size_le_LinearIK x hx
                      omega } }
                  { have ih1 := cd_size_lt_LinearIK x2 hx2 hx2_eq
                    have ih2 := cd_size_le_LinearIK x1 hx1
                    have ih3 := cd_size_le_LinearIK x hx
                    omega }
              | @app f2 x2 hf2 hx2 h_dup2 =>
                  have h_eq : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) =
                              ITerm.app (cd (ITerm.app (ITerm.app f2 x2) x1)) (cd x) := by
                    apply cd_app_of_not_redex
                    { intro h_contra; cases h_contra }
                    { intro y h_contra; cases h_contra }
                    { intro y z h_contra
                      injection h_contra with h_left _
                      cases h_left; cases hf2 }
                    { intro y z h_contra
                      injection h_contra with h_left _
                      cases h_left; cases hf2 }
                  rw [h_eq]
                  have hf_reconstructed : LinearIKTerm (ITerm.app (ITerm.app f2 x2) x1) :=
                    LinearIKTerm.app (LinearIKTerm.app hf2 hx2 h_dup2) hx1 h_dup1
                  by_cases hf_eq : (ITerm.app (ITerm.app f2 x2) x1) = cd (ITerm.app (ITerm.app f2 x2) x1)
                  { have h_ne : x ≠ cd x := by
                      intro hc
                      have hc2 : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) = ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x := by
                        rw [h_eq, ←hf_eq, ←hc]
                      exact h hc2.symm
                    have ih1 := cd_size_le_LinearIK (ITerm.app (ITerm.app f2 x2) x1) hf_reconstructed
                    have ih2 := cd_size_lt_LinearIK x hx h_ne
                    dsimp [term_size] at ih1
                    dsimp [term_size]
                    omega }
                  { have ih1 := cd_size_lt_LinearIK (ITerm.app (ITerm.app f2 x2) x1) hf_reconstructed hf_eq
                    have ih2 := cd_size_le_LinearIK x hx
                    dsimp [term_size] at ih1
                    dsimp [term_size]
                    omega }

theorem LinearIKTerm_cd {t : ITerm} (ht : LinearIKTerm t) : LinearIKTerm (cd t) := by
  induction ht with
  | norm => exact LinearIKTerm.norm
  | konst => exact LinearIKTerm.konst
  | app_dup hx ihx =>
      rename_i x
      exact LinearIKTerm.app_dup ihx
  | app hf hx h_dup ihf ihx =>
      rename_i f x
      cases hf with
      | norm =>
          exact ihx
      | konst =>
          apply LinearIKTerm.app
          { exact LinearIKTerm.konst }
          { exact ihx }
          { dsimp [cd, dupCount]
            have hx_zero := dupCount_of_LinearIKTerm ihx
            omega }
      | app_dup =>
          rename_i x1 hx1
          apply LinearIKTerm.app
          { exact ihf }
          { exact ihx }
          { dsimp [cd, dupCount]
            have hx_zero := dupCount_of_LinearIKTerm ihx
            omega }
      | app =>
          rename_i f1 x1 hf1 hx1 h_dup1
          cases hf1 with
          | norm =>
              apply LinearIKTerm.app
              { exact ihf }
              { exact ihx }
              { rw [dupCount_app ihf]
                have hf_zero := dupCount_of_LinearIKTerm ihf
                have hx_zero := dupCount_of_LinearIKTerm ihx
                omega }
          | konst =>
              cases ihf
              assumption
          | app_dup =>
              rename_i x2 hx2
              apply LinearIKTerm.app
              { exact ihf }
              { exact ihx }
              { rw [dupCount_app ihf]
                have hf_zero := dupCount_of_LinearIKTerm ihf
                have hx_zero := dupCount_of_LinearIKTerm ihx
                omega }
          | app =>
              rename_i f2 x2 hf2 hx2 h_dup2
              have h_eq : cd (ITerm.app (ITerm.app (ITerm.app f2 x2) x1) x) =
                          ITerm.app (cd (ITerm.app (ITerm.app f2 x2) x1)) (cd x) := by
                apply cd_app_of_not_redex
                { intro h_contra; cases h_contra }
                { intro y h_contra; cases h_contra }
                { intro y z h_contra; injection h_contra with hl _; cases hl; cases hf2 }
                { intro y z h_contra; injection h_contra with hl _; cases hl; cases hf2 }
              rw [h_eq]
              apply LinearIKTerm.app
              { exact ihf }
              { exact ihx }
              { rw [dupCount_app ihf]
                have hf_zero := dupCount_of_LinearIKTerm ihf
                have hx_zero := dupCount_of_LinearIKTerm ihx
                omega }

theorem cd_app_of_LinearIKTerm {f : ITerm} (x : ITerm) (hf : LinearIKTerm f)
    (h_norm : f ≠ .norm) (h_konst : ∀ y, f ≠ ITerm.app .konst y) :
    cd (ITerm.app f x) = ITerm.app (cd f) (cd x) := by
  apply cd_app_of_not_redex
  { exact h_norm }
  { exact h_konst }
  { intro y z h_contra
    have h_linear : LinearIKTerm (ITerm.app (ITerm.app .comp y) z) := by
      rw [←h_contra]
      exact hf
    cases h_linear with
    | app hf1 hx1 h_dup1 =>
        cases hf1 with
        | app hf2 hx2 h_dup2 =>
            cases hf2 }
  { intro y z h_contra
    have h_linear : LinearIKTerm (ITerm.app (ITerm.app .sₛ y) z) := by
      rw [←h_contra]
      exact hf
    cases h_linear with
    | app hf1 hx1 h_dup1 =>
        cases hf1 with
        | app hf2 hx2 h_dup2 =>
            cases hf2 }

theorem normal_of_cd_eq (t : ITerm) (ht : LinearIKTerm t) (h : t = cd t) : NormalI t := by
  intro u hstep
  induction ht generalizing u with
  | norm => cases hstep
  | konst => cases hstep
  | app_dup hx ihx =>
      rename_i x
      dsimp [cd] at h
      injection h with _ hx_eq
      cases hstep with
      | appL hf' => cases hf'
      | appR hx' =>
          have h_norm := ihx hx_eq _ hx'
          cases h_norm
  | app hf hx h_dup ihf ihx =>
      rename_i f x
      cases hstep with
      | normβ =>
          dsimp [cd] at h
          have h_sz := congrArg term_size h
          dsimp [term_size] at h_sz
          have h_le := cd_size_le_LinearIK x hx
          omega
      | konstβ =>
          dsimp [cd] at h
          have h_sz := congrArg term_size h
          dsimp [term_size] at h_sz
          have h_le := cd_size_le_LinearIK u (by
            cases hf with
            | app _ hx_arg _ => exact hx_arg)
          omega
      | compβ =>
          cases hf with
          | app hf1 hx1 h_dup1 =>
              cases hf1 with
              | app hf2 hx2 h_dup2 =>
                  cases hf2
      | sβ =>
          cases hf with
          | app hf1 hx1 h_dup1 =>
              cases hf1 with
              | app hf2 hx2 h_dup2 =>
                  cases hf2
      | appL hf' =>
          by_cases h_konst : ∃ y, f = ITerm.app .konst y
          { match h_konst with
            | ⟨y_val, hy⟩ =>
                subst hy
                dsimp [cd] at h
                have h_sz := congrArg term_size h
                dsimp [term_size] at h_sz
                have h_le := cd_size_le_LinearIK y_val (by
                  cases hf with
                  | app _ h_y _ => exact h_y)
                omega }
          { have h_fn_norm : f ≠ .norm := by
              intro hc; subst hc; cases hf'
            have h_fn_konst : ∀ y, f ≠ ITerm.app .konst y := by
              intro y hc; exact h_konst ⟨y, hc⟩
            have h_eq := cd_app_of_LinearIKTerm x hf h_fn_norm h_fn_konst
            by_cases hf_eq : f = cd f
            { have h_norm := ihf hf_eq _ hf'
              cases h_norm }
            { have h_lt := cd_size_lt_LinearIK f hf hf_eq
              have h_le := cd_size_le_LinearIK x hx
              rw [h_eq] at h
              have h_sz := congrArg term_size h
              dsimp [term_size] at h_sz
              omega } }
      | appR hx' =>
          by_cases h_norm : f = .norm
          { subst h_norm
            dsimp [cd] at h
            have h_sz := congrArg term_size h
            dsimp [term_size] at h_sz
            have h_le := cd_size_le_LinearIK x hx
            omega }
          { by_cases h_konst : ∃ y, f = ITerm.app .konst y
            { match h_konst with
              | ⟨y_val, hy⟩ =>
                  subst hy
                  dsimp [cd] at h
                  have h_sz := congrArg term_size h
                  dsimp [term_size] at h_sz
                  have h_le := cd_size_le_LinearIK y_val (by
                    cases hf with
                    | app _ h_y _ => exact h_y)
                  omega }
            { have h_fn_konst : ∀ y, f ≠ ITerm.app .konst y := by
                intro y hc; exact h_konst ⟨y, hc⟩
              have h_eq := cd_app_of_LinearIKTerm x hf h_norm h_fn_konst
              by_cases hx_eq : x = cd x
              { have h_norm' := ihx hx_eq _ hx'
                cases h_norm' }
              { have h_lt := cd_size_lt_LinearIK x hx hx_eq
                have h_le := cd_size_le_LinearIK f hf
                rw [h_eq] at h
                have h_sz := congrArg term_size h
                dsimp [term_size] at h_sz
                omega } } }

theorem cd_loop_fuel_spec (n : Nat) (t : ISKSubtype) (ht : LinearIKTerm t.val) (hn : term_size t.val ≤ n) :
    HasNF (cd_loop_fuel n t) ∧ NormalI (cd_loop_fuel n t).val := by
  induction n generalizing t with
  | zero =>
      have h_sz := term_size t.val
      have h_sz_ge : term_size t.val ≥ 1 := by
        cases t.val <;> dsimp [term_size] <;> omega
      omega
  | succ n' ih =>
      dsimp [cd_loop_fuel]
      split
      { rename_i h_eq
        have h_norm := normal_of_cd_eq t.val ht h_eq
        refine ⟨⟨t, Relation.ReflTransGen.refl, h_norm⟩, h_norm⟩ }
      { rename_i h_ne
        have h_sz_lt := cd_size_lt_LinearIK t.val ht h_ne
        have ht'_linear := LinearIKTerm_cd ht
        have hn' : term_size (cd t.val) ≤ n' := by omega
        exact ih ⟨cd t.val, ISKTerm_cd t.property⟩ ht'_linear hn' }

theorem sufficient_fuel_correct (t : ISKSubtype) (ht : LinearIKTerm t.val) :
    HasNF (cd_loop_fuel (term_size t.val) t) ∧
    NormalI (cd_loop_fuel (term_size t.val) t).val :=
  cd_loop_fuel_spec (term_size t.val) t ht (Nat.le_refl _)

end ISAR
