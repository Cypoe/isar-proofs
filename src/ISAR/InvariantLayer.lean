import ISAR.Kernel

open Relation

namespace ISAR

/-- The subtype of ISAR terms that belong to the pure SKI fragment. -/
def ISKSubtype := {t : ITerm // ISKTerm t}

/-- Two terms are operationally equivalent if they can reduce to a common term. -/
def OperEq (t u : ISKSubtype) : Prop :=
  ∃ v, IRed t.val v ∧ IRed u.val v

theorem OperEq.refl (t : ISKSubtype) : OperEq t t :=
  ⟨t.val, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem OperEq.symm {t u : ISKSubtype} (h : OperEq t u) : OperEq u t :=
  match h with
  | ⟨v, ht, hu⟩ => ⟨v, hu, ht⟩

theorem OperEq.trans {t u w : ISKSubtype} (h1 : OperEq t u) (h2 : OperEq u w) : OperEq t w := by
  match h1, h2 with
  | ⟨v1, ht, hu1⟩, ⟨v2, hu2, hw⟩ =>
      -- By confluence on the fragment, the two reductions from `u` can be joined.
      match ISAR.isar_fragment_confluence u.property hu1 hu2 with
      | ⟨z, hz1, hz2, _⟩ =>
          exact ⟨z, Relation.ReflTransGen.trans ht hz1, Relation.ReflTransGen.trans hw hz2⟩

instance operEqSetoid : Setoid ISKSubtype where
  r := OperEq
  iseqv := {
    refl := OperEq.refl
    symm := OperEq.symm
    trans := OperEq.trans
  }

/-- The Invariant Layer is defined as the operational equivalence quotient of the SKI fragment. -/
def InvariantLayer : Type := Quotient ISAR.operEqSetoid

/-- Application of raw fragment subtypes. -/
def app_raw (t u : ISKSubtype) : ISKSubtype :=
  ⟨ITerm.app t.val u.val, ISKTerm.app t.property u.property⟩

/-- Operational equivalence is a congruence under application. -/
theorem app_congruence (t1 t2 u1 u2 : ISKSubtype) (ht : OperEq t1 t2) (hu : OperEq u1 u2) :
    OperEq (app_raw t1 u1) (app_raw t2 u2) := by
  match ht, hu with
  | ⟨v1, ht1, ht2⟩, ⟨v2, hu1, hu2⟩ =>
      exact ⟨ITerm.app v1 v2, ISAR.IRed_app ht1 hu1, ISAR.IRed_app ht2 hu2⟩

/-- Application descends to a well-defined function on Invariant Layer quotient classes. -/
def InvariantLayer.app (t u : InvariantLayer) : InvariantLayer :=
  Quotient.lift₂ (fun t u => Quotient.mk _ (app_raw t u)) (by
    intro t1 u1 t2 u2 ht hu
    exact Quotient.sound (app_congruence t1 t2 u1 u2 ht hu)
  ) t u

/-- Canonical projection to the Invariant Layer. -/
def toInvariantLayer (t : ISKSubtype) : InvariantLayer :=
  Quotient.mk _ t

def HasNF (t : ISKSubtype) : Prop :=
  ∃ n : ISKSubtype, IRed t.val n.val ∧ NormalI n.val

theorem HasNF_of_OperEq {t u : ISKSubtype} (h : OperEq t u) (ht : ISAR.HasNF t) : ISAR.HasNF u := by
  match ht with
  | ⟨n, hn_red, hn_norm⟩ =>
      match h with
      | ⟨v, ht_red, hu_red⟩ =>
          match IRed_confluence hn_red ht_red with
          | ⟨w, hn_w, hv_w⟩ =>
              have heq := IRed_normal_eq hn_norm hn_w
              subst heq
              exact ⟨n, Relation.ReflTransGen.trans hu_red hv_w, hn_norm⟩

theorem OperEq_HasNF_eq {t u : ISKSubtype} (h : OperEq t u) : ISAR.HasNF t = ISAR.HasNF u :=
  propext ⟨HasNF_of_OperEq h, HasNF_of_OperEq (OperEq.symm h)⟩

def InvariantLayer.HasNF (q : InvariantLayer) : Prop :=
  Quotient.lift ISAR.HasNF (by
    intro t u h
    exact OperEq_HasNF_eq h
  ) q

open Classical

theorem ISKTerm_cd {t : ITerm} (ht : ISKTerm t) : ISKTerm (cd t) := by
  have h_ps := ParStep_cd t (ParStep.refl t)
  have h_ired := ParStep_to_IRed h_ps
  exact ISKTerm_IRed_preserved ht h_ired

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

partial def cd_loop (t : ISKSubtype) : ISKSubtype :=
  let t' := cd t.val
  if t.val = t' then
    t
  else
    cd_loop ⟨t', ISKTerm_cd t.property⟩

@[implemented_by cd_loop]
noncomputable def nf_of_term (t : ISKSubtype) : ISKSubtype :=
  if h : ISAR.HasNF t then
    Classical.choose h
  else
    ⟨ITerm.norm, ISKTerm.norm⟩

theorem unique_nf_of_OperEq {t u : ISKSubtype} (h : OperEq t u) :
    nf_of_term t = nf_of_term u := by
  by_cases ht : ISAR.HasNF t
  { have hu : ISAR.HasNF u := HasNF_of_OperEq h ht
    unfold nf_of_term
    rw [dif_pos ht, dif_pos hu]
    let n1 := Classical.choose ht
    let n2 := Classical.choose hu
    have h1 : IRed t.val n1.val ∧ NormalI n1.val := Classical.choose_spec ht
    have h2 : IRed u.val n2.val ∧ NormalI n2.val := Classical.choose_spec hu
    match h with
    | ⟨v, ht_red, hu_red⟩ =>
        match IRed_confluence h1.1 ht_red with
        | ⟨w1, hn1_w1, hv_w1⟩ =>
            have heq1 := IRed_normal_eq h1.2 hn1_w1
            have hv_n1 : IRed v n1.val := by
              rw [heq1]
              exact hv_w1
            match IRed_confluence h2.1 hu_red with
            | ⟨w2, hn2_w2, hv_w2⟩ =>
                have heq2 := IRed_normal_eq h2.2 hn2_w2
                have hv_n2 : IRed v n2.val := by
                  rw [heq2]
                  exact hv_w2
                match IRed_confluence hv_n1 hv_n2 with
                | ⟨w3, hn1_w3, hn2_w3⟩ =>
                    have heq3 := IRed_normal_eq h1.2 hn1_w3
                    have heq4 := IRed_normal_eq h2.2 hn2_w3
                    have h_val_eq : n1.val = n2.val := heq3.trans heq4.symm
                    exact Subtype.ext h_val_eq }
  { have hu : ¬ ISAR.HasNF u := fun h_u => ht (HasNF_of_OperEq (OperEq.symm h) h_u)
    unfold nf_of_term
    rw [dif_neg ht, dif_neg hu] }

noncomputable def InvariantLayer.canonical_rep (q : InvariantLayer) : ISKSubtype :=
  Quotient.lift nf_of_term (by
    intro t u h
    exact unique_nf_of_OperEq h
  ) q

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

def sufficient_fuel (t : ISKSubtype) : Nat := term_size t.val

theorem sufficient_fuel_correct (t : ISKSubtype) (ht : LinearIKTerm t.val) :
    HasNF (cd_loop_fuel (sufficient_fuel t) t) ∧
    NormalI (cd_loop_fuel (sufficient_fuel t) t).val :=
  cd_loop_fuel_spec (sufficient_fuel t) t ht (Nat.le_refl _)

end ISAR
