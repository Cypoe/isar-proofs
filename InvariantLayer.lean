import ISAR

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

end ISAR
