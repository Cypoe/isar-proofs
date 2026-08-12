import ISAR.InvariantLayer

namespace ISAR

/-!
# Canonical representatives via complete development

Representative selection for `OperEq`-classes should be given by the complete-development
function `cd` (iterated as `cd_loop_fuel`), not by `Quotient.out` / unconstrained
`Classical.choose`. Unique normal forms on the fragment make the choice well-defined.
-/

/-- One complete-development step, packed as an `ISKSubtype`. -/
def cd_rep (t : ISKSubtype) : ISKSubtype :=
  ⟨cd t.val, ISKTerm_cd t.property⟩

theorem OperEq_cd_rep (t : ISKSubtype) : OperEq (cd_rep t) t := by
  have h_ps := ParStep_cd t.val (ParStep.refl t.val)
  have h_ired := ParStep_to_IRed h_ps
  exact ⟨cd t.val, Relation.ReflTransGen.refl, h_ired⟩

/-- Fuelled complete development as an explicit choice function on terms. -/
def canonical_nf_fuel (fuel : Nat) (t : ISKSubtype) : ISKSubtype :=
  cd_loop_fuel fuel t

theorem canonical_nf_fuel_OperEq (fuel : Nat) (t : ISKSubtype) :
    OperEq (canonical_nf_fuel fuel t) t :=
  OperEq_cd_loop_fuel fuel t

/-- Linear fragment: enough fuel is `term_size`, and the result is a normal form. -/
def canonical_nf (t : ISKSubtype) (_ht : LinearIKTerm t.val) : ISKSubtype :=
  cd_loop_fuel (sufficient_fuel t) t

theorem canonical_nf_OperEq (t : ISKSubtype) (ht : LinearIKTerm t.val) :
    OperEq (canonical_nf t ht) t :=
  OperEq_cd_loop_fuel (sufficient_fuel t) t

theorem canonical_nf_normal (t : ISKSubtype) (ht : LinearIKTerm t.val) :
    NormalI (canonical_nf t ht).val :=
  (sufficient_fuel_correct t ht).2

theorem IRed_of_OperEq_normal {t n : ISKSubtype}
    (h : OperEq n t) (hn : NormalI n.val) : IRed t.val n.val := by
  rcases h with ⟨v, hn_v, ht_v⟩
  have heq := IRed_normal_eq hn hn_v
  simpa [heq] using ht_v

theorem IRed_canonical_nf (t : ISKSubtype) (ht : LinearIKTerm t.val) :
    IRed t.val (canonical_nf t ht).val :=
  IRed_of_OperEq_normal (canonical_nf_OperEq t ht) (canonical_nf_normal t ht)

/-- OperEq-classes share a unique normal form; `canonical_nf` is that representative. -/
theorem canonical_nf_unique {t u : ISKSubtype}
    (ht : LinearIKTerm t.val) (hu : LinearIKTerm u.val) (h : OperEq t u) :
    (canonical_nf t ht).val = (canonical_nf u hu).val := by
  have ht_nf := IRed_canonical_nf t ht
  have hu_nf := IRed_canonical_nf u hu
  have hn_t := canonical_nf_normal t ht
  have hn_u := canonical_nf_normal u hu
  rcases h with ⟨v, ht_v, hu_v⟩
  rcases IRed_confluence hu_v hu_nf with ⟨w, hv_w, hnf_u_w⟩
  have heq_u := IRed_normal_eq hn_u hnf_u_w
  have hv_nfu : IRed v (canonical_nf u hu).val := by
    simpa [heq_u] using hv_w
  have ht_nfu : IRed t.val (canonical_nf u hu).val :=
    Relation.ReflTransGen.trans ht_v hv_nfu
  exact isar_fragment_unique_normal_forms t.property ht_nf hn_t ht_nfu hn_u

theorem canonical_nf_unique_subtype {t u : ISKSubtype}
    (ht : LinearIKTerm t.val) (hu : LinearIKTerm u.val) (h : OperEq t u) :
    canonical_nf t ht = canonical_nf u hu :=
  Subtype.ext (canonical_nf_unique ht hu h)

/--
OperEq between a fuelled development and the original term — the representative theorem
used by computable kernels (`ComputableISAR_Kernel`).
-/
theorem cd_is_OperEq_representative (fuel : Nat) (t : ISKSubtype) :
    OperEq (cd_loop_fuel fuel t) t :=
  OperEq_cd_loop_fuel fuel t

/--
Under `HasNF`, the AC `nf_of_term` representative is `OperEq`-related to `t`.
This replaces the unchecked `canonical_rep_eq` axiom for the normalizing case.
-/
theorem nf_of_term_OperEq_of_HasNF (t : ISKSubtype) (ht : HasNF t) :
    OperEq (nf_of_term t) t := by
  unfold nf_of_term
  rw [dif_pos ht]
  have hspec := Classical.choose_spec ht
  exact ⟨(Classical.choose ht).val, Relation.ReflTransGen.refl, hspec.1⟩

theorem canonical_rep_eq_of_HasNF (t : ISKSubtype) (ht : HasNF t) :
    OperEq (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid t)) t := by
  change OperEq (nf_of_term t) t
  exact nf_of_term_OperEq_of_HasNF t ht

/-- Linear terms always have a normal form via `canonical_nf`. -/
theorem HasNF_of_LinearIKTerm (t : ISKSubtype) (ht : LinearIKTerm t.val) : HasNF t :=
  ⟨canonical_nf t ht, IRed_canonical_nf t ht, canonical_nf_normal t ht⟩

theorem canonical_rep_eq_of_LinearIKTerm (t : ISKSubtype) (ht : LinearIKTerm t.val) :
    OperEq (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid t)) t :=
  canonical_rep_eq_of_HasNF t (HasNF_of_LinearIKTerm t ht)

/-- Fuelled section on concrete terms (fully computable; no quotient out). -/
def section_fuel (fuel : Nat) (t : ISKSubtype) : ISKSubtype :=
  cd_loop_fuel fuel t

theorem section_fuel_OperEq (fuel : Nat) (t : ISKSubtype) :
    OperEq (section_fuel fuel t) t :=
  OperEq_cd_loop_fuel fuel t

/--
General `canonical_rep` coherence. Special cases `HasNF` / `LinearIKTerm` are theorems above;
the unrestricted statement remains an axiom used by HF/views until full normalization is settled.
-/
axiom canonical_rep_eq (t : ISKSubtype) :
    OperEq (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid t)) t

theorem canonical_rep_sound (q : InvariantLayer) :
    Quotient.mk operEqSetoid (InvariantLayer.canonical_rep q) = q := by
  induction q using Quotient.ind with | _ t =>
    dsimp [InvariantLayer.canonical_rep]
    exact Quotient.sound (canonical_rep_eq t)

end ISAR
