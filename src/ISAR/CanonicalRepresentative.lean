import ISAR.InvariantLayer

namespace ISAR

/-!
# Canonical representatives via complete development

Representative selection for `OperEq`-classes should be given by the complete-development
function `cd` (iterated as `cd_loop_fuel`) on the `HasNF` fragment, not by
unconstrained choice of a dummy. Unique normal forms make that choice well-defined.
For non-WN terms, `nf_of_term` falls back to `Quotient.exists_rep` choice (still OperEq-related).
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
-/
theorem nf_of_term_OperEq_of_HasNF (t : ISKSubtype) (ht : HasNF t) :
    OperEq (nf_of_term t) t :=
  nf_of_term_OperEq t

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
Unrestricted coherence of `canonical_rep`: always OperEq-related to the class.
Proved once `nf_of_term` uses NF when available and a class representative via
`Quotient.exists_rep` otherwise (never the old false `⟨norm,_⟩` fallback). Preferred
explicit section on the linear fragment remains `canonical_nf` / `cd_loop_fuel`.
-/
theorem canonical_rep_eq (t : ISKSubtype) :
    OperEq (InvariantLayer.canonical_rep (Quotient.mk operEqSetoid t)) t := by
  change OperEq (nf_of_term t) t
  exact nf_of_term_OperEq t

theorem canonical_rep_sound (q : InvariantLayer) :
    Quotient.mk operEqSetoid (InvariantLayer.canonical_rep q) = q := by
  induction q using Quotient.ind with | _ t =>
    dsimp [InvariantLayer.canonical_rep]
    exact Quotient.sound (canonical_rep_eq t)

/-! ### Finite `cd` as a unique section — and the ¬SN obstruction

`HasNF` is weak normalization: some `IRed` sequence hits a unique NF (confluence).
SKI is not SN, so `term_size` is not a fuel bound once `sβ` can grow. Iterated
`cd` is still a *normalizing* strategy: a length-indexed strip against complete
development shows that any parallel chain to an NF yields a fuel for
`cd_loop_fuel`. For `¬HasNF`, no fuel yields `NormalI` (expected: SKI is not SN);
that is not a gap. `nf_of_term` remains the AC section used by `canonical_rep`
(`Classical.choose` on `HasNF`, `exists_rep` otherwise) and is not claimed
computable. The linear fragment additionally gives an explicit bound `term_size`.
-/

/-- Length-indexed parallel reduction (head form, for induction on the first step). -/
inductive ParN : Nat → ITerm → ITerm → Prop where
  | zero (t : ITerm) : ParN 0 t t
  | succ {k : Nat} {t u v : ITerm} :
      ParStep t u → ParN k u v → ParN (k + 1) t v

theorem ParStep_eq_of_NormalI {n u : ITerm} (hn : NormalI n) (h : ParStep n u) :
    n = u :=
  IRed_normal_eq hn (ParStep_to_IRed h)

theorem ParN_trans {k m : Nat} {t u v : ITerm}
    (h1 : ParN k t u) (h2 : ParN m u v) : ParN (k + m) t v := by
  induction h1 with
  | zero _ =>
      simpa using h2
  | succ hstep _rest ih =>
      simpa [Nat.succ_add] using ParN.succ hstep (ih h2)

theorem ParN_single {t u : ITerm} (h : ParStep t u) : ParN 1 t u :=
  ParN.succ h (ParN.zero u)

theorem ParN_of_ParTransGen {t n : ITerm}
    (h : Relation.ReflTransGen ParStep t n) : ∃ k, ParN k t n := by
  induction h with
  | refl => exact Exists.intro 0 (ParN.zero t)
  | tail _hred hstep ih =>
      exact Exists.elim ih fun k hk =>
        Exists.intro (k + 1) (ParN_trans hk (ParN_single hstep))

/-- Diamond strip: one parallel step vs a `k`-chain, length preserved. -/
theorem ParN_strip {k : Nat} {t u n : ITerm}
    (h : ParStep t u) (p : ParN k t n) :
    ∃ n', ParN k u n' ∧ ParStep n n' := by
  induction p generalizing u with
  | zero t => exact Exists.intro u ⟨ParN.zero u, h⟩
  | succ hstep rest ih =>
      rcases ParStep_diamond h hstep with ⟨w, huw, htw⟩
      rcases ih htw with ⟨n', hn', hnn'⟩
      exact Exists.intro n' ⟨ParN.succ huw hn', hnn'⟩

theorem cd_loop_fuel_eq_of_cd_eq (fuel : Nat) (t : ISKSubtype)
    (h : t.val = cd t.val) : cd_loop_fuel fuel t = t := by
  cases fuel with
  | zero => rfl
  | succ _ =>
      dsimp [cd_loop_fuel]
      split
      { rfl }
      { rename_i hne
        exact (hne h).elim }

/-- Gross–Knuth: a parallel chain of length `k` to an NF is fuel for `cd_loop_fuel`. -/
theorem cd_loop_fuel_normal_of_ParN (t : ISKSubtype) (n : ITerm) (k : Nat)
    (p : ParN k t.val n) (hn : NormalI n) :
    NormalI (cd_loop_fuel k t).val := by
  induction k generalizing t n with
  | zero =>
      cases p
      simpa [cd_loop_fuel] using hn
  | succ k' ih =>
      cases p with
      | @succ _ _ u _ hstep rest =>
          dsimp [cd_loop_fuel]
          split
          { rename_i h_eq
            have h_to_t : ParStep u t.val :=
              (Eq.symm h_eq) ▸ ParStep_cd t.val hstep
            rcases ParN_strip h_to_t rest with ⟨n', hn', hnn'⟩
            have hn'_eq : n = n' := ParStep_eq_of_NormalI hn hnn'
            have h_short : ParN k' t.val n := hn'_eq.symm ▸ hn'
            have h_loop := ih t n h_short hn
            rw [cd_loop_fuel_eq_of_cd_eq k' t h_eq] at h_loop
            exact h_loop }
          { rename_i h_ne
            have h_cd : ParStep u (cd t.val) := ParStep_cd t.val hstep
            rcases ParN_strip h_cd rest with ⟨n', hn', hnn'⟩
            have hn'_eq : n = n' := ParStep_eq_of_NormalI hn hnn'
            have h_short : ParN k' (cd t.val) n := hn'_eq.symm ▸ hn'
            exact ih ⟨cd t.val, ISKTerm_cd t.property⟩ n h_short hn }

/-- `HasNF` classes have a unique normal-form representative. -/
theorem unique_normal_form_of_HasNF (t : ISKSubtype) (ht : HasNF t) :
    ∃ n : ISKSubtype, (IRed t.val n.val ∧ NormalI n.val) ∧
      ∀ m : ISKSubtype, IRed t.val m.val ∧ NormalI m.val → m = n := by
  rcases ht with ⟨n, hn_red, hn_nf⟩
  refine ⟨n, And.intro ⟨hn_red, hn_nf⟩ ?_⟩
  intro m hm
  exact Subtype.ext
    (isar_fragment_unique_normal_forms t.property hm.left hm.right hn_red hn_nf)

/-- Any fuel that lands on a normal form is a `HasNF` witness. -/
theorem HasNF_of_cd_loop_fuel_normal (t : ISKSubtype) {fuel : Nat}
    (hn : NormalI (cd_loop_fuel fuel t).val) : HasNF t :=
  ⟨cd_loop_fuel fuel t, IRed_of_OperEq_normal (OperEq_cd_loop_fuel fuel t) hn, hn⟩

/-- Obstruction: if there is no NF, finite complete development never produces one. -/
theorem cd_loop_fuel_not_normal_of_not_HasNF (t : ISKSubtype) (ht : ¬HasNF t)
    (fuel : Nat) : ¬NormalI (cd_loop_fuel fuel t).val :=
  fun hn => ht (HasNF_of_cd_loop_fuel_normal t hn)

theorem not_HasNF_no_finite_cd_NF (t : ISKSubtype) (ht : ¬HasNF t) :
    ∀ fuel, ¬NormalI (cd_loop_fuel fuel t).val :=
  cd_loop_fuel_not_normal_of_not_HasNF t ht

/-- Weak normalization iff some finite iterate of `cd` is a normal form. -/
theorem finite_cd_reaches_NF_iff (t : ISKSubtype) :
    HasNF t ↔ (∃ k : Nat, NormalI (cd_loop_fuel k t).val) :=
  Iff.intro
    (fun ht =>
      Exists.elim ht fun n hn =>
        Exists.elim (ParN_of_ParTransGen (IRed_to_ParTransGen hn.left)) fun k hk =>
          Exists.intro k (cd_loop_fuel_normal_of_ParN t n.val k hk hn.right))
    (fun h =>
      Exists.elim h fun k hk => HasNF_of_cd_loop_fuel_normal (fuel := k) t hk)

theorem HasNF_cd_loop_fuel (t : ISKSubtype) (ht : HasNF t) :
    ∃ k : Nat, NormalI (cd_loop_fuel k t).val :=
  (finite_cd_reaches_NF_iff t).mp ht

/-- Linear fragment: same iff, with explicit fuel `term_size`. -/
theorem finite_cd_reaches_NF_iff_of_Linear (t : ISKSubtype)
    (_ht : LinearIKTerm t.val) :
    HasNF t ↔ (∃ k : Nat, NormalI (cd_loop_fuel k t).val) :=
  finite_cd_reaches_NF_iff t

theorem sufficient_fuel_reaches_NF_of_Linear (t : ISKSubtype)
    (ht : LinearIKTerm t.val) :
    NormalI (cd_loop_fuel (sufficient_fuel t) t).val :=
  (sufficient_fuel_correct t ht).2

/-- On the linear fragment the fuelled section *is* the unique NF. -/
theorem canonical_nf_unique_section (t : ISKSubtype) (ht : LinearIKTerm t.val)
    (n : ISKSubtype) (hn : IRed t.val n.val ∧ NormalI n.val) :
    n.val = (canonical_nf t ht).val :=
  isar_fragment_unique_normal_forms t.property hn.1 hn.2
    (IRed_canonical_nf t ht) (canonical_nf_normal t ht)

/-- Under `HasNF`, some fuel of `cd` is the unique NF (not merely some NF). -/
theorem cd_loop_fuel_unique_section_of_HasNF (t : ISKSubtype) (ht : HasNF t)
    (n : ISKSubtype) (hn : IRed t.val n.val ∧ NormalI n.val) :
    ∃ k : Nat, (cd_loop_fuel k t).val = n.val :=
  Exists.elim (HasNF_cd_loop_fuel t ht) fun k hk =>
    Exists.intro k
      (isar_fragment_unique_normal_forms t.property
        (IRed_of_OperEq_normal (OperEq_cd_loop_fuel k t) hk) hk hn.left hn.right)

/-- Explicit Gross–Knuth section: the fuel is a parameter, not a chosen NF. -/
def nf_of_HasNF_fuel (t : ISKSubtype) (k : Nat)
    (_hk : NormalI (cd_loop_fuel k t).val) : ISKSubtype :=
  cd_loop_fuel k t

theorem nf_of_HasNF_fuel_normal (t : ISKSubtype) (k : Nat)
    (hk : NormalI (cd_loop_fuel k t).val) :
    NormalI (nf_of_HasNF_fuel t k hk).val :=
  hk

theorem nf_of_HasNF_fuel_OperEq (t : ISKSubtype) (k : Nat)
    (hk : NormalI (cd_loop_fuel k t).val) :
    OperEq (nf_of_HasNF_fuel t k hk) t :=
  OperEq_cd_loop_fuel k t

/-- Computational HasNF section: choice picks *fuel*, then the representative is
    `cd_loop_fuel`. Still not a computable `nf_of_term`; that AC section is what
    `canonical_rep` uses. `¬HasNF` remains `exists_rep` there (expected, not a gap). -/
noncomputable def nf_of_HasNF (t : ISKSubtype) (ht : HasNF t) : ISKSubtype :=
  cd_loop_fuel (Classical.choose (HasNF_cd_loop_fuel t ht)) t

theorem nf_of_HasNF_normal (t : ISKSubtype) (ht : HasNF t) :
    NormalI (nf_of_HasNF t ht).val :=
  Classical.choose_spec (HasNF_cd_loop_fuel t ht)

theorem nf_of_HasNF_OperEq (t : ISKSubtype) (ht : HasNF t) :
    OperEq (nf_of_HasNF t ht) t :=
  OperEq_cd_loop_fuel (Classical.choose (HasNF_cd_loop_fuel t ht)) t

theorem nf_of_HasNF_eq_nf_of_term (t : ISKSubtype) (ht : HasNF t) :
    (nf_of_HasNF t ht).val = (nf_of_term t).val := by
  have hn := nf_of_HasNF_normal t ht
  have hred := IRed_of_OperEq_normal (nf_of_HasNF_OperEq t ht) hn
  have hterm : nf_of_term t = Classical.choose ht := by
    unfold nf_of_term
    rw [dif_pos ht]
  have hspec : IRed t.val (Classical.choose ht).val ∧ NormalI (Classical.choose ht).val :=
    Classical.choose_spec ht
  simpa [hterm] using
    (isar_fragment_unique_normal_forms t.property hred hn hspec.1 hspec.2)

end ISAR
