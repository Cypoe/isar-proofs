import ISAR.InvariantLayer
import ISAR.ObservationRegime
import Mathlib.Tactic

namespace ISAR

/--
An admissible semantic kernel (view) over an observation regime.

A `Kernel P R` is a view over presentations of type `P` observed under the
regime `R` — the carrier, view map, coherence, and decode all live relative
to `R.sim`, not to any fixed substrate term type. It consists of:
1. A carrier type.
2. A view mapping presentations to the carrier.
3. An equivalence relation representing observational equivalence in the view.
4. Soundness: `R.sim` in the presentation implies equivalence in the view.
5. A decoding/reconstruction mapping back to the presentation.
6. Coherence axioms:
   - decode (view M) ≈ M
   - view (decode c) ≈ c
   - c1 ≈ c2 implies decode c1 ≈ decode c2

The ISAR substrate is one regime among peers (decision 068): existing
call sites spell the anchor explicitly as `Kernel ISKSubtype operEqRegime`;
the regime parameter is real for dialect-native presentations.
-/
structure Kernel (P : Type) (R : ObservationRegime P) : Type 1 where
  Carrier : Type
  view_of : P → Carrier
  view_eq : Carrier → Carrier → Prop
  is_equiv : Equivalence view_eq
  sound : ∀ (t u : P), R.sim t u → view_eq (view_of t) (view_of u)
  decode : Carrier → P
  decode_view : ∀ (t : P), R.sim (decode (view_of t)) t
  view_eq_decode : ∀ (c : Carrier), view_eq (view_of (decode c)) c
  decode_eq : ∀ (c1 c2 : Carrier), view_eq c1 c2 → R.sim (decode c1) (decode c2)

/-- Observational equivalence setoid on the carrier of a Kernel. -/
def Kernel.setoid {P : Type} {R : ObservationRegime P} (K : Kernel P R) :
    Setoid K.Carrier where
  r := K.view_eq
  iseqv := K.is_equiv

/-- A regime's substrate presentation itself as a Kernel — the terminal
object of `Kernel P R` for *any* regime `R`, not just the ISAR one. -/
def substrateKernel {P : Type} (R : ObservationRegime P) : Kernel P R where
  Carrier := P
  view_of := id
  view_eq := R.sim
  is_equiv := ⟨fun p => R.sim_refl p, fun h => R.sim_symm h,
              fun h1 h2 => R.sim_trans h1 h2⟩
  sound := fun _ _ h => h
  decode := id
  decode_view := fun t => R.sim_refl t
  view_eq_decode := fun c => R.sim_refl c
  decode_eq := fun _ _ h => h

/-- The canonical ISAR quotient presentation as a Kernel — the ISK
specialization of `substrateKernel`.  `OperEq` is `operEqRegime.sim`
up to the quotient characterization. -/
abbrev ISAR_Kernel : Kernel ISKSubtype operEqRegime where
  Carrier := ISKSubtype
  view_of := id
  view_eq := OperEq
  is_equiv := operEqSetoid.iseqv
  sound := fun _ _ h => (operEqRegime_sim_iff _ _).mp h
  decode := id
  decode_view := fun t => (operEqRegime_sim_iff _ _).mpr (OperEq.refl t)
  view_eq_decode := fun c => OperEq.refl c
  decode_eq := fun _ _ h => (operEqRegime_sim_iff _ _).mpr h

/-- The computable ISAR kernel parametrized by normalization fuel. -/
def ComputableISAR_Kernel (fuel : Nat) : Kernel ISKSubtype operEqRegime where
  Carrier := ISKSubtype
  view_of := id
  view_eq := OperEq
  is_equiv := operEqSetoid.iseqv
  sound := fun _ _ h => (operEqRegime_sim_iff _ _).mp h
  decode := cd_loop_fuel fuel
  decode_view := fun t =>
    (operEqRegime_sim_iff _ _).mpr (OperEq_cd_loop_fuel fuel t)
  view_eq_decode := fun c => OperEq_cd_loop_fuel fuel c
  decode_eq := fun c1 c2 h => (operEqRegime_sim_iff _ _).mpr (by
    have h1 := OperEq_cd_loop_fuel fuel c1
    have h2 := OperEq_cd_loop_fuel fuel c2
    exact OperEq.trans h1 (OperEq.trans h (OperEq.symm h2)))

/-- The optimal computable ISAR kernel for linearly-typed terms. -/
def ComputableISAR_Kernel_Optimal (t : ISKSubtype) (_ht : LinearIKTerm t.val) : Kernel ISKSubtype operEqRegime :=
  ComputableISAR_Kernel (sufficient_fuel t)


/--
A structure-preserving morphism between semantic kernels over the same
presentation and regime.
Must preserve the view mapping and map equivalent carrier elements to equivalent elements.
-/
structure KernelHom {P : Type} {R : ObservationRegime P}
    (K1 K2 : Kernel P R) : Type where
  hom : K1.Carrier → K2.Carrier
  hom_view : ∀ (t : P), K2.view_eq (hom (K1.view_of t)) (K2.view_of t)
  hom_congr : ∀ (c1 c2 : K1.Carrier), K1.view_eq c1 c2 → K2.view_eq (hom c1) (hom c2)

/-- The canonical structure-preserving morphism from any Kernel K into its
regime's substrate kernel. -/
def canonical_hom {P : Type} {R : ObservationRegime P} (K : Kernel P R) :
    KernelHom K (substrateKernel R) where
  hom := K.decode
  hom_view := K.decode_view
  hom_congr := K.decode_eq

/--
Uniqueness (Terminality) Theorem:
Every structure-preserving morphism f : K → substrateKernel R from any
admissible semantic kernel K over (P, R) is observationally equivalent to
the canonical decoding morphism.
-/
theorem morphism_uniqueness {P : Type} {R : ObservationRegime P}
    (K : Kernel P R) (f : KernelHom K (substrateKernel R)) (c : K.Carrier) :
    R.sim (f.hom c) (K.decode c) := by
  -- 1. By view coherence, the carrier element c is equivalent to its decoded reconstruction:
  have h_eq : K.view_eq (K.view_of (K.decode c)) c := K.view_eq_decode c
  -- 2. By morphism congruence, f preserves this equivalence:
  have h_f_congr := f.hom_congr (K.view_of (K.decode c)) c h_eq
  -- 3. By morphism view preservation, f mapped over the reconstructed view is equivalent to the decoded term:
  have h_f_view := f.hom_view (K.decode c)
  -- 4. By transitivity and symmetry, f.hom c ≈ K.decode c
  exact R.sim_trans (R.sim_symm h_f_congr) h_f_view

/-- Observational equivalence between morphisms K → substrateKernel R. -/
def HomEquiv {P : Type} {R : ObservationRegime P} (K : Kernel P R)
    (f g : KernelHom K (substrateKernel R)) : Prop :=
  ∀ c, R.sim (f.hom c) (g.hom c)

/-- Setoid instance for quotienting morphism space modulo observational equivalence. -/
instance homSetoid {P : Type} {R : ObservationRegime P} (K : Kernel P R) :
    Setoid (KernelHom K (substrateKernel R)) where
  r := HomEquiv K
  iseqv := {
    refl := fun _ _ => R.sim_refl _
    symm := fun h c => R.sim_symm (h c)
    trans := fun h1 h2 c => R.sim_trans (h1 c) (h2 c)
  }

/--
**Substrate Kernel Terminality.**

The quotient of the morphism space `KernelHom K (substrateKernel R)` modulo
observational equivalence is a singleton (unique existence holds) — for any
regime `R`, not just `operEqRegime`.  Terminality is *per regime*; cross-regime
composition lives in `QuotientMap`, not here.

**Proof**: Existence follows constructively from `canonical_hom K`. Uniqueness follows by applying
`morphism_uniqueness` to show that any structure-preserving morphism is observationally equivalent
to `canonical_hom K` (the canonical decoding).
-/
theorem substrateKernel_terminal {P : Type} {R : ObservationRegime P}
    (K : Kernel P R) :
    ∃! _f_class : Quotient (homSetoid K), True := by
  use Quotient.mk _ (canonical_hom K)
  refine ⟨trivial, fun y_class _ => ?_⟩
  refine Quotient.inductionOn y_class (fun g => ?_)
  apply Quotient.sound
  intro c
  exact morphism_uniqueness K g c

/-- The ISAR instance of substrate terminality — the `operEqRegime` case
of the general theorem. -/
theorem ISAR_Kernel_terminal (K : Kernel ISKSubtype operEqRegime) :
    ∃! _f_class : Quotient (homSetoid K), True :=
  substrateKernel_terminal K

/-! ### False-variant: junk on the carrier, not a disproof of terminality

`view_eq := True` cannot inhabit `Kernel`: `decode_eq` + `decode_view` would
force all terms `OperEq`-related, contradicting distinct atom NFs.

`DegenerateKernel` still inhabits `Kernel` by ignoring a `Bool` tag in
`view_eq`. Terminality holds; observations do not see the tag. This is a
regression that the interface does **not** force `view_eq` to be equality
on `Carrier`. It is **not** a disproof of `ISAR_Kernel_terminal`.
-/

theorem NormalI_norm_atom : NormalI ITerm.norm := fun _ h => by cases h

theorem NormalI_konst_atom : NormalI ITerm.konst := fun _ h => by cases h

theorem not_OperEq_norm_konst :
    ¬ OperEq ⟨ITerm.norm, ISKTerm.norm⟩ ⟨ITerm.konst, ISKTerm.konst⟩ := by
  intro h
  rcases h with ⟨v, hn, hk⟩
  have e1 := IRed_normal_eq NormalI_norm_atom hn
  have e2 := IRed_normal_eq NormalI_konst_atom hk
  cases e1
  cases e2

/-- An indiscrete `view_eq` would collapse `R.sim`; hence no such `Kernel`
over a non-degenerate regime. -/
theorem no_indiscrete_Kernel {P : Type} {R : ObservationRegime P}
    (K : Kernel P R) (h_nd : ∃ t u : P, ¬ R.sim t u)
    (h : ∀ c1 c2 : K.Carrier, K.view_eq c1 c2) : False := by
  obtain ⟨t, u, htu⟩ := h_nd
  have hn : R.sim (K.decode (K.view_of t)) t := K.decode_view _
  have hu : R.sim (K.decode (K.view_of u)) u := K.decode_view _
  have hvu : K.view_eq (K.view_of t) (K.view_of u) := h _ _
  have hdec := K.decode_eq _ _ hvu
  exact htu (R.sim_trans (R.sim_symm hn) (R.sim_trans hdec hu))

/-- `operEqRegime` is non-degenerate: norm and konst have distinct atoms. -/
theorem operEqRegime_nondegenerate :
    ∃ t u : ISKSubtype, ¬ operEqRegime.sim t u :=
  ⟨⟨ITerm.norm, ISKTerm.norm⟩, ⟨ITerm.konst, ISKTerm.konst⟩,
   fun h => not_OperEq_norm_konst ((operEqRegime_sim_iff _ _).mp h)⟩

/-- Carrier is `P × Bool`; `view_eq` ignores the tag — at regime
generality the same shape degenerates any substrate. -/
def DegenerateKernel {P : Type} (R : ObservationRegime P) : Kernel P R where
  Carrier := P × Bool
  view_of := fun t => (t, false)
  view_eq := fun c1 c2 => R.sim c1.1 c2.1
  is_equiv := {
    refl := fun c => R.sim_refl c.1
    symm := fun h => R.sim_symm h
    trans := fun h1 h2 => R.sim_trans h1 h2
  }
  sound := fun _ _ h => h
  decode := fun c => c.1
  decode_view := fun t => R.sim_refl t
  view_eq_decode := fun c => R.sim_refl c.1
  decode_eq := fun _ _ h => h

theorem DegenerateKernel_view_eq_ignores_tag {P : Type} {R : ObservationRegime P}
    (t : P) :
    (DegenerateKernel R).view_eq (t, false) (t, true) :=
  R.sim_refl t

theorem DegenerateKernel_carriers_not_eq {P : Type} {R : ObservationRegime P}
    (t : P) :
    (t, false) ≠ (t, true) := by
  intro h
  injection h with _ hb
  cases hb

theorem DegenerateKernel_terminal {P : Type} {R : ObservationRegime P} :
    ∃! _f_class : Quotient (homSetoid (DegenerateKernel R)), True :=
  substrateKernel_terminal (DegenerateKernel R)

end ISAR
