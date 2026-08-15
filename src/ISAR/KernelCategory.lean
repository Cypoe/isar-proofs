import ISAR.InvariantLayer
import Mathlib.Tactic

namespace ISAR

/--
An admissible semantic kernel (view) over the invariant quotient.
It consists of:
1. A carrier type.
2. A view mapping fragment terms to the carrier.
3. An equivalence relation representing observational equivalence in the view.
4. Soundness: operational equivalence in the fragment implies equivalence in the view.
5. A decoding/reconstruction mapping back to the fragment.
6. Coherence axioms:
   - decode (view M) ≈ M
   - view (decode c) ≈ c
   - c1 ≈ c2 implies decode c1 ≈ decode c2
-/
structure Kernel : Type 1 where
  Carrier : Type
  view_of : ISKSubtype → Carrier
  view_eq : Carrier → Carrier → Prop
  is_equiv : Equivalence view_eq
  sound : ∀ (t u : ISKSubtype), OperEq t u → view_eq (view_of t) (view_of u)
  decode : Carrier → ISKSubtype
  decode_view : ∀ (t : ISKSubtype), OperEq (decode (view_of t)) t
  view_eq_decode : ∀ (c : Carrier), view_eq (view_of (decode c)) c
  decode_eq : ∀ (c1 c2 : Carrier), view_eq c1 c2 → OperEq (decode c1) (decode c2)

/-- Observational equivalence setoid on the carrier of a Kernel. -/
def Kernel.setoid (K : Kernel) : Setoid K.Carrier where
  r := K.view_eq
  iseqv := K.is_equiv

/-- The canonical ISAR quotient presentation itself as a Kernel. -/
abbrev ISAR_Kernel : Kernel where
  Carrier := ISKSubtype
  view_of := id
  view_eq := OperEq
  is_equiv := operEqSetoid.iseqv
  sound := fun _ _ h => h
  decode := id
  decode_view := fun t => OperEq.refl t
  view_eq_decode := fun c => OperEq.refl c
  decode_eq := fun _ _ h => h

/-- The computable ISAR kernel parametrized by normalization fuel. -/
def ComputableISAR_Kernel (fuel : Nat) : Kernel where
  Carrier := ISKSubtype
  view_of := id
  view_eq := OperEq
  is_equiv := operEqSetoid.iseqv
  sound := fun _ _ h => h
  decode := cd_loop_fuel fuel
  decode_view := fun t => OperEq_cd_loop_fuel fuel t
  view_eq_decode := fun c => OperEq_cd_loop_fuel fuel c
  decode_eq := fun c1 c2 h => by
    have h1 := OperEq_cd_loop_fuel fuel c1
    have h2 := OperEq_cd_loop_fuel fuel c2
    exact OperEq.trans h1 (OperEq.trans h (OperEq.symm h2))

/-- The optimal computable ISAR kernel for linearly-typed terms. -/
def ComputableISAR_Kernel_Optimal (t : ISKSubtype) (_ht : LinearIKTerm t.val) : Kernel :=
  ComputableISAR_Kernel (sufficient_fuel t)


/--
A structure-preserving morphism between semantic kernels.
Must preserve the view mapping and map equivalent carrier elements to equivalent elements.
-/
structure KernelHom (K1 K2 : Kernel) : Type where
  hom : K1.Carrier → K2.Carrier
  hom_view : ∀ (t : ISKSubtype), K2.view_eq (hom (K1.view_of t)) (K2.view_of t)
  hom_congr : ∀ (c1 c2 : K1.Carrier), K1.view_eq c1 c2 → K2.view_eq (hom c1) (hom c2)

/-- The canonical structure-preserving morphism from any Kernel K into ISAR_Kernel. -/
def canonical_hom (K : Kernel) : KernelHom K ISAR_Kernel where
  hom := K.decode
  hom_view := K.decode_view
  hom_congr := K.decode_eq

/--
Uniqueness (Terminality) Theorem:
Every structure-preserving morphism f : K → ISAR_Kernel from any admissible semantic kernel K
into the canonical ISAR presentation is observationally equivalent to the canonical decoding morphism.
-/
theorem morphism_uniqueness (K : Kernel) (f : KernelHom K ISAR_Kernel) (c : K.Carrier) :
    OperEq (f.hom c) (K.decode c) := by
  -- 1. By view coherence, the carrier element c is equivalent to its decoded reconstruction:
  have h_eq : K.view_eq (K.view_of (K.decode c)) c := K.view_eq_decode c
  -- 2. By morphism congruence, f preserves this equivalence:
  have h_f_congr := f.hom_congr (K.view_of (K.decode c)) c h_eq
  -- 3. By morphism view preservation, f mapped over the reconstructed view is equivalent to the decoded term:
  have h_f_view := f.hom_view (K.decode c)
  -- 4. By transitivity and symmetry, f.hom c ≈ K.decode c
  exact OperEq.trans (OperEq.symm h_f_congr) h_f_view

/-- Observational equivalence between morphisms K → ISAR_Kernel. -/
def HomEquiv (K : Kernel) (f g : KernelHom K ISAR_Kernel) : Prop :=
  ∀ c, OperEq (f.hom c) (g.hom c)

/-- Setoid instance for quotienting morphism space modulo observational equivalence. -/
instance homSetoid (K : Kernel) : Setoid (KernelHom K ISAR_Kernel) where
  r := HomEquiv K
  iseqv := {
    refl := fun _ _ => OperEq.refl _
    symm := fun h c => OperEq.symm (h c)
    trans := fun h1 h2 c => OperEq.trans (h1 c) (h2 c)
  }

/--
**ISAR Kernel Terminality.**

The quotient of the morphism space `KernelHom K ISAR_Kernel` modulo observational equivalence
is a singleton (unique existence holds).

**Proof**: Existence follows constructively from `canonical_hom K`. Uniqueness follows by applying
`morphism_uniqueness` to show that any structure-preserving morphism is observationally equivalent
to `canonical_hom K` (the canonical decoding).
-/
theorem ISAR_Kernel_terminal (K : Kernel) :
    ∃! _f_class : Quotient (homSetoid K), True := by
  use Quotient.mk _ (canonical_hom K)
  refine ⟨trivial, fun y_class _ => ?_⟩
  refine Quotient.inductionOn y_class (fun g => ?_)
  apply Quotient.sound
  intro c
  exact morphism_uniqueness K g c

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

/-- An indiscrete `view_eq` would collapse `OperEq`; hence no such `Kernel`. -/
theorem no_indiscrete_Kernel (K : Kernel)
    (h : ∀ c1 c2 : K.Carrier, K.view_eq c1 c2) : False := by
  have hn : OperEq (K.decode (K.view_of ⟨ITerm.norm, ISKTerm.norm⟩))
      ⟨ITerm.norm, ISKTerm.norm⟩ := K.decode_view _
  have hk : OperEq (K.decode (K.view_of ⟨ITerm.konst, ISKTerm.konst⟩))
      ⟨ITerm.konst, ISKTerm.konst⟩ := K.decode_view _
  have hvu : K.view_eq (K.view_of ⟨ITerm.norm, ISKTerm.norm⟩)
      (K.view_of ⟨ITerm.konst, ISKTerm.konst⟩) := h _ _
  have hdec := K.decode_eq _ _ hvu
  exact not_OperEq_norm_konst (OperEq.trans (OperEq.symm hn) (OperEq.trans hdec hk))

/-- Carrier is `ISKSubtype × Bool`; `view_eq` ignores the tag. -/
def DegenerateKernel : Kernel where
  Carrier := ISKSubtype × Bool
  view_of := fun t => (t, false)
  view_eq := fun c1 c2 => OperEq c1.1 c2.1
  is_equiv := {
    refl := fun c => OperEq.refl c.1
    symm := fun h => OperEq.symm h
    trans := fun h1 h2 => OperEq.trans h1 h2
  }
  sound := fun _ _ h => h
  decode := fun c => c.1
  decode_view := fun t => OperEq.refl t
  view_eq_decode := fun c => OperEq.refl c.1
  decode_eq := fun _ _ h => h

theorem DegenerateKernel_view_eq_ignores_tag (t : ISKSubtype) :
    DegenerateKernel.view_eq (t, false) (t, true) :=
  OperEq.refl t

theorem DegenerateKernel_carriers_not_eq (t : ISKSubtype) :
    (t, false) ≠ (t, true) := by
  intro h
  injection h with _ hb
  cases hb

theorem DegenerateKernel_terminal :
    ∃! _f_class : Quotient (homSetoid DegenerateKernel), True :=
  ISAR_Kernel_terminal DegenerateKernel

end ISAR
