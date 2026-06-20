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

end ISAR
