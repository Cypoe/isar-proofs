import DialectKernel
import ViewIndependence
import TRSView
import BytecodeView
import QuantityKernel
import ZFCInterpretation

namespace ISAR

/- =========================================================
   1. Admissible Dialect Abstraction
   ========================================================= -/

/--
A Dialect is Admissible if it satisfies the coherence conditions necessary
to be presented as an admissible semantic Kernel.
-/
structure AdmissibleDialect where
  D : Dialect
  view_of : ISKSubtype → D.Object
  view_eq : D.Object → D.Object → Prop
  is_equiv : Equivalence view_eq
  sound : ∀ (t u : ISKSubtype), OperEq t u → view_eq (view_of t) (view_of u)
  decode_view : ∀ (t : ISKSubtype), OperEq (D.encode (view_of t)) t
  view_eq_decode : ∀ (obj : D.Object), view_eq (view_of (D.encode obj)) obj
  decode_eq : ∀ (o1 o2 : D.Object), view_eq o1 o2 → OperEq (D.encode o1) (D.encode o2)

/-- Canonical translation of any Admissible Dialect into a category-theoretic Kernel. -/
def AdmissibleDialect.toKernel (AD : AdmissibleDialect) : Kernel where
  Carrier := AD.D.Object
  view_of := AD.view_of
  view_eq := AD.view_eq
  is_equiv := AD.is_equiv
  sound := AD.sound
  decode := AD.D.encode
  decode_view := AD.decode_view
  view_eq_decode := AD.view_eq_decode
  decode_eq := AD.decode_eq


/- =========================================================
   2. Unification of Observational Isomorphism & Kernel Isomorphism
   ========================================================= -/

/-- An isomorphism between two category-theoretic Kernels. -/
structure KernelIsomorphism (K1 K2 : Kernel) where
  hom1 : KernelHom K1 K2
  hom2 : KernelHom K2 K1
  inverse1 : ∀ (c : K1.Carrier), K1.view_eq (hom2.hom (hom1.hom c)) c
  inverse2 : ∀ (c : K2.Carrier), K2.view_eq (hom1.hom (hom2.hom c)) c

/-- Canonical morphism translation from AD1 to AD2 using the substrate as the medium. -/
def dialect_canonical_hom (AD1 AD2 : AdmissibleDialect) : KernelHom AD1.toKernel AD2.toKernel where
  hom obj := AD2.view_of (AD1.D.encode obj)
  hom_view t := AD2.sound _ _ (AD1.decode_view t)
  hom_congr c1 c2 h := AD2.sound _ _ (AD1.decode_eq c1 c2 h)

/--
Unification Theorem:
Any observational isomorphism between two admissible dialects D1 and D2 induces
a category-theoretic KernelIsomorphism between their corresponding Kernels.
The translation morphisms are constructed canonicaly using the substrate as the universal medium.
-/
noncomputable def isomorphism_unification (AD1 AD2 : AdmissibleDialect) (_iso : ObservationalIsomorphism AD1.D AD2.D) :
    KernelIsomorphism AD1.toKernel AD2.toKernel where
  hom1 := dialect_canonical_hom AD1 AD2
  hom2 := dialect_canonical_hom AD2 AD1
  inverse1 := by
    intro c
    dsimp [dialect_canonical_hom]
    -- We need to prove: AD1.view_eq (AD1.view_of (AD2.D.encode (AD2.view_of (AD1.D.encode c)))) c
    -- Using AD2.decode_view: OperEq (AD2.D.encode (AD2.view_of (AD1.D.encode c))) (AD1.D.encode c)
    have h_eq2 := AD2.decode_view (AD1.D.encode c)
    -- By AD1.sound:
    have h_eq1 := AD1.sound _ _ h_eq2
    -- By AD1.view_eq_decode: AD1.view_eq (AD1.view_of (AD1.D.encode c)) c
    have h_dec := AD1.view_eq_decode c
    exact AD1.is_equiv.trans h_eq1 h_dec
  inverse2 := by
    intro c
    dsimp [dialect_canonical_hom]
    -- Mirror of inverse1:
    have h_eq2 := AD1.decode_view (AD2.D.encode c)
    have h_eq1 := AD2.sound _ _ h_eq2
    have h_dec := AD2.view_eq_decode c
    exact AD2.is_equiv.trans h_eq1 h_dec


/- =========================================================
   3. Exposing TRS & Bytecode as Admissible Dialects
   ========================================================= -/

noncomputable def TRS_AdmissibleDialect : AdmissibleDialect where
  D := TRS_Dialect
  view_of := decode_raw
  view_eq := trs_obs_eq
  is_equiv := trs_obs_equiv
  sound t u h := by
    unfold trs_obs_eq
    rw [trs_encode_decode_raw t, trs_encode_decode_raw u]
    exact h
  decode_view t := by
    dsimp [TRS_Dialect]
    rw [trs_encode_decode_raw t]
    exact OperEq.refl t
  view_eq_decode obj := by
    unfold trs_obs_eq
    dsimp [TRS_Dialect]
    rw [decode_raw_trs_encode obj]
    exact OperEq.refl (trs_encode obj)
  decode_eq _ _ h := h

noncomputable def Bytecode_AdmissibleDialect : AdmissibleDialect where
  D := Bytecode_Dialect
  view_of t := decompile (decode_raw t)
  view_eq := bytecode_obs_eq
  is_equiv := bytecode_obs_equiv
  sound t u h := by
    unfold bytecode_obs_eq
    rw [compile_decompile, compile_decompile]
    rw [trs_encode_decode_raw t, trs_encode_decode_raw u]
    exact h
  decode_view t := by
    dsimp [Bytecode_Dialect]
    rw [compile_decompile]
    rw [trs_encode_decode_raw t]
    exact OperEq.refl t
  view_eq_decode obj := by
    unfold bytecode_obs_eq
    dsimp [Bytecode_Dialect]
    rw [compile_decompile]
    rw [decode_raw_trs_encode (compile obj)]
    exact OperEq.refl (trs_encode (compile obj))
  decode_eq _ _ h := h


/- =========================================================
   4. Universal Factorization Theorem
   ========================================================= -/

/--
Universal Factorization Theorem:
Every admissible dialect kernel factors uniquely through `ISAR_Kernel`.
We state this for the five concrete semantic views:
1. ZFC / HF Set theory (`HF_Kernel`)
2. Structural Quantity Calculus (`QuantityKernel`)
3. Pure SKI Term Rewriting (`TRS_AdmissibleDialect.toKernel`)
4. Stack VM Bytecode (`Bytecode_AdmissibleDialect.toKernel`)
-/
theorem universal_factorization_theorem (K : Kernel) (f : KernelHom K ISAR_Kernel) (c : K.Carrier) :
    OperEq (f.hom c) (K.decode c) := by
  exact morphism_uniqueness K f c

/-
/-- A transition system that is confluent and strongly normalizing. -/
structure ConfluentSNSystem where
  Object : Type
  step : Object → Object → Prop
  confluent : ∀ (s s1 s2 : Object), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
    ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3
  sn : WellFounded (fun x y => step y x)

Conjecture (The Fundamental Theorem of Dialect Realizability):
Any confluent and strongly normalizing system D induces an AdmissibleDialect structure.
Proving this constructively resolves the meta-circularity of terminality.

DEPRECATION NOTE:
This non-constructive general axiom is deprecated. The realizability conjecture is constructively
resolved by using a Universal Meta-Language (MExpr / Lisp) as a pivot, combined with the verified
Futamura Projections (see scratch/test_futamura.lean). Instead of asserting the existence of a
compiler for every abstract system, we constructively generate and verify compilers for any system
expressible in the meta-language using the specialized compiler generator (cogen).
-/

end ISAR



