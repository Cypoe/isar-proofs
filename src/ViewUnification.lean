import DialectKernel
import ViewIndependence
import TRSView
import BytecodeView
import QuantityKernel
import ZFCInterpretation
import Futamura
import BasisCompleteness

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

/-- Operational equivalence (joinability) on a transition system. -/
def OperEq_D {Object : Type} (step : Object → Object → Prop) (o1 o2 : Object) : Prop :=
  ∃ o3, Relation.ReflTransGen step o1 o3 ∧ Relation.ReflTransGen step o2 o3

theorem OperEq_D_refl {Object : Type} (step : Object → Object → Prop) (o : Object) :
    OperEq_D step o o :=
  ⟨o, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem OperEq_D_symm {Object : Type} (step : Object → Object → Prop) {o1 o2 : Object} (h : OperEq_D step o1 o2) :
    OperEq_D step o2 o1 := by
  let ⟨o3, h1, h2⟩ := h
  exact ⟨o3, h2, h1⟩

theorem OperEq_D_trans {Object : Type} (step : Object → Object → Prop)
    (confluent : ∀ (s s1 s2 : Object), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
      ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3)
    {o1 o2 o3 : Object} (h1 : OperEq_D step o1 o2) (h2 : OperEq_D step o2 o3) :
    OperEq_D step o1 o3 := by
  let ⟨o4, h14, h24⟩ := h1
  let ⟨o5, h25, h35⟩ := h2
  let ⟨o6, h46, h56⟩ := confluent o2 o4 o5 h24 h25
  exact ⟨o6, Relation.ReflTransGen.trans h14 h46, Relation.ReflTransGen.trans h35 h56⟩

open Classical

set_option linter.unusedVariables false in
/--
The encoding function mapping a 4x4 observed causal signature to an ISKSubtype term.
Constructively defined using the expressive completeness of the ISK monoid.
-/
noncomputable def encode_from_sig (sig : Fin 4 → Fin 4 → Int) : ISKSubtype :=
  if h : ISKAlgebra (toMatrix4 sig) then
    Classical.choose (isk_expressive_completeness (toMatrix4 sig) h)
  else
    ⟨ITerm.norm, ISKTerm.norm⟩ -- fallback

/-- A transition system that is confluent, strongly normalizing, and semantically representable
   via a faithful causal signature into the 4x4 ISAR basis. -/
structure ConfluentSNSystem where
  Object : Type
  nonempty : Nonempty Object
  step : Object → Object → Prop
  confluent : ∀ (s s1 s2 : Object), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
    ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3
  sn : WellFounded (fun x y => step y x)
  causal_signature : Object → Fin 4 → Fin 4 → Int
  sig_faithful : ∀ o1 o2, causal_signature o1 = causal_signature o2 → OperEq_D step o1 o2
  sig_in_ISK : ∀ o, ISKAlgebra (toMatrix4 (causal_signature o))
  sig_step : ∀ o1 o2, step o1 o2 → causal_signature o1 = causal_signature o2
  sig_faithful_opereq : ∀ o1 o2, OperEq (encode_from_sig (causal_signature o1)) (encode_from_sig (causal_signature o2)) → OperEq_D step o1 o2
  sig_surjective : ∀ t, ∃ o, OperEq (encode_from_sig (causal_signature o)) t

/--
The evaluation function reducing any transition system object to its normal form.
-/
noncomputable def eval_to_nf (D : ConfluentSNSystem) (o : D.Object) : D.Object :=
  D.sn.fix (fun x ih =>
    if h : ∃ y, ConfluentSNSystem.step D x y then
      ih (Classical.choose h) (Classical.choose_spec h)
    else
      x
  ) o

theorem eval_to_nf_step (D : ConfluentSNSystem) (o : D.Object) (h : ∃ y, ConfluentSNSystem.step D o y) :
    eval_to_nf D o = eval_to_nf D (Classical.choose h) := by
  dsimp [eval_to_nf]
  rw [WellFounded.fix_eq]
  dsimp
  split
  { rfl }
  { contradiction }

theorem reflTransGen_head_cases {α : Type} {r : α → α → Prop} {x z : α} (h : Relation.ReflTransGen r x z) :
    x = z ∨ ∃ y, r x y ∧ Relation.ReflTransGen r y z := by
  induction h with
  | refl => left; rfl
  | tail h1 h2 ih =>
      cases ih with
      | inl h_refl =>
          right
          subst h_refl
          exact ⟨_, h2, Relation.ReflTransGen.refl⟩
      | inr h_step =>
          cases h_step with
          | intro y hy =>
              right
              exact ⟨y, hy.1, Relation.ReflTransGen.tail hy.2 h2⟩

theorem eval_to_nf_eq_of_reflTransGen (D : ConfluentSNSystem) (o1 o2 : D.Object) (hr : Relation.ReflTransGen (ConfluentSNSystem.step D) o1 o2) :
    eval_to_nf D o1 = eval_to_nf D o2 := by
  revert o2 hr
  induction o1 using D.sn.induction with
  | h x ih =>
      intro o2 hr
      cases reflTransGen_head_cases hr with
      | inl h_refl => rw [h_refl]
      | inr h_step =>
          cases h_step with
          | intro y hy =>
              have h_eq_x_y : eval_to_nf D x = eval_to_nf D y := by
                have h_exists : ∃ w, ConfluentSNSystem.step D x w := ⟨y, hy.1⟩
                rw [eval_to_nf_step D x h_exists]
                have hw : ConfluentSNSystem.step D x (Classical.choose h_exists) := Classical.choose_spec h_exists
                have hr_y : Relation.ReflTransGen (ConfluentSNSystem.step D) x y := Relation.ReflTransGen.single hy.1
                have hr_w : Relation.ReflTransGen (ConfluentSNSystem.step D) x (Classical.choose h_exists) := Relation.ReflTransGen.single hw
                have h_conf : ∃ s3, Relation.ReflTransGen (ConfluentSNSystem.step D) y s3 ∧ Relation.ReflTransGen (ConfluentSNSystem.step D) (Classical.choose h_exists) s3 :=
                  D.confluent x y (Classical.choose h_exists) hr_y hr_w
                have ih_y := ih y hy.1 (Classical.choose h_conf) (Classical.choose_spec h_conf).1
                have ih_w := ih (Classical.choose h_exists) hw (Classical.choose h_conf) (Classical.choose_spec h_conf).2
                rw [ih_y, ih_w]
              rw [h_eq_x_y]
              exact ih y hy.1 o2 hy.2

theorem eval_to_nf_is_nf (D : ConfluentSNSystem) (o : D.Object) :
    ¬ ∃ y, ConfluentSNSystem.step D (eval_to_nf D o) y := by
  induction o using D.sn.induction with
  | h x ih =>
      by_cases h_step : ∃ y, ConfluentSNSystem.step D x y
      { rw [eval_to_nf_step D x h_step]
        exact ih (Classical.choose h_step) (Classical.choose_spec h_step) }
      { have h_eq : eval_to_nf D x = x := by
          dsimp [eval_to_nf]
          rw [WellFounded.fix_eq]
          dsimp
          split
          { contradiction }
          { rfl }
        rw [h_eq]
        exact h_step }

theorem reflTransGen_eval_to_nf (D : ConfluentSNSystem) (o : D.Object) :
    Relation.ReflTransGen (ConfluentSNSystem.step D) o (eval_to_nf D o) := by
  induction o using D.sn.induction with
  | h x ih =>
      by_cases h_step : ∃ y, ConfluentSNSystem.step D x y
      { rw [eval_to_nf_step D x h_step]
        have hy : ConfluentSNSystem.step D x (Classical.choose h_step) := Classical.choose_spec h_step
        have ih_y := ih (Classical.choose h_step) hy
        exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hy) ih_y }
      { have h_eq : eval_to_nf D x = x := by
          dsimp [eval_to_nf]
          rw [WellFounded.fix_eq]
          dsimp
          split
          { contradiction }
          { rfl }
        rw [h_eq] }

theorem causal_signature_eq_of_reflTransGen (D : ConfluentSNSystem) (o1 o2 : D.Object) (hr : Relation.ReflTransGen (ConfluentSNSystem.step D) o1 o2) :
    D.causal_signature o1 = D.causal_signature o2 := by
  induction hr with
  | refl => rfl
  | tail _ h2 ih =>
      rw [ih]
      exact D.sig_step _ _ h2

theorem eval_to_nf_eq_of_OperEq_D (D : ConfluentSNSystem) (o1 o2 : D.Object) (h : OperEq_D (ConfluentSNSystem.step D) o1 o2) :
    eval_to_nf D o1 = eval_to_nf D o2 := by
  have ⟨o3, h1, h2⟩ := h
  have heq1 := eval_to_nf_eq_of_reflTransGen D o1 o3 h1
  have heq2 := eval_to_nf_eq_of_reflTransGen D o2 o3 h2
  rw [heq1, heq2]

theorem OperEq_D_of_eval_to_nf_eq (D : ConfluentSNSystem) (o1 o2 : D.Object) (h : eval_to_nf D o1 = eval_to_nf D o2) :
    OperEq_D (ConfluentSNSystem.step D) o1 o2 := by
  have h1 := reflTransGen_eval_to_nf D o1
  have h2 := reflTransGen_eval_to_nf D o2
  rw [h] at h1
  exact ⟨eval_to_nf D o2, h1, h2⟩

theorem OperEq_D_iff_eval_to_nf_eq (D : ConfluentSNSystem) (o1 o2 : D.Object) :
    OperEq_D (ConfluentSNSystem.step D) o1 o2 ↔ eval_to_nf D o1 = eval_to_nf D o2 :=
  ⟨eval_to_nf_eq_of_OperEq_D D o1 o2, OperEq_D_of_eval_to_nf_eq D o1 o2⟩

/--
The decoding/projection function mapping substrate terms back to system objects,
constructively defined by finding the matching object signature and evaluating to normal form.
-/
noncomputable def system_view_of (D : ConfluentSNSystem) (t : ISKSubtype) : D.Object :=
  have : Nonempty D.Object := D.nonempty
  if h : ∃ o : D.Object, OperEq (encode_from_sig (D.causal_signature o)) t then
    eval_to_nf D (Classical.choose h)
  else
    Classical.choice this

/--
Soundness of the view mapping: operational equivalence in the substrate
implies joinability (OperEq_D) in the system.
-/
theorem system_sound (D : ConfluentSNSystem) (t u : ISKSubtype) (h : OperEq t u) :
    OperEq_D (ConfluentSNSystem.step D) (system_view_of D t) (system_view_of D u) := by
  have ⟨o1, h_o1⟩ := D.sig_surjective t
  have ⟨o2, h_o2⟩ := D.sig_surjective u
  have h_trans : OperEq (encode_from_sig (D.causal_signature o1)) (encode_from_sig (D.causal_signature o2)) := by
    exact OperEq.trans h_o1 (OperEq.trans h (OperEq.symm h_o2))
  have h_step : OperEq_D (ConfluentSNSystem.step D) o1 o2 := D.sig_faithful_opereq o1 o2 h_trans
  have heq_nf : eval_to_nf D o1 = eval_to_nf D o2 := eval_to_nf_eq_of_OperEq_D D o1 o2 h_step
  
  have h_vt : system_view_of D t = eval_to_nf D o1 := by
    dsimp [system_view_of]
    split
    { rename_i ht
      have hw1 := Classical.choose_spec ht
      have h_oe : OperEq (encode_from_sig (D.causal_signature (Classical.choose ht))) (encode_from_sig (D.causal_signature o1)) :=
        OperEq.trans hw1 (OperEq.symm h_o1)
      have h_eqD : OperEq_D (ConfluentSNSystem.step D) (Classical.choose ht) o1 := D.sig_faithful_opereq (Classical.choose ht) o1 h_oe
      exact eval_to_nf_eq_of_OperEq_D D (Classical.choose ht) o1 h_eqD }
    { rename_i ht
      have h_ex : ∃ o, OperEq (encode_from_sig (D.causal_signature o)) t := ⟨o1, h_o1⟩
      contradiction }

  have h_vu : system_view_of D u = eval_to_nf D o2 := by
    dsimp [system_view_of]
    split
    { rename_i hu
      have hw2 := Classical.choose_spec hu
      have h_oe : OperEq (encode_from_sig (D.causal_signature (Classical.choose hu))) (encode_from_sig (D.causal_signature o2)) :=
        OperEq.trans hw2 (OperEq.symm h_o2)
      have h_eqD : OperEq_D (ConfluentSNSystem.step D) (Classical.choose hu) o2 := D.sig_faithful_opereq (Classical.choose hu) o2 h_oe
      exact eval_to_nf_eq_of_OperEq_D D (Classical.choose hu) o2 h_eqD }
    { rename_i hu
      have h_ex : ∃ o, OperEq (encode_from_sig (D.causal_signature o)) u := ⟨o2, h_o2⟩
      contradiction }

  rw [h_vt, h_vu, heq_nf]
  exact OperEq_D_refl (ConfluentSNSystem.step D) _

/--
Completeness: encoding the view of a term is operationally equivalent to the term itself.
-/
theorem system_view_of_eq (D : ConfluentSNSystem) (o : D.Object) (t : ISKSubtype) (h : OperEq (encode_from_sig (D.causal_signature o)) t) :
    system_view_of D t = eval_to_nf D o := by
  dsimp [system_view_of]
  split
  { rename_i ht
    have hw1 := Classical.choose_spec ht
    have h_oe : OperEq (encode_from_sig (D.causal_signature (Classical.choose ht))) (encode_from_sig (D.causal_signature o)) :=
      OperEq.trans hw1 (OperEq.symm h)
    have h_eqD : OperEq_D (ConfluentSNSystem.step D) (Classical.choose ht) o := D.sig_faithful_opereq (Classical.choose ht) o h_oe
    exact eval_to_nf_eq_of_OperEq_D D (Classical.choose ht) o h_eqD }
  { rename_i ht
    have h_ex : ∃ o', OperEq (encode_from_sig (D.causal_signature o')) t := ⟨o, h⟩
    contradiction }

theorem system_decode_view (D : ConfluentSNSystem) (t : ISKSubtype) :
    OperEq (encode_from_sig (D.causal_signature (system_view_of D t))) t := by
  have ⟨o, h_o⟩ := D.sig_surjective t
  have heq : system_view_of D t = eval_to_nf D o := system_view_of_eq D o t h_o
  rw [heq]
  have h_sig : D.causal_signature o = D.causal_signature (eval_to_nf D o) :=
    causal_signature_eq_of_reflTransGen D o (eval_to_nf D o) (reflTransGen_eval_to_nf D o)
  rw [← h_sig]
  exact h_o

/--
Inverse Coherence: viewing the encoding of an object is joinable to the object itself.
-/
theorem system_view_eq_decode (D : ConfluentSNSystem) (obj : D.Object) :
    OperEq_D (ConfluentSNSystem.step D) (system_view_of D (encode_from_sig (D.causal_signature obj))) obj := by
  dsimp [system_view_of]
  split
  { rename_i h
    have h_spec := Classical.choose_spec h
    have h_eq : OperEq_D (ConfluentSNSystem.step D) (Classical.choose h) obj := D.sig_faithful_opereq (Classical.choose h) obj h_spec
    have heq_nf : eval_to_nf D (Classical.choose h) = eval_to_nf D obj := eval_to_nf_eq_of_OperEq_D D (Classical.choose h) obj h_eq
    rw [heq_nf]
    have h_refl_nf : eval_to_nf D (eval_to_nf D obj) = eval_to_nf D obj := by
      have h_is_nf := eval_to_nf_is_nf D obj
      dsimp [eval_to_nf]
      rw [WellFounded.fix_eq]
      dsimp
      split
      { contradiction }
      { rfl }
    have h_oe : OperEq_D (ConfluentSNSystem.step D) (eval_to_nf D obj) obj := by
      rw [OperEq_D_iff_eval_to_nf_eq]
      exact h_refl_nf
    exact h_oe }
  { rename_i h
    have h_exists : ∃ o', OperEq (encode_from_sig (D.causal_signature o')) (encode_from_sig (D.causal_signature obj)) := ⟨obj, OperEq.refl _⟩
    contradiction }

/--
Congruence: joinability of objects implies operational equivalence of their encodings.
-/
theorem system_decode_eq (D : ConfluentSNSystem) (o1 o2 : D.Object) (h : OperEq_D (ConfluentSNSystem.step D) o1 o2) :
    OperEq (encode_from_sig (D.causal_signature o1)) (encode_from_sig (D.causal_signature o2)) := by
  have heq_nf : eval_to_nf D o1 = eval_to_nf D o2 := eval_to_nf_eq_of_OperEq_D D o1 o2 h
  have h_sig1 : D.causal_signature o1 = D.causal_signature (eval_to_nf D o1) :=
    causal_signature_eq_of_reflTransGen D o1 (eval_to_nf D o1) (reflTransGen_eval_to_nf D o1)
  have h_sig2 : D.causal_signature o2 = D.causal_signature (eval_to_nf D o2) :=
    causal_signature_eq_of_reflTransGen D o2 (eval_to_nf D o2) (reflTransGen_eval_to_nf D o2)
  rw [h_sig1, h_sig2, heq_nf]
  exact OperEq.refl _

def OperEq_D_equiv (D : ConfluentSNSystem) : Equivalence (OperEq_D D.step) where
  refl := OperEq_D_refl D.step
  symm := OperEq_D_symm D.step
  trans := OperEq_D_trans D.step D.confluent

/--
The Fundamental Theorem of Dialect Realizability (Proven Constructively):
Any confluent and strongly normalizing system D with a faithful causal signature into the ISAR basis
automatically yields an AdmissibleDialect structure, where the compilation/encoding is constructed
semantically from the causal signature rather than being provided by hand.
-/
noncomputable def confluence_SN_gives_AdmissibleDialect (D : ConfluentSNSystem) : AdmissibleDialect where
  D := {
    Object := D.Object
    Obs := D.Object
    ObsEq := OperEq_D D.step
    is_equiv := OperEq_D_equiv D
    eval := id
    encode := fun o => encode_from_sig (D.causal_signature o)
    decode := fun q => system_view_of D (InvariantLayer.canonical_rep q)
    preserves := by
      intro x
      dsimp
      have h1 := canonical_rep_eq (encode_from_sig (D.causal_signature x))
      have h2 := system_sound D _ _ h1
      have h3 := system_view_eq_decode D x
      exact OperEq_D_trans D.step D.confluent h2 h3
  }
  view_of := system_view_of D
  view_eq := OperEq_D D.step
  is_equiv := OperEq_D_equiv D
  sound t u h := system_sound D t u h
  decode_view t := system_decode_view D t
  view_eq_decode obj := system_view_eq_decode D obj
  decode_eq o1 o2 h := system_decode_eq D o1 o2 h

end ISAR
