import ISAR.KernelCategory
import ISAR.DialectKernel

namespace ISAR

/--
The Presuppositional IOB Triad on a carrier.
-/
structure IOB (Carrier : Type) where
  I : Carrier
  O : Carrier → Carrier → Carrier
  B : Carrier → Carrier

/--
An Admissible SARI structure on a carrier, constrained by confluence,
fixed-point identities, and pairing closure equations.
-/
structure AdmissibleSARI (Carrier : Type) (O : Carrier → Carrier → Carrier) where
  S : Carrier → Prop
  A : Carrier → Carrier → Prop
  R : Carrier → Carrier → Prop
  I : Carrier → Prop
  confluent : ∀ c c1 c2, R c c1 → R c c2 → ∃ c3, Relation.ReflTransGen R c1 c3 ∧ Relation.ReflTransGen R c2 c3
  fixed_point : ∀ c, I c ↔ (∀ c', ¬ R c c')
  pairing_closure : ∀ c1 c2, S c1 → S c2 → S (O c1 c2)

/--
The category Adm of Admissible Carriers.
An object consists of a carrier, an IOB triad, and a self-composition functor compatibility.
-/
structure AdmCarrier : Type 1 where
  Carrier : Type
  iob : IOB Carrier
  F : Carrier → Carrier
  is_fixed_point : ∀ c, F c = c

/--
Operational equality relation induced by reduction/rewriting.
-/
def OperationalEq {C : Type} (step : C → C → Prop) (c1 c2 : C) : Prop :=
  ∃ c3, Relation.ReflTransGen step c1 c3 ∧ Relation.ReflTransGen step c2 c3

theorem oper_eq_refl {C : Type} (step : C → C → Prop) (c : C) :
    OperationalEq step c c :=
  ⟨c, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem oper_eq_symm {C : Type} (step : C → C → Prop) {c1 c2 : C} (h : OperationalEq step c1 c2) :
    OperationalEq step c2 c1 := by
  rcases h with ⟨c3, h1, h2⟩
  exact ⟨c3, h2, h1⟩

theorem oper_eq_trans {C : Type} (step : C → C → Prop)
    (confluent : ∀ (s s1 s2 : C), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
      ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3)
    {c1 c2 c3 : C} (h1 : OperationalEq step c1 c2) (h2 : OperationalEq step c2 c3) :
    OperationalEq step c1 c3 := by
  rcases h1 with ⟨c4, h14, h24⟩
  rcases h2 with ⟨c5, h25, h35⟩
  rcases confluent c2 c4 c5 h24 h25 with ⟨c6, h46, h56⟩
  exact ⟨c6, Relation.ReflTransGen.trans h14 h46, Relation.ReflTransGen.trans h35 h56⟩

/-- Setoid structure on a carrier under operational equivalence. -/
def operSetoid {C : Type} (step : C → C → Prop)
    (confluent : ∀ (s s1 s2 : C), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
      ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3) :
    Setoid C where
  r := OperationalEq step
  iseqv := {
    refl := oper_eq_refl step
    symm := fun h => oper_eq_symm step h
    trans := fun h1 h2 => oper_eq_trans step confluent h1 h2
  }

/--
Inductive Statehood predicate on an AdmCarrier.
States are inductively generated from the identity under the self-application operator O.
-/
inductive Statehood (C : AdmCarrier) : C.Carrier → Prop where
  | identity : Statehood C C.iob.I
  | application (x y : C.Carrier) : Statehood C x → Statehood C y → Statehood C (C.iob.O x y)

/--
The induced quotient carrier structure, containing the emergent AdmissibleSARI
and next-level IOB structures.
-/
structure QuotientCarrier (C : AdmCarrier) (step : C.Carrier → C.Carrier → Prop)
    (confluent : ∀ (s s1 s2 : C.Carrier), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
      ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3) where
  Carrier : Type
  iob : IOB Carrier
  sari : AdmissibleSARI Carrier iob.O

/--
The Recurrence Step construction:
If a carrier C admits an IOB structure and is closed under self-application,
its operational quotient constructively yields an SARI-typed operational structure
and a new IOB embedding.
-/
def recurrence_step (C : AdmCarrier) (step : C.Carrier → C.Carrier → Prop)
    (confluent : ∀ (s s1 s2 : C.Carrier), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
      ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3)
    (O_compat : ∀ c1 c2 d1 d2, OperationalEq step c1 d1 → OperationalEq step c2 d2 → OperationalEq step (C.iob.O c1 c2) (C.iob.O d1 d2))
    (B_compat : ∀ c d, OperationalEq step c d → OperationalEq step (C.iob.B c) (C.iob.B d)) :
    QuotientCarrier C step confluent :=
  let Q := Quotient (operSetoid step confluent)
  let lift_I := Quotient.mk (operSetoid step confluent) C.iob.I
  let lift_O (q1 q2 : Q) : Q := Quotient.liftOn₂ q1 q2
    (fun c1 c2 => Quotient.mk (operSetoid step confluent) (C.iob.O c1 c2))
    (fun c1 c2 d1 d2 h1 h2 => by
      apply Quotient.sound
      exact O_compat c1 c2 d1 d2 h1 h2)
  let lift_B (q : Q) : Q := Quotient.liftOn q
    (fun c => Quotient.mk (operSetoid step confluent) (C.iob.B c))
    (fun c d h => by
      apply Quotient.sound
      exact B_compat c d h)
  let iob_next : IOB Q := { I := lift_I, O := lift_O, B := lift_B }
  let S_pred (q : Q) : Prop := ∃ c, q = Quotient.mk (operSetoid step confluent) c ∧ Statehood C c
  let A_pred (q1 q2 : Q) : Prop := ∃ q3, q2 = lift_O q1 q3 ∨ q2 = lift_O q3 q1
  let R_pred (q1 q2 : Q) : Prop := ∃ c1 c2, q1 = Quotient.mk (operSetoid step confluent) c1 ∧ q2 = Quotient.mk (operSetoid step confluent) c2 ∧ step c1 c2 ∧ q1 ≠ q2
  let I_pred (q : Q) : Prop := Quotient.liftOn q (fun c => C.F c = c) (fun c1 c2 _ => by
    have h1 := C.is_fixed_point c1
    have h2 := C.is_fixed_point c2
    ext
    exact ⟨fun _ => h2, fun _ => h1⟩)
  {
    Carrier := Q
    iob := iob_next
    sari := {
      S := S_pred
      A := A_pred
      R := R_pred
      I := I_pred
      confluent := fun q q1 q2 h1 h2 => by
        rcases h1 with ⟨c1, c2, hq1, hq1_eq, hstep1, hne1⟩
        rcases h2 with ⟨d1, d2, hq2, hq2_eq, hstep2, hne2⟩
        have h_eq : Quotient.mk (operSetoid step confluent) c1 = Quotient.mk (operSetoid step confluent) d1 := hq1.symm.trans hq2
        have h_op : OperationalEq step c1 d1 := Quotient.exact (s := operSetoid step confluent) h_eq
        rcases h_op with ⟨w, hw1, hw2⟩
        have ⟨w1, hw1a, hw1b⟩ := confluent c1 c2 w (Relation.ReflTransGen.single hstep1) hw1
        have ⟨w2, hw2a, hw2b⟩ := confluent d1 d2 w (Relation.ReflTransGen.single hstep2) hw2
        have ⟨w3, hw3a, hw3b⟩ := confluent w w1 w2 hw1b hw2b
        have hc2 : Relation.ReflTransGen step c2 w3 := Relation.ReflTransGen.trans hw1a hw3a
        have hd2 : Relation.ReflTransGen step d2 w3 := Relation.ReflTransGen.trans hw2a hw3b
        have h_op2 : OperationalEq step c2 d2 := ⟨w3, hc2, hd2⟩
        have heq_q : q1 = q2 := by
          rw [hq1_eq, hq2_eq]
          apply Quotient.sound (s := operSetoid step confluent)
          exact h_op2
        subst heq_q
        exact ⟨q1, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      fixed_point := fun q => by
        constructor
        { intro _ q' hR
          rcases hR with ⟨c1, c2, hq, hq', hstep, hne⟩
          have h_op : OperationalEq step c1 c2 := ⟨c2, Relation.ReflTransGen.single hstep, Relation.ReflTransGen.refl⟩
          have heq : Quotient.mk (operSetoid step confluent) c1 = Quotient.mk (operSetoid step confluent) c2 := Quotient.sound (s := operSetoid step confluent) h_op
          rw [← hq, ← hq'] at heq
          exact hne heq }
        { intro _
          exact Quotient.inductionOn q (fun c => C.is_fixed_point c) }
      pairing_closure := fun q1 q2 h1 h2 => by
        rcases h1 with ⟨c1, hq1, hs1⟩
        rcases h2 with ⟨c2, hq2, hs2⟩
        use C.iob.O c1 c2
        constructor
        { rw [hq1, hq2]
          rfl }
        { exact Statehood.application c1 c2 hs1 hs2 }
    }
  }

/--
An Admissible Kernel extends the base Kernel with the Operational SARI Quartet.
-/
structure AdmissibleKernel extends Kernel where
  O : Carrier → Carrier → Carrier
  sari : AdmissibleSARI Carrier O

/--
Universal Mapping Theorem:
Constructs a category-theoretic AdmissibleKernel from the recurrence quotient space Q of an AdmCarrier C,
given a sound and coherent projection/embedding mapping to ISKSubtype.

NOTE: This definition uses `Quotient.out` to construct the decode representative,
making it noncomputable and dependent on the Axiom of Choice. Downstream Kernels
constructed via this mapping are suitable for logical verification rather than decidable computation.
-/
noncomputable def recurrence_to_Kernel (C : AdmCarrier) (step : C.Carrier → C.Carrier → Prop)
    (confluent : ∀ (s s1 s2 : C.Carrier), Relation.ReflTransGen step s s1 → Relation.ReflTransGen step s s2 →
      ∃ s3, Relation.ReflTransGen step s1 s3 ∧ Relation.ReflTransGen step s2 s3)
    (O_compat : ∀ c1 c2 d1 d2, OperationalEq step c1 d1 → OperationalEq step c2 d2 → OperationalEq step (C.iob.O c1 c2) (C.iob.O d1 d2))
    (B_compat : ∀ c d, OperationalEq step c d → OperationalEq step (C.iob.B c) (C.iob.B d))
    (view_of : ISKSubtype → C.Carrier)
    (decode : C.Carrier → ISKSubtype)
    (sound : ∀ (t u : ISKSubtype), OperEq t u → OperationalEq step (view_of t) (view_of u))
    (decode_view : ∀ (t : ISKSubtype), OperEq (decode (view_of t)) t)
    (view_eq_decode : ∀ (c : C.Carrier), OperationalEq step (view_of (decode c)) c)
    (decode_eq : ∀ (c1 c2 : C.Carrier), OperationalEq step c1 c2 → OperEq (decode c1) (decode c2)) :
    AdmissibleKernel :=
  let Q := Quotient (operSetoid step confluent)
  let lift_O (q1 q2 : Q) : Q := Quotient.liftOn₂ q1 q2
    (fun c1 c2 => Quotient.mk (operSetoid step confluent) (C.iob.O c1 c2))
    (fun c1 c2 d1 d2 h1 h2 => by
      apply Quotient.sound (s := operSetoid step confluent)
      exact O_compat c1 c2 d1 d2 h1 h2)
  {
    toKernel := {
      Carrier := Q
      view_of t := Quotient.mk _ (view_of t)
      view_eq q1 q2 := q1 = q2
      is_equiv := {
        refl := fun _ => rfl
        symm := fun h => h.symm
        trans := fun h1 h2 => h1.trans h2
      }
      sound t u h := Quotient.sound (s := operSetoid step confluent) (sound t u h)
      decode q := decode (Quotient.out q)
      decode_view t := by
        have h_out := Quotient.exact (s := operSetoid step confluent) (Quotient.out_eq (s := operSetoid step confluent) (Quotient.mk (operSetoid step confluent) (view_of t)))
        have h_dec := decode_eq (Quotient.out (Quotient.mk (operSetoid step confluent) (view_of t))) (view_of t) h_out
        exact OperEq.trans h_dec (decode_view t)
      view_eq_decode q := by
        have h1 := Quotient.sound (s := operSetoid step confluent) (view_eq_decode (Quotient.out q))
        have h2 := Quotient.out_eq (s := operSetoid step confluent) q
        exact h1.trans h2
      decode_eq q1 q2 h := by
        have h_eq : OperationalEq step (Quotient.out q1) (Quotient.out q2) := by
          have heq : Quotient.mk (operSetoid step confluent) (Quotient.out q1) = Quotient.mk (operSetoid step confluent) (Quotient.out q2) := by
            rw [Quotient.out_eq (s := operSetoid step confluent) q1, Quotient.out_eq (s := operSetoid step confluent) q2, h]
          exact Quotient.exact (s := operSetoid step confluent) heq
        exact decode_eq (Quotient.out q1) (Quotient.out q2) h_eq
    }
    O := lift_O
    sari := {
      S := fun q => ∃ c, q = Quotient.mk (operSetoid step confluent) c ∧ Statehood C c
      A := fun q1 q2 => ∃ q3, q2 = lift_O q1 q3 ∨ q2 = lift_O q3 q1
      R := fun q1 q2 => ∃ c1 c2, q1 = Quotient.mk (operSetoid step confluent) c1 ∧ q2 = Quotient.mk (operSetoid step confluent) c2 ∧ step c1 c2 ∧ q1 ≠ q2
      I := fun q => Quotient.liftOn q (fun c => C.F c = c) (fun c1 c2 _ => by
        have h1 := C.is_fixed_point c1
        have h2 := C.is_fixed_point c2
        ext
        exact ⟨fun _ => h2, fun _ => h1⟩)
      confluent := fun q q1 q2 h1 h2 => by
        rcases h1 with ⟨c1, c2, hq1, hq1_eq, hstep1, hne1⟩
        rcases h2 with ⟨d1, d2, hq2, hq2_eq, hstep2, hne2⟩
        have h_eq : Quotient.mk (operSetoid step confluent) c1 = Quotient.mk (operSetoid step confluent) d1 := hq1.symm.trans hq2
        have h_op : OperationalEq step c1 d1 := Quotient.exact (s := operSetoid step confluent) h_eq
        rcases h_op with ⟨w, hw1, hw2⟩
        have ⟨w1, hw1a, hw1b⟩ := confluent c1 c2 w (Relation.ReflTransGen.single hstep1) hw1
        have ⟨w2, hw2a, hw2b⟩ := confluent d1 d2 w (Relation.ReflTransGen.single hstep2) hw2
        have ⟨w3, hw3a, hw3b⟩ := confluent w w1 w2 hw1b hw2b
        have hc2 : Relation.ReflTransGen step c2 w3 := Relation.ReflTransGen.trans hw1a hw3a
        have hd2 : Relation.ReflTransGen step d2 w3 := Relation.ReflTransGen.trans hw2a hw3b
        have h_op2 : OperationalEq step c2 d2 := ⟨w3, hc2, hd2⟩
        have heq_q : q1 = q2 := by
          rw [hq1_eq, hq2_eq]
          apply Quotient.sound (s := operSetoid step confluent)
          exact h_op2
        subst heq_q
        exact ⟨q1, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      fixed_point := fun q => by
        constructor
        { intro _ q' hR
          rcases hR with ⟨c1, c2, hq, hq', hstep, hne⟩
          have h_op : OperationalEq step c1 c2 := ⟨c2, Relation.ReflTransGen.single hstep, Relation.ReflTransGen.refl⟩
          have heq : Quotient.mk (operSetoid step confluent) c1 = Quotient.mk (operSetoid step confluent) c2 := Quotient.sound (s := operSetoid step confluent) h_op
          rw [← hq, ← hq'] at heq
          exact hne heq }
        { intro _
          exact Quotient.inductionOn q (fun c => C.is_fixed_point c) }
      pairing_closure := fun q1 q2 h1 h2 => by
        rcases h1 with ⟨c1, hq1, hs1⟩
        rcases h2 with ⟨c2, hq2, hs2⟩
        use C.iob.O c1 c2
        constructor
        { rw [hq1, hq2]
          rfl }
        { exact Statehood.application c1 c2 hs1 hs2 }
    }
  }

end ISAR
