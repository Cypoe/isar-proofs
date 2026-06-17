import ISAR.ISARMatrices
import ISAR.InvariantLayer

namespace ISAR

/- =========================================================
   1. Matrix Operations for Matrix4
   ========================================================= -/

/-- Matrix addition. -/
def add (A B : Matrix4) : Matrix4 where
  m00 := A.m00 + B.m00
  m01 := A.m01 + B.m01
  m02 := A.m02 + B.m02
  m03 := A.m03 + B.m03
  m10 := A.m10 + B.m10
  m11 := A.m11 + B.m11
  m12 := A.m12 + B.m12
  m13 := A.m13 + B.m13
  m20 := A.m20 + B.m20
  m21 := A.m21 + B.m21
  m22 := A.m22 + B.m22
  m23 := A.m23 + B.m23
  m30 := A.m30 + B.m30
  m31 := A.m31 + B.m31
  m32 := A.m32 + B.m32
  m33 := A.m33 + B.m33

instance : Add Matrix4 where
  add := add

/-- Matrix negation. -/
def neg (A : Matrix4) : Matrix4 where
  m00 := -A.m00; m01 := -A.m01; m02 := -A.m02; m03 := -A.m03
  m10 := -A.m10; m11 := -A.m11; m12 := -A.m12; m13 := -A.m13
  m20 := -A.m20; m21 := -A.m21; m22 := -A.m22; m23 := -A.m23
  m30 := -A.m30; m31 := -A.m31; m32 := -A.m32; m33 := -A.m33

instance : Neg Matrix4 where
  neg := neg

/-- Matrix subtraction. -/
def sub (A B : Matrix4) : Matrix4 :=
  add A (neg B)

instance : Sub Matrix4 where
  sub := sub


/- =========================================================
   2. Function ↔ Matrix Conversions
   ========================================================= -/

/-- Convert a 4x4 function over Fin 4 to a Matrix4. -/
def toMatrix4 (f : Fin 4 → Fin 4 → Int) : Matrix4 where
  m00 := f 0 0
  m01 := f 0 1
  m02 := f 0 2
  m03 := f 0 3
  m10 := f 1 0
  m11 := f 1 1
  m12 := f 1 2
  m13 := f 1 3
  m20 := f 2 0
  m21 := f 2 1
  m22 := f 2 2
  m23 := f 2 3
  m30 := f 3 0
  m31 := f 3 1
  m32 := f 3 2
  m33 := f 3 3

/-- Convert a Matrix4 back to a 4x4 function over Fin 4. -/
def fromMatrix4 (M : Matrix4) (i j : Fin 4) : Int :=
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => M.m00
  | ⟨0, _⟩, ⟨1, _⟩ => M.m01
  | ⟨0, _⟩, ⟨2, _⟩ => M.m02
  | ⟨0, _⟩, ⟨3, _⟩ => M.m03
  | ⟨1, _⟩, ⟨0, _⟩ => M.m10
  | ⟨1, _⟩, ⟨1, _⟩ => M.m11
  | ⟨1, _⟩, ⟨2, _⟩ => M.m12
  | ⟨1, _⟩, ⟨3, _⟩ => M.m13
  | ⟨2, _⟩, ⟨0, _⟩ => M.m20
  | ⟨2, _⟩, ⟨1, _⟩ => M.m21
  | ⟨2, _⟩, ⟨2, _⟩ => M.m22
  | ⟨2, _⟩, ⟨3, _⟩ => M.m23
  | ⟨3, _⟩, ⟨0, _⟩ => M.m30
  | ⟨3, _⟩, ⟨1, _⟩ => M.m31
  | ⟨3, _⟩, ⟨2, _⟩ => M.m32
  | ⟨3, _⟩, ⟨3, _⟩ => M.m33

/-- Theorem: converting a matrix to function and back is the identity. -/
theorem toMatrix4_fromMatrix4 (M : Matrix4) : toMatrix4 (fromMatrix4 M) = M := by
  rfl

/-- Theorem: converting a function to matrix and back is the identity. -/
theorem fromMatrix4_toMatrix4 (f : Fin 4 → Fin 4 → Int) : fromMatrix4 (toMatrix4 f) = f := by
  funext i j
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => rfl
  | ⟨0, _⟩, ⟨2, _⟩ => rfl
  | ⟨0, _⟩, ⟨3, _⟩ => rfl
  | ⟨1, _⟩, ⟨0, _⟩ => rfl
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨1, _⟩, ⟨2, _⟩ => rfl
  | ⟨1, _⟩, ⟨3, _⟩ => rfl
  | ⟨2, _⟩, ⟨0, _⟩ => rfl
  | ⟨2, _⟩, ⟨1, _⟩ => rfl
  | ⟨2, _⟩, ⟨2, _⟩ => rfl
  | ⟨2, _⟩, ⟨3, _⟩ => rfl
  | ⟨3, _⟩, ⟨0, _⟩ => rfl
  | ⟨3, _⟩, ⟨1, _⟩ => rfl
  | ⟨3, _⟩, ⟨2, _⟩ => rfl
  | ⟨3, _⟩, ⟨3, _⟩ => rfl


/- =========================================================
   3. Basis Algebra Generation
   ========================================================= -/

/-- The nilpotent core operator K1 representing konst combinator's matrix. -/
def K1 : Matrix4 := I1 * R1 * A1 * S1

/-- The ISK monoid: what ISK can represent under application (multiplication). -/
inductive ISKAlgebra : Matrix4 → Prop where
  | I : ISKAlgebra I1
  | S : ISKAlgebra S1
  | K : ISKAlgebra K1
  | zero : ISKAlgebra zero
  | mul (M1 M2 : Matrix4) (h1 : ISKAlgebra M1) (h2 : ISKAlgebra M2) : ISKAlgebra (M1 * M2)

/-- The full ISAR monoid: what requires R and A (dup and swap). -/
inductive BasisAlgebra : Matrix4 → Prop where
  | I : BasisAlgebra I1
  | R : BasisAlgebra R1
  | A : BasisAlgebra A1
  | S : BasisAlgebra S1
  | zero : BasisAlgebra zero
  | mul (M1 M2 : Matrix4) (h1 : BasisAlgebra M1) (h2 : BasisAlgebra M2) : BasisAlgebra (M1 * M2)

/-- Constructive term signature valuation function mapping ITerm directly to Matrix4. -/
def term_signature_val : ITerm → Matrix4
  | .var _   => zero
  | .norm    => I1
  | .sₛ      => S1
  | .konst   => I1 * R1 * A1 * S1
  | .dup     => A1
  | .swap    => R1
  | .comp    => zero
  | .app f x => term_signature_val f * term_signature_val x

/-- Bijective term signature mapping in the substrate. -/
noncomputable def term_signature (t : ISKSubtype) : Fin 4 → Fin 4 → Int :=
  fromMatrix4 (term_signature_val t.val)

/-- The matrix representative of a substrate term. -/
noncomputable def term_matrix (t : ISKSubtype) : Matrix4 :=
  toMatrix4 (term_signature t)

/-- Theorem: The identity term I maps to I1. -/
theorem term_matrix_I : term_matrix ⟨ITerm.norm, ISKTerm.norm⟩ = I1 := by
  dsimp [term_matrix, term_signature, term_signature_val]
  rw [toMatrix4_fromMatrix4]

/-- Theorem: The combinator S maps to S1. -/
theorem term_matrix_S : term_matrix ⟨ITerm.sₛ, ISKTerm.sₛ⟩ = S1 := by
  dsimp [term_matrix, term_signature, term_signature_val]
  rw [toMatrix4_fromMatrix4]

/-- Theorem: Application of terms corresponds to matrix multiplication. -/
theorem term_matrix_mul (t1 t2 : ISKSubtype) :
    term_matrix (app_raw t1 t2) = term_matrix t1 * term_matrix t2 := by
  dsimp [term_matrix, term_signature]
  rw [toMatrix4_fromMatrix4, toMatrix4_fromMatrix4, toMatrix4_fromMatrix4]
  rfl

/-- Theorem: The zero matrix is constructively representable by applying konst to konst. -/
theorem term_matrix_zero : ∃ (t : ISKSubtype), term_matrix t = zero := by
  have h_eq : term_matrix (app_raw ⟨ITerm.konst, ISKTerm.konst⟩ ⟨ITerm.konst, ISKTerm.konst⟩) = zero := by
    dsimp [term_matrix, term_signature, term_signature_val]
    rw [toMatrix4_fromMatrix4]
    exact K1_nilpotent
  exact ⟨app_raw ⟨ITerm.konst, ISKTerm.konst⟩ ⟨ITerm.konst, ISKTerm.konst⟩, h_eq⟩


/- =========================================================
   4. Row Invariant Preservation & Unreachability Proofs
   ========================================================= -/

def Row1OK (M : Matrix4) : Prop :=
  (M.m10 = 0 ∧ M.m11 = 0 ∧ M.m12 = 0 ∧ M.m13 = 0) ∨
  (M.m10 = 0 ∧ M.m11 = 1 ∧ M.m12 = 0 ∧ M.m13 = 0)

def Row3OK (M : Matrix4) : Prop :=
  (M.m30 = 0 ∧ M.m31 = 0 ∧ M.m32 = 0 ∧ M.m33 = 0) ∨
  (M.m30 = 0 ∧ M.m31 = 0 ∧ M.m32 = 0 ∧ M.m33 = 1)

theorem Row1OK_mul (M1 M2 : Matrix4) (h1 : Row1OK M1) (h2 : Row1OK M2) : Row1OK (M1 * M2) := by
  change Row1OK (mul M1 M2)
  unfold Row1OK mul
  cases h1 with
  | inl h1a =>
      cases h1a with
      | intro h10 h_rest1 =>
      cases h_rest1 with
      | intro h11 h_rest2 =>
      cases h_rest2 with
      | intro h12 h13 =>
          rw [h10, h11, h12, h13]
          left
          dsimp
          refine ⟨by simp, ⟨by simp, ⟨by simp, by simp⟩⟩⟩
  | inr h1b =>
      cases h1b with
      | intro h10 h_rest1 =>
      cases h_rest1 with
      | intro h11 h_rest2 =>
      cases h_rest2 with
      | intro h12 h13 =>
          rw [h10, h11, h12, h13]
          dsimp
          have h_m10 : 0 * M2.m00 + 1 * M2.m10 + 0 * M2.m20 + 0 * M2.m30 = M2.m10 := by simp
          have h_m11 : 0 * M2.m01 + 1 * M2.m11 + 0 * M2.m21 + 0 * M2.m31 = M2.m11 := by simp
          have h_m12 : 0 * M2.m02 + 1 * M2.m12 + 0 * M2.m22 + 0 * M2.m32 = M2.m12 := by simp
          have h_m13 : 0 * M2.m03 + 1 * M2.m13 + 0 * M2.m23 + 0 * M2.m33 = M2.m13 := by simp
          rw [h_m10, h_m11, h_m12, h_m13]
          exact h2

theorem Row3OK_mul (M1 M2 : Matrix4) (h1 : Row3OK M1) (h2 : Row3OK M2) : Row3OK (M1 * M2) := by
  change Row3OK (mul M1 M2)
  unfold Row3OK mul
  cases h1 with
  | inl h1a =>
      cases h1a with
      | intro h30 h_rest1 =>
      cases h_rest1 with
      | intro h31 h_rest2 =>
      cases h_rest2 with
      | intro h32 h33 =>
          rw [h30, h31, h32, h33]
          left
          dsimp
          refine ⟨by simp, ⟨by simp, ⟨by simp, by simp⟩⟩⟩
  | inr h1b =>
      cases h1b with
      | intro h30 h_rest1 =>
      cases h_rest1 with
      | intro h31 h_rest2 =>
      cases h_rest2 with
      | intro h32 h33 =>
          rw [h30, h31, h32, h33]
          dsimp
          have h_m30 : 0 * M2.m00 + 0 * M2.m10 + 0 * M2.m20 + 1 * M2.m30 = M2.m30 := by simp
          have h_m31 : 0 * M2.m01 + 0 * M2.m11 + 0 * M2.m21 + 1 * M2.m31 = M2.m31 := by simp
          have h_m32 : 0 * M2.m02 + 0 * M2.m12 + 0 * M2.m22 + 1 * M2.m32 = M2.m32 := by simp
          have h_m33 : 0 * M2.m03 + 0 * M2.m13 + 0 * M2.m23 + 1 * M2.m33 = M2.m33 := by simp
          rw [h_m30, h_m31, h_m32, h_m33]
          exact h2

theorem Row1OK_term (t : ITerm) (h : ISKTerm t) : Row1OK (term_signature_val t) := by
  induction h with
  | norm =>
      dsimp [term_signature_val, I1, Row1OK]
      left
      refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  | konst =>
      dsimp [term_signature_val, Row1OK]
      left
      refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  | sₛ =>
      dsimp [term_signature_val, S1, Row1OK]
      right
      refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  | app hf hx ihf ihx =>
      dsimp [term_signature_val]
      exact Row1OK_mul (term_signature_val _) (term_signature_val _) ihf ihx

theorem Row3OK_term (t : ITerm) (h : ISKTerm t) : Row3OK (term_signature_val t) := by
  induction h with
  | norm =>
      dsimp [term_signature_val, I1, Row3OK]
      left
      refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  | konst =>
      dsimp [term_signature_val, Row3OK]
      left
      refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  | sₛ =>
      dsimp [term_signature_val, S1, Row3OK]
      right
      refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  | app hf hx ihf ihx =>
      dsimp [term_signature_val]
      exact Row3OK_mul (term_signature_val _) (term_signature_val _) ihf ihx

/-- Theorem: Rotation matrix R1 is unreachable in the pure ISK fragment. -/
theorem term_matrix_R_unreachable (t : ISKSubtype) : term_matrix t ≠ R1 := by
  intro h_eq
  have h_val : term_matrix t = term_signature_val t.val := by
    dsimp [term_matrix, term_signature]
    rw [toMatrix4_fromMatrix4]
  have h_sig_eq : term_signature_val t.val = R1 := by
    rw [← h_val, h_eq]
  have h_ok := Row3OK_term t.val t.property
  rw [h_sig_eq] at h_ok
  dsimp [R1, Row3OK] at h_ok
  cases h_ok with
  | inl h_ok_a =>
      cases h_ok_a with
      | intro _ h_rest1 =>
      cases h_rest1 with
      | intro _ h_rest2 =>
      cases h_rest2 with
      | intro h_contra _ =>
          contradiction
  | inr h_ok_b =>
      cases h_ok_b with
      | intro _ h_rest1 =>
      cases h_rest1 with
      | intro _ h_rest2 =>
      cases h_rest2 with
      | intro h_contra _ =>
          contradiction

/-- Theorem: Adjacency matrix A1 is unreachable in the pure ISK fragment. -/
theorem term_matrix_A_unreachable (t : ISKSubtype) : term_matrix t ≠ A1 := by
  intro h_eq
  have h_val : term_matrix t = term_signature_val t.val := by
    dsimp [term_matrix, term_signature]
    rw [toMatrix4_fromMatrix4]
  have h_sig_eq : term_signature_val t.val = A1 := by
    rw [← h_val, h_eq]
  have h_ok := Row1OK_term t.val t.property
  rw [h_sig_eq] at h_ok
  dsimp [A1, Row1OK] at h_ok
  cases h_ok with
  | inl h_ok_a =>
      cases h_ok_a with
      | intro h_contra _ =>
          contradiction
  | inr h_ok_b =>
      cases h_ok_b with
      | intro h_contra _ =>
          contradiction


/- =========================================================
   5. Monoid Expressive Completeness Theorems
   ========================================================= -/

/-- Expressive completeness of the pure functional ISK fragment monoid.
    Any matrix generated in ISKAlgebra is representable by an ISKSubtype term. -/
theorem isk_expressive_completeness (M : Matrix4) (h : ISKAlgebra M) :
    ∃ (t : ISKSubtype), term_matrix t = M := by
  induction h with
  | I =>
      exact ⟨⟨ITerm.norm, ISKTerm.norm⟩, term_matrix_I⟩
  | S =>
      exact ⟨⟨ITerm.sₛ, ISKTerm.sₛ⟩, term_matrix_S⟩
  | K =>
      have h_K : term_matrix ⟨ITerm.konst, ISKTerm.konst⟩ = K1 := by
        dsimp [term_matrix, term_signature, term_signature_val, K1]
        rw [toMatrix4_fromMatrix4]
      exact ⟨⟨ITerm.konst, ISKTerm.konst⟩, h_K⟩
  | zero =>
      exact term_matrix_zero
  | mul M1 M2 h1 h2 ih1 ih2 =>
      let ⟨t1, ht1⟩ := ih1
      let ⟨t2, ht2⟩ := ih2
      exact ⟨app_raw t1 t2, by rw [term_matrix_mul, ht1, ht2]⟩

/-- Expressive completeness of the full ISAR monoid.
    Any matrix generated in BasisAlgebra is representable by an ITerm. -/
theorem basis_expressive_completeness (M : Matrix4) (h : BasisAlgebra M) :
    ∃ (t : ITerm), term_signature_val t = M := by
  induction h with
  | I =>
      exact ⟨ITerm.norm, rfl⟩
  | R =>
      exact ⟨ITerm.swap, rfl⟩
  | A =>
      exact ⟨ITerm.dup, rfl⟩
  | S =>
      exact ⟨ITerm.sₛ, rfl⟩
  | zero =>
      exact ⟨ITerm.app ITerm.konst ITerm.konst, K1_nilpotent⟩
  | mul M1 M2 h1 h2 ih1 ih2 =>
      let ⟨t1, ht1⟩ := ih1
      let ⟨t2, ht2⟩ := ih2
      exact ⟨ITerm.app t1 t2, by dsimp [term_signature_val]; rw [ht1, ht2]⟩

end ISAR
