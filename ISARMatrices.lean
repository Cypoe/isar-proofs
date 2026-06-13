namespace ISAR

/--
A concrete 4x4 matrix over the integers Int.
Using a structure allows automatic derivation of decidable equality,
meaning equality of computed matrices is decidable by computation (via rfl/decide).
-/
structure Matrix4 where
  m00 : Int
  m01 : Int
  m02 : Int
  m03 : Int
  m10 : Int
  m11 : Int
  m12 : Int
  m13 : Int
  m20 : Int
  m21 : Int
  m22 : Int
  m23 : Int
  m30 : Int
  m31 : Int
  m32 : Int
  m33 : Int
deriving DecidableEq, Repr

/-- Matrix multiplication. -/
def mul (A B : Matrix4) : Matrix4 where
  m00 := A.m00 * B.m00 + A.m01 * B.m10 + A.m02 * B.m20 + A.m03 * B.m30
  m01 := A.m00 * B.m01 + A.m01 * B.m11 + A.m02 * B.m21 + A.m03 * B.m31
  m02 := A.m00 * B.m02 + A.m01 * B.m12 + A.m02 * B.m22 + A.m03 * B.m32
  m03 := A.m00 * B.m03 + A.m01 * B.m13 + A.m02 * B.m23 + A.m03 * B.m33

  m10 := A.m10 * B.m00 + A.m11 * B.m10 + A.m12 * B.m20 + A.m13 * B.m30
  m11 := A.m10 * B.m01 + A.m11 * B.m11 + A.m12 * B.m21 + A.m13 * B.m31
  m12 := A.m10 * B.m02 + A.m11 * B.m12 + A.m12 * B.m22 + A.m13 * B.m32
  m13 := A.m10 * B.m03 + A.m11 * B.m13 + A.m12 * B.m23 + A.m13 * B.m33

  m20 := A.m20 * B.m00 + A.m21 * B.m10 + A.m22 * B.m20 + A.m23 * B.m30
  m21 := A.m20 * B.m01 + A.m21 * B.m11 + A.m22 * B.m21 + A.m23 * B.m31
  m22 := A.m20 * B.m02 + A.m21 * B.m12 + A.m22 * B.m22 + A.m23 * B.m32
  m23 := A.m20 * B.m03 + A.m21 * B.m13 + A.m22 * B.m23 + A.m23 * B.m33

  m30 := A.m30 * B.m00 + A.m31 * B.m10 + A.m32 * B.m20 + A.m33 * B.m30
  m31 := A.m30 * B.m01 + A.m31 * B.m11 + A.m32 * B.m21 + A.m33 * B.m31
  m32 := A.m30 * B.m02 + A.m31 * B.m12 + A.m32 * B.m22 + A.m33 * B.m32
  m33 := A.m30 * B.m03 + A.m31 * B.m13 + A.m32 * B.m23 + A.m33 * B.m33

instance : Mul Matrix4 where
  mul := mul

/-- The zero matrix. -/
def zero : Matrix4 where
  m00 := 0; m01 := 0; m02 := 0; m03 := 0
  m10 := 0; m11 := 0; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 0; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 0

instance : Zero Matrix4 where
  zero := zero

/- =========================================================
   1. ISAR Matrices - Version 1 (from isar_categorical_proof.py)
   ========================================================= -/

/-- Invariant layer projection matrix (I). -/
def I1 : Matrix4 where
  m00 := 1; m01 := 0; m02 := 0; m03 := 0
  m10 := 0; m11 := 0; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 0

/-- Rotation matrix (R). -/
def R1 : Matrix4 where
  m00 := 1; m01 := 0; m02 := 0; m03 := 0
  m10 := 0; m11 := 0; m12 := 0; m13 := 0
  m20 := 0; m21 := 1; m22 := 0; m23 := 0
  m30 := 0; m31 := 0; m32 := 1; m33 := 0

/-- Adjacency matrix (A). -/
def A1 : Matrix4 where
  m00 := 0; m01 := 0; m02 := 0; m03 := 0
  m10 := 1; m11 := 0; m12 := 0; m13 := 0
  m20 := 0; m21 := 1; m22 := 0; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 0

/-- Selection matrix (S). -/
def S1 : Matrix4 where
  m00 := 1; m01 := 1; m02 := 0; m03 := 0
  m10 := 0; m11 := 1; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 1

/-- Theorem: The invariant projection matrix I1 is idempotent. -/
theorem I1_idempotent : I1 * I1 = I1 := rfl

/-- Theorem: The core rewrite operator K1 = I1 * R1 * A1 * S1 is nilpotent (K1² = 0). -/
theorem K1_nilpotent : (I1 * R1 * A1 * S1) * (I1 * R1 * A1 * S1) = zero := rfl


/- =========================================================
   2. ISAR Matrices - Version 2 (from verify_isar_ZFC.py)
   ========================================================= -/

/-- Invariant layer projection matrix (I) - version 2. -/
def I2 : Matrix4 where
  m00 := 1; m01 := 0; m02 := 0; m03 := 0
  m10 := 0; m11 := 0; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 0

/-- Rotation matrix (R) - version 2. -/
def R2 : Matrix4 where
  m00 := 1; m01 := 0; m02 := 0; m03 := 0
  m10 := 0; m11 := 0; m12 := 0; m13 := 1
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 0

/-- Adjacency matrix (A) - version 2. -/
def A2 : Matrix4 where
  m00 := 0; m01 := 0; m02 := 0; m03 := 0
  m10 := 1; m11 := 0; m12 := 0; m13 := 0
  m20 := 0; m21 := 1; m22 := 0; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 0

/-- Selection matrix (S) - version 2. -/
def S2 : Matrix4 where
  m00 := 1; m01 := 1; m02 := 0; m03 := 0
  m10 := 0; m11 := 1; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 1

/-- Theorem: The invariant projection matrix I2 is idempotent. -/
theorem I2_idempotent : I2 * I2 = I2 := rfl

/-- Theorem: The core rewrite operator K2 = I2 * R2 * A2 * S2 is nilpotent (K2² = 0). -/
theorem K2_nilpotent : (I2 * R2 * A2 * S2) * (I2 * R2 * A2 * S2) = zero := rfl


/- =========================================================
   3. Gauge Equivalence (Isomorphism Verification)
   ========================================================= -/

/-- The 4D Identity matrix. -/
def I_id : Matrix4 where
  m00 := 1; m01 := 0; m02 := 0; m03 := 0
  m10 := 0; m11 := 1; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 1

/-- Lower-triangular gauge transformation matrix (P). -/
def P : Matrix4 where
  m00 := 1; m01 := 0; m02 := 0; m03 := 0
  m10 := 1; m11 := 1; m12 := 0; m13 := 0
  m20 := 0; m21 := 0; m22 := 1; m23 := 0
  m30 := 0; m31 := 0; m32 := 0; m33 := 1

/-- Inverse gauge transformation matrix (P_inv). -/
def P_inv : Matrix4 where
  m00 := 1;  m01 := 0; m02 := 0; m03 := 0
  m10 := -1; m11 := 1; m12 := 0; m13 := 0
  m20 := 0;  m21 := 0; m22 := 1; m23 := 0
  m30 := 0;  m31 := 0; m32 := 0; m33 := 1

/-- Theorem: P_inv is the left inverse of P. -/
theorem P_inv_left : P_inv * P = I_id := rfl

/-- Theorem: P_inv is the right inverse of P. -/
theorem P_inv_right : P * P_inv = I_id := rfl

/--
Theorem: Gauge Equivalence.
The two kernel representations are conjugate (similar) via the gauge matrix P.
This formally unifies the two inconsistent representations of R used in the python scripts.
-/
theorem K1_K2_gauge_equiv : P * (I1 * R1 * A1 * S1) * P_inv = (I2 * R2 * A2 * S2) := rfl

end ISAR

