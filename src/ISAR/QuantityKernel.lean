import ISAR.KernelCategory
import ISAR.HFSetEncoding

namespace ISAR

/- =========================================================
   1. Algebraic Types for Structural Arithmetic
   ========================================================= -/

/-- Exact rational numbers represented as a pair of numerator and denominator. -/
structure Rational where
  num : Int
  den : Nat
deriving DecidableEq, Repr

def Rational.mul (r1 r2 : Rational) : Rational where
  num := r1.num * r2.num
  den := r1.den * r2.den

def Rational.add (r1 r2 : Rational) : Rational where
  num := r1.num * Int.ofNat r2.den + r2.num * Int.ofNat r1.den
  den := r1.den * r2.den

/-- Base SI dimensions. -/
inductive DimBase where
  | L | T | M | I | Θ | N | J
deriving DecidableEq, Repr

/-- Dimensional expressions forming a free abelian group. -/
inductive DimExpr where
  | DimUnit : DimExpr
  | DimBase : DimBase → Int → DimExpr
  | DimMul : DimExpr → DimExpr → DimExpr
  | DimInv : DimExpr → DimExpr
deriving DecidableEq, Repr

/-- Symbolic base constants and expressions. -/
inductive SymbolBase where
  | Pi : SymbolBase
  | E : SymbolBase
  | Sqrt : Rational → SymbolBase
  | Symbolic : String → SymbolBase
deriving DecidableEq, Repr

/-- Symbolic relational layer allowing exact algebraic manipulations. -/
inductive SymbolExpr where
  | Rational : Rational → SymbolExpr
  | Add : SymbolExpr → SymbolExpr → SymbolExpr
  | Mul : SymbolExpr → SymbolExpr → SymbolExpr
  | Pow : SymbolExpr → SymbolExpr → SymbolExpr
  | Symbol : SymbolBase → SymbolExpr
deriving DecidableEq, Repr

/-- Metric representation layer, mapping to numerical magnitude. -/
inductive MetricExpr where
  | MetricExact : Rational → MetricExpr
  | MetricApprox : Float → MetricExpr
  | MetricSymbolic : SymbolExpr → MetricExpr
deriving Repr

/-- Map MetricExpr to SymbolExpr for symbolic propagation. -/
def toSymbol : MetricExpr → SymbolExpr
  | MetricExpr.MetricExact r => SymbolExpr.Rational r
  | MetricExpr.MetricApprox _ => SymbolExpr.Symbol (SymbolBase.Symbolic "approx_float")
  | MetricExpr.MetricSymbolic s => s

/-- Uncertainty definition (mean and variance). -/
structure Uncertainty where
  mean : MetricExpr
  var : MetricExpr
deriving Repr

/-- Covariance/correlation representation. -/
structure Correlation where
  id1 : Nat
  id2 : Nat
  covar : MetricExpr
deriving Repr

/-- Epistemic layer representing uncertainties and correlations. -/
structure EpistemicExpr where
  uncertainties : List (Nat × Uncertainty)
  correlations : List Correlation
deriving Repr

/-- The unified Quantity type, stacking structural, symbolic, metric, and epistemic. -/
structure Quantity where
  dim : DimExpr
  sym : SymbolExpr
  mag : MetricExpr
  epis : EpistemicExpr
deriving Repr


/- =========================================================
   2. Epistemic Propagation Rules
   ========================================================= -/

/-- Linearized variance propagation for addition: var(A + B) = var(A) + var(B) + 2 * covar(A,B). -/
def propagateVarAdd (var1 var2 covar : MetricExpr) : MetricExpr :=
  MetricExpr.MetricSymbolic (
    SymbolExpr.Add
      (SymbolExpr.Add (toSymbol var1) (toSymbol var2))
      (SymbolExpr.Mul (SymbolExpr.Rational ⟨2, 1⟩) (toSymbol covar))
  )

/-- Linearized variance propagation for multiplication:
    var(A * B) = B^2 * var(A) + A^2 * var(B) + 2 * A * B * covar(A,B). -/
def propagateVarMul (mean1 mean2 var1 var2 covar : MetricExpr) : MetricExpr :=
  MetricExpr.MetricSymbolic (
    SymbolExpr.Add
      (SymbolExpr.Add
        (SymbolExpr.Mul (SymbolExpr.Pow (toSymbol mean2) (SymbolExpr.Rational ⟨2, 1⟩)) (toSymbol var1))
        (SymbolExpr.Mul (SymbolExpr.Pow (toSymbol mean1) (SymbolExpr.Rational ⟨2, 1⟩)) (toSymbol var2)))
      (SymbolExpr.Mul (SymbolExpr.Rational ⟨2, 1⟩) (SymbolExpr.Mul (toSymbol mean1) (SymbolExpr.Mul (toSymbol mean2) (toSymbol covar))))
  )

/-- Dimension-compatible addition of two quantities. -/
def addQ (q1 q2 : Quantity) (_h_dim : q1.dim = q2.dim) : Quantity where
  dim := q1.dim
  sym := SymbolExpr.Add q1.sym q2.sym
  mag := match q1.mag, q2.mag with
    | MetricExpr.MetricExact r1, MetricExpr.MetricExact r2 => MetricExpr.MetricExact (Rational.add r1 r2)
    | _, _ => MetricExpr.MetricSymbolic (SymbolExpr.Add q1.sym q2.sym)
  epis := EpistemicExpr.mk [] [] -- Consolidated/empty for simplification

/-- Multiplication of two quantities. -/
def mulQ (q1 q2 : Quantity) : Quantity where
  dim := DimExpr.DimMul q1.dim q2.dim
  sym := SymbolExpr.Mul q1.sym q2.sym
  mag := match q1.mag, q2.mag with
    | MetricExpr.MetricExact r1, MetricExpr.MetricExact r2 => MetricExpr.MetricExact (Rational.mul r1 r2)
    | _, _ => MetricExpr.MetricSymbolic (SymbolExpr.Mul q1.sym q2.sym)
  epis := EpistemicExpr.mk [] []


/- =========================================================
   3. Substrate Mapping & QuantityKernel
   ========================================================= -/

/-- Countable bijection axioms between Quantity and Nat. -/
axiom quantityToNat : Quantity → Nat
axiom natQuantity : Nat → Quantity
axiom quantityToNat_inverse (q : Quantity) : natQuantity (quantityToNat q) = q
axiom natQuantity_inverse (n : Nat) : quantityToNat (natQuantity n) = n

/-- Mapping from substrate to Quantity. -/
noncomputable def view_of (t : ISKSubtype) : Quantity :=
  natQuantity (layerToNat (Quotient.mk operEqSetoid t))

/-- Mapping from Quantity back to substrate. -/
noncomputable def decode (q : Quantity) : ISKSubtype :=
  InvariantLayer.canonical_rep (natToLayer (quantityToNat q))

/-- Equivalence on Quantity is standard equality. -/
def quantity_eq_equivalence : Equivalence (fun (x y : Quantity) => x = y) where
  refl _ := rfl
  symm h := h.symm
  trans h1 h2 := h1.trans h2

theorem sound (t u : ISKSubtype) (h : OperEq t u) : view_of t = view_of u := by
  dsimp [view_of]
  have h_eq : Quotient.mk operEqSetoid t = Quotient.mk operEqSetoid u := Quotient.sound h
  rw [h_eq]

theorem decode_view (t : ISKSubtype) : OperEq (decode (view_of t)) t := by
  dsimp [decode, view_of]
  rw [natQuantity_inverse]
  rw [layerToNat_inverse]
  exact canonical_rep_eq t

theorem view_eq_decode (q : Quantity) : view_of (decode q) = q := by
  dsimp [view_of, decode]
  have h_sound : Quotient.mk operEqSetoid (InvariantLayer.canonical_rep (natToLayer (quantityToNat q))) =
                 natToLayer (quantityToNat q) := by
    exact canonical_rep_sound _
  rw [h_sound]
  rw [natToLayer_inverse]
  rw [quantityToNat_inverse]

theorem decode_eq (q1 q2 : Quantity) (h : q1 = q2) : OperEq (decode q1) (decode q2) := by
  rw [h]
  exact OperEq.refl (decode q2)

/-- QuantityKernel definition as an admissible semantic kernel. -/
noncomputable abbrev QuantityKernel : Kernel where
  Carrier := Quantity
  view_of := view_of
  view_eq := (· = ·)
  is_equiv := quantity_eq_equivalence
  sound := sound
  decode := decode
  decode_view := decode_view
  view_eq_decode := view_eq_decode
  decode_eq := decode_eq

/- =========================================================
   4. Stable Arithmetic on Quotient Layer
   ========================================================= -/

/-- Stable addition on the Invariant Layer quotient class. -/
noncomputable def InvariantLayer.add (q1 q2 : InvariantLayer) : InvariantLayer :=
  natToLayer (layerToNat q1 + layerToNat q2)

/-- Theorem proving that InvariantLayer.add is a stable invariant preserving arithmetic addition. -/
theorem quantity_addition_invariant (q1 q2 : InvariantLayer) :
    layerToNat (InvariantLayer.add q1 q2) = layerToNat q1 + layerToNat q2 := by
  unfold InvariantLayer.add
  rw [natToLayer_inverse]

end ISAR
