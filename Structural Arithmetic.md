# Structural Arithmetic — Extended Model with Epistemic Layer

This document extends the previous algebraic model of **structural arithmetic** — where quantities are treated as symbolic, dimensional, and metric structures — to include *epistemic* information: uncertainty, variance, and correlation. Together, these define a complete framework for representing, transforming, and reasoning about quantities as humans intuitively do.

---

## I. Conceptual Overview

We decompose a **Quantity** into four mutually reinforcing layers:

| Layer                                     | Role                                                                  | Formal Object   | Notes                                                                    |
| ----------------------------------------- | --------------------------------------------------------------------- | --------------- | ------------------------------------------------------------------------ |
| **Structural (Dimensional)**              | Encodes relationships between fundamental dimensions (e.g., L, T, M). | `DimExpr`       | Category object; monoidal under tensor ⊗ (unitless quantity = identity). |
| **Symbolic (Relational)**                 | Encodes algebraic or transcendental structure (e.g., √2, π, e).       | `SymbolExpr`    | Vector space or algebraic field extension over ℚ.                        |
| **Metric (Magnitude)**                    | Encodes specific measurable magnitude in real numbers.                | `MetricExpr`    | Functor from structural-symbolic space → ℝ.                              |
| **Epistemic (Uncertainty & Correlation)** | Encodes imprecision, variance, and relational uncertainty.            | `EpistemicExpr` | Covariance structure over MetricExpr values.                             |

Thus each quantity becomes:

[
Q = (S, Y, M, E)
]
where:

* S: Dimensional structure (category of units)
* Y: Symbolic relational structure (field extensions, constants)
* M: Metric value (real-valued, possibly approximate)
* E: Epistemic uncertainty + correlation information

---

## II. Formalization

### 1. Structural Layer — Dimensional Category

```haskell
data DimBase = L | T | M | I | Θ | N | J  -- example SI primitives

data DimExpr = DimUnit
              | DimBase DimBase Int      -- exponent form, e.g. L^2 T^-1
              | DimMul DimExpr DimExpr   -- monoidal tensor (⊗)
              | DimInv DimExpr           -- dual or inverse
```

This layer forms a **free abelian group** over dimension symbols.
Arithmetic over this layer is symbolic and closed — no metrics involved.

---

### 2. Symbolic Layer — Algebraic Field Extension

```haskell
data SymbolBase = Pi | E | Sqrt Rational | Symbolic Text

data SymbolExpr = Rational Rational
                 | Add SymbolExpr SymbolExpr
                 | Mul SymbolExpr SymbolExpr
                 | Pow SymbolExpr SymbolExpr
                 | Symbol SymbolBase
```

Represents a symbolic field extension over ℚ. For example:
`(1/2)*π*√2` is represented without flattening to floating-point.

This allows symbolic simplification, exact arithmetic, and compositional algebra.

---

### 3. Metric Layer — Quantitative Magnitude

```haskell
data MetricExpr = MetricExact Rational
                 | MetricApprox Double
                 | MetricSymbolic SymbolExpr
```

This layer represents numerical approximation *within* a chosen metric system. It is the only layer with a projection into ℝ (evaluation functor):

[
Eval_M : (SymbolExpr) → ℝ
]

but this is deferred until explicitly requested.

---

### 4. Epistemic Layer — Variance and Correlation

We define uncertainty as a first-class structure:

```haskell
data Uncertainty = Sigma { mean :: MetricExpr
                           , var  :: MetricExpr }

data Correlation = Corr { pair  :: (QuantityID, QuantityID)
                         , covar :: MetricExpr }

data EpistemicExpr = Epistemic { uncertainties :: Map QuantityID Uncertainty
                                , correlations  :: Set Correlation }
```

This allows representation of both *local variance* and *cross-quantity correlation*.
When quantities are composed, their epistemic structures propagate by rule:

#### Addition

[
(μ₁,σ₁²) + (μ₂,σ₂²) = (μ₁ + μ₂, σ₁² + σ₂² + 2·cov(1,2))
]

#### Multiplication (linearized propagation)

[
(μ₁,σ₁)·(μ₂,σ₂) ≈ (μ₁μ₂, (μ₂σ₁)² + (μ₁σ₂)² + 2μ₁μ₂·cov(1,2))
]

These propagate through symbolic expressions just as structural composition propagates dimensions.

---

## III. Unified Quantity Definition

```haskell
data Quantity = Quantity {
    dim   :: DimExpr,       -- structural
    sym   :: SymbolExpr,    -- symbolic
    mag   :: MetricExpr,    -- metric
    epis  :: EpistemicExpr  -- epistemic
}
```

Composition is defined by layerwise algebra:

```haskell
mulQ (Quantity s1 y1 m1 e1) (Quantity s2 y2 m2 e2) =
  Quantity (DimMul s1 s2)
           (Mul y1 y2)
           (MulMetric m1 m2)
           (Propagate e1 e2 Mul)
```

All operations preserve structural and epistemic information.

---

## IV. Symbolic Simplification and Deferred Evaluation

Simplification operates structurally, before any numeric evaluation:

```text
Simplify(Q₁ * Q₂):
  → CombineDim(Q₁.dim, Q₂.dim)
  → SimplifySymbol(Q₁.sym * Q₂.sym)
  → Defer metric evaluation until requested
```

This means constants such as π or √2 remain symbolic, uncertainty propagation is exact in symbolic form, and only final numeric projection introduces approximation.

---

## V. Minimal-Relation Inference

Given a set of observed quantities {Qᵢ} with epistemic uncertainty, we define a cost functional to infer the simplest relational law:

[
C(R) = Var(residuals(R, Qᵢ)) + λ·Complexity(R)
]

Minimizing C yields the *minimal-constant structural law* — analogous to least action or minimal description length. Symbolic simplification and variance-aware regression cooperate to identify invariant relations.

---

## VI. Categorical Interpretation

The full system can be viewed as a **stacked functorial composition**:

[
Quantity ≅ (Epistemic ∘ Metric ∘ Symbolic ∘ Dimensional)(Base)
]

Each layer is a functor enriching the one below it:

* **Dimensional:** free monoidal category over base units.
* **Symbolic:** field extension functor, adding algebraic structure.
* **Metric:** numeric functor → ℝ, adding evaluable magnitude.
* **Epistemic:** probabilistic functor → Covariance category, adding uncertainty semantics.

Together, these form a **hierarchical category of quantities**, closed under composition, invertible under dimensional and symbolic transformations, and exact up to explicitly declared epistemic limits.

---

## VII. Closing Remarks

This formalization realizes computation as a direct analogue of human mathematical reasoning:

* Relations, not raw numbers, are first-class.
* Approximation, not truncation, is managed explicitly.
* Uncertainty is structural, not incidental.
* Dimensional and symbolic integrity are preserved throughout.

Computation thus becomes *structural epistemic arithmetic*: a reasoning process over relational quantities that unifies algebra, measurement, and knowledge representation.


## VIII. Examples

Let’s walk through a concrete, end-to-end example using the extended Quantity model (structural + symbolic + metric + epistemic). We will show the symbolic composition, metric projection, and explicit uncertainty/correlation propagation for the kinetic energy formula

[
E = \tfrac{1}{2} m v^2
]

then give a small aside where your “shaped lambda calculus” idea fits.

---

### 1) Setup: Quantities (declarative)

We represent each physical variable as a `Quantity = (Dim, Sym, Mag, Epis)`.

* Mass (m):

  * `Dim` = (M)
  * `Sym` = `m` (symbolic identifier)
  * `Mag` = (\mu_m) (mean metric)
  * `Epis` = variance (\sigma_m^2) (and correlations if any)

* Velocity (v):

  * `Dim` = (L,T^{-1})
  * `Sym` = `v`
  * `Mag` = (\mu_v)
  * `Epis` = variance (\sigma_v^2)

Constant (\tfrac12) is structural/symbolic constant (dimensionless).

We will keep structure and symbolic form exact throughout manipulation; only the `Mag` and `Epis` will be numerically computed / propagated.

---

### 2) Symbolic composition (exact, deferred evaluation)

Symbolically:

```
E.sym = (1/2) * m.sym * (v.sym)^2
E.dim = (M) * (L T^-1)^2 = M L^2 T^-2  (energy)
```

No numeric rounding. `E.sym` remains (\tfrac12 , m , v^2).

---

### 3) Epistemic propagation rules (linearized / first order)

We use first-order (delta/linear) uncertainty propagation — standard and appropriate when relative uncertainties are small:

* For a scalar function (f(\mathbf{x})) with mean (\mu) and covariance matrix (\Sigma),
  [
  \operatorname{Var}(f) \approx \nabla f(\mu)^\top , \Sigma , \nabla f(\mu).
  ]

We’ll apply this in stages to keep the algebra clear.

---

### 4) Stepwise propagation for (E = \tfrac12 m v^2)

Define intermediate (w = v^2). Then (E = \tfrac12 m w).

**(A) Compute mean values (metrics):**
[
\mu_w = \operatorname{E}[v^2] \approx \mu_v^2  \quad\text{(use mean-of-square ≈ square-of-mean in linearized propagation)}
]
[
\mu_E = \tfrac12 \mu_m \mu_w = \tfrac12 \mu_m \mu_v^2
]

**(B) Variance of (w = v^2):**
Using (f(v)=v^2) so (f'(μ_v)=2μ_v),
[
\operatorname{Var}(w) \approx (2\mu_v)^2 \operatorname{Var}(v) = 4 \mu_v^2 \sigma_v^2.
]

If you have higher moments or need exact (\operatorname{E}[v^2]) use the true value; for small σ this linearization is fine.

**(C) Variance of product (m \cdot w):**
For product (z = m \cdot w) with means (\mu_m,\mu_w), variances (\sigma_m^2,\sigma_w^2), and covariance (\operatorname{Cov}(m,w)),
[
\operatorname{Var}(z) \approx \mu_w^2 \sigma_m^2 + \mu_m^2 \sigma_w^2 + 2 \mu_m \mu_w \operatorname{Cov}(m,w).
]
Finally (E = \tfrac12 z) so
[
\operatorname{Var}(E) = \tfrac14 \operatorname{Var}(z).
]

**(D) Handling correlation (\operatorname{Cov}(m,w)):**
If (m) and (v) are correlated, we need (\operatorname{Cov}(m,w)). Linearize (w = v^2 \approx \mu_v^2 + 2\mu_v (v-\mu_v)), so
[
\operatorname{Cov}(m,w) \approx 2\mu_v,\operatorname{Cov}(m,v).
]
If (m) and (v) are independent, (\operatorname{Cov}(m,v)=0) and this term vanishes.

---

### 5) Numerical example (concrete)

Pick:

* (\mu_m = 2.0\ \mathrm{kg},\quad \sigma_m = 0.1\ \mathrm{kg})  (so (\sigma_m^2 = 0.01))
* (\mu_v = 3.0\ \mathrm{m/s},\quad \sigma_v = 0.05\ \mathrm{m/s}) (so (\sigma_v^2 = 0.0025))
* assume independence: (\operatorname{Cov}(m,v)=0)

Compute step-by-step (digit-by-digit shown):

1. (\mu_v^2 = 3.0^2 = 9.0.)

2. Mean energy:
   [
   \mu_E = \tfrac12 \cdot \mu_m \cdot \mu_v^2
   = 0.5 \cdot 2.0 \cdot 9.0
   = 1.0 \cdot 9.0
   = 9.0\ \mathrm{J}.
   ]

3. Variance of (w=v^2):
   [
   \operatorname{Var}(w) = 4 \mu_v^2 \sigma_v^2
   = 4 \cdot 9.0 \cdot 0.0025
   = 36 \cdot 0.0025
   = 0.09.
   ]

4. Now (\mu_w = 9.0), (\sigma_w^2 = 0.09).

5. Variance of (z = m \cdot w) (independent case, Cov=0):
   [
   \operatorname{Var}(z) = \mu_w^2 \sigma_m^2 + \mu_m^2 \sigma_w^2
   = 9.0^2 \cdot 0.01 + 2.0^2 \cdot 0.09.
   ]
   Compute terms:

* (9.0^2 = 81.0). Then (81.0 \cdot 0.01 = 0.81.)
* (2.0^2 = 4.0). Then (4.0 \cdot 0.09 = 0.36.)
  Sum: (0.81 + 0.36 = 1.17.)

6. Variance of (E = \tfrac12 z):
   [
   \operatorname{Var}(E) = \tfrac14 \cdot 1.17 = 0.2925.
   ]
   Standard deviation:
   [
   \sigma_E = \sqrt{0.2925} \approx 0.5407\ \mathrm{J}.
   ]

**Final result (rounded sensibly):**
[
E = 9.00 \pm 0.54\ \mathrm{J}.
]

We preserved structure (units (M L^2 T^{-2})), symbolic form ((\tfrac12 m v^2)), and propagated epistemic uncertainty through the calculation — only the metric layer was numerically evaluated at the end.

---

### 6) If m and v are correlated

Include (\operatorname{Cov}(m,v) \neq 0). Then
[
\operatorname{Cov}(m,w) \approx 2\mu_v \operatorname{Cov}(m,v),
]
and
[
\operatorname{Var}(z) = \mu_w^2 \sigma_m^2 + \mu_m^2 \sigma_w^2 + 2\mu_m\mu_w \operatorname{Cov}(m,w).
]
Plug that into (\operatorname{Var}(E)=\tfrac14\operatorname{Var}(z)). This makes correlations first-class and clearly traceable in the epistemic graph.

---

### 7) Short aside: “Shaped lambda calculus” idea

Yes — your intuition is right. A *shaped lambda calculus* (or a dependently typed lambda calculus with “shape” annotations) would be a natural formal substrate for these Quantities:

* Types encode **DimExpr** (shape = unit signature).
* Terms carry **SymbolExpr** and **Metric/Epistemic** annotations.
* Function types express allowed transformations (e.g., only functions that map `L T^-1` to `L T^-2` by dividing by `T` are well typed).
* Evaluation is staged: symbolic reductions and type-level rewrites happen at compile/type-check time; numeric projection happens at run-time when a metric functor is applied.

It will be self-referential in the sense that terms may contain metavariables that are themselves Quantities, but that’s solvable with standard techniques (normalization, guarded recursion, staged evaluation). In short: a perfect fit for a typed, staged DSL for your Bootstrap IDE.

---

### 8) Next steps (practical)

If you want I can:

* produce a minimal Python reference that implements `Quantity` with `DimExpr`, `SymbolExpr`, `MetricExpr`, and `EpistemicExpr` plus the propagation rules used above, **and** run the numeric example so you get a downloadable notebook; or
* sketch a small typed-DSL (shaped lambda calculus) design that enforces dimensional types and stages symbolic vs numeric evaluation.

Which would you prefer?
