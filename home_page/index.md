---
layout: default
title: "ISAR: Invariant Scalable Fractal Addressable Representations"
description: "A Formally Verified Framework for Symbolic Calculus, Set Semantics, Category Theory, and Continuous Embeddings in Lean 4"
usemathjax: true
---

# ISAR: Invariant Scalable Fractal Addressable Representations

Welcome to the homepage of **ISAR** (Invariant Scalable Fractal Addressable Representations), a project dedicated to the complete formal verification of symbolic operations, set-theoretic semantics, category-theoretic kernels, and continuous metric embeddings using the **Lean 4** proof assistant.

All theorems and modules in the repository are fully verified, **sorry-free**, and compiled under the Lean 4 package manager (Lake).

---

## 🛠️ Project Links

To explore the mathematical, physical, and formal details of the ISAR codebase:

* **[Interactive Web Blueprint](./blueprint/)**: Browse the mathematical definition-dependency graph and see which sections are formally verified in Lean 4 (covering the unified monograph).
* **[PDF Full Monograph](./blueprint_monograph.pdf)**: The full unified mathematical monograph of the ISAR calculus, set-theoretic interpretations, and continuous completions.
* **Publications (ISAR Core Paper Triad)**:
  * **[Paper A (TCS / PL): ISAR Semantic Kernel](./paper_a.pdf)**: A Quotient-Mediated Semantic Kernel for Closed Dialects (discrete kernel, confluence, quotients, category, dialects).
  * **[Paper B (Logic / Philosophy): Reverse Rosetta & Decoder Theory](./paper_b.pdf)**: Logical and philosophical exploration of representation, decoder theory, closed vs. open systems.
  * **[Paper C (Math / Applied): Structural Arithmetic & Continuous Approximation](./paper_c.pdf)**: Metric completion, continuous address spaces, matrix primitives, and the Universal Approximation Theorem.
* **[Lean API Reference](./docs/)**: Auto-generated documentation for the full Lean 4 codebase, complete with formal definitions, types, and proof source links.
* **[GitHub Source Repository](https://github.com/cypoe/isar-proofs)**: The main repository containing the complete Lean 4 implementation and proof sources.

---

## 🏛️ Pillars of the Formalization

The ISAR mathematical stack is organized into four major verified components:

### 1. Symbolic ISAR Calculus
We formalize the syntax, reduction rules, and confluence properties of the base untyped combinatory fragment (`ITerm`).
* **Confluence & Normal Forms**: Proof of unique normal forms for the `ISKTerm` fragment.
* **Bracket Abstraction Compiler**: Compilation mapping de Bruijn untyped lambda terms (`LTerm`) to the combinator substrate, verified to simulate beta-reductions.
* **Futamura Projections**: Constructive proofs of the First, Second, and Third Futamura projections, showing that partial evaluation and compiler generation are direct consequences of self-representation correctness.

### 2. Set-Theoretic Semantics
We establish a set-theoretic interpretation of the symbolic calculus:
* **Hereditarily Finite Sets**: Formalization of finite sets (`HF` sets) via Ackermann's bijective encoding (`toNat`).
* **Homomorphic Encoding**: Verification of the bijection between the operational quotient (`InvariantLayer`) and `HF` sets, proving that set-theoretic constructors (empty set, insert, pair, union) are algebraic homomorphisms.
* **Interpretation Theorem**: Proof that the set-theoretic kernel (`HF_Kernel`) satisfies the category-theoretic laws and factors uniquely through `ISAR_Kernel`.

### 3. Category Theory & Optimal Computability
We define the semantic framework of operations as a category of **Kernels**:
* **Kernel Category**: Morphisms between kernels are defined up to observational equivalence ($f \approx g$).
* **Terminality Theorem**: Formal proof that the operational quotient `ISAR_Kernel` is the terminal object in the category of kernels (every kernel maps uniquely into it).
* **Optimal Execution & Interaction Nets**: Connection to **linear interaction nets** (such as executed by HVM2) via bounded-fuel size-decreasing termination invariants on the linear duplication fragment (`LinearIKTerm`), proving that evaluation terminates within a linear number of interactions.
* **Matrix Nilpotency**: Constructive proof of idempotency ($I^2 = I$) and operational nilpotency ($(I \cdot R \cdot A \cdot S)^2 = 0$) using $4 \times 4$ integer matrices.

### 4. Continuous Metric Completion & Physics
We extend the discrete calculus to continuous spaces and physical systems:
* **Metric Address Space**: Construction of the pseudo-metric structure on address spaces (`KernelAddress d k σ`) using the supremum norm over compact subsets.
* **Metric Completion**: Formalization of the extension of continuous realizations to the metric completion (`KernelAddressLimit`), proving the dense embedding extends to a bijection.
* **Universal Approximation Theorem**: Formal statement of the UAT for non-polynomial activations based on **Leshno, Lin, Pinkus, and Schocken (1993)**:
  $$\forall (f \in C(K, \mathbb{R}^k)), \forall (\varepsilon > 0), \exists (q \in \text{KernelAddress}), \forall (x \in K), \| \text{continuousRealization}(q)(x) - f(x) \| < \varepsilon$$
* **Physical System Attractors**: Embeddings showing that the stable attractors of the Lorenz system, Gray-Scott reaction-diffusion equations, and Ising models possess concrete invariant addresses in `InvariantLayer`.

---

## 📖 Summary of Lean Modules

| Lean Module | Description | Verification Status |
| :--- | :--- | :--- |
| **`ISAR.lean`** | Syntax, reduction rules, confluence, unique normal forms, and basis translations. | **Fully Verified** |
| **`InvariantLayer.lean`** | Operational equivalence, quotients, linear duplication size-decreasing termination, and fuel certificates. | **Fully Verified** |
| **`LambdaFragment.lean`** | Lambda fragment compilation, bracket abstraction, and simulation. | **Fully Verified** |
| **`TensorSemantics.lean`** | Tensor denotation, compositionality, and pairwise separation. | **Fully Verified** |
| **`KernelCategory.lean`** | Category definition, terminality proof, and computable/optimal kernels. | **Fully Verified** |
| **`HFSet.lean`, `HFSetEncoding.lean`, `HFSetSemantics.lean`, `ZFCInterpretation.lean`** | Hereditarily finite sets, Ackermann bijection, set-theoretic kernel representation, and interpretation. | **Fully Verified** |
| **`TRSView.lean`, `BytecodeView.lean`, `QuantityKernel.lean`** | Dialect views (SKI rewrites, Stack VM, physical quantities) and universal unification. | **Fully Verified** |
| **`Futamura.lean`** | Substitution lemmas, partial evaluation, and first/second/third Futamura projections. | **Fully Verified** |
| **`ISARMatrices.lean`** | $4 \times 4$ integer matrices, idempotency, nilpotency, and gauge equivalence. | **Fully Verified** |
| **`ISARApproximation.lean`** | Metric completion, Leshno UAT, and physical system embeddings. | **Fully Verified** |

---

## 🚀 How to Build and Run Locally

To check the proofs locally, install Lean 4 via `elan` and run:

```bash
# Clone the repository
git clone https://github.com/cypoe/isar-proofs.git
cd isar-proofs

# Build the Lean modules
lake build
```

To build the HTML/PDF blueprint:

```bash
# Compile web and print versions
cd blueprint
latexmk -pdf src/print.tex
plastex -c plastex.cfg src/web.tex
```