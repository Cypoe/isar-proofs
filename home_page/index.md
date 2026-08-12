---
layout: default
title: "ISAR: Invariant Kernel for Closed Computational Dialects"
description: "A Lean 4 formalization of a combinatory substrate whose observational quotient is the terminal object in the category of closed computational dialects."
usemathjax: true
---

# ISAR: Invariant Kernel for Closed Computational Dialects

**ISAR** is a Lean 4 formalization of a four-operator combinatory calculus (`norm`, `konst`, `comp`, `dup`) and its observational quotient, the **Invariant Layer** (`InvariantLayer := ISKSubtype / OperEq`). The central result is `morphism_uniqueness`: the Invariant Layer is the terminal object in the category of admissible semantic kernels, so every closed dialect &mdash; lambda calculus, term rewriting, stack bytecode, hereditarily finite sets, linear interaction nets &mdash; admits a unique structure-preserving morphism into it. All theorems are machine-checked in Lean 4 with no `sorry`.

---

## Project

* **[Interactive Blueprint]({{ site.baseurl }}/blueprint/)** &mdash; Theorem dependency graph with per-node Lean verification status.
* **[Monograph PDF]({{ site.baseurl }}/pdf/blueprint_monograph.pdf)** &mdash; Full monograph: all modules and phases.
* **[Paper A PDF]({{ site.baseurl }}/pdf/blueprint_paper_a.pdf)** &mdash; Calculus, confluence, Invariant Layer, category-theoretic terminality, dialect views.
* **[Paper B PDF]({{ site.baseurl }}/pdf/blueprint_paper_b.pdf)** &mdash; HF set interpretation, view pluralism, Futamura projections.
* **[Paper C PDF]({{ site.baseurl }}/pdf/blueprint_paper_c.pdf)** &mdash; Linear duplication, optimal kernels, matrix geometry, metric completion.
* **[Lean API Docs]({{ site.baseurl }}/docs/)** &mdash; Generated documentation for the Lean 4 source.
* **[Formal Systems Zoo]({{ site.baseurl }}/zoo/)** &mdash; Executable dialect explorer: SKI, Iota, lambda, TRS, bytecode.
* **[Demos]({{ site.baseurl }}/visualizations/)** &mdash; Kernel geometry and invariant layer interactive diagrams.
* **[GitHub](https://github.com/cypoe/isar-proofs)** &mdash; Source, proofs, and build instructions.

---

## Four Verified Results

### 1. Confluence and Normal Forms
The `ITerm` calculus with operators `norm`, `konst`, `comp`, `dup` is proven confluent: every term has at most one normal form. `S` is constructively derived from the basis. A bracket-abstraction compiler maps de Bruijn lambda terms to `ITerm` and is proven to preserve beta-reduction steps.

### 2. Terminality of the Invariant Layer
`InvariantLayer := ISKSubtype / OperEq` is proven to be the terminal object in the category of admissible semantic kernels (`morphism_uniqueness`). Lambda, TRS, bytecode, HF-set, and quantity-kernel interpretations each yield a unique factorization morphism. The layer is not postulated as a universal structure; it is derived as the quotient of a concrete calculus and proven terminal within a formally stated category.

### 3. Futamura projections (mix formulation)
Substitution soundness (`futamura_first`) is proved at the meta specializer. Object-level 2nd/3rd projections are mix instantiations over `PESetup` (`specTerm` + `selfApp`). `TrivialPE` shows mix+selfApp alone need not optimize; fragment `OptimizingPE` (identity/konstβ folds) proves `Nontrivial`. Full Jones–Gomard–Sestoft BTA for all of ISAR remains open.

### 4. Linear Reduction, Matrix Geometry, Metric Completion
`LinearIKTerm` admits a bounded-fuel normalization certificate (`sufficient_fuel_correct`), structurally isomorphic to HVM2 interaction net reduction. The $4 \times 4$ ISAR operator matrices satisfy $I^2 = I$ (idempotency) and $(I \cdot R \cdot A \cdot S)^2 = 0$ (nilpotency). Gauge equivalence $P K_1 P^{-1} = K_2$ is proven, unifying two matrix representations of the same kernel. Metric completion and a formalized Universal Approximation result are given in `ISARApproximation.lean`; these are currently the least-constrained results in the project.

---

## Module Status

| Lean Module | Content | Status |
| :--- | :--- | :--- |
| `ISAR.lean` | Syntax, reduction, confluence, basis completeness | **Verified** |
| `InvariantLayer.lean` | Quotient construction, linear fragment, fuel certificate | **Verified** |
| `LambdaFragment.lean` | Bracket abstraction, beta-simulation | **Verified** |
| `TensorSemantics.lean` | Tensor denotation, compositionality, separation | **Verified** |
| `KernelCategory.lean` | Terminal object, `morphism_uniqueness` | **Verified** |
| `HFSet.lean`, `ZFCInterpretation.lean` | HF set axioms, Ackermann bijection, HF kernel morphism | **Verified** |
| `TRSView.lean`, `BytecodeView.lean`, `QuantityKernel.lean` | Dialect morphisms, universal factorization | **Verified** |
| `ViewIndependence.lean`, `ViewUnification.lean` | Syntax-independence theorem, isomorphism unification | **Verified** |
| `ReverseRosetta.lean` | Forward invariance, referential openness | **Verified** |
| `Futamura.lean` | Three Futamura projections | **Verified** |
| `ISARMatrices.lean` | Idempotency, nilpotency, gauge equivalence | **Verified** |
| `ISARApproximation.lean` | Metric completion, UAT, attractor structure | **Verified** |

---

## Build Locally

```bash
git clone https://github.com/cypoe/isar-proofs.git
cd isar-proofs
lake build
```

Blueprint PDFs (run twice each for cross-references):

```bash
latexmk -pdflatex=pdflatex -pdf blueprint/src/print_monograph.tex
latexmk -pdflatex=pdflatex -pdf blueprint/src/print_paper_a.tex
latexmk -pdflatex=pdflatex -pdf blueprint/src/print_paper_b.tex
latexmk -pdflatex=pdflatex -pdf blueprint/src/print_paper_c.tex
```

HTML blueprint:

```bash
plastex -c blueprint/src/plastex.cfg blueprint/src/web.tex
```

Check all blueprint declarations against Lean source:

```bash
lake exe checkdecls blueprint/lean_decls
```
