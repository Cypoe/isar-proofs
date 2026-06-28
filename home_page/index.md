---
layout: default
title: "ISAR: Invariant Kernel for Closed Computational Dialects"
description: "A formally verified quotient-mediated semantic kernel in Lean 4: unifying lambda calculus, term rewriting, bytecode, and set-theoretic views under a single algebraic substrate."
usemathjax: true
---

# ISAR: Invariant Kernel for Closed Computational Dialects

**ISAR** is a Lean 4 formalization of a minimal combinatory substrate whose operational quotient — the **Invariant Layer** — is the terminal object in the category of closed computational dialects. Lambda calculus, term rewriting systems, stack VM bytecode, hereditarily finite sets, and linear interaction nets all factor uniquely through this quotient via structure-preserving morphisms. Every theorem is machine-checked and **sorry-free**.

---

## Project Links

* **[Interactive Blueprint](./blueprint/)** — Dependency graph of definitions and theorems, with Lean verification status per node.
* **[Blueprint Monograph PDF](./blueprint.pdf)** — Full monograph: all 22 modules, all phases.
* **[Blueprint PDF — Paper A](./blueprint_paper_a.pdf)** — Core calculus, invariant layer, category theory, and dialect views.
* **[Blueprint PDF — Paper B](./blueprint_paper_b.pdf)** — Set-theoretic interpretation, view pluralism, Futamura projections.
* **[Blueprint PDF — Paper C](./blueprint_paper_c.pdf)** — Linear duplication, optimal kernels, matrix geometry, metric completion.
* **[Lean API Docs](./docs/)** — Auto-generated documentation for the Lean 4 codebase.
* **[Formal Systems Zoo](./zoo/)** — Interactive explorer: SKI, Iota, lambda, TRS, bytecode, and dialect morphisms.
* **[Demos &amp; Visualizations](./visualizations/)** — Kernel geometry, invariant layer diagrams, and combinator reduction flows.
* **[GitHub Source](https://github.com/cypoe/isar-proofs)** — Complete Lean 4 source and proof files.

---

## Four Verified Pillars

### 1. Symbolic Calculus & Confluence
The base untyped combinatory fragment (`ITerm`) with its four operators — identity `norm`, constant `konst`, composition `comp`, duplication `dup` — is proven confluent with unique normal forms. The $S$ combinator is constructively derived from the basis, and a bracket-abstraction compiler maps de Bruijn lambda terms to the substrate while preserving beta-reduction steps.

### 2. Invariant Layer & Category-Theoretic Terminality
The quotient `InvariantLayer := ISKSubtype / OperEq` is the bisimulation final coalgebra of the substrate's observable functor. `morphism_uniqueness` proves it is the **terminal object** in the category of semantic kernels: every admissible closed dialect maps into it via a unique structure-preserving morphism. ZFC/HF-sets, TRS, bytecode, and physical quantities all factor through this single quotient.

### 3. Futamura Projections & Partial Evaluation
Substitution and partial evaluation are formalized over `ITerm`. The **First**, **Second**, and **Third Futamura Projections** are constructively proved: specialization soundness, compiler generation from a specializer applied to an interpreter, and compiler-generator (`cogen`) generation from self-application of the specializer.

### 4. Linear Duplication, Optimal Kernels & Matrix Geometry
The linear duplication fragment (`LinearIKTerm`) admits a fuel certificate (`sufficient_fuel_correct`) proving bounded-time normalization — directly isomorphic to HVM2 linear interaction net reduction. The $4 \times 4$ ISAR matrices satisfy $I^2 = I$ (idempotency) and $(I \cdot R \cdot A \cdot S)^2 = 0$ (nilpotency), and gauge equivalence $P K_1 P^{-1} = K_2$ unifies the two representation models.

---

## Module Status

| Lean Module | Role | Status |
| :--- | :--- | :--- |
| `ISAR.lean` | Syntax, reduction, confluence, basis completeness | **Verified** |
| `InvariantLayer.lean` | Quotient, linear fragment, optimal fuel certificate | **Verified** |
| `LambdaFragment.lean` | Bracket abstraction, beta-simulation | **Verified** |
| `TensorSemantics.lean` | Tensor denotation, compositionality, separation | **Verified** |
| `KernelCategory.lean` | Terminal object, computable/optimal kernels | **Verified** |
| `HFSet.lean` + `ZFCInterpretation.lean` | HF set axioms, Ackermann bijection, HF kernel | **Verified** |
| `TRSView.lean`, `BytecodeView.lean`, `QuantityKernel.lean` | Dialect views, universal factorization | **Verified** |
| `ViewIndependence.lean`, `ViewUnification.lean` | No-preferred-syntax theorem, isomorphism unification | **Verified** |
| `ReverseRosetta.lean` | Forward invariance, referential openness | **Verified** |
| `Futamura.lean` | Three Futamura projections | **Verified** |
| `ISARMatrices.lean` | Idempotency, nilpotency, gauge equivalence | **Verified** |
| `ISARApproximation.lean` | Metric completion, UAT, physical attractors | **Verified** |

---

## Build Locally

```bash
git clone https://github.com/cypoe/isar-proofs.git
cd isar-proofs
lake build
```

Blueprint (PDF + HTML):

```bash
cd blueprint
latexmk -pdf src/print_monograph.tex   # full monograph (run twice)
latexmk -pdf src/print_paper_a.tex     # paper A
latexmk -pdf src/print_paper_b.tex     # paper B
latexmk -pdf src/print_paper_c.tex     # paper C
plastex -c src/plastex.cfg src/web.tex # HTML blueprint
```

Validate all blueprint declarations against Lean source:

```bash
lake exe checkdecls blueprint/lean_decls
```
