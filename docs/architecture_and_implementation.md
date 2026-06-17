# Document A: Architecture & Implementation

## 1. Problem Statement

Modern software engineering and formal methods are plagued by fragmentation. Different formalisms—such as the untyped lambda calculus, term rewriting systems (TRS), stack-based virtual machines, and set-theoretic databases—are treated as disjoint worlds. They occupy different namespaces, employ different metatheories, and rely on incompatible toolchains. 

When interoperability is required, engineers resort to ad-hoc, pairwise compilers. These compilers:
* Leak representation details.
* Fail to preserve observational equivalence boundaries.
* Lack a verified, common semantic core.

In domains like robotics, state-space representations, and distributed version control, this translation overhead and semantic drift create severe barriers to verification and model transfer. What is missing is a unified, view-independent semantic substrate that can mediate between these representations while formally preserving operational semantics.

---

## 2. Kernel Architecture

ISAR solves this representation problem by establishing a quotient-mediated semantic kernel at the tensor level. The core computational substrate is defined by the **IRAS** matrix operators:

### The IRAS Core Matrices
The operational dynamics are represented by four sparse $4 \times 4$ matrices acting on a 4-dimensional carrier space:

* **Identity (I)**: Projects states onto observational equivalence classes.
  $$ I = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 0 \end{pmatrix} $$
* **Rewrite (R)**: An oriented, non-invertible selection operator encoding asymmetry.
  $$ R = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \end{pmatrix} $$
* **Adjacency (A)**: Maps interaction topology and connects references.
  $$ A = \begin{pmatrix} 0 & 0 & 0 & 0 \\ 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & 0 & 0 \end{pmatrix} $$
* **State/Closure (S)**: Enforces pairing and maintains structural closure.
  $$ S = \begin{pmatrix} 1 & 1 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix} $$

### The ISAR Abstract Machine
The kernel itself is computed as the non-commutative matrix product:
$$ U(K) = I \cdot R \cdot A \cdot S $$
This yields the sparse, nilpotent projection:
$$ U(K) = \begin{pmatrix} 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 \\ 1 & 1 & 0 & 0 \\ 0 & 0 & 0 & 0 \end{pmatrix} $$

At runtime, this tensor space is stored and manipulated inside a SQLite database. The core relations are defined by a sparse 4D tensor table `U` and a symbol table `NAMES`:

```sql
CREATE TABLE U (
    i INTEGER, -- Term index / ID
    s INTEGER, -- Source carrier coordinate (1..4)
    a INTEGER, -- Adjacency / Argument coordinate (1..4)
    r INTEGER, -- Rewrite / Reduction coordinate (1..4)
    value REAL, -- Numeric coefficient / Connectivity weight
    PRIMARY KEY(i, s, a, r)
);

CREATE TABLE NAMES (
    id INTEGER PRIMARY KEY,
    name TEXT UNIQUE
);
```

---

## 3. Implementation Overview

The mathematical core of the stack is implemented and mechanically verified in **Lean 4**:

* **[ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ISAR.lean)**: Defines the symbolic term algebra `ITerm` and the one-step reduction relation `IStep`. It proves the confluence of parallel reductions and the uniqueness of normal forms for the combinator fragment.
* **[InvariantLayer.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/InvariantLayer.lean)**: Establishes operational equivalence `OperEq` (joinability) on terms. It proves that `OperEq` is an equivalence relation and constructs the quotient type `InvariantLayer`. It also proves that term application (`InvariantLayer.app`) is well-defined on equivalence classes (`app_congruence`).
* **[TensorSemantics.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/TensorSemantics.lean)**: Defines the semantic mapping `denot` from terms to `TensorSpace` and verifies the extensional soundness (`denot_sound`) of the rewrite rules.
* **[IotaView.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/IotaView.lean)**: Implements the Barker Iota universal combinator dialect, encoding/decoding maps, and verifies the round-trip correctness.
* **SQLite & egglog Runtime**: The Python prototype (`isar.py` and `isar_ski_kernel.py`) implements this relational schema, evaluating terms by performing SQL queries that execute tensor contraction steps.

---

## 4. Worked Examples (The Cycle)

Any admissible closed formalism enters the stack through a uniform, four-stage loop:

```
    [Dialect Term]
          │
          │ (encode)
          ▼
     [ISAR Term] ──(normalize/quotient)──► [Invariant Layer]
          │                                     │
          │ (decode)                            │ (decode)
          ▼                                     ▼
    [Normal Form] ◄─────────────────────────────┘
```

### A. Lambda Calculus
* **Encode**: compilation of lambda terms (with de Bruijn indices) into `ITerm` via bracket abstraction (`compile` in `LambdaFragment.lean`).
* **Kernel**: Evaluation of the compiled term under `IStepBasis` rules.
* **Quotient**: Observational equivalence classes in `InvariantLayer` identify lambda terms that have the same reduction behavior.
* **Decode**: Translates normal form `ITerm` back to normal form lambda terms.

### B. Hereditarily Finite (HF) Sets
* **Encode**: Maps set constructors (`empty`, `pair`, `union`) to corresponding algebraic combinator terms in `HFSetEncoding.lean`.
* **Kernel**: Reduces the terms to canonical forms.
* **Quotient**: Syntactically distinct terms representing the same set (e.g., $\{a, b\}$ and $\{b, a\}$) project to the same element in the `InvariantLayer` quotient.
* **Decode**: Maps terms back to `HF` set trees.

### C. Term Rewriting Systems (TRS)
* **Encode**: Translates tree-structured rewrite terms to the `ITerm` basis in `TRSView.lean`.
* **Kernel**: Executes rewrite paths via `IStepBasis` contractions.
* **Quotient**: Identifies subterms that can be proven equivalent under the rewrite rules.
* **Decode**: Reconstructs the simplified algebraic tree.

### D. VM Bytecode
* **Encode**: Compiles sequential stack machine instructions (`push`, `app`) to prefix application terms (`BytecodeView.lean`).
* **Kernel**: Simulates stack evaluation in the substrate.
* **Quotient**: Observes stack configurations modulo computation equivalence.
* **Decode**: Recovers the final stack output.

### E. Barker Iota
* **Encode**: Translates Barker iota trees to prefix application terms in `IotaView.lean`.
* **Kernel**: Evaluates the iota terms via `IStep` contractions.
* **Quotient**: Projects terms onto equivalence classes in `InvariantLayer`, showing how the iota orbit closure maps to the four carriers.
* **Decode**: Reconstructs the simplified iota trees.

---

## 5. The Shared Pattern

The fundamental architectural finding is that **the invariant layer is representation-independent**. Rather than building pairwise compilers, we establish a single mediator pattern:

1. **Total Encoder**: $E_F : \text{Term}_F \to \text{ITerm}$ maps the dialect syntax to the substrate.
2. **Substrate Evaluation**: The common reduction relation `IRed` performs the computation.
3. **Quotient Projection**: The canonical quotient map $\Pi : \text{ITerm} \to \text{InvariantLayer}$ abstracts away representation-specific syntax.
4. **Decoder**: $D_F : \text{InvariantLayer} \to \text{Term}_F$ reconstructs the result in the target domain.

Because this factorization is proven sound and unique for all admissible dialects, we do not require custom translators; compiling from Dialect A to Dialect B is simply the composition of A's encoder with B's decoder:
$$ \text{Compile}_{A \to B} = D_B \circ \Pi \circ E_A $$

---

## 6. Engineering Applications

* **Language Interoperability**: Direct translation between functional (Lambda), declarative (Sets), and imperative (VM Bytecode) dialects without intermediate translation schemas.
* **State Space Representation in Robotics**: Serializing robot state changes into the invariant layer to enable lightweight, verifiably sound model updates.
* **Delta-Communication**: Transmitting minimal matrix diffs (state updates) over the network instead of transmitting full serialized term graphs.
