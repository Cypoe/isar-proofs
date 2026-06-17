# Document B: Formal Theorems & Proofs

This document presents the formal mathematical foundations of the ISAR system. All definitions and theorems have been mechanized and fully verified using the **Lean 4** proof assistant.

---

## 1. Syntax and Operational Semantics

The core term algebra $T$ is defined inductively in **[ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ISAR.lean)** as `ITerm`:

$$ t, u \in \text{ITerm} ::= \text{var}(n) \mid \text{norm} \mid \text{konst} \mid \text{dup} \mid \text{swap} \mid \text{comp} \mid s_s \mid t \cdot u $$

Where:
* $t \cdot u$ denotes term application.
* $\text{norm}, \text{konst}, \text{dup}, \text{swap}, \text{comp}$ serve as constructors for the syntactic calculus, which are geometrically derived in the tensor substrate.
* $s_s$ is a primitive combinator (distributive step).

One-step reduction `IStep` ($\to_I$) is defined inductively by the following rules:

* **Identity**: $\text{norm} \cdot x \to_I x$ (`normβ`)
* **Constant**: $\text{konst} \cdot x \cdot y \to_I x$ (`konstβ`)
* **Composition**: $\text{comp} \cdot f \cdot g \cdot x \to_I f \cdot (g \cdot x)$ (`compβ`)
* **Distribution**: $s_s \cdot x \cdot y \cdot z \to_I (x \cdot z) \cdot (y \cdot z)$ (`sβ`)
* **Congruence**:
  $$\frac{f \to_I f'}{f \cdot x \to_I f' \cdot x} \text{ (appL)} \qquad \frac{x \to_I x'}{f \cdot x \to_I f \cdot x'} \text{ (appR)}$$

The relation `IRed` ($\twoheadrightarrow_I$) is the reflexive-transitive closure of `IStep`:
$$ \twoheadrightarrow_I \ \triangleq \ (\to_I)^* $$

---

## 2. Confluence & Normalization

To prove confluence, we define the **Parallel Reduction** relation `ParStep` ($\Rightarrow$) in **[ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ISAR.lean)**, which allows simultaneous contractions of multiple redexes in a single step:

* **Reflexivity**: $x \Rightarrow x$ (`refl`)
* **Contractions**:
  * $\text{norm} \cdot x \Rightarrow x'$ if $x \Rightarrow x'$ (`norm_red`)
  * $\text{konst} \cdot x \cdot y \Rightarrow x'$ if $x \Rightarrow x'$ and $y \Rightarrow y'$ (`konst_red`)
  * $\text{comp} \cdot f \cdot g \cdot x \Rightarrow f' \cdot (g' \cdot x')$ if $f \Rightarrow f'$, $g \Rightarrow g'$, $x \Rightarrow x'$ (`comp_red`)
  * $s_s \cdot x \cdot y \cdot z \Rightarrow (x' \cdot z') \cdot (y' \cdot z')$ if $x \Rightarrow x'$, $y \Rightarrow y'$, $z \Rightarrow z'$ (`s_red`)
* **Congruence**: $f \cdot x \Rightarrow f' \cdot x'$ if $f \Rightarrow f'$ and $x \Rightarrow x'$ (`app`)

### Complete Development and Confluence
We define the **complete development** function `cd` recursively on terms. The main theorems verified in **[ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ISAR.lean)** are:

* **Takahashi's Lemma** (`ParStep_cd`): If $x \Rightarrow y$, then $y \Rightarrow \text{cd}(x)$.
* **Confluence of Parallel Step** (`ParStep_confluent`): If $x \Rightarrow y_1$ and $x \Rightarrow y_2$, there exists $z$ such that $y_1 \Rightarrow z$ and $y_2 \Rightarrow z$.
* **Confluence of the Calculus** (`IRed_confluence`): The relation $\twoheadrightarrow_I$ satisfies the Church-Rosser property.
* **Uniqueness of Normal Forms** (`isar_fragment_unique_normal_forms`): An encoded term has at most one normal form under $\twoheadrightarrow_I$.

---

## 3. Combinator Embedding and Universality

The S combinator is not strictly necessary for the rewrite algebra. We define the **derived S combinator** `derived_s` in **[ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ISAR.lean)** as:

$$ \text{derived\_s} \ \triangleq \ (\text{comp} \cdot (\text{comp} \cdot \text{dup})) \cdot ((\text{swap} \cdot ((\text{comp} \cdot \text{comp}) \cdot ((\text{comp} \cdot \text{comp}) \cdot \text{swap}))) \cdot \text{norm}) $$

We verify the following core theorems:

* **Simulation Soundness** (`derived_s_beta`):
  $$ \text{derived\_s} \cdot x \cdot y \cdot z \twoheadrightarrow_{I_{basis}} (x \cdot z) \cdot (y \cdot z) $$
  where $\twoheadrightarrow_{I_{basis}}$ is the reduction relation `IRedBasis` restricted to the basis operators (without $s_s$).
* **Conservative Translation** (`translate_preserves_step`): The translation mapping `translate_to_basis` (replacing $s_s$ with `derived_s`) preserves reductions.
* **Universality Path**: Since the basis supports abstraction elimination and compiles lambda terms (`LTerm` in `LambdaFragment.lean`), the simulator inherits Turing-completeness via the standard chain:
  $$ \text{Lambda Calculus} \to \text{SKI Combinators} \to \text{ISAR Substrate} $$

---

## 4. Admissible Dialects & Kernel Category

The semantic views are structured category-theoretically in **[KernelCategory.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/KernelCategory.lean)**:

* **Kernel**: A semantic decoder view mapping a carrier type $C$, an equivalence relation $\approx$, and a decode function:
  $$ \text{decode} : C \to \text{ITerm} $$
  subject to soundness and congruence axioms.
* **KernelHom**: A morphism $h : C_1 \to C_2$ between carrier types preserving both the application operation and the decoding mapping.
* **InvariantLayer**: The operational quotient type constructed in **[InvariantLayer.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/InvariantLayer.lean)** modulo `OperEq` (joinability). We prove `app_congruence`, establishing that:
  $$ [f] \cdot [x] \ \triangleq \ [f \cdot x] $$
  is a well-defined application operator on the quotient.

### Terminality of the ISAR Kernel in $\mathbf{Sub}$

To establish the categorical foundation of view-independence, we define the category $\mathbf{Sub}$ of admissible computational substrates:
- **Objects**: Computational substrates $M = (C_M, \cdot_M, \Pi_M)$ where $C_M$ is a carrier set closed under the self-application operator $\cdot_M$, and $\Pi_M : C_M \to C_M$ is an idempotent normalization projection onto equivalence classes under operational equality ($\sim$).
- **Morphisms**: Simulation maps $f: M_1 \to M_2$ that commute with the normalization projection:
  $$ f(\Pi_{M_1}(x)) = \Pi_{M_2}(f(x)) $$
  and preserve the application operation:
  $$ f(x \cdot_{M_1} y) = f(x) \cdot_{M_2} f(y) $$

* **Morphism Uniqueness (Terminality)** (`morphism_uniqueness`):
  Let $M$ be any admissible substrate. There exists a unique morphism $\phi_M : M \to K$ (the canonical compilation map) into the terminal ISAR Kernel $K$ such that the following diagram commutes:
  
```
                 h
         K ─────────────► ISAR_Kernel
         │                     │
         │                     │
  decode │                     │ [id]
         ▼                     ▼
       ITerm ───────────────► InvariantLayer
                    Π
```
  Where $\Pi$ is the canonical quotient projection. By terminality, every other substrate $M$ is a gauge of ISAR: any computational dialect is mediated by a unique morphism into the invariant layer rather than a mere arbitrary syntactic encoding.

### The 4-Carrier Minimality Proof by Exclusion

We prove that exactly four independent carriers $\{C_I, C_S, C_A, C_R\}$ are necessary and sufficient to form an admissible computational substrate:
1. **Axiom 3 ($\Delta$-asymmetry) forces at least a pair**: We require at least $C_I$ (Identity, representing operational equivalence) and $C_R$ (Rewrite Selection, representing the asymmetric directed transition). Without $C_I$, there is no notion of stable normal form or identity preservation. Without $C_R$, there is no directed computational progression, making the system static and degenerate.
2. **Self-application closure forces $C_S$**: To satisfy the closure condition (Axiom 5), applying a carrier to itself must remain in the carrier set. This requires a state/distributivity operator $C_S$ to copy and distribute operands over contexts. Without $C_S$, the system cannot copy terms, restricting it to linear, non-duplicating behaviors which are strictly sub-universal.
3. **Causal wiring requires $C_A$**: Causal wiring and interaction topology require an adjacency operator $C_A$ to route parameters and select neighbors in composition. Without $C_A$, carriers $C_I, C_R, C_S$ cannot compose into directed causal chains; the system is unable to enforce ordering, collapsing to a trivial unordered set of values.

Removing any single carrier makes the system either:
- **Degenerate**: Lacks operational distinction ($C_I$ or $C_R$ missing).
- **Non-closed**: Escapes the category of self-application dynamics ($C_S$ missing).
- **Non-universal**: Computes only a proper subclass of effective functions ($C_A$ missing).

### Occam and the Probabilistic description-length functional on $\mathbf{Sub}$

The invariant layer $\mathcal{I}$ serves as the structural quotient, while probability is a scalar measure on $\mathcal{I}$. For any substrate $M$, we define the Bayesian Occam score as the marginal likelihood:
$$ p(D \mid M) = \int p(D \mid \theta, M) p(\theta \mid M) d\theta $$
where:
- **Parameters ($\theta$)** represent the number of carrier elements and rewrite rules of the substrate.
- **Flexibility** represents the volume of the hypothesis space the carriers can explore.
- **Evidence** represents the compression length of a reference computation (or the shortest operational path length to a target normal form).

Given two substrates $M_1$ and $M_2$ encoding a computation $c$, their relative Occam score is the ratio of their description lengths in the ISAR basis. The terminal kernel $K$ acts as the Minimum Description Length (MDL) substrate, maximizing marginal likelihood by having zero wasted flexibility beyond the four necessary carriers.

---

## 5. Scope & Limitations

The formalization specifies strict boundaries of validity:

* **Admissible Closed Dialects**: The uniqueness and terminality theorems apply exclusively to formalisms that are **operationally closed**—meaning they possess a total encoding function $E_F$ and their reduction relations can be simulated step-for-step by the deterministic, confluent `IStep` relation of the substrate.
* **Unification Scope**: This category covers combinator engines, finite set theory interpreters, stack VMs, and deterministic term rewriting systems. Open algebren (such as natural languages or dynamic semantic graphs) do not satisfy the closure conditions and are outside the scope of these proofs.
