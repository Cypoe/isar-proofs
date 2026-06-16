# ISAR: A Unified Narrative of the Verified Vertical Stack

This document presents the complete narrative of the ISAR stack, describing the relationship between the ontological substrate, the operational quotient, the symbolic rewrite calculus, and the universal category of semantic views.

---

## 1. The Ontological Substrate (Tensor Space)

At the bottom of the stack lies the **Tensor Space** ($T$): the ontological substrate of the computational model.

* **Extensional Equivalence ($\approx_{ext}$)**: Instead of syntactic identity, calculations in Tensor Space are compared via extensional equivalence (`ExtEq`), allowing different concrete implementations to represent the same underlying computation.
* **IRAS Primitive Carriers**: The substrate is characterized by four core geometric primitive operators:
  * **I** (Identity/Quotient): Projection onto equivalence classes.
  * **R** (Rewrite/Select): Oriented, irreversible selection (asymmetry operator).
  * **A** (Adjacency/Apply): Coordinates interaction topology.
  * **S** (State/Closure): Maintains structural invariants.
* **Derived Operators**: Rather than treating combinators as primitive carriers, the standard computational operators are explicitly derived from the IRAS primitive basis via composition:
  * **Identity (norm / $I$)**: Derived as $S \cdot I$.
  * **Constant (konst / $K$)**: Derived as $I \cdot S$.
  * **Composition (comp / $B$)**: Derived as $R \cdot A \cdot S$.
  * **Duplication (dup / $W$)**: Derived as $S \cdot S$.
  * **Argument Swap (swap / $C$)**: Derived as $R \cdot S$.
  * **Application (app)**: Derived as $A \cdot R$.
* **Derived $S$ Combinator**: In `BasisCompleteness.lean`, we constructively derive the standard distributive combinator $S$ from the structural basis:
  $$ S = B(BW)(C(BB(BBC))I) $$
  and prove that it satisfies the expected $S$-combinator beta-reduction rule:
  $$ S \cdot x \cdot y \cdot z \approx_{ext} x \cdot z \cdot (y \cdot z) $$
  This demonstrates that the computational substrate is built constructively from the IRAS primitives.

---

## 2. The Invariant Layer (Operational Quotient)

Directly above the substrate is the **Invariant Layer** ($\Delta$):

* **The Invariant Layer as a Terminal Object**: The invariant layer is a terminal object in the category of admissible computational substrates, and the quotient specifically is a coinvariant — more precisely, the cofinal quotient under operational equivalence.
* **The Bisimulation Quotient**: Two terms are identified if and only if they have the same infinite continuation behavior — i.e., no observation can distinguish them. In process algebra, this is called **bisimilarity** (Park/Milner), and the quotient space is the **final coalgebra** of the observable functor. Axiom 6 states this exactly:
  $$ I = C / \sim $$
  where $t_1 \sim t_2$ if and only if they share the same infinite continuation.
* **Coinductive Nature**: The invariant layer $\Delta$ is the greatest fixed point of the observable equivalence relation — which is why it is coinductive rather than inductive, and why it cannot be constructed from below, only witnessed from above.
* **Quotient Space**: Modulo operational equivalence (joinability under multi-step reduction in the symbolic calculus), symbolic terms are quotiented to form the type `InvariantLayer` in `InvariantLayer.lean`.
* **Canonical Representatives**: We proved that for any term possessing a normal form, there exists a well-defined canonical representative in the quotient. This establishes that the invariant layer packages computation up to equivalence, independent of concrete evaluation paths.

---

## 3. The Symbolic ISAR Calculus

The **Symbolic ISAR Calculus** (`ITerm`) is the canonical rewrite presentation of the invariant quotient.

* **Syntactic Rewrite Rules**: Implements one-step reduction (`IStep`) and multi-step reduction (`IRed`) in `ISAR.lean`.
* **Confluence & Uniqueness**: Proves confluence and uniqueness of normal forms on the symbolic fragment, ensuring that evaluation is deterministic at the quotient level.
* **Conservative Definability**: To prove that the primitive $S$ combinator is not strictly necessary for the rewrite calculus, we proved that reductions in the full system can be simulated in a system using only the derived basis (`IStepBasis`).

---

## 4. The Lambda Compiler & Adequacy

To demonstrate the expressive power of the stack, we compiled the **Untyped Lambda Calculus** (`LTerm`) with de Bruijn indices into the symbolic ISAR calculus:

* **Simulation**: Compilation preserves operational behavior; a beta-reduction step in Lambda Calculus maps to a multi-step reduction in ISAR.
* **Compositionality**: Denotation of compiled terms is a homomorphism with respect to application:
  $$ \text{denot}(\text{compile}(t \cdot u)) \approx_{ext} \text{denot}(\text{compile}(t)) \cdot \text{denot}(\text{compile}(u)) $$
* **Restricted Adequacy (Separation)**: We proved that the tensor semantics distinguishes distinct closed normal forms of the lambda fragment. Specifically, we defined a three-element family:
  1. $I = \lambda x. x$
  2. $K = \lambda x y. x$
  3. $K_2 = \lambda x y z. x$
  and proved that their compiled tensor denotations are pairwise distinct under extensional equality.

---

## 5. Categorical Universality (Terminality of ISAR)

To close the arc, we formalized the **Category of Admissible Semantic Kernels** ($\mathcal{K}$):

* **Objects**: A `Kernel` is a semantic decode view consisting of a carrier, a view map from the fragment, an equivalence relation, and coherence axioms mapping back and forth via a `decode` function.
* **Morphisms**: A `KernelHom` is a function between carrier types that preserves the view mappings and congruence relations.
* **Terminal Object**: The quotient-level ISAR presentation (`ISAR_Kernel`) is proven to be the **terminal object** in this category:
  * We proved the **Uniqueness (Terminality) Theorem** (`morphism_uniqueness` in `KernelCategory.lean`): any structure-preserving morphism from an arbitrary semantic kernel $K$ into `ISAR_Kernel` is observationally equivalent to the canonical decoding morphism.
  * This establishes ISAR as the canonical semantic presentation of the computational substrate.

---

## 6. Sizing Hierarchies: The Construction of Nibbles and Bytes

The hierarchy of token sizes is derived constructively from the pair primitive, independent of hardware design:

* **1 Bit**: Distinguishes atom from void (existence vs. absence).
* **2 Bits**: Identifies one of the four carriers (**I, S, A, R**) — the minimum needed to name an active role.
* **4 Bits (One Nibble)**: Encodes a directed pair of names (one pointer to a carrier, one pointer from a carrier). This is the minimum structure required to express adjacency (a relation between two carriers). An atom needs 2 bits to be named, and a pair needs 4 bits to be expressed. The nibble is the first pair-level token.
* **8 Bits (One Byte)**: A pair of pairs — source context and target context — representing one complete directed rewrite step (a morphism between two carrier contexts).

### Why Bytes: The Historical Reason (Without ISAR)

The original target was purely hardware economics. Early CPU designers needed an addressable memory unit small enough to be cheap but large enough to encode a character of text. ASCII requires 7 bits for the English alphabet plus control characters. Adding one parity bit for error detection gave 8 bits = 1 byte — and that became the standard addressable unit on the IBM System/360 in 1964, purely for character encoding and memory alignment reasons, with no foundational justification.

### The Connection to ISAR

The connection to ISAR is then: the engineers were solving a representational problem — what is the minimum unit to encode a directed symbol-to-symbol mapping (one character transforming to another, with error detection) — and they empirically landed on a nibble-pair because a directed symbol mapping is precisely one ISAR rewrite step, and the minimum faithful encoding of that is 8 bits. They got the right answer for the wrong stated reason. The parity bit is particularly telling: it encodes asymmetry — exactly $\Delta$ — as an explicit redundancy check.
