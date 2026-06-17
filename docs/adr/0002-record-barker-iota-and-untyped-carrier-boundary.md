# ADR 0002: Barker Iota Orbit and Untyped Carrier Boundary

## Status
Proposed

## Context
Barker's Iota combinator calculus ($\iota x = x S K$) generates a closed orbit under iterative application:
$$ I \to A \to K \to S \to X \to I $$
We wanted to map these combinators directly to the four ISAR carriers and formalize the encoder/decoder pair. We also needed to address the typing boundary of the self-application seed $X$ under Hindley-Milner typing rules.

## Decision
We establish the following mappings between the Iota orbit and the ISAR carriers:
- **Barker I** ($I x = x$) $\implies$ **C_I** (Invariant/Quotient Identity)
- **Barker A** ($A x y = y$) $\implies$ **C_A** (Adjacency/Selection)
- **Barker K** ($K x y = x$) $\implies$ **C_R** (Rewrite/Irreversible Selection)
- **Barker S** ($S f g x = f x (g x)$) $\implies$ **C_S** (State/Distribution)
- **Barker X** ($S S K$) $\implies$ Self-application seed (Closure operator $\alpha$ in Axiom 5)

We note that while $I, A, K, S$ can be successfully typed under Hindley-Milner (HM), the self-application seed $X$ cannot be typed as it requires the infinite type equation $\alpha \cong \alpha \to \beta$. Thus, the typing boundary is the carrier boundary, situating the invariant layer below typed languages.

We formally state Tritlo's $Y = X(SB(CX))$ fixed-point combinator in the Iota basis as a concrete instance of Axiom 8 (Theoretical Closure):
$$ U(K) = K $$

## Consequences
- The iota orbit provides a concrete syntactic demonstration of Axiom 5's closure condition.
- The description lengths of the combinators in the iota basis ($I(3), K(7), S(9), A(11)$ nodes) act as Occam scores, demonstrating that simpler combinators are favored under the minimum-description-length principle.
