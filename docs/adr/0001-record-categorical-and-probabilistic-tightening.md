# ADR 0001: Categorical and Probabilistic Tightening of the Invariant Layer

## Status
Proposed

## Context
The ISAR kernel was previously described as a terminal object in the category of admissible computational substrates, but the category was not explicitly formulated, nor were the morphisms mathematically defined. Additionally, the Occam/probabilistic interpretation of the invariant layer was loose and needed a formal attachment to description-length functionals.

## Decision
We formally define the category $\mathbf{Sub}$ of admissible computational substrates as follows:
- **Objects**: Substrates $M = (C_M, \cdot_M, \Pi_M)$ where $C_M$ is a carrier set closed under the application operator $\cdot_M$, and $\Pi_M : C_M \to C_M$ is an idempotent normalization projection mapping terms to their operational normal forms.
- **Morphisms**: Simulation maps $f : M_1 \to M_2$ that commute with normalization:
  $$ f(\Pi_{M_1}(x)) = \Pi_{M_2}(f(x)) $$
  and preserve the application homomorphism:
  $$ f(x \cdot_{M_1} y) = f(x) \cdot_{M_2} f(y) $$

We establish the terminal-object status of the ISAR Kernel $K$ by demonstrating that for any admissible substrate $M$, there exists a unique morphism $\phi_M : M \to K$ (the compilation map) that factors any view through the invariant quotient.

We formally attach the Bayesian Occam measure to $\mathbf{Sub}$ using the description-length functional:
$$ p(D \mid M) = \int p(D \mid \theta, M) p(\theta \mid M) d\theta $$
where parameters $\theta$ correspond to carrier elements/rewrite rules, and the evidence is defined by the description length of a reference computation in the basis. The relative Occam score is defined as the ratio of description lengths in the ISAR basis, proving that the kernel $K$ is the minimum-description-length substrate.

## Consequences
- The uniqueness of the compilation map guarantees that all admissible dialects factor uniquely through the Invariant Layer (representation-independence).
- The Occam metric provides a formal explanation for why a 4-carrier basis is optimal, as any additional flexibility would increase the description length and penalize the marginal likelihood.
