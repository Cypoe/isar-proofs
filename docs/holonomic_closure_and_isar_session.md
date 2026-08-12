# ISAR/Plex Holonomic Closure Session

## Status and scope

This document records the complete technical thread from the modular-forms benchmark through the holonomic closure work, including verified results, corrected claims, explicit boundaries, and artifact-delivery failures. It is a session record, not a claim that every proposed idea has already been formalized in Lean.

The durable Python kernel for sections 3–8 lives at [`scratch/isar_holonomic_closure_algebra.py`](../scratch/isar_holonomic_closure_algebra.py). See §10 for lineage, self-test, and continuity rules. Lean-checked counterparts live in `src/ISAR/Holonomic*.lean`; see §12.

## 1. Modular-forms benchmark

The initial goal was to evaluate modular forms in an ISAR/Plex algebra and benchmark the updated kernel against larger levels. The kernel was tested against an independent genus/dimension oracle for levels through large composite and prime levels. The oracle matched known values and remained fast; the sparse exact backend extended the practical range substantially compared with dense rational linear algebra.

The important result was not completion of higher-level modular-form bases. It was the honesty property: the kernel refused to claim completeness when the provider rank was below the true dimension. At levels greater than one, the naive monomial provider remained incomplete while the dimension deficit grew. This established that the kernel's refusal behavior generalized under load.

The sparse transition was therefore principled: retain exact algebraic semantics, move rank and elimination into sparse/modular arithmetic, and use independent-prime or reconstruction checks before treating a result as unconditional. A single-prime rank check is a bounded probabilistic check; two-prime agreement or CRT/rational reconstruction is the appropriate proof boundary.

## 2. Finite proof obligations

The proposed application was to use ISAR/Plex invariants and symmetries to prove properties over an entire infinite field or function space without enumerating infinitely many tests. The correction is precise: this is not merely testing one representative instead of many examples. It is proving that the relevant object lies in a finite generated space and that the property is linear or otherwise preserved by the defining closure operations.

Manin-symbol style presentations illustrate the pattern. An infinite family of modular-symbol paths can be reduced to a finite generating set with finite relations. A linear operator, period pairing, Hecke action, or invariant functional is then determined by its values on that finite presentation. A proof obligation on the generators plus proof that the relations are respected implies the obligation for every represented path.

The SupGen connection is consequently a synthesis architecture: enumerate candidate operators or algorithms in a finite invariant basis, impose the defining symmetry and relation constraints algebraically, and retain only candidates in the relation kernel. The output is not empirical confidence from examples; it is a certificate consisting of generation, relation preservation, and the relevant closure theorem.

## 3. Holonomic algebra

The working artifact was rebuilt around a small kernel:

- a symbol and explicit seed expression;
- differentiation;
- polynomial arithmetic over exact coefficients;
- linear algebra;
- a registry of verified certificates and provenance.

No named special function is used as a primitive in the derivation. Named functions such as erf, Ei, Fresnel functions, and Bell numbers appear only as external ground truth or in the theorem explanation.

A holonomic certificate is a polynomial-coefficient differential equation

\[
\sum_{i=0}^{m} p_i(x) f^{(i)}(x)=0.
\]

`derive_holonomic_ode` searches for such a relation by introducing undetermined coefficients for the polynomials \(p_i\), expanding the residual as a power series, and solving the resulting exact linear system. This is a bounded constructive search: failure within the requested order and degree is reported as "not found within bounds," never as a proof of non-holonomicity.

`verify_certificate` independently differentiates the original expression and simplifies the residual. A certificate enters the registry only when this residual is exactly zero. Every derived generator records order, coefficients, expansion point, verification status, and provenance.

## 4. Integral closure

If \(g\) satisfies

\[
\sum_{i=0}^{m}p_i(x)g^{(i)}(x)=0
\]

and \(h'=g\), then \(h\) satisfies the shifted equation

\[
0\,h + \sum_{i=0}^{m}p_i(x)h^{(i+1)}=0.
\]

This is a direct theorem and needs no elimination. The registry implements it by prepending a zero coefficient. The seed, first integral, and second integral form a composable chain, and the resulting certificate was checked against the independent expression

\[
x\,\operatorname{erf}(x)+e^{-x^2}/\sqrt{\pi}
\]

with exact residual zero.

## 5. Product closure and subgraph merging

For generators \(f\) and \(g\) of orders \(m\) and \(n\), consider the finite tensor basis

\[
V=\operatorname{span}\{f^{(i)}g^{(j)}:0\le i<m,\;0\le j<n\}.
\]

Differentiation preserves this space. An overflowing derivative index is reduced by substituting the verified ODE of the corresponding factor. Thus the derivative action is represented by an exact matrix over rational functions.

The product \(h=fg\) and its first \(mn\) derivatives give \(mn+1\) vectors in a space of dimension at most \(mn\). Their nullspace supplies a differential certificate for \(h\). This is the Wronskian/differential-module principle expressed as explicit companion-basis linear algebra. It is easier to audit than an opaque determinant while encoding the same closure argument.

The implementation was checked on:

- \(e^x e^{-x^2}=e^{x-x^2}\), order 1 times order 1, residual zero;
- \(\sin(x^2)e^{-x^2}\), order 2 times order 1, with certificate
  \[
  8x^3h+(4x^2-1)h'+xh''=0,
  \]
  residual zero;
- a minimality sanity check showing the mixed-order result reaches the tensor upper bound and is not a mistaken lower-order artifact.

This gives a precise answer to subgraph merging: if a subgraph denotes a finite derivative-closed generator space, product merging is the tensor-product construction, with exact reduction and a new verified certificate. It is well-defined up to the representation's canonical equality and deterministic once normalization choices are fixed.

## 6. Sum closure

Sums can be handled by the direct-sum analogue. Track the derivative bases of the two operands separately, close each under its own ODE, initialize with the sum vector, and extract a dependency. The implementation was checked against \(e^x+e^{-x^2}\) with residual zero.

Product and sum therefore belong to the same finite differential-module architecture, although their basis constructions differ: tensor product for multiplication, direct sum for addition.

## 7. Composition is a boundary, not a missing method

The earlier wording treated composition as an unimplemented bridge. That was too weak. General composition is not closed in the holonomic/D-finite class.

The counterexample is

\[
\exp(\exp(x)),
\]

which composes two order-1 holonomic functions. Its Taylor coefficients are related to Bell numbers. Bell-number growth satisfies the known super-exponential asymptotic involving the Lambert \(W\) function, and \(B_n^{1/n}\) grows without bound. D-finite coefficient sequences obey a polynomial-coefficient recurrence and have a bounded exponential root-growth condition. Therefore \(\exp(\exp(x))\) is not D-finite.

The correct registry behavior is consequently not an endless search or a guessed certificate. A general `compose` operation returns a structured impossibility result with the counterexample and growth evidence. Restricted composition subclasses may still be added later, but they require separate theorems and must not be confused with general closure.

## 8. ISAR/Plex interpretation

The closure algebra suggests a clean ISAR interpretation:

- **Invariant:** canonical differential certificates, normalized coefficient vectors, grades/orders, and proof status;
- **Rewrite:** exact derivative reduction, polynomial normalization, sparse elimination, and relation normalization;
- **Adjacency:** generator edges for derivative, integral, sum, product, imported basis, and theorem-backed refusal;
- **State:** evaluation, truncation, modular rank computation, reconstruction, and proof obligations.

A subgraph import should therefore carry its generators, rewrite rules, invariant normal form, relation certificates, and provenance. Merging is valid only when the imported invariant equality and closure interface are verified. The merge operation should return either a canonical merged certificate or an explicit obstruction; it should never create a second unverified path merely to satisfy a requested composition.

## 9. Sparse and larger-scale direction

The modular-form benchmark established the computational policy for larger spaces: use sparse representations and modular arithmetic internally, then independently verify or reconstruct at the boundary. Exact dense rational elimination is appropriate for small certificates and reference tests; it is not the scalable default.

The next principled engineering step is to make the differential-module representation sparse as well: sparse companion actions, sparse tensor basis vectors, modular nullspace computation at multiple primes, and exact reconstruction. The invariant layer should record the primes used, rank agreement, reconstruction data, and residual proof.

## 10. Artifact and continuity audit

The session exposed a process failure. The execution sandbox reset and removed the generated Python artifact. A later rebuild preserved most core logic but initially omitted three demonstrations: the mixed-order product test, its minimality check, and the double-integral level-up chain. An explicit checklist caught the omission; all three were re-derived independently with residual zero and restored into the rebuilt file.

The lesson is architectural as well as operational: generated artifacts must be treated as durable repository inputs, not as ephemeral notebook state. Every artifact should have a stable path, a content hash, a self-test command, and a repository commit. A claim of continuity must distinguish identical content, reconstructed equivalent content, and the same physical file.

### Canonical repository artifact

| Field | Value |
| :--- | :--- |
| Stable path | [`scratch/isar_holonomic_closure_algebra.py`](../scratch/isar_holonomic_closure_algebra.py) |
| SHA-256 (2026-08-12 install) | `2ABC84E406B705C46A59FB1429EC7DF6E580D1E4B6C243F80A64210CD7C712DA` |
| Self-test | `python scratch/isar_holonomic_closure_algebra.py` (requires `sympy`) |
| Role | Exploratory Python kernel matching this session record; **not** a Lean formalization |
| Status | Durable input under ADR 0003 scratch segregation; self-test exit 0 with all residual checks PASS |

**Lineage consolidated into the path above** (Downloads forks superseded):

1. `isar_holonomic_closure_algebra.py` (v5) — integral closure and decision tower; `product_closure` raised `NotImplementedError`.
2. `isar_holonomic_closure_algebra_v7.py` — product/sum closures and theorem-backed composition refusal; initially missing restored demos 4b/4c.
3. `isar_plex_holonomic_closure_algebra.py` — v7 plus restored mixed-order product (minimality check) and double-integral level-up chain.

The repository file is the plex content with a repository header. After any edit, recompute `Get-FileHash scratch/isar_holonomic_closure_algebra.py -Algorithm SHA256` (or `sha256sum`) and record the hash in the commit message or below when claiming bit-identical continuity.

Self-test checklist expected to report residual zero / PASS:

- product \(e^x e^{-x^2}\) and sum \(e^x+e^{-x^2}\)
- mixed-order product \(\sin(x^2)e^{-x^2}\) with order matching the tensor bound
- double-integral chain vs \(x\,\operatorname{erf}(x)+e^{-x^2}/\sqrt{\pi}\)
- composition refusal with strictly increasing Bell-root samples

## 11. Current conclusions

1. Sparse exact computation is the correct scaling direction for the modular-form and ISAR tensor workloads.
2. Finite invariant presentations can turn infinite families of obligations into finite exact proof obligations when generation, relations, and preservation are proved.
3. Holonomic generators form a useful algebra under integral, sum, and product closure.
4. Product merging is a derivative-closed tensor-space construction with exact nullspace certificates.
5. General composition is not a closure operation; the obstruction is mathematical, not an unfinished implementation.
6. ISAR/Plex should model both successful constructions and theorem-backed refusals as first-class invariant outcomes.
7. Repository artifacts, not transient execution state, are the source of truth.

This document records the boundary honestly: the construction layer is strong where closure theorems exist, sparse where scale demands it, and explicit about operations that leave the represented class.

## 12. Lean formalization status

Lean modules (imported from [`src/ISAR.lean`](../src/ISAR.lean)):

| Module | Role |
| :--- | :--- |
| [`ISAR.Holonomic`](../src/ISAR/Holonomic.lean) | `HolonomicCertificate`, `satisfiesODE`, `IsHolonomic`, `integralShift` |
| [`ISAR.HolonomicClosure`](../src/ISAR/HolonomicClosure.lean) | `integral_closure_shift`; order-1 product; constant-rate sum |
| [`ISAR.HolonomicInstances`](../src/ISAR/HolonomicInstances.lean) | Concrete certificates: `exp`, `gaussian`, product, sum, `sin(x²)`, mixed product, double-integral shift, tensor bound |
| [`ISAR.HolonomicCompose`](../src/ISAR/HolonomicCompose.lean) | `ComposeOutcome` refusal; `holonomic_not_closed_under_compose` |

### Proved (Lean-checked, no `sorry`)

| Python claim | Lean name |
| :--- | :--- |
| Integral closure shift | `integral_closure_shift` |
| Order-1 multiplicative product | `product_holonomic_orderOne` |
| Constant-rate sum | `sum_holonomic_const_rates`, `exp_add_exp_holonomic` |
| `exp` certificate | `exp_holonomic` |
| `exp(-x²)` certificate | `gaussian_holonomic` |
| `exp·exp(-x²)` product | `exp_mul_gaussian_holonomic` |
| `exp+exp(-x²)` sum (TEST 4) | `exp_add_gaussian_holonomic` |
| `sin(x²)` certificate | `fresnelSin_holonomic` |
| `sin(x²)·exp(-x²)` mixed (TEST 4b) | `fresnelSin_mul_gaussian_holonomic` |
| Double-integral level-up | `gaussian_double_integral_closure` |
| Mixed tensor bound order = 2 | `fresnel_gaussian_tensor_bound` |
| Compose refuses | `compose_refuses_in_general` |
| General compose impossible given `exp∘exp` | `holonomic_not_closed_under_compose` |

### Sole named axiom (honest boundary in `HolonomicCompose.lean`)

| Axiom | Purpose |
| :--- | :--- |
| `exp_exp_not_holonomic` | `exp∘exp` is not D-finite / holonomic (Stanley + Bell root growth; not yet in Mathlib) |

Unused supporting axioms (`bell_root_diverges`, `exp_exp_taylor_bell`) and residual axioms for the two order-2 certificates were removed once those residuals were proved in `HolonomicInstances`.

Build: `lake build ISAR` (or `lake build ISAR.HolonomicCompose`).
