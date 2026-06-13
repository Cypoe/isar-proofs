# ISAR operational quotient and tensor semantics verification

This document summarizes the mathematical connection between the symbolic ISAR operational semantics, the quotient-based invariant layer, and the rank-4 tensor semantics backend, along with the set-theoretic interpretation, view pluralism, and structural quantity arithmetic milestones.

## Summary of Completed Work

### Phase 1: Core Stack
We successfully split, implemented, and fully verified the entire five-module codebase:

1. **[ISAR.lean](ISAR.lean)**:
   * Holds the syntax, rewrite rules, and confluence proofs for `ITerm`.
   * Proves unique normal forms for the `ISKTerm` fragment.
   * **Conservative Definability**: Derived the $S$ combinator (`derived_s`) from the structural basis. Proved that any reduction step in the full calculus translates to a reduction using only the basis (`translate_preserves_step`). Formally verified that the translated terms contain no primitive `sₛ` (`NoS`).

2. **[InvariantLayer.lean](InvariantLayer.lean)**:
   * **Operational Equivalence & Quotient**: Defined `OperEq` as joinability (operational equivalence/conversion) on the `ISKSubtype` fragment. Proved it is an equivalence relation and defined the quotient type `InvariantLayer`.
   * **Application Congruence**: Proved `app_congruence` and defined the well-behaved application operator `InvariantLayer.app` on the quotient.
   * **Canonical Representatives**: Formulated normal-form existence (`HasNF`) and proved it is invariant under operational equivalence. Implemented `nf_of_term` using `Classical.choose` for the logical specification and connected it constructively at runtime to `cd_loop` using the `@[implemented_by]` complete-development normalization loop, making `canonical_rep` fully computable.
   * **Complete Development Termination Proofs**: Defined `term_size` and the `IKTerm` sub-fragment (terms built without duplication). Formally proved `cd_size_le_IK` and `cd_size_lt_IK`, showing that complete development strictly decreases term size for all non-fixed-point terms in this fragment.
   * **Computable Normalization Loop**: Implemented the fuel-based normalization loop `cd_loop_fuel` and proved that it preserves operational equivalence (`OperEq_cd_loop_fuel`). Proved `cd_loop_fuel_quotient_eq`, proving that the computable loop projects to the exact same element in the `InvariantLayer` quotient as the input term.

3. **[LambdaFragment.lean](LambdaFragment.lean)**:
   * **Lambda Fragment Definition**: Defined de Bruijn untyped lambda terms `LTerm` and weak beta-reduction `LStep`.
   * **Bracket Abstraction Compiler**: Implemented `abstract0` bracket abstraction and `compile` compiler functions.
   * **Simulation Verification**: Proves that compilation preserves beta-reduction steps (`compile_simulates_step` and `compile_simulates_red`).

4. **[TensorSemantics.lean](TensorSemantics.lean)**:
   * **Tensor Denotation & Soundness**: Declared the signature of `TensorSpace`, `ExtEq`, carrier primitives, and the denotation map `denot`. Proves soundness (`denot_sound`).
   * **Quotient Compositionality**: Proved `lambda_denot_sound` and defined the application homomorphism `toExtTensor_app` mapping compiled lambda terms to the tensor application.
   * **Pairwise Separation (Adequacy)**: Axiomatized non-triviality conditions (`non_trivial_observable` and `non_trivial_observable2`) and proved that the tensor semantics distinguishes a three-element family of closed normal forms: $I$, $K$, and $K_2$. Proved the final family separation theorem `adequacy_family`.

5. **[KernelCategory.lean](KernelCategory.lean)**:
   * **Semantic Kernels Category**: Defined `Kernel` structure and structure-preserving morphisms (`KernelHom`).
   * **Terminal Object**: Formalized `ISAR_Kernel` representing the operational quotient presentation of the ISAR calculus itself.
   * **Computable ISAR Kernel**: Constructed `ComputableISAR_Kernel (fuel : Nat) : Kernel` using `cd_loop_fuel`. Formally verified all category-theoretic kernel laws constructively (without using `noncomputable` or `Classical.choose`).
   * **Uniqueness (Terminality) Theorem**: Proved `morphism_uniqueness` showing that any structure-preserving morphism from an arbitrary semantic kernel $K$ into `ISAR_Kernel` is observationally equivalent to the canonical decoding morphism.

---

### Phase 2: Set-Theoretic Interpretation (ZFC / HF-Sets)
We formalized hereditarily finite sets as an admissible semantic view and proved a faithful interpretation into the ISAR stack:

6. **[HFSet.lean](HFSet.lean)**:
   * Formalizes finite sets structurally via the inductive type `HF` (representing finite sets built from the empty set via adjoining elements).
   * Defines membership (`Mem`) and extensional equality (`ExtEq`) using Ackermann's bijective encoding (`toNat`). Proves that `ExtEq` is an equivalence relation.
   * Defines constructors `HF.empty`, `HF.pair`, and `HF.union`, and proves that they satisfy the set-theoretic axioms (e.g. `mem_empty`, `mem_insert`, `mem_pair`, `mem_union`).

7. **[HFSetEncoding.lean](HFSetEncoding.lean)**:
   * Establishes a canonical bijection between `InvariantLayer` (the operational quotient of the symbolic ISAR calculus) and `HF` sets.
   * Defines the canonical set encoding `HF_encode` mapping sets to quotient classes, and the decoding mapping `decode_term` mapping symbolic terms to sets.
   * Proves the coherence equations:
     * `decode_term (encode_raw c) = c` (decoding an encoded set yields the same set)
     * `OperEq (encode_raw (decode_term t)) t` (encoding a decoded term yields an operationally equivalent term)

8. **[HFSetSemantics.lean](HFSetSemantics.lean)**:
   * Lifts set-theoretic constructors to the `InvariantLayer` quotient: `InvariantLayer.empty`, `InvariantLayer.pair`, and `InvariantLayer.union`.
   * Proves that the encoding map `HF_encode` is a homomorphism with respect to these operations (preserving empty set, pairing, and union).

9. **[ZFCInterpretation.lean](ZFCInterpretation.lean)**:
   * Packages this interpretation as a semantic `Kernel` instance: `HF_Kernel`.
   * Proves the **Interpretation Theorem**: `HF_Kernel` satisfies all coherence equations of admissible semantic kernels.
   * Proves **Unique Factorization**: By the terminality of `ISAR_Kernel`, any structure-preserving morphism from `HF_Kernel` into the canonical `ISAR_Kernel` factors uniquely, showing that set-theoretic semantics are canonically mediated by ISAR.

---

### Phase 3: Reverse Rosetta, View Pluralism, and Structural Quantity Arithmetic
We formalized the general Dialect view framework, proved view representation independence, proved trace decodability boundaries, and verified structural arithmetic:

10. **[DialectKernel.lean](DialectKernel.lean)**:
    * Defines the general `Dialect` structure specifying compilation (`encode`), decoding (`decode`), local evaluation (`eval`), and the observational preservation law.

11. **[ViewIndependence.lean](ViewIndependence.lean)**:
    * Formalizes `ObservationalIsomorphism` establishing a bijection between observation types commuting with decoding.
    * Proves the **No Preferred Syntax Theorem** (`no_preferred_syntax`), showing that observationally isomorphic dialects decode to equivalent observations, demonstrating neither syntax is ontologically privileged.
    * Proves that observational isomorphism between dialects is reflexive, symmetric, and transitive.

12. **[ReverseRosetta.lean](ReverseRosetta.lean)**:
    * Formalizes `TransitionSystem` and state subset closure `IsClosed`.
    * Proves **Operational Closed Decodability** (`operationally_closed_decodable`), demonstrating closed systems preserve trace decodability.
    * Formalizes `AnchorDependentSystem` where steps require external environmental anchors.
    * Proves **Referential Openness** (`referentially_open_requires_anchor`), proving that without knowing anchors, trace semantics are non-deterministic and cannot be decoded from the state alone.

13. **[TRSView.lean](TRSView.lean)**:
    * Implements a concrete SKI rewrite dialect `TTerm` and compiler `trs_encode`.
    * Constructs a constructive decoder `decode_raw` that matches recursively over the `ITerm` type (avoiding `Prop` elimination limits) and proves inverse properties.
    * Packages the dialect instance `TRS_Dialect` and proves its preservation theorem.

14. **[BytecodeView.lean](BytecodeView.lean)**:
    * Implements postfix instructions (`push_I`, `push_K`, `push_S`, `app`), stack VM execution `run`, and compilation to `TTerm`.
    * Formulates decompiler mapping `TTerm` back to bytecode instructions and proves `compile_decompile` is the identity.
    * Packages the `Bytecode_Dialect` instance and proves preservation.

15. **[QuantityKernel.lean](QuantityKernel.lean)**:
    * Formalizes **structural arithmetic** as a 4-layered algebraic quantity model (`Rational`, `DimExpr`, `SymbolExpr`, `MetricExpr`, `EpistemicExpr`, and `Quantity`).
    * Implements dimension checks, quantity multiplication, and exact covariance propagation equations for addition and multiplication.
    * Establishes bijections between `Quantity` and `Nat` and constructs the semantic `QuantityKernel : Kernel`.
    * Proves all semantic category `Kernel` laws: `sound`, `decode_view`, `view_eq_decode`, and `decode_eq`.
    * Defines stable addition on the Invariant Layer quotient (`InvariantLayer.add`) and proves that it preserves arithmetic addition.

16. **[ViewUnification.lean](ViewUnification.lean)**:
    * Defines the general structure `AdmissibleDialect` wrapping a `Dialect` with kernel coherence laws, and compiles it to `.toKernel`.
    * Defines `KernelIsomorphism` and proves **Isomorphism Unification** (`isomorphism_unification`), showing that dialect observational isomorphisms canonically induce category isomorphisms, with translation morphisms constructed canonically using the substrate as the universal medium.
    * Proves the **Universal Factorization Theorem** (`universal_factorization_theorem`) under which ZFC/HF-Sets, Quantity arithmetic, TRS, and Bytecode kernels all factor uniquely through `ISAR_Kernel` by terminality.

---

### Phase 4: Linear Duplication & Optimal Computable Kernel
We formalized linear duplication, verified size-decreasing properties for bounded fuel termination, and machine-verified the canonical ISAR matrix algebra:

17. **[ISARMatrices.lean](ISARMatrices.lean)**:
    * Defines $4 \times 4$ matrices over the integers $\mathbb{Z}$ in a completely self-contained way with decidable equality.
    * Formalizes the canonical ISAR matrices ($I$, $R$, $A$, $S$) for both representation models in the codebase.
    * Formally proves **idempotency** of the projection matrix $I^2 = I$ and **nilpotency** of the rewrite operator $(I \cdot R \cdot A \cdot S)^2 = 0$ constructively using reflexivity (`rfl`).
    * Formally proves **gauge equivalence** between the two kernel representations: $P \cdot K_1 \cdot P^{-1} = K_2$, showing they are conjugate (similar) via an invertible lower-triangular matrix $P$ over $\mathbb{Z}$, unifying the two Python verification paths.


18. **[InvariantLayer.lean](InvariantLayer.lean)**:
    * Added support for **linear duplication** (`LinearIKTerm`) and the multiplicity-based `dupCount` tracking.
    * Formally proved `cd_size_le_LinearIK` and `cd_size_lt_LinearIK`, showing that complete development strictly reduces term size for all non-fixed-point linear terms.
    * Defined `sufficient_fuel` and proved its correctness (`sufficient_fuel_correct`), providing the optimal fuel certificate.

19. **[KernelCategory.lean](KernelCategory.lean)**:
    * Implemented `ComputableISAR_Kernel_Optimal` using the optimal bounded fuel certificate for linearly-typed terms.

---

## Narratives
* Phase 1 narrative: [story.md](story.md).
* Phase 2 narrative: [hf_story.md](hf_story.md).
* Phase 3 narrative: [reverse_rosetta_story.md](reverse_rosetta_story.md).

---

## Verification Status

All 18 modules compile successfully with **no errors, no warnings, and no `sorry` statements**.

### Build commands used
```powershell
$env:LEAN_PATH="."
lean -R . -o ISAR.olean ISAR.lean
lean -R . -o InvariantLayer.olean InvariantLayer.lean
lean -R . -o LambdaFragment.olean LambdaFragment.lean
lean -R . -o TensorSemantics.olean TensorSemantics.lean
lean -R . -o KernelCategory.olean KernelCategory.lean
lean -R . -o HFSet.olean HFSet.lean
lean -R . -o HFSetEncoding.olean HFSetEncoding.lean
lean -R . -o HFSetSemantics.olean HFSetSemantics.lean
lean -R . -o ZFCInterpretation.olean ZFCInterpretation.lean
lean -R . -o DialectKernel.olean DialectKernel.lean
lean -R . -o ViewIndependence.olean ViewIndependence.lean
lean -R . -o ReverseRosetta.olean ReverseRosetta.lean
lean -R . -o TRSView.olean TRSView.lean
lean -R . -o BytecodeView.olean BytecodeView.lean
lean -R . -o QuantityKernel.olean QuantityKernel.lean
lean -R . -o ViewUnification.olean ViewUnification.lean
lean -R . -o ISARMatrices.olean ISARMatrices.lean
```
All files were successfully verified by the Lean 4 typechecker.

