# ISAR operational quotient and tensor semantics verification

This document summarizes the mathematical connection between the symbolic ISAR operational semantics, the quotient-based invariant layer, and the rank-4 tensor semantics backend, along with the set-theoretic interpretation, view pluralism, and structural quantity arithmetic milestones.

## Summary of the Work

### Phase 1: Core Stack
We successfully split, implemented, and fully verified the entire five-module codebase:

1. **[ISAR.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ISAR.lean)**:
   * Holds the syntax, rewrite rules, and confluence proofs for `ITerm`.
   * Proves unique normal forms for the `ISKTerm` fragment.
   * **Conservative Definability**: Derived the $S$ combinator (`derived_s`) from the structural basis. Proved that any reduction step in the full calculus translates to a reduction using only the basis (`translate_preserves_step`). Formally verified that the translated terms contain no primitive `sₛ` (`NoS`).

2. **[InvariantLayer.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/InvariantLayer.lean)**:
   * **Operational Equivalence & Quotient**: Defined `OperEq` as joinability (operational equivalence/conversion) on the `ISKSubtype` fragment. Proved it is an equivalence relation and defined the quotient type `InvariantLayer`.
   * **Application Congruence**: Proved `app_congruence` and defined the well-behaved application operator `InvariantLayer.app` on the quotient.
   * **Canonical Representatives**: Formulated normal-form existence (`HasNF`) and proved it is invariant under operational equivalence. Implemented `nf_of_term` using `Classical.choose` and lifted it to the quotient-level mapping `canonical_rep`.

3. **[LambdaFragment.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/LambdaFragment.lean)**:
   * **Lambda Fragment Definition**: Defined de Bruijn untyped lambda terms `LTerm` and weak beta-reduction `LStep`.
   * **Bracket Abstraction Compiler**: Implemented `abstract0` bracket abstraction and `compile` compiler functions.
   * **Simulation Verification**: Proves that compilation preserves beta-reduction steps (`compile_simulates_step` and `compile_simulates_red`).

4. **[TensorSemantics.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/TensorSemantics.lean)**:
   * **Tensor Denotation & Soundness**: Declared the signature of `TensorSpace`, `ExtEq`, carrier primitives, and the denotation map `denot`. Proves soundness (`denot_sound`).
   * **Quotient Compositionality**: Proved `lambda_denot_sound` and defined the application homomorphism `toExtTensor_app` mapping compiled lambda terms to the tensor application.
   * **Pairwise Separation (Adequacy)**: Axiomatized non-triviality conditions (`non_trivial_observable` and `non_trivial_observable2`) and proved that the tensor semantics distinguishes a three-element family of closed normal forms: $I$, $K$, and $K_2$. Proved the final family separation theorem `adequacy_family`.

5. **[KernelCategory.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/KernelCategory.lean)**:
   * **Semantic Kernels Category**: Defined `Kernel` structure and structure-preserving morphisms (`KernelHom`).
   * **Terminal Object**: Formalized `ISAR_Kernel` representing the operational quotient presentation of the ISAR calculus itself.
   * **Uniqueness (Terminality) Theorem**: Proved `morphism_uniqueness` showing that any structure-preserving morphism from an arbitrary semantic kernel $K$ into `ISAR_Kernel` is observationally equivalent to the canonical decoding morphism.

---

### Phase 2: Set-Theoretic Interpretation (ZFC / HF-Sets)
We formalized hereditarily finite sets as an admissible semantic view and proved a faithful interpretation into the ISAR stack:

6. **[HFSet.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/HFSet.lean)**:
   * Formalizes finite sets structurally via the inductive type `HF` (representing finite sets built from the empty set via adjoining elements).
   * Defines membership (`Mem`) and extensional equality (`ExtEq`) using Ackermann's bijective encoding (`toNat`). Proves that `ExtEq` is an equivalence relation.
   * Defines constructors `HF.empty`, `HF.pair`, and `HF.union`, and proves that they satisfy the set-theoretic axioms (e.g. `mem_empty`, `mem_insert`, `mem_pair`, `mem_union`).

7. **[HFSetEncoding.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/HFSetEncoding.lean)**:
   * Establishes a canonical bijection between `InvariantLayer` (the operational quotient of the symbolic ISAR calculus) and `HF` sets.
   * Defines the canonical set encoding `HF_encode` mapping sets to quotient classes, and the decoding mapping `decode_term` mapping symbolic terms to sets.
   * Proves the coherence equations:
     * `decode_term (encode_raw c) = c` (decoding an encoded set yields the same set)
     * `OperEq (encode_raw (decode_term t)) t` (encoding a decoded term yields an operationally equivalent term)

8. **[HFSetSemantics.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/HFSetSemantics.lean)**:
   * Lifts set-theoretic constructors to the `InvariantLayer` quotient: `InvariantLayer.empty`, `InvariantLayer.pair`, and `InvariantLayer.union`.
   * Proves that the encoding map `HF_encode` is a homomorphism with respect to these operations (preserving empty set, pairing, and union).

9. **[ZFCInterpretation.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ZFCInterpretation.lean)**:
   * Packages this interpretation as a semantic `Kernel` instance: `HF_Kernel`.
   * Proves the **Interpretation Theorem**: `HF_Kernel` satisfies all coherence equations of admissible semantic kernels.
   * Proves **Unique Factorization**: By the terminality of `ISAR_Kernel`, any structure-preserving morphism from `HF_Kernel` into the canonical `ISAR_Kernel` factors uniquely, showing that set-theoretic semantics are canonically mediated by ISAR.

---

### Phase 3: Reverse Rosetta, View Pluralism, and Structural Quantity Arithmetic
We formalized the general Dialect view framework, proved view representation independence, proved trace decodability boundaries, and verified structural arithmetic:

10. **[DialectKernel.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/DialectKernel.lean)**:
    * Defines the general `Dialect` structure specifying compilation (`encode`), decoding (`decode`), local evaluation (`eval`), and the observational preservation law.

11. **[ViewIndependence.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ViewIndependence.lean)**:
    * Formalizes `ObservationalIsomorphism` establishing a bijection between observation types commuting with decoding.
    * Proves the **No Preferred Syntax Theorem** (`no_preferred_syntax`), showing that observationally isomorphic dialects decode to equivalent observations, demonstrating neither syntax is ontologically privileged.
    * Proves that observational isomorphism between dialects is reflexive, symmetric, and transitive.

12. **[ReverseRosetta.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/ReverseRosetta.lean)**:
    * Formalizes `TransitionSystem` and state subset closure `IsClosed`.
    * Proves **Operational Closed Decodability** (`operationally_closed_decodable`), demonstrating closed systems preserve trace decodability.
    * Formalizes `AnchorDependentSystem` where steps require external environmental anchors.
    * Proves **Referential Openness** (`referentially_open_requires_anchor`), proving that without knowing anchors, trace semantics are non-deterministic and cannot be decoded from the state alone.

13. **[TRSView.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/TRSView.lean)**:
    * Implements a concrete SKI rewrite dialect `TTerm` and compiler `trs_encode`.
    * Constructs a constructive decoder `decode_raw` that matches recursively over the `ITerm` type (avoiding `Prop` elimination limits) and proves inverse properties.
    * Packages the dialect instance `TRS_Dialect` and proves its preservation theorem.

14. **[BytecodeView.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/BytecodeView.lean)**:
    * Implements postfix instructions (`push_I`, `push_K`, `push_S`, `app`), stack VM execution `run`, and compilation to `TTerm`.
    * Formulates decompiler mapping `TTerm` back to bytecode instructions and proves `compile_decompile` is the identity.
    * Packages the `Bytecode_Dialect` instance and proves preservation.

15. **[QuantityKernel.lean](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/QuantityKernel.lean)**:
    * Formalizes **structural arithmetic** as a 4-layered algebraic quantity model (`Rational`, `DimExpr`, `SymbolExpr`, `MetricExpr`, `EpistemicExpr`, and `Quantity`).
    * Implements dimension checks, quantity multiplication, and exact covariance propagation equations for addition and multiplication.
    * Establishes bijections between `Quantity` and `Nat` and constructs the semantic `QuantityKernel : Kernel`.
    * Proves all semantic category `Kernel` laws: `sound`, `decode_view`, `view_eq_decode`, and `decode_eq`.
    * Defines stable addition on the Invariant Layer quotient (`InvariantLayer.add`) and proves that it preserves arithmetic addition.

---

## Narratives
* Phase 1 narrative: [story.md](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/story.md).
* Phase 2 narrative: [hf_story.md](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/hf_story.md).
* Phase 3 narrative: [reverse_rosetta_story.md](file:///C:/Users/fabi0/Documents/antigravity/joyful-lavoisier/reverse_rosetta_story.md).

---

## Verification Status

All 15 modules compile successfully with **no errors, no warnings, and no `sorry` statements**.

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
```
All files were successfully verified by the Lean 4 typechecker.
