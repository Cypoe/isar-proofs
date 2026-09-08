# ISAR: Invariant Kernel for Closed Computational Dialects

[![Lean](https://github.com/Cypoe/ISAR-proofs/actions/workflows/lean.yml/badge.svg)](https://github.com/Cypoe/ISAR-proofs/actions/workflows/lean.yml)

ISAR is a Lean 4 formalization of a minimal combinatory calculus whose operational quotient — the **Invariant Layer** — is the terminal object in a stated category of closed computational dialects (`Kernel`). Lambda calculus, term rewriting systems, stack VM bytecode, hereditarily finite sets, and linear interaction nets are modelled as views that factor through this quotient via structure-preserving morphisms. Modules are machine-checked; see [STATUS](STATUS.md) for axiom / vacuity notes and a dated **program status / next** list (sorry-free ≠ non-vacuous).

Related literature for the intended claims: Rutten–Aczel (coalgebras), Abramsky–Ong (applicative bisimilarity), Jones/Gomard/Sestoft (partial evaluation). Terminality is relative to the formal `Kernel` interface, not a claim that other calculi lack models or encodings.

The core factorization pattern is:
$$\text{Encoder} \to \text{Kernel} \to \text{Quotient (InvariantLayer)} \to \text{Decoder}$$
Different formalisms are the views/decoders; the quotient is the shared observational presentation.

---

## Summary of Verified Modules

### Phase 1: Core Calculus

1. **[ISAR.lean](ISAR.lean)** — Syntax, rewrite rules, confluence, unique normal forms for `ISKTerm`, and basis completeness (derives $S$ from $I, K, W, C, B$).

2. **[InvariantLayer.lean](src/ISAR/InvariantLayer.lean)** — `OperEq` joinability quotient, `app_congruence`, `cd_loop_fuel`, linear fuel certificates.

2a. **[CanonicalRepresentative.lean](src/ISAR/CanonicalRepresentative.lean)** — `cd` / `cd_loop_fuel` as explicit OperEq representatives; Gross–Knuth: finite `cd` reaches the unique NF iff `HasNF`; unrestricted `canonical_rep_eq` proved (`nf_of_term` = NF or class `exists_rep`).

3. **[LambdaFragment.lean](LambdaFragment.lean)** — de Bruijn `LTerm`, bracket abstraction `abstract0`, compiler `compile`, simulation: `compile_simulates_step` and `compile_simulates_red`.

4. **[TensorSemantics.lean](TensorSemantics.lean)** — Term model (`TensorSpace := ITerm`, `ExtEq` = `IRed` joinability, B/C/W); `denot_sound`, adequacy separating $I$, $K$, $K_2$.

5. **[KernelCategory.lean](KernelCategory.lean)** — `Kernel` structure, `ISAR_Kernel` terminal object, `ComputableISAR_Kernel`, `morphism_uniqueness` (terminality).

---

### Phase 2: Set-Theoretic Interpretation

6. **[HFSet.lean](HFSet.lean)** — Inductive `HF` type, Ackermann `toNat` bijection, membership, extensional equality, set axioms.

7. **[HFSetEncoding.lean](src/ISAR/HFSetEncoding.lean)** — Constructed Ackermann `fromNat` / ISK Gödel numbering; constructed `noncomputable` `layerToNat` / `natToLayer` (min-Gödel enumeration); `HF_encode` / `decode_layer`.

8. **[HFSetSemantics.lean](HFSetSemantics.lean)** — Lifts set constructors to `InvariantLayer`; proves `HF_encode` is a homomorphism.

9. **[ZFCInterpretation.lean](ZFCInterpretation.lean)** — `HF_Kernel` instance, interpretation theorem, unique factorization through `ISAR_Kernel`.

---

### Phase 3: Admissible Observation Category \(\mathcal O\)

10. **[DialectKernel.lean](DialectKernel.lean)** — `Dialect` structure: encode, decode, eval, preservation law.

10a. **[ObservationRegime.lean](src/ISAR/ObservationRegime.lean)** — admissible \(\mathcal O\): `ObservationRegime`, `sim` (\(\sim_{\mathcal O}\)), `operEqRegime`, `QuotientMapO`; dialects as regime-preserving maps. **Phase 3 formal core** (OperEq is the primary instance).

10b. **[CoGen.lean](src/ISAR/CoGen.lean)** — Realize / `LoaderPlan` / `Budget` / `LoaderFamily.fasm`; host `cogen.py` (IdentityRealize + FasmRealize).

10c. **[FASMView.lean](src/ISAR/FASMView.lean)** — FASM presentation = bytecode `Instruction` carrier; host owns fasmg-ish text. Phase 4b.

11. **[ViewIndependence.lean](ViewIndependence.lean)** — `ObservationalIsomorphism`, **No Preferred Syntax Theorem** (`no_preferred_syntax`), reflexivity/symmetry/transitivity.

12. **[ReverseRosetta.lean](ReverseRosetta.lean)** — `closure_preserved_under_reachability` (forward invariance), `referentially_open_requires_anchor` (referential openness).

13. **[TRSView.lean](TRSView.lean)** — `TTerm` SKI dialect, `trs_encode`, `decode_raw`, `TRS_Dialect`.

14. **[BytecodeView.lean](BytecodeView.lean)** — Stack VM (`push_I`, `push_K`, `push_S`, `app`), `run`, `compile_decompile` identity, `Bytecode_Dialect`.

15. **[QuantityKernel.lean](QuantityKernel.lean)** — 4-layer quantity algebra, `QuantityKernel : Kernel`; named `Quantity ≃ Nat` bridge (`String`/`Float` block `Encodable`).

16. **[ViewUnification.lean](ViewUnification.lean)** — `AdmissibleDialect`, `KernelIsomorphism`, **Universal Factorization Theorem** (`universal_factorization_theorem`).

17. **[Futamura.lean](src/ISAR/Futamura.lean)** — Subst-layer mix; `PESetup` 2nd/3rd projections; `TrivialPE` (`¬Nontrivial`), fragment `OptimizingPE`, and online `JGS_PE` for the full `IStep` signature (proved `Nontrivial`). Not 1993 polyvariant mix.

---

### Phase 4: Linear Duplication, Optimal Kernels & Matrix Geometry

18. **[ISARMatrices.lean](ISARMatrices.lean)** — $4 \times 4$ integer matrices, $I^2 = I$ (idempotency), $(IRAS)^2 = 0$ (nilpotency), gauge equivalence $P K_1 P^{-1} = K_2$.

19. **[InvariantLayer.lean](InvariantLayer.lean)** — `LinearIKTerm`, `dupCount`, `cd_size_lt_LinearIK`, `sufficient_fuel` certificate and `sufficient_fuel_correct`.

20. **[KernelCategory.lean](KernelCategory.lean)** — `ComputableISAR_Kernel_Optimal` with optimal fuel certificate.

---

### Phase 5: Continuous semantics (named UAT / completion axioms)

21. **[ISARApproximation.lean](src/ISAR/ISARApproximation.lean)** — Named analytic axiom `ISAR_UAT` (Leshno-style, not proved) plus named completion/embedding axioms. `KernelAddress` has no metric; `KernelAddressLimit` is **not** Mathlib `Metric.Completion`. Frozen pending a metric.

---

## Connection to HVM2 & Linear Interaction Nets

| `LinearIKTerm` Property | HVM2 / Interaction Net Concept |
|:---|:---|
| `LinearIKTerm` predicate | Linearity constraint (no nested duplicator nodes) |
| `dupCount t = 0` | Pure linear fragment, $O(1)$ per redex |
| `dup` operator | Duplicator / fan node |
| Complete development `cd` | Parallel reduction layer |
| `cd_size_lt_LinearIK` | Size decrease, termination |
| `sufficient_fuel_correct` | Max interaction bound |
| Relational $U$-table contraction | Port linking |

---

## Runnable Reduce

Two computable reduction strategies, both sound w.r.t. the proved `IStep` relation:

| Strategy | File | What it does |
|:---------|:-----|:-------------|
| `cd` (parallel) | `Eval.lean` | Complete development: contracts every redex in one pass. Iterated via `cd_loop_fuel`. |
| `step?` (LO) | `Reduce.lean` | Leftmost-outermost single step. `reduceFuel` iterates it. Proved sound: `step? t = some u → IStep t u`. |

```bash
# In-Lean #eval / #guard (compile-time checked):
lake env lean src/ISAR/Eval.lean      # cd strategy goldens
lake env lean src/ISAR/Reduce.lean    # step? strategy goldens

# CLI golden suite (both strategies, printed NF + step count):
lake env lean --run Main.lean

# Reduce a single term (S-expression, atoms: I K S B C D):
lake env lean --run Main.lean --term "((S K) K) I"

# Host congruence check (Python step must match Lean NF):
python host/congruence.py

# Phase 2 proper-toy: shared composition-graph (LO / ParStep-cd / kürzen):
python host/graph_runtime.py
python host/graph_congruence.py
python host/graph_congruence.py --lean   # also vs Main.lean
python host/graph_bench.py --rounds 3    # tree vs graph wall + unique nodes

# ObservationRegime + QuotientMaps (preserve ~_O; OperEq primary):
python host/observation_regime.py
python host/quotient_map.py
python host/lambda_dialect.py
python host/lambda_dialect.py --tree
python host/lambda_dialect.py --abstract0
python host/bytecode_dialect.py
python host/fasm_dialect.py
python host/observational_suite.py
python host/host_pieces.py
python host/strategy.py
python host/cogen.py
python host/mine_adopt.py
python host/lambda_congruence.py
```

Pipeline: presentations → **ObservationRegime** \(\mathcal O\) induces \(\sim_{\mathcal O}\) → **QuotientMap.encode** → Graph/host piece → decode. Maps **preserve** \(\mathcal O\) (not invent \(\sim\)). Lean: `ISAR.ObservationRegime`, `operEqRegime`, `QuotientMapO`. Tree `--tree` is A/B only.

**Runtime roadmap:** carriers → kernel → runtime → **\(\mathcal O\)** → QuotientMaps → host pieces + strategy → **CoGen choose/emit/adopt** → **FasmRealize** (first non-identity emit) → later native fasmg/CPU loaders.

### Alphabet layers

| Layer | What | Source of truth |
|:------|:-----|:----------------|
| Pure tower L0 | `norm, app, comp, dup, swap` | `host/tower.py` |
| Pure tower L1 | `s=derived_s`; `k` macro (`konst_macro`) | `host/tower.py`, Lean `IStepKMacro` |
| Shared graph host | L0+L1 rewrite + kürzen | `host/graph_runtime.py` |
| **ObservationRegime** | \(\sim_{\mathcal O}\); OperEq primary | `ObservationRegime.lean`, `host/observation_regime.py` |
| QuotientMap | encode/decode **preserving** \(\mathcal O\) | `host/quotient_map.py`, λ + Bytecode + **FASM** |
| Host pieces + strategy | Graph piece; Identity/Mix stubs | `host/host_pieces.py`, `host/strategy.py` |
| **CoGen / Realize** | choose/emit/adopt; IdentityRealize + **FasmRealize** | `host/cogen.py`, `host/mine_adopt.py`, `CoGen.lean` |
| FASM(g) dialect | fasmg-ish text QuotientMap; reduce still graph | `host/fasm_dialect.py`, `FASMView.lean` |
| Later: native loaders | external fasmg / CPU-SIMD-GPU HostPieces | not this wave |

### Noted for later

1. **Mine ≠ invent encode.** `mine_adopt.try_adopt`: OperEq match a known map, else explicit QuotientMap.
2. **CoGen loader shape.** `choose(..., budget, c)` → `LoaderPlan` → `emit` into host_pieces. SERIAL+x86_64 → `fasm`; SIMD/GPU families stub to graph until loaders exist.
3. Lean `konst_macro` — L1 macro layer; **BCWI ⊬ K** (never derive). BCWIK was construction scaffolding only.
4. **Not** EAL / Interaction Combinators as semantic source — possible realization backends \(R_{c,\mathcal O}\) only.
5. **Native fasmg / PE** — assemble/link and real CPU HostPiece; FASM presentation ≠ native exec. Never "InvariantLayer IT".

### What this is not

- **Not Lafont interaction nets.** No δ/ε/γ annihilation — superfluous for composition/tensor graphs; we don't have ports. Sharing is node identity + edges.
- **Not plex-core product surface.** Ports / five lowerings / wire are not the kernel. The proper-toy keeps composition-shaped sharing only.
- **plex-shell is parked.** No kernel work, no emit/cogen claims from that tree. The ISAR kernel lives here in `isar-proofs`.
- **No external fasmg yet.** FASM QuotientMap + FasmRealize ship; reduce remains `graph.lo`.

---

## Local Build

```bash
git clone https://github.com/cypoe/isar-proofs.git
cd isar-proofs
lake build
```

Blueprint (PDF + HTML):

```bash
cd blueprint
latexmk -pdf src/print.tex          # twice to resolve cross-refs
plastex -c src/plastex.cfg src/web.tex
```

Or via Docker (no local LaTeX install):

```powershell
docker run --rm -v "${PWD}:/doc" -w /doc/blueprint/src texlive/texlive xelatex print.tex
```

Validate all 87 blueprint declarations against the Lean source:

```bash
lake exe checkdecls blueprint/lean_decls
```

---

## Narratives

- Phase 1: [story.md](docs/story/story.md)
- Phase 2: [hf_story.md](docs/story/hf_story.md)
- Phase 3: [reverse_rosetta_story.md](docs/story/reverse_rosetta_story.md)

## Exploratory: Holonomic Closure Algebra

Session record and Python/Lean kernels for D-finite certificates under integral / sum / product closure, with theorem-backed refusal of general composition.

- Session: [docs/holonomic_closure_and_isar_session.md](docs/holonomic_closure_and_isar_session.md) (§12 Lean status)
- Python: [scratch/isar_holonomic_closure_algebra.py](scratch/isar_holonomic_closure_algebra.py) — `python scratch/isar_holonomic_closure_algebra.py`
- Lean: `ISAR.Holonomic`, `ISAR.HolonomicClosure`, `ISAR.HolonomicInstances`, `ISAR.HolonomicCompose`
