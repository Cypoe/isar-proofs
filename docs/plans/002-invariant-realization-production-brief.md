# Invariant realization: production-chain brief

**Purpose:** A plan for the local agent, not a claim that the proposed end state already exists. Preserve the working host and make its semantic and staging contracts explicit. Prefer a small coherent construction over a new framework of manifests, registries, certificates, and parallel compiler paths.

## 1. What is being built

The subject is an operation described through a dialect map under an observation regime, not a source file belonging to a privileged frontend. A realization chooses a lawful way to execute that operation on a host. Static interpretation and emission happen before deployment; the deployed path is **load → run**, with only genuinely dynamic inputs left.

Conceptual shape:

```text
Dialect expression or constructed term
  ── QuotientMap / ObservationRegime O ──► operational meaning
  ── specialization with Realization + host data ──► residual HostPiece
  ── existing emit chain, if needed ──► artifact
  ── run and compare observations ──► evidence about this realization
```

This is not a demand for a single canonical term, a globally optimal equivalent program, or a general program-equivalence solver. The desired invariant is preservation of the *specified observations* along each actual realization step.

Separate two structures that were conflated in earlier sketches:

- **Operational structure:** what is executed/reduced and what `O` observes.
- **Realization dependency structure:** which known dialect, specialization, ISA, ABI, routines, packer, payload, and builder produced an artifact. This resembles a Nix derivation, but provenance is not semantic proof.

Do not materialize either structure a second time merely to satisfy the diagram. Describe existing objects and seams first.

## 2. Corrected distinctions

| Concern | Existing/desired role | Not its role |
|---|---|---|
| `lambda_`, `bytecode_`, `fasm_`, `xdu_` | Dialect `QuotientMap`s under a specified observation regime | Sequential frontend passes or target ISAs |
| `ObservationRegime O` | Defines the projection of behavior a particular claim concerns | A universal equality oracle |
| `OperEq` / `IStepBasis` | Operational contract and proof obligations | An automatic optimizer or a completed proof of every host implementation |
| `Realization`, `toolchain.json` | Declared parameters and catalog entries | Proof of legality, correctness, or optimality merely by being listed |
| `strategy`, `cogen`, `HostPiece` | Select/construct a supported realization | An exact global cost optimizer unless separately specified and proved |
| `emit_chain`, `seed.emit` | Staged and seed constructions with an exact byte-comparison seam | Two product compilers that should be maintained independently |
| `graph.lo`, PE/ELF, C, fasmg, CUDA IR | Execution/emission witnesses with different applicable comparisons | Votes that automatically establish truth by majority |
| `congruence`, `cross_verify` | Executable gates comparing observations on specified cases | Universal proof of program equivalence |

**Correction to the earlier answer:** “Truth is agreement across witnesses” was too strong. Agreement on a finite test set is evidence, not a theorem. The semantic contract is defined by `O` and the operational laws; Lean obligations, construction arguments, and executable cross-checks supply different kinds of support. No witness is *automatically* foundational, but the graph implementation can serve as a practical baseline without being promoted to an infallible oracle.

## 3. The smallest useful contract

For a supported dialect `D`, operation `p`, observation regime `O`, realization request `R`, selected host `h`, and dynamic input `x`, the desired behavioral claim is:

```text
Observe_O( run_h(realize(D, R, p), x) )
  =
Observe_O( operate_D(p, x) ).
```

Specify the domain and observations before claiming that equality: termination/fuel, failure, effects, allocation and step counts matter only if the chosen `O` includes them. A normal-form gate and a stdout+exit-code gate are different claims. Do not infer cross-ISA equality of every internal step from equality of output tokens.

Specialization is a separate property:

```text
run( specialize(realizer, static = (D, R, p, target data)), x )
  ~_O
run( realizer, static = (D, R, p, target data), dynamic = x ).
```

`~_O` is observational equivalence *in the specified domain*. The first Futamura-shaped result concerns residual execution of one operation; a second-projection-shaped result specializes the specializing/emitting machinery for a family of operations. Neither property requires calling the realizer a self-interpreter. Nor does a suggestive shape alone establish a fully general, polyvariant Futamura-2 implementation.

The existing construction seam has a narrower claim:

```text
emit_chain_image(R) == seed.emit(R)  # byte-exact, for declared R and target
```

That proves agreement of two construction routes for those inputs. It does **not** prove that the shared semantics are right, that a binary is fast, or that all dialects are covered.

## 4. Production shape without a second architecture

Keep the live path recognizable:

```text
Static build work:
  dialect map / observation contract
    + Realization / toolchain data
    + static operation or payload
      → specialization / plan
      → resolve → routines.program → peephole → assemble → pack
      → HostPiece or image
      → applicable gates

Deployment:
  load → run(dynamic input) → observe
```

`emit_chain` is the *staged expression of the same emission*, not a request to implement an extra compiler. `seed.emit` is a comparison point/bootstrap route. Python remains host plumbing/staging where needed; do not claim Python has disappeared merely because the residual native program has no parser or reducer.

The emitted artifact need not carry a large new metadata format. Begin with a minimal record of the already-existing inputs and checks: dialect/map identity, `O`, `R`, selected host/target, artifact identity, construction seam result, and the exact witness cases and observations. Only add persistence, cache keys, remote builds, or attestations if an actual consumer needs them. A hash records declared inputs and bytes; it is not a semantic theorem. Performance observations additionally depend on machine, runtime, workload, and measurement protocol, so do not cache them as an intrinsic property of the operation.

## 5. Jones optimality and cost

The system can erase an interpretation layer without solving global optimization. **Jones-optimality is a further cost statement**, not a synonym for correct staging, byte-exact emission, or absence of a reducer in the native image. It needs a directly comparable baseline, a cost model, and a scope of programs/inputs. For example:

```text
Cost_C(residual_D,p(x)) <= Cost_C(direct_D,p(x))
```

Only assert this where both sides have defined comparable costs and the inequality is established. The currently described Identity/Mix-Subst strategy does not by itself establish general Jones-optimality or a complete polyvariant binding-time analysis.

Likewise, a declared machine model (latency, procedures, legality, capabilities) does not make choice of a realization exact. Either state a finite candidate set and a cost function, then prove optimality within **that set**, or call the selection a strategy. Keep `NotRealized` when a declared target lacks an implementation. Do not introduce a silent fallback, a special flag, or a second semantic path to make a target appear supported.

## 6. Existing host and the real gap

As recorded in the host-architecture snapshot (tip `99dc32d`): the catalog/`Realization`, dialect maps under `O`, CoGen/HostPieces, native PE and multi-ISA ELF/object output, C and fasmg witnesses, staged `emit_chain`, and `congruence`/`cross_verify` are already present in some form. Do **not** reimplement them because a conceptual diagram suggests another layer. Check the live tree before changing any code; this snapshot may be stale.

The open CUDA claim has two distinct parts:

1. **Behavioral:** compare the packed-IR CUDA execution and `graph.lo` under the *same declared `O`*, inputs, termination/fuel regime, and workload. A passing finite gate is test evidence for those cases.
2. **Tempo:** if claiming improvement, measure the same useful work and report kernel time and end-to-end time, including transfers and setup as applicable. Detect missing work and graph fallback. A GPU semantics witness is not automatically a production GPU HostPiece, and a fast kernel-only number is not an end-to-end speedup.

Do not use QEMU wall time as a native performance claim. Do not force CUDA into the QuotientMap axis: it is a host/witness realization.

## 7. Local-agent execution order

1. **Inventory before design.** Read the live `isar-proofs` implementation around `host/toolchain.json`, `observation_regime.py`, `quotient_map.py`, dialect modules, `strategy.py`, `cogen.py`, `emit_chain.py`, `host_pieces.py`, `congruence.py`, `cross_verify.py`, `seed/seed.py`, and CUDA entry points. Record which conceptual edges already have executable witnesses and which exist only as Lean statements or declarations. Report discrepancies with the snapshot.
2. **Write one precise commuting claim.** Pick an already-supported operation, dialect, `O`, and host pair. Record the actual input domain, observed fields, error/fuel behavior, and exact gate used. If the current model cannot state one consistent claim, stop and correct the model; do not invent an adapter.
3. **Trace static versus dynamic work.** For that case, identify what specialization consumes and what the emitted HostPiece still does at runtime. Confirm `load → run` for the residual native case without claiming universal interpreter elimination.
4. **Check the staged construction seam.** Locate the existing `emit_chain` versus `seed.emit` comparison, its domain and bytes compared. Preserve the *same chain*; repair a violated invariant at its source rather than adding a second implementation or normalizing away mismatches.
5. **Only then close one missing edge.** Prioritize a demonstrable CUDA/`graph.lo` workload-and-timing seam if it is actually executable on the local machine; otherwise report the concrete blocker and choose a smaller supported target. Do not claim performance from a simulator, stub, or graph wrapper.
6. **Report evidence with scope.** Distinguish proved Lean proposition, deterministic construction equality, passing finite cross-witness tests, and measured performance. State `NotRealized` for everything else.

## Acceptance criterion

For one supported end-to-end instance, the local agent can show:

- the operation and its observation regime are explicit;
- the selected realization is declared and legal for that host;
- the residual artifact runs on genuinely dynamic input;
- the existing applicable construction and observation gates pass;
- no new parallel semantic route or hidden fallback was introduced;
- any speed claim has a comparable baseline and complete timing boundaries.

The final system may later acquire Nix-like caching and provenance, Jones-style cost theorems, or more realization families. Those are consequences of clear contracts, **not prerequisites to invent before the current seam works**.

**One-line target:** A deployed artifact is a residual host realization of a specified operation, with explicitly scoped evidence that it preserves the designated observations. Construction provenance and performance are separate claims.
