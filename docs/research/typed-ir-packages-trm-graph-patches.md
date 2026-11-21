# Typed IR-node packages + TRM-style graph-patch agent loops (vision note)

Captured 2025 — long-horizon architecture for what the toolchain catalog /
spec layer wants to become.  Not a current decision; informs why the
term-level work keeps data structured (pairs, assoc graphs) rather than
flattening to JSON-shaped strings.

## The shape

JSON is an AST; XML is an interoperable subset of SGML.  Neither is the
load-bearing layer we want.  What we want is closer to **typed IR nodes
as packages**:

```
Package = signed / content-addressed Merkle DAG
Root manifest
 ├── typed immutable resources
 ├── declarative composition rules
 ├── schema/semantic-profile imports
 ├── executable modules (if needed)          — e.g. .wasm reference impl
 ├── conformance tests / expected outputs
 └── capability and reproducibility declarations
```

Interfaces carry real typing + effects, WIT-flavoured:

```
effect: Host.ZigProc(popcount@sha256:...)
requires: Capability[HostIntrinsic]
target: zig-0.15 / x86_64 / ...
fallback: portable-koru-implementation
```

Judgment shape: `Γ; E ⊢ e : τ` — an effect row `E`, not just a type.

Key correctness point: JSON Schema constrains `x ∈ L(schema)` but never
establishes `Correct(x, world, intent)`.  A serious system must never
`eval(model_output)` — validation is by deterministic checkers over the
typed graph, not by running generated text.

Stack: WIT-like typed interfaces + content-addressed package resolution
+ capability/effect declarations + declarative pre/postconditions +
deterministic validators + optional WASM reference semantics +
trace/provenance model + explicit host adapters for real-world effects.
World interaction = `portable semantics + host-provided capability
adapter`.

## The agent-loop consequence (TRM-shaped)

With latent-refinement recurrence `z_{t+1}=f_θ(x,y_t,z_t)`,
`y_{t+1}=g_θ(x,y_t,z_{t+1})`, an agent loop only iterates:

```
inspect local modules
 → find compatible module?
 → verify interface + semantics hash
 → construct binding patch
 → run linker
 → inspect new residual state
 → repeat
```

No schemas in the loop at all — only a serialized internal state:

```
typed goal + current graph/AST fragment + valid local moves
+ checker diagnostics + evaluator output
+ compact history / latent recurrence state
```

Canonical typed state after parsing+resolution:

```
ArtifactState =
  ResourceDAG
  × TypedSemanticBindings
  × CapabilityEnvironment
  × ResidualGoals
  × InvariantSet
  × Diagnostics
  × ProvenanceTrace
```

Example normalized graph:

```
N1 = import(urn:fabian:geom:mesh@1)
N2 = module(hash=sha256:...)
N3 = capability(LocalArtifactRead)
N4 = link-error(interface-hash-mismatch)

N1 ─requires─> interface-hash A
N2 ─provides─> interface-hash B
N3 ─permits─>  inspect(N2)
N4 ─blocks─>   resolve(N1)
```

Source syntax is then just a view / editing surface.  The loop
manipulates **semantic graph patches**, each declarative, replayable,
serializable, independently verified before becoming the next state:

```
BindModule  AddVerifiedEdge  ReplacePureSubgraph  DischargeObligation
SplitGoal   IntroduceFixpoint  SelectFallback  ReturnBlocked
```

## Why it matters here

- The `resolve → program → assemble → pack` chain at term level is the
  proto-instance: catalog = declarative resources; the sparse→dense seam
  (decision 024) is the same "structured graph → projected view" split.
- Keeping term-level observables structured (field lists, (tag,name)
  pairs, assoc maps) instead of flattened strings is the down-payment on
  this model — the patch/checker layer wants typed edges, not text.
- `!` NotRealized shadows ≈ `ReturnBlocked` diagnostics, already.
