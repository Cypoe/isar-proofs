---
type: frag
id: 0066
provenance: devin-cli
ts: 2026-11-19
tags: [isar, interaction-net, interaction-combinators, lambda-calculus,
       lafont, lamping, sharing, translation-validation, kernel-carrier,
       invariant-layer]
---

# 0066 — λ over the interaction combinators; splice-resolve replaces
`livePeer`; `check` preservation is a corollary, not a discipline

## What landed

Two halves of one change in `src/ISAR/`, plus an abstraction-layer
correction that fell out of them.

**`LambdaNet.lean`** — λ-calculus over the *interaction combinators
in the abstract*, not a bespoke λ-labeled net system. Three agent
shapes — `γ` (constructor, arity 2), `δ` (duplicator, arity 2),
`ε` (eraser, arity 0) — under the **universal `γδε` rule table**.
No λ-specific labels: `λ` and `@` are **both γ**, told apart only
by which port faces the consumer (Taelin's reading of Asperti:
interaction combinators = λ + superposition). `λ`'s port 0 is the
principal facing the application's fun-seeker; `@`'s port 0 *is* the
fun-seeker — so a β-redex is a γ⋈γ principal pair and **β is
annihilation**, the same index-wise splice that deletes any γγ
pair. The `lamRules` table from the first pass is gone; the
universal table runs everything.

Shared variables fan out through right-linear δ-trees on the
binder's var-port; unused binders get ε; **free variables are
interface binders** — each distinct free var gets a free port and
its own δ-tree to its use-sites, so sharing at the boundary is net
data like any other (the earlier draft wired one free port to
multiple uses — `check`-invalid, now structurally impossible).

**Readback — the degenerate classifier.** `readback` inverts the
encoding *on the fragment where it inverts*: at a term slot it
inspects the facing end's port (`γ.0` = λ-root, `γ.1` = @-root,
`λ.2`/`δ.aux` = a variable leaf through the stack of binder
leaf-sets and free-port leaf-sets). A δ or ε **principal** facing a
term slot is a *superposition* — a well-formed net with no
λ-denotation — and readback refuses it. `readback.isSome` is
literally the classification "degenerate": the subset of net-space
where Lamping's abstract algorithm is defined. A bare δ with its
principal at the root interface is the canonical honest test
(`supNet`): the aux ports alone are just shared free vars, the
principal at a term slot is not.

**Observation through the Invariant Layer.** `lambdaObs` composes
`nfBounded → readback → compileISK → ⟦·⟧`, so a net's observation
is a class in the *same* `Quotient operEqSetoid` that observes ISK
terms — cross-carrier `sim` is literal. `LObs` is four-valued:
`.nf` a layer class, `.superposed` a non-degenerate nf (each its
own class — no semantic quotient claimed), `.divergent`,
`.refused`. `compileISK` is a pure S/K/I bracket abstraction
(`LambdaFragment.compile` optimizes with `comp`, which leaves the
`ISKTerm` fragment); free vars inject as the closed family
`varEnc` — distinct normal forms, an honest injection. `DegNFNet`
(nets already normal *and* degenerate) carries `degMap`, a
`QuotientMap` into the ISK substrate whose `preserves` holds by
construction there; extending past the nf subtype *is* the
simulation theorem and is deliberately not asserted.

**Engine redesign** (`InteractionNet.lean`) — `livePeer`'s
"refuse ends that die with the pair" was correct for the γδε
fragment but wrong for λ encodings: `(λx.x) y` compiles an
internal body-variable wire (`λ.1 ↔ λ.2`) that dies with the
pair and must *collapse*, not refuse. The step engine is now a
splice plan (`SplicePlan`: aux-port substitution + fresh agents
+ construction wires) plus `resolveEnd`, which chases dead ends
transitively through the substitution until it lands on a live
end or a principal (the pair's own edge — dropped). Real
dead-end cycles exhaust fuel and refuse. `rewire` maps every
surviving wire through the resolve and dedupes mirror images.

## Preservation as corollary

`netStep` is now two functions: `netStepRaw` produces a
candidate; `netStep` adopts it only if `n'.check = true` —
translation validation, verify the transform not the
transformer. The theorem

    netStep rt n = some (some n') → n'.check = true

is then a one-split corollary (`netStep_checked`). Wiring
coherence no longer depends on construction discipline; any
future plan constructor is checked at the boundary by the same
guard.

## Mechanical evidence (all `example`/`decide`-checked in-file)

| input | observation |
|---|---|
| `(λx.x) y` | `.nf ⟦var 0⟧` — and *literally equal* to the observation of bare `y`: same `InvariantLayer` class, cross-carrier observational equivalence evaluated |
| `(λx.λy.x) z` | readback `λy.·` — K-shape with ε on the unused slot |
| `(λx.x x) y` | readback `x x` — the δ sits on the *shared* argument edge, one occurrence feeding both use sites — optimal sharing made visible |
| `(λx.x)(λx.x)` | readback `λx.x` — closed round-trip |
| `x` alone | `nf` — interface wire only, no agents |
| bare δ principal at root (`supNet`) | `.superposed` — readback refuses; non-degenerate, honestly named |
| γδ commute | `nf` — the textbook 4-copy bipartite grid |
| `loopNet` | `.divergent` — a real feedback loop that grows fresh agents, no longer a refusal |
| γδε @ fuel 0 | `.divergent` — the ⊥ class |

## Trade-offs / refusals

- `resolveEnd`'s chase is fuel-bounded by `dead.length + 1`; a
  genuine dead-cycle (agents whose ports wire only into the
  dying pair, unreachable from any live end) refuses rather than
  looping — the honest answer, since such a component is
  untethered either way.
- `check` is per-step revalidation — O(net) per rewrite. The
  honest price of validation over verification at this stage;
  an inductive invariant proof is the upgrade path if the
  carrier stabilizes.
- `degMap` is only honest on the `DegNFNet` subtype — past
  normal-and-degenerate nets, the encode/decode round trip is
  the readback-correctness simulation theorem, deliberately not
  asserted. `.superposed` keeps non-degenerate nfs as their own
  observations rather than manufacturing a quotient we can't
  justify.
- `lambdaObs`'s `.nf` reads the root branch's *term shape* —
  for nets with a non-trivial interface environment (e.g. the
  γδ grid) the observation is the root projection's class, not
  a claim about the whole net's semantics.
