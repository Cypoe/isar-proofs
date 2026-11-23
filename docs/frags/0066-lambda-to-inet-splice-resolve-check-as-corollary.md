---
type: frag
id: 0066
provenance: devin-cli
ts: 2026-11-19
tags: [isar, interaction-net, lambda-calculus, lafont, sharing,
       translation-validation, kernel-carrier]
---

# 0066 — λ→inet compilation lands; splice-resolve replaces `livePeer`;
`check` preservation is a corollary, not a discipline

## What landed

Two halves of one change, in `src/ISAR/`:

**`LambdaNet.lean`** — the standard interaction-net encoding of
the λ-calculus, compiling `LambdaFragment.LTerm` (the same de
Bruijn syntax bracket abstraction feeds to ISK — one source
language, two carriers). `λ` is an arity-2 agent whose
*principal* faces the application's fun-seeker; `@`'s principal
*is* the fun-seeker, so a β-redex is a principal-principal pair
and β-reduction is **annihilation** — the same index-wise splice
that deletes γγ pairs. Repeated variable uses fan out through a
γ-dup tree on the binder's var-port; unused binders get an ε;
free variables become interface ports. `lamRules` is declared
data: ε erases, γγ and λ⋈@ annihilate, γ commutes against
anything else (lazy copying — the duplicator only descends when
it meets a constructor), unhandled pairs refuse via
`RuleTable.action`'s new `Option` return.

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

## Mechanical evidence (all `#eval`uated in-file)

| input | observation |
|---|---|
| `(λx.x) y` | `nf` — collapses to the bare wire `y ↔ root` |
| `(λx.λy.x) z` | `nf` — `λy.z`: λ agent, ε on y's var-port |
| `(λx.x x) y` | `nf` — a γ sits on the *shared* argument edge, one occurrence feeding both use sites — optimal sharing made visible |
| `x` alone | `nf` — interface only, no agents |
| γδ commute | `nf` — the textbook 4-copy bipartite grid |
| `loopNet` | `divergent` — a real feedback loop that grows fresh agents, no longer a refusal |
| γδε @ fuel 0 | `divergent` — the ⊥ class |

## Trade-offs / refusals

- `resolveEnd`'s chase is fuel-bounded by `dead.length + 1`; a
  genuine dead-cycle (agents whose ports wire only into the
  dying pair, unreachable from any live end) refuses rather than
  looping — the honest answer, since such a component is
  untethered either way.
- Dropping a wire on principal-hit is unreachable in a checked
  net (the principals' only wire is the pair's own edge); the
  post-validation `check` would catch any plan that produced it.
- `check` is per-step revalidation — O(net) per rewrite. The
  honest price of validation over verification at this stage;
  an inductive invariant proof is the upgrade path if the
  carrier stabilizes.
