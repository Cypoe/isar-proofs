---
type: decision
id: 0007
provenance: host/phi_rel.py; host/rel_schema.py; host/rel_eval.py;
  host/rel_witness.py; host/specs/schema-rel.json;
  isa-physics patent/phi-lang/*.phi; megaplan 10a/10b/10c
ts: 2026-10-08
tags: [phi.rel, parser, schema, admissible-construction, evaluator, substrate]
---
# phi.rel parses, is checked admissible, and runs on a relational substrate

Three files landed in one wave because they are one contract split
into stages — declaration → admissible construction → runtime:

- `host/phi_rel.py` — surface bytes → `phi.rel/1` rel-graph. Grammar is
  the patent `.phi` verbatim: `name : <in> <-> <out> shape? where {
  | guard { goals } }`, plus `when`, `fresh`, calls `rel<a> = out`,
  `ATOM(n, v)`/`PAIR`/`[]` literals, `RUN`/`CHOICE`/builtins, `T[n]`/
  `T[*]` type slots, `x.f` projections, `n±k` atom deltas. The graph
  persists as a `.plex` bundle (REALIZATION `dialect=phi.rel/1` +
  BYTES blob) — a storable artifact, same discipline as emit.plex.
- `host/rel_schema.py` — the phantom stage. `check(graph)` admits or
  refuses, naming the invariant: direction vocabulary, single-term out,
  arity, builtin registry, declared/bound grounding (binding positions
  introduce; consuming positions require grounding), `->`/`<=>` call
  sites need bound args, guards see sig vars only, directed rels must
  bind their out, **recursive rels must declare
  `shape ∈ {self, pairwise, step, reduce}`** — never inferred.
- `host/rel_eval.py` — the miniKanren substrate the patent bootstraps
  describe: substitution + walk + unify over `atom`/`pair` terms,
  per-clause fresh renaming, clause disjunction as guarded union,
  `RUN(g, n)` bounded take — `n=1` committed read, `n=0` stream.
  Fuel is declared data: exhaustion is an empty stream, never a hang.

## What the evidence says

`python host/rel_eval.py`: `append` forward yields the one solution,
backward `append<xs,ys> = [1,2]` yields the three splits — `RUN(3)`
commits at the count; `run*` would diverge searching for a fourth
(honest divergence, the quotient is the fix, not the search).
`add<2,3> = 5` and `fib<5> = 5` evaluate through relational
succ/pred chains — no Church-numeral shortcut in the corpus.

`python host/rel_schema.py`: the 12-rel corpus admits; the merged
patent corpus **refuses as-is** — `nibble_half_add` is called but
never defined in the patent sketch. That refusal is the point: the
patent files are reference syntax, not admissible construction; our
corpus is the admissible core with complete call edges.

## Bugs this wave surfaced, all in my machinery

- **`ren` scope** — surface-name→fresh-var map must live for the whole
  clause, not per goal; otherwise `cons<h,t> = xs` and
  `append<t,ys> = r` bind different `t`s. First draft had it per-goal.
- **fresh counter reset** — `_reset_fresh` inside `run_*` invalidated
  vars allocated before the call; fresh ids collided with the query's
  own vars and unification corrupted into a depth-first dive.
- **`atom_lazy` carried the node, not the var** — resolving a lazy
  `ATOM(8, n-1)` needed `ren` at unify time, which `unify` doesn't
  have. Now the lazy tuple embeds the var itself
  (`("atom_lazy", ("const",8), ("delta", var, -1))`) — self-contained,
  resolved by `_force` under any substitution, inside `unify`/`reify`.
- **bare goals were clauses** — `call`'s patent body
  (`env_lookup; MATCH; APPLY`) is ONE conjunctive clause; the parser
  split each line into an alternative. `|`/`when`/`fresh` open
  clauses; a run of bare goals accumulates into one.
- **`n-1` ate the minus** — `-` was in the ident continuation class,
  so `var_delta` saw `"n-1"` with delta 0. Only comments use hyphens;
  `-` is punct now and the delta idiom lexes `n` + `-1`.
- **grounding vs `x.f` projections** — `def.pat` is a field access on
  bound `def`, not a fresh var. Declared/bound comparisons run on
  var *roots*.

## The basis-term slice — `rel_witness.py`

The plan's heavy item was a full miniKanren in basis terms; the slice
that proves the claim (rel ops as *derived* term constructions, not a
privileged host) is UNIFY computed by the reducer the emitted kernel
actually runs: `bracket(parse(λ-src)) → Graph.import_tree →
reduce_cd → export`. Four computations:

- `PAIR(VAR1,ATOM2)` vs `PAIR(ATOM3,VAR4)` → `VAR1 := ATOM3` (264 cd
  rounds)
- `ATOM5` vs `ATOM7` → the declared FAIL marker (134)
- nested pair-of-pairs → `VAR2 := ATOM4` (326)
- `VAR1` vs `PAIR(VAR1,ATOM2)` → binds the pair — **no occurs check**;
  declared bound, not a hidden divergence

Encoding: `VAR k|ATOM n|PAIR l r` as Scott data, subst as a Scott
list of `(k . t)` pairs — substitution is data, same as the patent's
`MATCH = subst`. `unify` is depth-unfolded (`U_i` binds `U_{i-1}`
once per level via `\self`, linear source); the unfold depth IS the
fuel — no Y, no magic recursion, exhaustion is a `no` result not a
hang.

Two traps the slice had to clear: `reduce.py`'s `step`/`cd` implement
IStep exactly — I/K/B/S only, no Dβ/Cβ — so `bracket()` output (which
contains D and C) stalls after ~50 steps at the first D-headed redex.
The witness must run `graph_runtime.reduce_tree_cd`, where D/C are
real. And `reduce` is spine-lazy at partial applications — results
are compared as exported NF trees, not step counts.

Scope is deliberately bounded: var/atom/pair, single-threaded unify,
bounded depth. What it is NOT: interleaved streams, `RUN`/CHOICE,
occurs check, or the emitted leg — `phi.rel` stays `status: declared`
until a seed-side leg exists. It IS evidence that the relational
vocabulary lands on the same basis as everything else rather than
needing a second machine.

## Where this sits

The evaluator is the **Python witness** — the semantics spelled out
on the same term model the substrate uses, independent of the
bracket/SKI reducer (which remains an egress view, not the kernel).
`rel_witness` is the **basis witness** — bounded unify computed by
the kernel's own cd fixpoint. The `step|reduce` lowerings stay
declared-not-realized; `schema-rel.json` is `status: declared` until
the emitted leg exists. The patent `.phi` files parse verbatim
(28 rels) — surface fidelity without importing the sketch's
incomplete edges.

Refusals live where the contract says: parser refuses malformed form,
schema refuses inadmissible construction, evaluator refuses unknown
rels/builtins and honors fuel. Nothing silently falls back.
