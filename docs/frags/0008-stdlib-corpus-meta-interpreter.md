---
type: decision
id: 0008
provenance: host/corpus/stdlib.phi; host/rel_eval.py (meta-interpreter);
  host/phi_rel.py ('sym literal, bare-op arg boundary);
  isa-physics patent/phi-lang/{phi-lang,phi-stdlib}.phi + phi_boot.py;
  megaplan 10e
ts: 2026-10-08
tags: [phi.rel, stdlib, corpus, meta-interpreter, call, congruence]
---
# The stdlib is admissible: 27 rels, every edge bound, congruent with phi_boot

`host/corpus/stdlib.phi` is the patent `phi-lang ∪ phi-stdlib` union
made admissible — 27 relations, every call edge bound, every
recursive rel shape-declared. The schema's earlier refusal of the
patent sketch (`nibble_half_add` called-but-undefined) is now closed
by construction: the carry chain is implemented relationally.

## What had to become real for the corpus to run

The patent's `call` is `env_lookup(name) = def; MATCH(def.pat, args)
= subst; APPLY(subst, def.body) = result` — definitions as data. For
that to dispatch rather than pattern-match vacuously, the evaluator
grew a meta-interpreter on the same term model:

- **reldef field projection** — `def.pat` / `def.body` lift to vars
  aliased to root `def` (`_FIELDS`); when the root walks to a
  `("reldef", n)`, the field projects to `("pat", n)` /
  `("bodycall", n)` markers. Pending fields stay bindable vars.
- **`("pat", n)` in MATCH** — the rel's declared in-pattern lifted
  with surface var names; MATCH binds them **match-scoped** (each
  MATCH shadows — a second `call` on the same rel must re-bind, or
  `map`'s second element unifies stale `n=1` against `n=2` and
  silently fails — found by running it, not reading it).
- **`("bodycall", n)` in APPLY** — instantiate the in-pattern under
  the decoded subst and dispatch `_rel_call`: `call` is a rel call,
  honest, not an engine hook.
- **`("goalterm", name, args)`** — a `rel<args>` in term position is
  a suspended goal — goals are data. `RUN(g,n)`, `CHOICE`, and the
  `any`/`norm`/`find`/`stream` rels dispatch on goalterm values;
  `norm<append<a,b>>` works end-to-end.
- **`'name` symbol literal** — the surface's way to pass a rel name
  as a VALUE (`map<'succ, xs>`). The patent left names-as-values
  unspecified; `'n` closes it without changing bare-idents (still
  vars).
- **arg-tuple convention** — `call<f, PAIR(acc,h)>` for 2-arg f:
  right-nested pairs, no NIL tail, patent-verbatim.

## The carry chain (relational, no primitives)

`nibble_succ` = 16 facts `PAIR(next, wrap)`; `nibble_add_b` applies
successor `b` times and merges wraps through `bor` — the second
clause calls `nibble_succ` **backward** (`bp = pred b`, a declared
use of `<->` reversibility). `nibble_half_add<an,bn,cin>` =
`PAIR(sn,cn)` where `sn=(a+b+cin)&15`, `cn=(a+b+cin)>>4` — verified:
`<15,2,1>` → `PAIR(2,1)`. `nibble_add` is the patent's list carry
chain verbatim except the inline `PAIR(sn, nibble_add<..>)` — inline
calls inside terms are sequenced as goal lines (same semantics, no
term-embedding of calls; divergence documented in the corpus header).

`succ`/`pred`/`add`/`fib` stay atom-level on T[8] (the proven chain);
patent's `add` delegated to the list chain, which exists under its
patent name — different decomposition, same signature.

## Congruence witness vs phi_boot

`phi_boot.appendo` (the patent's own miniKanren) and `rel_eval` run
the same backward-append query `append<x,y> = [1,2]`:

```
phi_boot: [] [1,2] | [1] [2] | [1,2] []     (3 splits)
rel_eval: [] [1,2] | [1] [2] | [1,2] []     (3 splits)
```

Identical decompositions in identical order — observational
equivalence on the shared program, recorded in the selftest.

## Declared bounds (not bugs)

- `RUN(g,n)` with `n > solutions` diverges — honest miniKanren
  search, the quotient is the boundary.
- `contract`/`compose`/`compose_inv` are admissible constructions but
  their `APPLY(MATCH(...), x.body)` out-patterns contain op-terms —
  op-terms in out position are declared-not-evaluated (they need
  out-pattern evaluation, the next meta step).
- phi-runtime's Futamura rels (`interp`/`specialize`/`cogen`/`llvm_*`)
  are absent by design — egress layer, codegen deps unrealized.
- `phi.rel` stays `status: declared` — no emitted leg.

Challenges: `rel-corpus-admissible` (27 rels, schema-clean),
`rel-corpus-eval` (call/map/fold/half/norm outcomes), plus the
selftest's congruence section — 14/14 rel challenges, 0 drift.
