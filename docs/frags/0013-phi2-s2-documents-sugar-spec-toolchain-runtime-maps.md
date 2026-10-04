---
type: feature
id: 0013
provenance: session
ts: 2026-01-05
tags: [phi2, s2, corpus, sugar, toolchain, runtime, maps]
---

# phi2 S2: the document layer + surface sugar + first real map

S2 closes the corpus spine.  The flat shape now exists:

    kernel eval specialize realize cogen comp runtime toolchain
    std/ (6 bundles)  maps/assemble_rules_x86

## Sugar (surface only)

`'tag(a, b, ...) = PAIR('tag, a-PAIR-b-...)` right-nested;
`[h|t]` is open-tail cons; pairs render as `'tag(...)` /
`[...]` / `[car|cdr]` by shape.  Canonical graphs keep raw
PAIR/ATOM — eval/realize/cogen `.phi` rewritten in sugar
regenerate **byte-identical** `.plex`, the strongest possible
check that the sugar is presentational.  Motivation: every bug
this stretch was a hand-encoded term slipping (raw ATOM where an
enc node belonged); `'nvar('x)` is harder to write wrong than
`PAIR('nvar, 'x)`.

## `;; uses:` — declared dep closure

Each `.phi` declares its cross-bundle rel deps; `--set` merges
the transitive closure (a dep's own `uses` followed) for schema
checking, and the canonical graph records the list.  Render
emits `;; uses:` back so round-trips don't strip declarations.
Donor std bundles carry no `uses` (captured pre-uses) — the
consumer declares the full closure.

## The documents

- `toolchain` — catalog rows as data: `'regime`, `'target`,
  `'map` rows; `map_of`/`target_of` scan via `member`.  File
  refs are `'file('maps, 'name)` nodes (syms can't hold `/`).
- `comp` — the compiler's own spec: `'spec('src('kernel_corpus),
  [assemble,link,pack], 'qmaps('toolchain), 'sym('operEq),
  'ctx('win64_x86_64_pe))`.  `cogen<comp_spec>` refuses honestly
  today — `qmaps` is a deferred ref until a loader binds bundles.
- `runtime` — `Load → bind → Run`: `'img(env, entry)` + caps
  alist; `'loader` cap absent → `'graph` baseline (declared,
  not a silent default); `bind` prepends caps onto the program
  env (self-contained cons-fold — the donor `append` drags a
  `cons` dep); fasm/cpu/simd loaders refuse.
- `maps/assemble_rules_x86` — first real quotient map: op-terms
  → x86-64 bytes.  Encoding rows are clause-shaped data; arity
  is enforced in the pattern (`mov_ri` wants exactly 8 LE imm
  bytes).  Refusals: r8-r15 (REX.B axis), scalar immediates,
  unknown ops — all empty-stream.

## Real bug found via the exclusivity discipline

`subst_env`'s generic tagged-node clause also fired on
pair-headed cons-spines — `s` unified with the pair itself,
`tag_known` absent, yielding a second **unsubstituted**
residual.  `is_pair` guard added; subst_env is a function
again (verified: 1 solution where 2 streamed before).

## Verified

```
seed selftest: ... docs [catalog+spec+runtime+map, refusals hold]: pass
seed gate: 15 congruence checks vs oracle — pass
```

`reduce.plex` (stepper-as-corpus) remains — the deep
meta-circular target, closer to H0 than to S2's fold.
