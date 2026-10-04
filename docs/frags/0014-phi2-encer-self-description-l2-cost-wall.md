---
type: frag
id: 0014
provenance: devin-cli
ts: 2026-02-18
tags: [phi2, enc-domain, self-description, futamura, eval, l2]
---

# 0014 — the enc'er: any .plex becomes program data; L2 verified on primitives, whole-chain cost is the H0 argument

## What landed

- **`enc_term / enc_goal / enc_rel / enc_env`** in `phi2/seed.py`
  (module level, after `load_corpus`): dict-form surface
  rel-graphs → enc'd `'def(ins, outP, clauses)` env terms. Any
  `.plex` bundle now becomes corpus-eval program data — no
  hand-built `ePair/eAtom` chains. Covers vars, wildcards
  (`_`/`wild` → fresh `_wN` 'nvars), atoms, `atom_dyn` → `'adyn`,
  pairs, unify/`=` goals, `cmp` ops (`!=`→`neq`, `==`→`eq`, others
  named-refused), `call`, `RUN` → `'run`, sig-only rels → one
  empty-goal clause. `builtin`/`emit`/`choice`/nested-`fresh`
  refuse by axis name, not silently.
- **`eval.phi`: `'adyn` added to `walk` and `nonvar`.** Real bug
  found by the enc'd `next_id` probe: `unify_enc` walks *before*
  `adyn_res`, so `'adyn` nodes died in `walk` (no clause). Now
  walk passes them through (resolution is `adyn_res`'s job) and
  `nonvar` admits them so an unresolvable dynamic can still bind
  a var. `eval.plex` regenerated, 25 rels.

## Verified

- `enc_env(lists_member_assoc)` → enc'd `assoc<'b>` through
  corpus eval → `'atom(8,20)` — standing selftest evidence.
- `enc_env(eval.plex)` — all 25 rels enc as data, including
  `RUN`s, `cmp`s, `'adyn` in `next_id`.
- L2 primitives through `'call('sym('eval'))` on the enc'd
  self-env: `next_id` → `'atom(8,2)`, `inst` renames enc'd
  `'nvar` → `'var(1)`, `env_find` resolves on `'pair'd` alists,
  `unify_w`/`unify_enc`/`walk` on re-enc'd (`enc_t`) terms.

## The L2 cost wall (honest finding)

Full `'call` dispatch at L2 — enc'd eval interpreting enc'd
`gD` — is mechanically consistent but fuel/memory-bound under
the Python stepper: every clause application `inst`s the whole
enc'd def, `eval_clauses` insts before it knows a clause will
match, and `env_find` linear-scans ~16k-node envs. 3M fuel
→ OOM-killed before exhausting.

That is not a defect to paper over — it is **the argument for
H0**. Interpreting an interpreter on a naive DFS stepper costs
what it costs; a compiled host that can afford meta-level
inst/scan churn is exactly the next milestone. The L1→L2
encoding discipline is proven uniform: `enc_t` applied to the
L1 env/goals yields the `'pair'd` L2 domain, and every
primitive of the dispatch chain verifies in isolation.

## Level discipline (recorded, easy to get wrong)

- L1 env (corpus eval's env arg): raw `PAIR(sym, 'def-node)`
  spine — corpus rels decompose it via *surface* patterns.
- L2 env/goal terms: `enc_t` of the L1 forms — every structural
  pair becomes a `'pair` node; only then do enc'd `'pair`
  patterns match. `enc_env_L2(g) == enc_t(enc_env(g))`.
- Top-level `out` slots: L1 `'var` nodes (bind + reify); inside
  defs, `'nvar`/`'var` per the enc'd program's own convention.

## Anti-smuggling note

The enc'er lives in the seed bootstrap as a mechanical
dict→term transform — no Python semantics cross into the
enc'd programs; unsupported surface forms refuse by name.
Whether it later becomes corpus data itself (an `enc` rel
operating on parsed graph terms) is a real axis, deferred.
