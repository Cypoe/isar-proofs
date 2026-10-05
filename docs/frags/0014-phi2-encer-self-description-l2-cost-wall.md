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
- **`eval.phi`: open-tag domain.** `walk`, `nonvar`, `unify_w`,
  `reify_w`, `inst` generalized from closed tag-enumeration to
  structural rules: `'var` is the only subst-driven leaf; every
  other enc node is a PAIR spine over leaves. Enc'd programs
  carry `'call`/`'unify`/`'def`/`'clause` node tags beyond the
  original five — per-tag clauses silently excluded them.
- **Arena stepper (`_ND`/`_GR`/`_nd`).** Terms are interned
  hash-consed ids, not copied tuples; subst is `var_id→term_id`
  redirect (`walk` pointer-chases); groundness is a
  construction-time bit so `_tab_key` costs O(1) and keys are
  ints — the id-keyed table unsoundness (Python `id()` reuse
  across gc) is gone with it. Table keys are structural
  (interned ids), producers replay lazily. Selftest + 15-check
  oracle gate green.
- **`_e(tag, *xs)` = `PAIR(sym(tag), right-nested-args)`.** All
  enc nodes are leaf-car tagged pairs; thaw prints every pair as
  `('pair',…)`, which made raw spines and `'pair`-nodes look
  alike in traces. Print discipline: tag shows as
  `('sym',tag)` only for leaf cars.

## Verified

- `enc_env(lists_member_assoc)` → enc'd `assoc<'b>` through
  corpus eval → `'atom(8,20)` — standing selftest evidence.
- `enc_env(eval.plex)` — all 25 rels enc as data, including
  `RUN`s, `cmp`s, `'adyn` in `next_id`.
- L2 machine rels verified *through their enc'd defs* under
  corpus eval (each resolved via `env_find` in the inner env,
  clause-inst'd, body-evaluated): `subst_lookup` hit/miss and
  empty-subst `'unbound`, `walk` bound/unbound, `nonvar`,
  `unify_w` var-bind, `unify_enc` var←atom (4.0s),
  `unify_args` one element (7.8s), `env_find` on `'pair`-spine
  env (instant), `inst`/`inst_list` on enc'd `'nvar` (0.5s).
- **L2 `'unify` completes end-to-end** (9.2s): enc'd eval
  pattern-matches the grammar-2 `'unify` goal, dispatches
  `'call('unify_enc')` in the inner env, and the enc'd
  `walk`/`subst_lookup`/`unify_w`/`adyn_res` chain runs to a
  real solution. The metacircular envelope is correct.

## The L2 cost wall (honest finding)

Full `'call` dispatch at L2 — enc'd eval interpreting an
inner program through `env_find` + `eval_call` → `eval_clauses`
→ `eval_clause` → `eval_body` — is mechanically consistent but
cost-bound under the Python stepper: a leaf `unify_args` alone
is ~8s through the enc'd def, and `eval_clause` nests ~5 such
sub-calls per clause probe (`inst_list`/`inst`/`unify_args`/
`unify_enc`/`eval_body`), each `unify_enc` walking env-sized
terms with per-node `subst_lookup` scans. Empty-body `k0`
exceeded 600s; 3M-fuel runs OOM-kill. Tabled calls fire (all
leaves are ground) — the wall is throughput, not divergence:
~0.6ms per corpus goal-step, and the dispatch tower multiplies
steps across two interpretation levels.

That is not a defect to paper over — it is **the argument for
H0**. Interpreting an interpreter on the Python stepper costs
what it costs; the native host that executes declared data
without meta-level inst/scan churn is exactly the next
milestone. Every link of the chain now verifies in isolation,
and the `'unify` goal completes end-to-end.

## H0 measured (the number, and the new wall)

The combinator machine landed: all 31 rels lowered to λ,
`abstract0`-bracketed onto I/K/S, unrolled `F^fuel(BOT)` as a
balanced-selector tuple (selection depth ~5, was up to 31),
reduced by `reducer_cd.exe` through `pack_ir`. Congruence vs
`run_value` is observational (decode via selector probes), never
structural.

**L1 evaluator chain — fully validated natively.** Every
`eval.phi` clause exercised, all congruent modulo rep names:

| probe | native steps | native time | Python graph |
|---|---|---|---|
| `eval 'unify` | 76,256 | 0.52s | 92.1s |
| `eval 'call` | 504,371 | 0.98s | >15min (nf) |
| `cmp-eq` / `cmp-neq` | 327k / 356k | 0.69s / 0.28s | — |
| `run` (meta take+run_res) | 181k | 0.12s | — |
| two-goal call | 1.72M | 1.04s | — |
| `reify` | 255k | 0.30s | — |

Roughly 100–180× vs the Python graph witness, and `'call`
dispatch completes sub-second where the graph runtime could not
finish at all.

**L2 through the machine — OOM-class, measured not mysterious.**
Direct enc'd calls over the self-env are congruent
(`'call('subst_lookup)` on the enc'd 25-rel env: 1.29M steps,
output identical to the oracle). But the full L2
`'call('eval,[ienv,g2,NILe,1])` — machine interpreting enc'd
eval interpreting the goal — has a sharp transition:

- `mfuel ≤ 96`: every path bottoms at BOT → empty stream, fast
  (783k steps at 96). Not a semantic miss — truncated unrolling.
- `mfuel ≥ ~128`: real derivation begins and exhausts a **32 GB**
  arena; at `mfuel=160` it exhausts **96 GB** (~4B nodes),
  `take(1)`-bounded — i.e., the prefix *to the first answer*
  alone is retention-bound. `rc=4`, never silent.

This is the documented OOM class, not divergence: the corpus
oracle reaches the answer (fuel 500k, len=1), so the derivation
is finite — a bump-arena kernel with no intra-root GC retains
the whole lazy search tree (same wall as the monolithic asm
root, `emit_chain` L1094). The Python stepper completes it only
because its GC frees dead alternatives continuously. The axis
for a single lazy search tree is not stream-staging but a
GC'd/reclaiming realization — a real work item, queued for H0's
next slice rather than papered over.

## Level discipline (recorded, easy to get wrong)

The strict hybrid law — two grammars coexisting in one run:

- **Corpus machinery** (consumed by corpus-dict patterns):
  env1 spine, corpus `'call` arglists, `def`/`clause`/`unify`/
  `call`/`nvar`/`var` node shells, `ins`/`clauses`/`goals`
  lists, subst spines — all **raw `t_pair` cells ending raw
  `NIL`**. Corpus `env_find`/`unify_args`/`inst`/`subst_lookup`
  decompose these.
- **Enc'd-domain data** (consumed by enc'd defs' `'pair`
  patterns): inner env spine AND `'pair('sym'-key, def)` cells,
  inner defs' `ins`/`clauses`/`goals` lists, L2 goal/metavar
  nodes, L2 subst spines — all **`'pair`-nodes ending the
  enc'd empty list** = `'atom(0,0)`-node (`enc_t([])` =
  `PAIR('atom', PAIR(atom(0,0), atom(0,0)))`). Passing raw
  `NIL` or a different-base `'atom` node here silently fails
  `subst_lookup`'s `lst=[]` case — the last bug found.
- **Name keys**: `'sym`-node keys at *both* levels — enc'd
  eval's clause-5 unwraps `nm='sym(x)` then `env_find`s the
  whole node; corpus `env_find` just unifies key terms, so the
  same convention works at L1.
- **Goal grammar is relative to the interpreter**: corpus eval
  consumes grammar-1 goals (raw-car `'call`/`'unify`); enc'd
  eval consumes grammar-2 goals (`'pair('sym'call',…)`). A def
  interpreted by enc'd eval carries grammar-2 goals in its
  clauses; a def *inside* that program's inner env still has
  grammar-2 everything, since only enc'd rels touch it.
- Top-level `out` slots: corpus-level `'var` nodes for
  binding/reification; `'nvar` only ever appears inside defs
  (inst renames it to `'var`); never at call sites.

## Anti-smuggling note

The enc'er lives in the seed bootstrap as a mechanical
dict→term transform — no Python semantics cross into the
enc'd programs; unsupported surface forms refuse by name.
Whether it later becomes corpus data itself (an `enc` rel
operating on parsed graph terms) is a real axis, deferred.
