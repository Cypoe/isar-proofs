# 062 — rel-eval dispatch: HAMT subst + clause index + clause-template compile

## Context

After 061's generated x86 map proved byte-identical on both
engines, the residual per-item cost broke down as:

- Python: subst ops dominated (64% — `_tset`/`_tget` on a 2-way
  Patricia trie at ~16 levels/insert for sequential var ids),
  clause scans second (~70 failed trials per `enc2_len` call).
- Rust (rel.rs): neither — `im::HashMap` subst already persistent,
  per-clause-trial ~µs. Its time is per-activation machinery
  (`lift`/`Ren` churn per clause trial).

## Decision

Three evaluation-only optimizations, declared relations unchanged:

1. **Subst: 64-way HAMT** (`phi2/seed.py::_PMap`). 6-bit fanout;
   depth ~3-4 vs ~16. Persistent semantics retained — the same
   discipline as rel.rs's `im::HashMap`, matching the engines.
2. **Head-literal clause index** (both engines). Per rel, the
   (argpos, spine-path) with the most distinct sym/atom keys in
   `invar = literal` unifies becomes the dispatch table.
   Correctness invariants:
   - keyless clauses are always candidates (`rest`);
   - unresolvable args (var/lazy/non-pair mid-path) → full scan;
   - candidate order = source order.
   Skipping is sound: a clause whose key differs must fail its
   literal-unify to yield.
3. **Clause-template compile** (both engines, lazy `cl["cx"]` /
   `ccx` cache). Clause terms/goals compile once to programs:
   ground subtrees pre-interned to arena consts, vars → slot
   indices, goals → typed ops (unify/cmp/emit/call). Activation =
   one slot array + `cp` runs. Raw fallback for
   run/choice/builtin/nested-fresh goals (unreachable via
   `enc_env` anyway) via lazy name→tid `ren`.
   - Correctness detail: `fresh` vars shadow pattern vars — slots
     allocated unconditionally AFTER pins/pout compile (matches
     the post-unify `ren[n]=fresh()` rebind ordering).
   - Templates are evaluator caches, NOT serialized: `enc_rel` /
     `enc_env` read explicit clause keys only; `.plex` output
     unchanged.
4. **Subst: `im::HashMap` → `im::Vector` trie (rel.rs).**
   `VarId::N` keys are dense u64s — index on the id bits directly
   (no hash/probe); `VarId::S` keeps a small side map. Measured:
   THE wall — 78M walks at ~400ns hashed vs ~40ns indexed.
5. **Det-clause fast path (rel.rs).** all-unify/cmp/emit goals →
   ≤1 sol → inline eval, no stream tree. ~87% of full-src
   relcalls eligible. Effect ~1% — stream boxing was never the
   wall; kept for structure.

## Why this shape (and not the alternatives)

- **Trail-based subst** rejected again: `run()`/`run_solutions`
  hold raw substs persistently; mutability is unsafe.
- **Index on head patterns** rejected: the generated map keeps
  discrimination in body unifies (`op = 'op('f,…)`), not `in`
  patterns — the index must read guard/body literals, matching
  where the corpus actually puts dispatch.
- **Not a semantic change**: confluence/ParStep/cd license
  schedule freedom; indexing/compiling only lower per-step cost.
  No new Lean theorem required — same judgment the user applied
  ("enough to make an informed decision").

## Measured

- Python full-src: 450.8s → 176.2s (2.6×), byte-identical.
  `lift` out of top-15 profile entirely.
- rel.rs full-src: pass1 13.7→2.78s, assemble 60.6→12.06s
  (~5× cumulative). Per-lever: index ~3%, compile ~17%,
  vector-subst 3.6× (the real wall), det-path ~1%.
- interpreter² probes (rel.rs): ~2.1-2.4× cumulative
  (cogen spec-full 299→126ms).
- 43/43 probes identical both engines; battery 31/31.

## Consequence

The evaluator is now within ~2-3× of its irreducible per-op
cost — the residual is the corpus's declared call density
(~1140 relcalls/insn: nibble chains, head/tail destructuring),
which is a corpus-level batch-primitive question, not evaluator
mechanics. Separately: rel.rs's monotonic arena (no GC) makes
genuinely unbounded evals OOM — the rt interpreter² probes hit
>100GB; Python's frag-0016 GC covers that leg. Porting the
collector to rel.rs is a separate line item if needed.

Related: frag 0020; supersedes the "_PMap Patricia" half of the
earlier subst decision (HAMT is the persistent-map realization
that survived measurement).
