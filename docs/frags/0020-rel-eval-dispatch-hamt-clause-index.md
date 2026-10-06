---
type: frag
id: 0020
provenance: phi2/seed.py + plexus/crates/plex-core/src/rel.rs
ts: 2025-01-01
tags: [cogen, emit-chain, rel-eval, perf, dispatch, clause-index, hamt, clause-compile]
---

# 0020 — rel-eval dispatch: HAMT subst + clause index + clause-template compile

## What landed

Three evaluation-side changes (declared relations untouched):

1. **`phi2/seed.py` subst: 2-way Patricia → 64-way HAMT.** The
   `_PMap` persistent map (from the earlier O(n²) fix) still spent
   ~16 trie levels per insert — 7.35M `_tset` calls / 2.14M `_tget`
   for a 60-item assemble. 64-way fanout (6-bit levels) drops depth
   to ~3-4 for sequential var ids. Same persistent semantics — held
   substs stay correct under backtracking.

2. **Head-literal clause index, both engines.** A rel whose clauses
   discriminate on `invar = literal` unifies (guard or body) gets a
   key→clause-ids map: the (argpos, spine-path) with the most
   distinct sym/atom keys wins. Keyless clauses stay in `rest` and
   are always tried; an arg that resolves to a var/lazy/non-leaf at
   the discriminating path falls back to the full scan. Semantics
   preserved: a skipped clause's literal-unify would have failed
   anyway, and candidate order is source order.

   On the generated x86 map this yields `enc2`/`enc2_len` dispatch
   on the form sym (45 keys, path `(1,0)` — `'op('f,…)`'s second
   element), `regc`/`rfx`/`rnx1`/`symtab` keyed on the reg sym,
   `rflo`/`lon4`/`hin4` atom-keyed. `assemble2`/`mem_f`/`nibble_*`
   correctly get no index (no discriminating literals).

   This is the relational-eval analogue of `cd`'s structural
   dispatch — the term's shape picks the rule directly instead of
   scanning all clauses. Semantically orthogonal to
   ParStep/cd/confluence: those license *schedule* freedom; this
   lowers the per-step *dispatch* cost.

3. **Clause-template compile, both engines.** Each clause compiles
   once (lazy, cached) into programs: ground subtrees pre-interned
   to arena consts at compile time, vars become slot indices into a
   per-activation slot array, goal dicts become typed goal ops
   (unify/cmp/emit/call). Per activation: one slot allocation +
   `cp` runs — no JSON-node dispatch, no `ren` name lookups, no
   re-interning of literals. Rare goal kinds (run/choice/builtin/
   nested fresh — unreachable via `enc_env` anyway) stay raw and
   see a lazily-materialized name→tid `ren`.

   Correctness detail: `fresh` vars shadow same-named pattern vars
   — compiled as unconditional new slots AFTER pins/pout compile,
   matching the post-unify `ren[n]=fresh()` rebind ordering.

4. **Subst: `im::HashMap` → `im::Vector` trie (rel.rs).**
   `VarId::N` keys are dense sequential u64s (the `fresh_i`
   counter), so a persistent vector trie indexed on the id bits
   directly — no hash, no probe — beats hashing into a 32-way
   HAMT: ~2-3 array derefs per lookup. `VarId::S` (named corpus
   vars, rare) keeps a small `im::HashMap` side map. This was the
   actual wall: 78M walks per assemble at ~400ns hashed vs ~40ns
   indexed. (Python's `_PMap` was already a direct-indexed HAMT —
   this brings rel.rs to the same discipline.)

5. **Det-clause fast path (rel.rs).** A clause whose goals are all
   unify/cmp/emit yields ≤1 solution — evaluated inline (slots +
   `cp` + goal loop, early-exit), no stream tree, same fuel
   accounting. ~87% of full-src relcalls are det-eligible
   (`head`/`tail`/`nadd_*`/`nibble_*`/`bor`/`regc` tables).
   Measured effect was small (~1%) — stream boxing was never the
   wall; kept anyway since the structure is strictly simpler and
   the path is now the common case.

## Measured

- Python witness, full-src assemble (568 items): **450.8s → 176.2s
  (2.6× cumulative)**, 2053B still **byte-identical** to
  `isa_x86_64.assemble`. `lift` dropped out of the top-15 profile.
- rel.rs, same full-src probes: **pass1 13.7s → 2.78s, assemble
  60.6s → 12.06s (~5× cumulative)**, byte-identical. The vector
   trie alone took assemble 43.7s → 12.06s — the last big
  constant was subst lookup, not activation or dispatch.
- interpreter² probes on rel.rs: `cogen spec-full` 299→126ms,
  `apply<map,src>` 270→146ms, `rfold` 297→139ms (~2.1-2.4×
  cumulative from the three levers).

## Correctness

- All 43 `_rel_probes.json` probes produce identical sols/errors on
  both engines (refusal catalog intact).
- `battery --tier fast`: 31/31.
- Note: truncated-program prefixes legitimately return 0 sols on
  forward `'l` refs (pass1 `labs` lacks labels defined later) —
  not a regression; assemble requires the whole item list.

## What remains the wall

After the vector-trie subst the residual is structural, not
mechanical: 78M walks / 18M mk / 4.9M unify for 505 insns is the
work the corpus's declared algorithms *do* — nibble-adder chains
(`nadd_b` 110K calls), list head/tail destructuring (~200K),
byte-splice `append`s — ~1140 relcalls per insn. Cutting that is
a corpus-level decision (batch primitives — e.g. a declared
byte-add op instead of nibble chains — change the relation
corpus, not the evaluator). The evaluator itself is now within
~2-3× of its irreducible per-op cost.

The fat-env interpreter² rt probes remain beyond budget on
rel.rs — not for speed now but for SPACE: the arena is monotonic
(no GC port) and the workload allocates ~4.7 nodes/fuel-unit,
growing over time — >100GB committed before kill. The Python
witness covers that leg via its persist-aware GC (frag 0016);
the rt probes are witnessed by direct mapg2 assemble on both
sides. Porting the GC to rel.rs is the honest fix if genuinely
unbounded Rust eval is ever required.
