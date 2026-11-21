# 066 — substitution as declared strategy: assoc list -> LSB-first bit trie

## Context

Decision 065/frag 0026's corrected measurement pair isolated the
last wall between byte-domain `assemble` and MEGAPLAN §7:
`eval.phi` threads one **assoc-list** substitution through every
nested `'call`, and `subst_lookup` scans it linearly. Host
instrumentation: +2,372 walks/op × +164 bindings/op ⇒ quadratic in
op count; the native discriminating probe (`pass1[ret]@pc=1` =
548,555,085 vs @pc=0 548,551,658) proved op-2's intrinsic work is
identical — the >1.45G marginal was pure subst depth.

The constraint: the strategy must stay **declared corpus data** —
no engine special-casing, no smuggled host map.

## Decision

Subst is a **binary trie keyed on little-endian bit-list var
ids** (`sget`/`sput`/`sput_new`, `binc` for id issue, `beq` total
structural equality). Sequential ids keep an LSB-first trie
balanced by construction (Okasaki–Gill IntMap) — no rotations
encodable relationally. Var ids changed `ATOM(8,i)` → bit lists;
`n` is now an opaque bit-list counter. Trie overwrite ≡ assoc
first-match shadowing.

`beq` is total (`'yes`/`'no`) so `unify_w` calls it directly —
the earlier `RUN(beq…)` form spawned a nested eval per var-var
unify; even so the machine mirror used `eq_term` throughout.

## Why not the alternatives

- **Scoped per-call substs**: breaks the triangular-subst
  contract (`walk` chases bindings across the whole derivation);
  reification needs the full map.
- **BST on atom ids**: monotonic ids degenerate to a list —
  same quadratic.
- **Peano-atom ids + trie**: bit extraction needs O(v) peano
  halving per level — worse than assoc for deep keys.
- **HAMT (decision 062's host trick)**: needs hash/array indexing
  not expressible as plain corpus relations; the bit trie is the
  same idea at the declared-data level.

## Outcome (native, gc=sweep)

- `pass1 [ret,ret]` 816,333,786 sols=1 (was rc=2 >1.45G);
  marginal ~410M/op constant through 8 ops — quadratic gone.
- `assemble [push;ret]` 2,701,513,499 sols=1 → bytes `55 c3`
  fasmg-MATCH; `[lab;call;ret]` `e8 fb ff ff ff c3` MATCH.
- Cost shifted to a **persist-zone** wall: the input-tier reduct
  cache below `irstart` fills on multi-op evals → `exit4`,
  invariant to `ir_arena_bytes`.
- Trie overhead ~+20% steps on small substs (`enc2_len` 483M vs
  397M) — per-bit descent wins only beyond ~100 bindings.

## Full-src outcome (2026-10-13, frag 0028)

The imm32 encoding ceiling on `persist_bytes` was widened to imm64
(`4720a08`) and the full-src run measured:

| persist | pass1 769-op |
|---|---|
| 1 GiB | rc=4 @ 277 s |
| 2.147 GiB | rc=4 @ 1841 s |
| 16 GiB | rc=4 @ 24891 s |

Instrumented (`stats_p` + `pfree=`): the zone saturates early,
rides `flhead_p` recycling, and concedes on the first collect that
frees ~nothing. Root cause: `gc_collect` marks **all input cells
as permanent roots**, so input-descended reducts pin forever —
live-persist = the cumulative derivation closure, monotone and
unbounded for a single long root. The memoization is built for
streams of small roots, not one 774-item take-1. **MEGAPLAN §7
misses** — closing it needs mark-roots = live root cells only
(retention-model change, new substrate), which the freeze forbids.

Frags: `docs/frags/0027-subst-bitlist-trie-quadratic-cleared.md`,
`docs/frags/0028-fullsrc-persist-wall-measured-miss.md`.

## Postscript 2026-10-14 — wall lifted (frag 0029, decision 067)

The retention-model change landed and was *refuted as sufficient*
by `plive` measurement; the working fix is final-root dynamic
routing: `irj == irnroots-1` reducts allocate in the dynamic arena
since no future root can read their FWDs. Single-root evals no
longer touch persist. §7 re-opens as a runtime bound (~410M
steps/op × 774 ≈ 320G steps), not a space bound.
