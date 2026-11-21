# 030 — Memory accounting: retention, not drift, is the wall

Instrumented `Graph` (host/graph_runtime.py) with an always-on `stats`
Counter (alloc sites, intern outcomes, redirect outcomes, memo hits)
plus `census()` (node/dict residency, est bytes) and `live_reachable()`
(semantically live set via resolved-child BFS). Probe: host/_mem_trace.py.

## Measured

| run | nodes | live | retained | est bytes | intern hit rate |
| --- | --- | --- | --- | --- | --- |
| PAIR zf64 zf128 (cd) | 7,987 | 301 | 25x | 2.3MB | 10.7% |
| JOIN zf64 zf128 (cd) | 3.33M | 409 | 8,146x | 1.04GB | 0.10% |
| JOIN zf128 zf256 (cd) | 13.05M | 793 | 16,460x | 4.12GB | 0.046% |
| linkOf mini (lo, 40k steps) | 2.79M | 724 | ~3,850x | 1.04GB | 5.7% |

## What the counters settled

1. **Drift is NOT the leak.** `mk_app.drifted` + `mk_app.pending` ≈
   0.05–0.2% of allocs. The earlier ~1850x allocs/unique guess blamed
   abandoned intern hits; the counters show the misses are genuine
   misses — sequential development simply never revisits a term.
2. **Dicts dominate residency**: ~86% of est bytes is `_app_intern`
   (13M entries on JOIN zf128/256) + `_step_memo` (13M entries — one
   per `redirect.ok`, seeded unconditionally in `redirect()`).
   Node lists are only ~10%.
3. **Retention is monotonic**: `forwarded` ≈ `redirect.ok` — every
   intermediate state stays resident forever. Live set is ~400–800
   nodes out of millions.
4. `cd.memo_hit` ~13M on 6,711 rounds — each round re-walks the whole
   resident cone and memo-hits (~1.9k hits/round ≈ allocs/round).

## Fix directions (ranked by honesty/cost)

- **Per-round arena compaction — IMPLEMENTED, verified.**
  `Graph.compact(root)` rebuilds the arena from the reachable set +
  permanent atoms: re-indexes, rebuilds `_app_intern`/`_var_intern`/
  `_atom`/`_macro_k` on new indices (re-keying also eliminates
  drifted-hit entries — the stale-key population is rebuilt clean),
  carries `_nf`, drops memos. `reduce_cd(..., compact=True)`.
  Measured: JOIN zf64/zf128 — 3,383 rounds, NF byte-identical,
  nodes 3,332,072 -> 410, est 1.04GB -> 0.26MB, ~18% slower
  (per-round live-set BFS). zf128/zf256: 6,711 rounds — 13.05M
  nodes -> 794, ~4.1GB -> 0.37MB.
- `_step_memo` seeding is engine-conditional — DONE: `reduce_cd`
  clears `_memo_step` for the run (restored in `finally`), so
  `redirect()` skips the write.  Verified: linkOf cd run ends with
  `step_memo` empty (was ~2.7M dead entries).

## Diagnostics harness — host/diag.py

Registered engine set: tree.lo, tree.cd, graph.lo, graph.cd,
graph.cd+compact, native (subprocess — child RSS sampled via
psutil).  Per (term, engine): wall ms, peak RSS delta, cycles
(steps/rounds), allocs, nodes, reachable — plus NF congruence across
engines (surface-quoted).  Spec-term cases are kind-filtered to
graph+native (tree.lo doesn't know L0 atoms).  `--full` adds the
JOIN retention case; `--no-native` skips the exe.

Measured linkOf-mini: graph.cd+compact — 4,045 rounds, NF identical,
peak RSS 1.4MB vs 1,230.8MB un-compacted (~880x), +42% wall.
Native witness: 4.7s, 1.1GB RSS, 302k cycles, 46.1M allocs — the
exe retains the same way.
- Intern-table value on sequential workloads is near-zero (0.05%
  hit rate) yet it's the biggest structure — interning could be
  capped/evicted, but hash-cons identity is load-bearing for the
  quotient claims; compaction preserves it correctly, eviction
  doesn't.

## Frontier worklist — implemented, measured, FALSIFIED for speed

`reduce_cd(frontier=True)` develops only the residual redexes born
the previous round (collected at mk_app/_freeze via _is_redex_r)
instead of re-walking the live cone from root.  One birth path is
NOT construction-visible: a live rep `app(a,b)` built while `a` is
undeveloped goes redex-shaped when `a` later redirects to a
redex-headed form (shared child developed through another parent).
So frontier rounds interleave with full `cd(cur)` convergence walks
whenever the frontier empties — redirect-births are caught there.

Measured (NF identical everywhere — correctness holds):

| term | plain cd | frontier | f+compact |
| --- | --- | --- | --- |
| JOIN zf32/64 | 1,719r / 3.1s / 868k nodes | 3,767r / 5.2s / 1.26M nodes | 3,800r / 8.7s / 282 nodes |
| linkOf-mini | 4,045r / 26.7s / 6.78M | 14,263r / 24.7s / 5.55M | 14,644r / 77.9s / 734 |

Why it's not a win: the re-walk theory overstated the walk — cd's
per-round memo already dedups it, so walk ≈ real work in size.
Frontier pays per-entry cd-call overhead, ~30% dead entries (nodes
consumed via a different parent first), and convergence walks
(809 on linkOf — redirect-births aren't rare).  The dominant cost is
per-round contractum volume + repr/op constants, not traversal.
Kept as opt-in flag; compact remains the clear memory win.

## Eager tail-calls — implemented, correct, minor win

`reduce_cd(eager_tail=True)`: tail-call redexes = app spines whose
left chain contains an `app(g,g)` link (repr-equal children — the
self-application fold-continuation signature of FOLDL/JOIN/MAP).
Decidable in O(spine) by inspection — the spec's own principled
bound.  They're developed eagerly within the round (drain queue +
budget guard); payloads stay round-sealed.  Legal because
combinators are an orthogonal TRS — all complete developments
converge to the same NF — the seal is strategy, not correctness.

Measured: NF identical everywhere.  JOIN zf32/64: 1,719→1,584
rounds (-8%), tail.dev=2,211.  The headline number it exposed:
**626 redirects/round average** — the per-round parallelism is
already exploited massively.  The 1,584 rounds are the critical
path — a sequential residual chain inside payload computations
(arithmetic ripple, decoder walks — each contractum births the
next redex).  That's real dependency in the spec vocabulary, not
schedulable work.  Fold-level parallelism was decidable and is now
exploited; the remaining critical path needs spec-level change
(balanced adders / different encodings) — the generator-layer move.

## repr-storm fix — Python call overhead, not chain walking

Measured on JOIN zf32/64 cd: 16.48M repr calls, **99.94% immediate
hits** (`fwd[i] < 0`), 10,315 misses at 1.71 avg hops — the storm was
pure method-dispatch cost, not forwarding chains.  Fixed by inlining
the `fwd[i] < 0` fast path at the hot sites (mk_app, redirect,
_fun_arg, _is_redex_r, _is_tail_call, cd, step, _drain_tails, reduce
loops, compact/live_reachable walks; `fwd` re-bound after each
compact() since it rebuilds the lists).  Result: repr calls
9.77M -> 7.6k at this scale, ~18-20% wall off cd (JOIN 3.1s -> 2.55s,
eager 4.9s -> 4.08s).  NF congruence holds across
plain/eager/compact/frontier combos.  New profile: cd recursion
(1.74M calls), dict.get storm (5M — cd_memo/nf/app_intern),
mk_app+_alloc — interpreter floor; further wins need structural
change, not repr tuning.

## Auto-balance — investigated, falsified for APPEND/JOIN

Idea: balanced append trees to expose parallelism.  Analysis and
the spec's own comment agree it's already optimal: `APPEND xs ys`
costs O(|xs|) (REV xs + fold), so `JOIN` emits right-nested appends
whose LEFT args are the individual data fragments — disjoint cones,
already developed in parallel (the 626-redirects/round
measurement).  A balanced tree `(a++b)++(c++d)` makes the outer
append's left an *accumulated result* — REV+fold of it costs O(n)
per level → O(n log n) total AND a deeper critical path.  Strictly
worse.  Left-fold accumulators (`emit`, `evalf`, `ALOOK`) are
genuinely sequential and can't be reassociated without a proven-
associative step.  The real remaining critical path is carry-ripple
arithmetic (B4INC/bytes4) inside payloads — that needs new spec
vocabulary (carry-lookahead/balanced adders), a generator-layer
encoding change, not reducer scheduling.

## Formal cross-examination — what confluence licenses vs. doesn't

Lean corpus already proves the order-freedom the scheduling work
relies on: `IRedBasis_confluence` (BasisDev:521 — the n!→1 order
quotient is a theorem), `ParStepBasis_diamond/commute` (disjoint
cones commute), `cdJoin`/`cdJoin_of_join` (Join commutes with
cdBasis — the license for eager_tail/frontier/any seal), and
`Splice_join` (redirects preserve the Join class).  `dagUnfold`
quotients away fwd AND hash-consing — interning is formalized as
representation-level, not semantics.

NOT licensed: step-function reassociation (`Join (APPEND (APPEND a
b) c) (APPEND a (APPEND b c))` — an equational theorem on the
λ-encoding, per-operator, a real work item — and moot anyway since
right-nesting is optimal for O(|left|) append).

Hash-cons amortization: the intern key is now a packed int
`l << 32 | r` (was tuple) — kills the tuple alloc/hash per mk_app.
Neutral-to-small win; dict.get still dominates.  The amortization
that actually pays is a hit skipping re-development — tax on
sequential loads (0.05% hit), win on recurrent ones (10.7%).

## Memo scoping (why memoization "doesn't hit")

Three memos, three scopes — none broken:

| memo | scope | measured | persistence |
| --- | --- | --- | --- |
| `_cd_memo` | one round | 12.98M hits — sharing works | cleared per round by necessity: the seal `cd_memo[out]=out` means "developed this round"; `out`'s residuals must re-develop next round |
| `_nf` | persistent | ~1.4k entries | the only sound cross-round memo — fully-normal subtrees |
| `_step_memo` | persistent | 13M entries, zero reads on cd | redirect() seeds unconditionally; step() only runs on lo |

No memo can help sequential development: each round's contractum is
genuinely new — the 99.95% intern miss rate is real misses.

## HDev_total status

Scratch file `_hdev_total_work.lean` compiles green (image-map
bundle, path lemmas, `HSteps_img`, `repr_stay`, `weaken`, `oldSub`
containment). Remaining: `HDev_steps` per-constructor discharge,
measure, strong recursion — deferred; proof work resumes when the
formalization sprint is the priority.

## append_assoc: PROVEN (not moot)

`_spec_assoc_work.lean` now compiles green — `append_assoc_basis`:

    Join (tr∘compile (APPEND (APPEND sa sb) sc))
         (tr∘compile (APPEND sa (APPEND sb sc)))

for `sa = scottList as` etc., on the faithful λ-encodings of
spec_term.py's `_FOLDL`/`_REV`/`_CONSS`/`_NIL`. Axioms: propext,
Quot.sound only. The theorem is the observational equivalence the
balanced-emission question needed — `translate_to_basis ∘ compile`
is exactly host `import_tree(expand_s=True)`, so the statement is
about the real host terms.

Proof architecture (what worked):
- Head-spine β evaluator `hstep`/`hsteps` + `hsteps_red` soundness
  (Option-free: `hstep` is identity where inert → `LRed_app_left`
  closes the recursive case without a fallback helper).
- Milestones discharged by `hsteps k lhs = rhs` — fuel-bounded so
  evaluation stops AT the claimed form (k=1,5,7,4,4).
- The de Bruijn wall: `subst`/`shift` get STUCK on symbolic subterms
  (`subst s c (shift 2 0 h)` never normalizes for opaque h). Fixed
  with a `closed` predicate + `shift_of_closed0`/`subst_of_closed0`
  rewrite lemmas — all lemmas carry `closed 0` side-conditions on
  list elements/accumulators. Honest condition: real toolchain
  payloads are closed subterms.
- List-level algebra: `fold_read` (GGB·scott cs·a →* foldr cellLit
  a (rev cs)) by spine induction; `List.reverse_reverse` +
  `foldr_append` kill the double-rev in _APPEND; `List.append_assoc`
  does the rest.

Correction to the earlier note: reassociation was called "moot"
because right-nesting is optimal for O(|left|) append — that
cost-argument stands, but the *equational theorem* is now proven
infrastructure, not dismissed. The same shape (fold readback +
List algebra) is the template for `Join ripple_add carry_lookahead`
once a balanced-adder spec term exists.

## adder vocabulary: PROVEN — Join ripple vs carry-lookahead

`_spec_adder_work.lean` compiles green — `b4add_b4cla_basis`:

    Join (tr∘compile (B4ADD·(b4 as)·(b4 bs)))
         (tr∘compile (B4CLA·(b4 as)·(b4 bs)))

for all 4-byte inputs `as, bs : List (Fin 16 × Fin 16)` — the faithful
λ-encodings of spec_term.py's `_B4ADD` (FOLDL zip-ripple) and `_B4CLA`
(depth-2 carry-lookahead, added to spec_term.py alongside `_B4BC`/`_B4BS`
byte-cell splits). Axioms: propext, Classical.choice, Quot.sound —
kernel `decide`, not `native_decide`, so no trusted-compiler axioms.

Both sides reduce to the same reduct `scottList (resList as bs 0)` —
a shared normal form, not bit-matching. The CLA decomposition is
honest algebra: `byteCoutB_mono` proves `cout(c) = g ∨ (p ∧ c)`
(byte carry-out monotone in carry-in), and the lookahead tree is
unfolded cell-by-cell through `b4bc`/`b4bs`/`b2n`/`or`/`and` leaf
lemmas; CLA spine milestone at k=58.

New machinery beyond the append proof: symbolic `nibLit i` can't
dispatch under `subst` (var index `15-i` is kernel-stuck) — nibble
ops are proven as `∀`-enumerated tables (`∀ i j : Fin 16`, 256
instances, `decide` — each instance concrete). Byte cells destructure
to app-spine milestones (weak β has no ξ — milestones stop before
pair-formation so stuck nibble-apps stay LRed-reachable), then
leaf-normalize by table-lemma congruence rewrites.

The Fin-valued ite problem in `byteCoutB_mono`: `omega` atomizes
`Fin.val`-wrapped `if`s, so don't `simp`-normalize hyps before
splitting — instead `split` the Nat-ite conditions raw, case on the
`decide`s, close by `omega` only once all conditionals are concrete.

## promotion: both spec proofs are now a library module

`src/ISAR/SpecVocabulary.lean` merges `_spec_assoc_work.lean` +
`_spec_adder_work.lean` (dedup: the adder file's `cell_unfold`/
`nil_unfold` are the strict generalizations — `st`-parameterized —
the assoc versions are the `stepConsL` instances; `fold_read_sc`
renamed `fold_read`). Registered in `src/ISAR.lean`; `lake build`
green (3160 jobs). Axiom audits print in-build:
`append_assoc_basis` [propext, Quot.sound],
`b4add_b4cla_basis` [propext, Classical.choice, Quot.sound].
Scratch files remain at repo root as work artifacts.

Host witness: `_B4CLA` vs `_B4ADD` cd-congruence on 4 critical carry
pairs (wraparound cascade 0x1+0xFFFFFFFF, mixed carries) — all NFs
identical to the literal. Round structure confirms the design: CLA
~267 rounds vs ripple ~424 (carry chain collapses to independent
cones), at ~30% more allocs (wider fan-out). Lean covers all inputs;
this is the encoding-level check on `spec_term.py`/`reduce_cd`.
