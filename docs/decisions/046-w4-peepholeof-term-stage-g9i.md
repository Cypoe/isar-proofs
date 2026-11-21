# 046 — W4: peepholeOf, the H' modification test at term level (2026-10)

## What was built

`spec_term.peephole_query` wraps `_PEEPHOLE_OF` — a bracket-abstracted
NExpr mirroring `opt_peephole.optimize` rule-for-rule.  The stage
consumes `programOf`'s fragment-list NF and emits ONE fragment (the
flat optimized item list), so `decode_program` and `assembleOf` see
the same representation on either side.

## How the oracle maps to term machinery

- **Pass structure:** one pass = `FOLDL` over the flat item list
  carrying `(out_rev, skip_dead, changed, index)`.  The fixpoint is
  `((\f. f f) (\g.\p. pass p -> (ch, l2); ch (g g l2) l2))` — the
  recursive call sits in the taken branch only, so it is
  **normal-order only** (lo-routed, like every stage before it; cd
  would evaluate `g g l2` eagerly and not terminate).
- **Rule order mirrors Python:** label → emit + clear skip_dead;
  skip_dead → drop; ujmp → chase/emit + set skip_dead; ret → emit +
  set skip_dead; selfmove → drop; else emit.
- **Jump threading** needs `label -> index`: built by a second fold
  (`ALOOK` last-match on a cons-prepend assoc = Python `setdefault`,
  first occurrence wins).  The chase walks `NTH (idx+1)` while the
  target is an insn, in UJMP, and fresh — a `seen` list breaks `jmp`
  cycles (the oracle's `ret`-check already broke them, but cycles of
  pure jmps would loop; term keeps the same termination reason).
- **Fallthrough / unreachable / selfmove** are direct: `NTH (i+1)`
  for the next-item test, `MEMB` on the ISA class lists, `OPEQ`
  fieldwise on the two declared operand cells.
- **Indices are Church numerals** — `NTH` walks + `SUCC` only, no
  arithmetic.  Names are nibble-strings; `EQSTR` is `_LEN`-bounded.
- **ISACLASS as parameters:** `peepholeOf UJMP RET SELFMOVE frags` —
  the table is lifted from `opt_peephole.ISACLASS["x86_64"]` itself,
  so the classification data is shared, not re-declared.

## G9i (suite spec_term, tier full, regime bytes)

`decode_program(peepholeOf frags) == opt_peephole.optimize(items)`:

- `mini`: hand-cut 11-item fragment exercising all four rules plus
  their interaction (fallthrough + threading + unreachable + selfmove
  in one pass, a second fixpoint round for the threaded fallthrough).
  → 6 items, `lo 735469` steps (fixed term; the per-pass `lat`
  rebuild is honest ~10% over the frozen-`lat` bug).  PASS.
- `win64`: the real `programOf` (553 items: 493 insns, 60 labels,
  30 jmps; laziness normalizes it inside the JOIN — the composed
  query is literally the emit_chain stage term).  Runs through the
  **batched decomposed seam** on the naive IR exe — measured end to
  end: 2 passes / 167M exe-steps / ~6min / sub-GB host RSS, output
  552 items == oracle.  (The undecoposed monolith on graph.lo needed
  ~40M+ lo steps — hours; fuel there was the runaway guard, never
  the budget.)

## OOM → compact_every

The first win64 leg ran `reduce_tree_lo` un-compacted: the retained
scaffold reached ~70-90GB RSS and the process was OOM-killed.
`Graph.reduce` already had the `compact_every` mechanism (decision
030) — `reduce_tree_lo` now exposes it and the G9i win64 leg runs
`compact_every=200_000`, the same interval `_graph_run` uses for
emit_chain stages.  Live set stays ~4-9GB instead of unbounded.

## Runtime measurements (supersedes the "stuck" reads)

The two W4 legs weren't hung or diverging — they were CPU-bound at
~1.3K steps/s under two-process contention.  Measured solo:

- graph.lo + compact: **~6,500 steps/s** on peephole-fold terms —
  win64 ≈ ~2-3h, not ~10h+.
- naive IR exe (`reclaim=none`, 32GB arena): **OOM in ~18-38s** on
  fold-shaped terms — ~160M fresh cells/s (immutable-cell zipper
  rebuild, ~3,900 allocs/step); arena size doesn't help.
- redirect IR exe: bounded but ~250 steps/s — 5.4× slower.
- ir_cuda: one thread per root → a single sequential fold gets one
  GPU thread on an immutable 3GB arena — inapplicable.

Per-stage-kind runner table and the shared NF store: see decision
048.  Term-level NTH/ALOOK elimination measured at ~2% of steps —
the fold machinery itself is the cost; skipped the rewrite.  **The
resolution was decomposition, not a faster host**: the pass's folds
became per-item batched queries (sk/ch speculation + repair for the
sequential flags; latprobe batch for the label table — every
verdict still a real term evaluation, the seam only schedules).

## Bug found by the medium-scale probe

First version bound `prog` and `lat` OUTSIDE the fixpoint (one _lets
block covering the self-application).  Mini passed anyway — its
threading converged within per-item work.  A synthetic 29-item probe
with `jmp Lk` two slots before each label exposed it: pass 1 drops
unreachable insns between a jmp and its label, and only pass 2 sees
the fallthrough — but the term re-read `label_at`/`nxt` from the
ORIGINAL list forever, returning pass-1 output frozen.

Fix: `passt` binds `prog := p` and rebuilds `lat` on the fold input
every iteration — exactly the oracle's `_pass`-local `label_at`.
Probe after fix: 29 items, 2319612 steps, output == oracle.

Scaling is linear in items (~70-80K steps/item — the nibble-string
EQSTR/MEMB classification and acc-record machinery dominate), so
win64 is heavy but not pathological.

## emit_chain wiring

- `_prog_nf()` runs `peephole` as its own stage on the program NF
  when `R.peephole` — the same NF-seam shape as linkOf→assembleOf;
  `stage_runs["peephole"]` is routable like every other stage.
- `_ck_keys` keys `program.items` on the post-peephole term
  (`peephole_query(program_query(R))` digest) — otherwise a
  peephole=False checkpoint would serve unoptimized items silently.
- The `NotRealized` refusal is gone; `--win64 --peephole` adds the
  leg, byte-compared against `seed.emit(R(peephole=True))` (the seed
  route's `opt_peephole` remains the independent oracle).
- Under `--ir-redir` the `peephole` stage still rides the naive
  item exe — per-item queries are bounded terms, so redirect's
  persist probing is pure cost there.
- Registry: `G9i` obligation (suite spec_term, `--gate G9i`) and
  `G10-peephole` (suite emit_chain,
  `--win64 --insns-on-exe --ir --peephole`), both tier full /
  regime bytes.  The `peephole` stage defaults to
  `_peephole_item_runner()` — `make_ir_runner` on the naive IR exe
  (`fuel=8M`, `ir_arena_bytes=8<<30` for the chase-heaviest item's
  ~3G cells, `workers=4`, NF cache `emit_work/nf_cache/peepitem`) —
  per-item queries content-addressed, so G9i's leg and the
  G10-peephole leg serve the same verified NFs.
- seed.py/toolchain.json text updated: peephole is realized on both
  routes.

## Trade-offs stated

- Term-level `O(items · jmp-distance)` per pass via `NTH` walks —
  the honest price of list-of-items representation; a label→item
  tree-map would need a second representation seam.
- The fixpoint does full list rebuilds per pass (sharing keeps
  untouched item cells, the spine is fresh) — normal for the
  consume-on-collapse kernel too.
- `OPEQ` compares exactly 2 operand cells; the SELFMOVE class fixes
  arity per mnemonic so that is the honest predicate (Python tuple
  equality there).
