# 036 — Self-emission: staged seams, LO compaction, insn-granular assemble

The seed emitting its own host = `emit_chain.py`: the full
resolve→program→link→assemble→pack chain as staged basis-term
reductions, NF terms serialized across every stage boundary, fresh
arena (or process) per stage. Gate: image bytes == `seed.emit`
oracle byte-for-byte.

## What the win64 attempt measured

Single-arena composition is dead at this scale — not correctness,
retention:

- `programOf` win64 on graph.lo: **82K steps / 11.4M nodes / 53s** —
  cheap.
- `linkOf` win64 on graph.lo: 233K steps / 4.6M nodes / ~107s.
- `assembleOf` win64 monolithic: ballooned past ~85GB pre-compaction
  (killed); with LO-reduce compaction it is bounded (~4GB peak) but
  only ~1.7K steps/s → estimated many hours — feasible, slow.
- `pack2Of` win64 on graph: probe-verified ~2.1M steps; live set is
  image-scale (~100M nodes peak even compacted — accumulators stay
  reachable, compaction can't shrink genuine working set).
- Naive PE exe on whole-stage terms: **infeasible** — the tree
  reducer re-reduces every shared redex; assemble/pack mini already
  exceed 20-30M fuel at ~5KB/step allocation (94-100GB arenas seen;
  kill before OOM).

## Two mechanisms that made win64 reachable

**1. `Graph.reduce(compact_every=N)`** — between-step arena
compaction. `_pending` is empty between `step()` returns, so
`compact(cur)` is legal mid-reduce; drops `_step_memo` (semantically
transparent — redirects recompute identically). Mini chain verified
byte-exact with compaction on. Peaks bounded to ~4GB where the
uncompacted run hit 85GB+.

**2a. `Graph.reduce_cd(compact=True)`** — the pack-stage engine.
pack2Of's JOIN spine keeps every section intermediate reachable on
LO — the live set itself cycles to ~65GB+ and never shrinks.  On cd
the pad/join chunks are disjoint cones developed per round, and
per-round compact keeps residency at ~157MB (pack-mini: 18,354
rounds / 4,655 nodes / byte-exact vs ~14GB on lo).  Round counts are
not step counts — the NF is the observable.  At win64 scale cd is
bounded but SLOW (the output-spine critical path still sequences
rounds) — a chunk-level pack decomposition (mirroring
assemble_staged) is the next lever if wall-time matters.

**2. `assemble_staged`** — assembleOf decomposed at insn granularity:
- pass-1: per-insn `encodeOf item ZRESV` (zero resolver — length is
  correct since rel fields are always 4 cells), memoized per unique
  item;
- labels: `loc[name] = base + pos` as boundary data;
- pass-2: only resv-sensitive items (op tags `"l"`/`"p"`) re-encode
  with `RESVMK sym loc end4` — the same resolver closure
  `_assemble_src` builds, spliced as data per site;
- non-rel items reuse pass-1 bytes (resv never applied).
- win64 kernel: 540 items = 484 insns + 56 labels → **~323 term
  encodes** (166 unique non-rel + 157 per-site rel) instead of one
  giant fold.

Verified byte-exact vs `isa.assemble` on ASM_PROG (fwd/bwd rel32,
rip-syms, shadowing, mem-disp, nonzero base).

The trade-off stated plainly: pass structure and B4ADD bookkeeping
move from a proven fold term to boundary data ops. What stays
term-computed: every emitted byte of every insn. The final image is
still oracle-gated byte-exact. This decomposition is also exactly
the shape parallel/CUDA evaluation takes — independent redexes in
independent contexts.

## Host-per-stage cost profile (the real finding)

| workload | graph.lo | naive PE exe |
| --- | --- | --- |
| big folds (program/link/pack) | sharing wins; needs compact | path-explodes (no sharing) |
| small independent terms (encodes) | ~10-20s each (import+reduce) | **~0.3-1s each** — wins |

One insn encode on `reducer_default.exe`: 261,695 steps, 11.9M
allocs, <1s, `4889e5` byte-exact. The emitted host computing the
encodings of its own image — self-hosting through the seam, not
around it — is wired via `emit_chain --win64 --insns-on-exe`.

**3. `pack_staged`** — pack2Of decomposed at chunk granularity
(mirrors `_pack_body`'s chunk list exactly).  Measured at win64:

- LO monolithic: live set cycles past ~65GB, infeasible even with
  `compact_every` (the JOIN spine's intermediates are genuinely
  reachable, not retention garbage).
- cd+compact monolithic: bounded (~350MB) but >90min — the
  output-spine critical path sequences rounds.
- naive exe on `LENB4 text` alone (2696 cells): **72GB bump arena,
  OOM** — sequential folds over serialized data are the exe's worst
  case (per-step alloc ∝ term size, never frees).
- chunk-level decomposition: **byte-exact 3584B in ~35s** on the
  default LO runner.

Seam discipline sharpened: the three `LENB4` folds are the only
O(section-size) work in pack, and they re-derive a quantity the
serialized seam already carries — `len()` on the checkpointed
`text.bin`/`idata`/`datab` is the same category as assemble_staged's
`pos += len(b)` bookkeeping.  lt/li/ld enter as bytes4 literals;
every DERIVED value (ALIGN512, B4ADD chains, PADLIST pads, ZEROFILL
runs, U64 stackres) is still a term reduction on the same vocabulary
constants.  An expert could object that lengths become
Python-observed, not term-computed — the counter is that the staged
contract is "sections are term-produced, container bookkeeping is
the seam", and the final image is oracle-gated byte-exact anyway.

## Checkpointed seams

`emit_work/<tag>/` persists decoded artifacts —
`program.items` (pickled item list), `link.sections`
(idata/datab/symtab), `text.bin` (pickled (text, localmap)),
`image.bin` — so any stage can resume without recomputing ancestors.
The byte data on disk IS the stage seam.

## Gate results (win64)

- `default` realization: **3584B byte-exact** — program 81K
  steps/54s + link 233K steps/81s on graph.lo, ~480 per-insn
  encodes on `reducer_default.exe` (~33min), pack* ~39s.
- `fuse_s` realization: same pipeline, fresh checkpoints.

## Deferred

- CUDA remains the eventual parallel/round witness for graph.lo
  (divergent step size expected); the per-insn/chunk decompositions
  are the seams it would slot into.
- Monolithic `assembleOf` at win64 stays as the long-running control
  — it validates that the decomposition computes the same bytes.
- Revisit stage serialization format at full-native-synthesis time:
  JSON/toolchain loading is temporary; plex-wire is the candidate.
