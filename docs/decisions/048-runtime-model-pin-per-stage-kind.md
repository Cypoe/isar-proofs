# 048 — runtime model pin: runner table per stage kind

## Status

implemented (emit_chain `stage_runs` + `make_graph_runner`; shared
`emit_work/nf_cache/graphlo` content-addressed NF store)

## Context

The W4 peephole legs ran ~10h on graph.lo under two-process
contention and looked deadlocked.  The user pushed: pin the runtime
model to the fastest/most modular one — probably the parallel
packed-IR/CUDA reducer.  So the question was measured, not argued.

## Measured (this machine, same term family)

| runtime | steps/s | memory | peephole fold (735K-step mini) |
|---|---|---|---|
| graph.lo + compact_every=200K | ~6,500 solo (~1,360 contended×2) | bounded | completes |
| native.x86_64.pe.ir (naive, reclaim=none) | ~160M cells/s alloc churn | unbounded retention | **OOM at ~2.9G cells (32GB arena)** — ~3,900 fresh cells/step: every congruence step rebuilds the whole zipper spine with immutable cells |
| native.x86_64.pe.ir reclaim=redirect | ~250 | bounded (persist zone) | completes but 5.4× slower than graph.lo — persist-probe dominated |
| ir_cuda.exe | 1 GPU thread/root | 3GB immutable arena | impossible: single root → one thread, arena dies at ~260M cells |

Two-process contention on graph.lo halves-to-fifths throughput
(memory bandwidth + compaction thrash): schedule heavy legs solo.

## Decision

Runner selection is a per-stage-kind table, not one runtime:

- **Deep sequential folds** (program/link/peephole — FOLDL chains
  whose congruence zipper depth is the per-step cost):
  `make_graph_runner` — graph.lo + compaction, fuel as runaway guard.
- **Batch seams** (assemble*/pack*: hundreds of independent roots):
  the packed-IR exe pool (`make_ir_runner`, workers=cpu_count) and
  the byte-egress kernel — already pinned via `stage_runs`.
- **CUDA** (`ir_cuda.exe`): same batch contract, one GPU thread per
  root — the right realization for wide batches (G17 proves parity);
  gains nothing on a single sequential fold (intra-root parallelism
  is thin by measurement, ~77 descents per firing).

## The NF cache is the seam, made a store

`make_graph_runner(cache_dir=…)` + the G9i gate write/read
`emit_work/nf_cache/graphlo/<merkle>.nf`: the key is the query
term's packed-IR digest (what would go over the wire to an exe), the
value is the bc-decompile NF line (what an exe would print).  Any
host that computes the stage serves every later run — G9i's win64
leg and emit_chain's peephole stage reduce the identical query, so
the fold is paid once total, not once per gate.

## What the workload actually needs next

**Update (W4 landed):** the decomposition changed the workload
shape, which changed the pin.  `peephole_fixpoint_seamed` runs the
pass as PER-ITEM queries (`latprobe` batch + `step'` batch under
sk/ch speculation + a repair round for dead regions) — each a
bounded term — on `make_ir_runner(workers=4)` with a content-keyed
NF cache.  Measured on win64's 553 items: 2 passes / 167M exe-steps
/ ~6min / sub-GB host RSS (naive kernel, `ir_arena_bytes=8<<30` —
the chase-heaviest single item legitimately commits ~3G cells under
reclaim=none; per-root DECOMMIT reset keeps the batch at the worst
root, not the sum).  Same driver verified on mini under graph.lo:
monolith ≡ pass-seam ≡ decomp-seam ≡ oracle.

So the pin is now: **batched bounded queries → packed-IR exe pool**
(which is also the CUDA-contract shape — a wide batch is a grid);
**deep monolithic folds** (program/link until they decompose) stay
on graph.lo+compact.  The original gap is narrower but still real:
a reclaim kernel without persist probing would let UNDECOMPOSED
folds ride the exe too.
