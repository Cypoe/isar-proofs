# 063 — freduce: spine-stack LO machine is the runtime reducer

## Context

The native kernels drove normalization with `red_loop:
step(root)` repeated — each `step` re-descended the left spine
from the root, contracted one redex, and returned. Per-step
re-descent is O(depth) per contraction and re-allocates the spine
each time (deep-spine terms were quadratic: I-chain n=50K took
18.2s and 1.25G cell allocations).

The user's requirement: the compiled native must do *immediate
collapse* — when a redex completes the suspended parent front
fires in place, with no additional branch re-walks. A runtime
strategy knob was considered and rejected: "we only want the
proven golden / fastest in that runtime, the rest is emittance."

## Decision

`freduce` is the single runtime reducer for win64-PE and the C
witness — landed in place, no `spine=` axis. Alternatives remain
an emittance/property concern (other kernels, other orders like
`cd`), not runtime selection.

Mechanism, not strategy: the machine realizes the same
`IStepBasis` LO order — Python prototype showed identical NF and
step sequences vs `reduce_lo` — so `steps=` oracle parity is
preserved exactly.

Key mechanisms:

- Spine as 16B machine-stack frames (node|phase in the node's
  low bit, lrep slot). Chosen deliberately over a heap stack:
  `gc="sweep"` scans the C-stack window conservatively, so frames
  root their targets for free.
- Contract at tip consumes top-`a` ph0 frames; reduct is the new
  tip — that is the front-collapse.
- ph1 combine: unchanged children → return parent cell
  unallocated; writable → patch in place; perm/input →
  `mkapp_p` rebuild (the `st_l_fr`/`st_r_fr` zone rule as a
  pending-combine).
- Contract-depth check requires ALL top-`a` frames ph0 — a ph1
  frame in the span is a right-descended ancestor, not an arg
  spine.
- `step` stays emitted (eg_probe, step_congr internals) but no
  driver loop calls it.

C witness (`routines_c.freduce`) runs the same algorithm — PE↔C
`alloc=` byte-parity depends on the same mechanism on both
hosts; allocation drift between mechanisms is a real parity
signal, not noise.

## Consequences / hazards

- `_bump` (audit counters) clobbers rax — bumps must sit where
  rax is dead: before `setup3` arg loads, after the ph=1 frame
  store. Two crashes found and fixed.
- Frozen layer-composition tuples in `np_gates_kernel` now
  include `freduce` between `step_congr` and `count_nodes`.
- `_MT_THREADED` includes `freduce` — per-worker private arena,
  `("p", slot)` operands rewritten to r10 ctx.
- linux/aarch64/riscv64 legs unchanged (still `step` loop) —
  win64 is the realized deployment leg.

## Verified

cross_verify 0 divergences (139 probes, alloc parity, fuel, WWW
divergence) · nanopass 32/32 (MT equivalence, ingest, layers) ·
battery 31/31 · sweep collections over live frames · audit
histogram sane. See frag 0021 for numbers.
