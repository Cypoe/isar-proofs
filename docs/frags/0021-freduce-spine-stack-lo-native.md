---
type: frag
id: 0021
provenance: host/routines_x86_64_win64.py r_freduce + host/routines_c.py freduce
ts: 2025-01-01
tags: [reducer, spine-stack, lo, immediate-collapse, native, c-witness, perf, parity]
---

# 0021 — freduce: spine-stack LO machine, no root re-walk

## What landed

`r_freduce` replaces the repeated `step(root)` loop as the reduction
driver in the Win64 x86-64 PE kernels and the C witness. One call
normalizes the whole term:

- **unwind** pushes the left spine as 16B machine-stack frames
  (`[rsp]=node|phase`, `[rsp+8]=lrep`; phase rides bit0 of the
  24-aligned node pointer),
- **contract at the tip** consumes the top-`a` ph0 frames, performs
  the same zone/FWD discipline as the `st_*` arms, and the reduct
  becomes the new tip — the pending front collapses in place,
- **feed/combine** on a normal tip: ph0 frame records `lrep`,
  descends right; ph1 frame combines reps — unchanged children
  return the parent cell unallocated, writable cells patch in
  place, perm/input cells rebuild via `mkapp_p` (the
  `st_l_fr`/`st_r_fr` rule as a pending-combine).

The stack *is* the frontier — no wavefront bookkeeping, no root
re-descent. `step` stays emitted for `eg_probe` and `step_congr`'s
internal congruence calls; all four driver loops (`red_loop`,
`ir_rloop` ×3 incl. MT worker and residual kernel) call `freduce`
once.

## Semantics: mechanism change, not strategy change

The machine realizes the same `IStepBasis` leftmost-outermost
order — identical redex sequence, identical per-contract step
count. Python prototype parity vs `graph_runtime.reduce_lo`
before porting: identical NFs and step counts on Church-numeral,
`2^n`, `fact` benches.

Contract-depth check subtlety: all top-`a` frames must be ph0 — a
ph1 frame inside the span is a right-descended ancestor whose
pending right subtree is not an argument.

## Measured

Identical `steps=` on every probe; allocation count is now the
honest witness of the mechanism (fewer allocs = fewer rebuilds):

```
I-chain n=20K:   step-loop 2.53s alloc=200M    freduce 0.04s alloc=40K
I-chain n=50K:   step-loop 18.2s alloc=1.25B   freduce 0.01s alloc=100K
c_12000 I K:     step-loop 0.04s alloc=2.5M    freduce 0.02s alloc=1.0M
```

The I-chain is the pathological case for re-descent (O(n²) → O(n));
c_k workloads keep a bounded spine, so the win is ~2× wall and
~2.5× allocs.

## Verification

- `cross_verify`: 139 probes × PE↔C byte-identity incl. `alloc=`
  (C witness runs the same machine), fuel axis, identical WWW
  divergence — 0 divergences.
- `gates_nanopass`: 32/32 — MT equivalence (ST↔MT × 3 egress ×
  threads {2,4} byte-identical + steps parity) under
  reclaim="redirect", .plex ingest, layer composition tuples
  updated for `freduce`.
- `battery --tier fast`: 31/31.
- `gc="sweep"`: spine frames are C-stack-window conservative roots
  for free — c_k I K under a 4MB arena: gc=1/4/9 collections,
  correct NF and steps throughout.
- `audit=True`: rule histogram intact (bumps must precede the
  `setup3` arg loads — `_bump` clobbers rax).

## Trade-offs / honest edges

- Fixed 16B/frame machine-stack cost; deep spines consume C stack
  (mitigated by the same limits `step` recursion had — now linear
  data, not call frames).
- `rules=` L/R counts measure unwind/right-feed events, not
  re-descents — same axis name, honestly different mechanism;
  no gate asserts the values.
- aarch64/riscv64/linux kernels still run the `step` loop —
  win64 is the deployment leg; porting is mechanical when those
  legs are realized for real use.
