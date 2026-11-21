# 047 — W5: G17 CUDA behavioural gate (2026-09-30)

## What was built

`host/cuda_gate.py` — G17 (quotient/congruence, regime `operEq`,
tier env, `requires: ["nvcc"]`): `ir_cuda.exe` vs the emitted
`native.x86_64.pe.ir` kernel on **identical packed-IR batches**.

Same contract class as G12 (xisa): stdout NF lines, stderr
`steps=`/`alloc=` aggregates and return codes must be identical —
**no tempo claim** (GPU-vs-CPU wall time is never recorded).

## Legs

- **xisa corpus as PIR**: the G12 term corpus (`I`, `K I`, `S K K I`,
  `B W I …`, `W I`, t24, t28 towers) — `bc_compile` → `t_to_host` →
  `st.pack_ir(*terms)` into one multi-root batch.
- **G9b instantiation batch**: `_residual_state()[3]` — the real
  Futamura instance queries, the batch shape the fork pool carries.
- **Fuel**: t24+t28 under budget 10 — native `fuel=` baked at emit,
  CUDA via `IR_CUDA_FUEL` env; both must `rc=2`.
- **Malformed**: bad version, truncated body, tag ≥ 7, self-edge
  node — both readers must `rc=3` (the depack validators are the
  equivalence under test, not the reduction).
- Both views: default build and `-DFUSE_S` vs native `fuse_s=True`.

## Verified so far

- env: RTX 3060, nvcc 12.1, `available()` probes nvcc + `nvcuda.cuInit`
- xisa batch: **stdout identical, steps/alloc identical** —
  plain `102400 st / 1351776 al`, fuse `102400 st / 1351757 al`
  (identical steps across builds: the corpus is dup-tower dominated;
  the sβ-vs-ds delta shows in alloc, where it should)
- malformed ×4 and fuel: all rc equal (3 / 2)
- `spec_term.T` vs `seed.T` pitfall: `pack_ir` wants reduce.T —
  conversion is `seed.t_to_host(bc_compile(s), reduce)`

## Verified (full gate green)

- env: RTX 3060, nvcc 12.1
- xisa batch both views: identical NF lines, steps, alloc, rc.
- **G9b instantiation batch both views** — cell-identical stats:
  plain `8177435 st / 343917322 al`, fuse `5063037 st / 197333675 al`,
  all 24 NF lines byte-equal, rc 0.  First run failed with every
  root at ST_OOM at exactly 2^28 cells: the CUDA arena is ONE shared
  bump counter across the stream (`g_top`), while the native kernel
  DECOMMIT-resets per root — the G9b batch legitimately needs ~343M
  cells total vs the 3GB default's 268.4M (Cell=12B).  Fix is the
  declared host knob `IR_CUDA_HEAP_MB=8192` on the g9b legs — the
  CUDA-side counterpart of `Realization.ir_arena_bytes`, not a
  semantic change.
- fuel → rc2 both; malformed ×4 → rc3 both.  `OK cuda_gate`.

## Per-root retake (added, same wave)

`IR_CUDA_PER_ROOT=1` makes the shared-`g_top` bump optional: each
root-thread keeps a private `(mytop, myend)` cursor and claims
`SLAB_CELLS` (1<<20 cells) slabs from `g_slabtop` on demand —
the native kernel's per-root DECOMMIT model carried to the GPU,
with slab-claiming instead of equal slices so uneven roots are
capped by the stream total only.  Gate legs `xisa/*+per_root`,
`g9b/*+per_root`, `fuel+per_root` all green, stats cell-identical
(`8177435/343917322`, `5063037/197333675`).

`IR_CUDA_MANAGED=1` swaps `cudaMalloc` for `cudaMallocManaged` —
UVM demand-paging: 16GB arena on a 12GB RTX 3060 verified
(oversubscription works on this platform), so the arena bound is
host memory, not VRAM — the GPU analog of commit-on-touch.

## Trade-offs stated

- Runs the exes directly rather than through `make_ir_runner`'s
  Merkle cache — the gate's claim is *the two kernels* on the same
  stream, cache hits would silently skip the witness.
- NF cap (`IR_CUDA_NFCAP`) stays default; heap is raised to 8192MB
  on the g9b legs because the shared stream-arena must hold the
  batch's total live cells (per-root reset would be the alternative
  realization — would change the kernel, not the claim).
- Status mapping compresses ST_OOM/ST_DEEP/ST_NFOVF to rc3 at the
  host — a failed root is still reported (status in the debug line),
  and the stats mismatch made the failure visible before the fix.
