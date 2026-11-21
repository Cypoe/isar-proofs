# 038 — fasmg witness + CUDA worker on the packed-IR seam

Status: implemented (aab7816, cuda worker pending commit).

## fasmg syntactic witness

- `host/isa_fasmg.py`: renders the same `Program`/`LBL`/`I` tuples to fasmg
  source — symbolic labels, `near` branches, explicit operand sizes. Sibling of
  `isa_c.py`.
- `host/target_fasmg.py`: wraps the stream in `format PE64 console` + .text/
  .data/.idata (canonical pe.inc import shape, `iat_<name>` IAT labels) and
  compiles via fasmg.exe (ISAR_FASMG env or isa-physics/boostrap path).
- Toolchains `native.x86_64.fasmg` / `native.x86_64.ir.fasmg` resolve through
  the declarative map.
- Gate is BEHAVIORAL, not byte-exact: fasmg legally picks different encodings
  (imm8 group forms, short jumps). Verified: identical NFs/stats/rc on token +
  packed-IR + fuse_s + audit variants.
- fasmg-format gotcha: `at` is greedy and ends the settings match — stack/heap
  are standalone pe.inc directives, not format-line args.

## CUDA parallel evaluator (skeleton)

- `host/ir_cuda.cu` + `host/_build_cuda.bat` (nvcc via vcvars64): a real
  device evaluator speaking the same packed-IR stream contract — drop-in
  worker for `make_ir_runner(exe=...)`.
- One thread per ROOT (audit data: ~77 congruence descents per firing →
  intra-root parallelism is thin; root/cone is the parallel unit).
- Device cells {u32 tag,l,r}; input depacks to [0..n_nodes), rule allocs via
  global atomic bump. Zipper-stack LO step mirrors kernel semantics exactly:
  I/K/W/B/C (+ sβ under -DFUSE_S), congruence rebuilds alloc fresh cells.
- Default view expands tag-3 cells to the ds template like the kernel depack.
- Verified byte-identical stdout + identical steps/alloc vs the emitted kernel
  (SKKI 10/59; 32-root batch 42/202; fuel -> rc2; malformed -> rc3).
- Per-root diagnostics behind IR_CUDA_DEBUG env.
- Limits (honest skeleton): no warp cooperation, fixed per-root NF emit cap
  (IR_CUDA_NFCAP, overflow -> rc3), zipper depth cap IR_CUDA_FRAMES.
