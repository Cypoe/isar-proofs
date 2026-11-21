# 042 — -O3 seam: opt_peephole (Program-level) + res graft inline

Date: this session. Commit `99dc32d`.

## Decision

The `-O3` item landed as two distinct optimizations, deliberately
**not** touching the interpreter `step` loop:

1. `host/opt_peephole.py` — a Program-level rewrite pass spliced into
   `seed.emit()` between `rts.program()` and `isa.assemble()`.
   Rules: fallthrough-jmp elimination, unreachable-after-jmp/ret
   pruning, unconditional jump threading, self-move removal.
   Per-ISA branch/move classification is a data table (`ISACLASS`);
   the rules know only "unconditional jump", "return", "register
   move". Conditional branches are never inverted or retargeted —
   that would require a flag model, which is the smuggling this
   layer exists to avoid. Fixpoint-iterated; returns a new list.
   `x86_64.fasmg` normalizes to `x86_64` classification.

   Applies uniformly to every emitted kernel: all three linux.lo
   kernels, both win64 kernels, the res kernel, and the `.o`
   relocatable path. Measured effect is small (1–5 insns/text
   section) — the builders were already tight — but the seam is now
   where any future Program-level optimization lives.

2. `routines_x86_64_win64.res` — the graft loop's `res_remap` helper
   inlined twice per APP cell, with the invariants (`rescells` base,
   `resend`, `resarg`, `resdelta`) hoisted into callee-saved
   registers (r12/r14/r15) that survive `mkapp`/`mkleaf`/`grow_heap`.
   Removes call+ret ×2 per residual node per arg root. `res_remap`
   removed from `ROUTINES_RES`; the routine builder deleted.

## Revision (commit `4c8120d`)

The unconditional splice into `seed.emit` broke the `emit_image(R) ==
seed.emit(R)` byte seam: the staged chain has no peephole stage, so
the images differed by one `jmp_rel32` (every later rel32 off by 5).
Nothing caught it because the seam had no registered gate; G10 now
does. Peephole is now `Realization.peephole` (default **off**). The
seed route applies it only when it is set, and `emit_chain` refuses it
with `NotRealized`. The fix is deliberately not a Python pass over the
decoded staged items, because that would be a stage outside the term
chain. A term-level `peepholeOf` stage is the path to "on" on both
routes. The res-graft inline is unaffected: it lives in the routine
builder, so both routes see it.

## Verified

- `res_g9b_opt.exe` (inlined graft) reproduces `res_g9b.exe`
  bit-for-bit on the 20-name batch: 24 lines, `steps=6720554`,
  `alloc=270563066`, rc=0.
- All three linux kernels + `.o` objects emit through the opt seam;
  x86_64 `.o` still links via `ld` and runs; cross-ISA qemu
  byte-identical stdout/stderr/rc on the probe set.
- Audit (`R.audit`) histograms identical across ISAs through the
  opt seam.
- fuse_s variants emit and run correctly.

## Architectural note

This is the honest shape of "-O3" here: the interpreter loop is the
proved core and stays untouched; optimizations live on the *stages*
the emit chain produces — the Program list is data, so a peephole is
just another stage transform; the graft is a specialized stage, so
specialization-level rewrites (inlining, hoisting) belong in the
routine builder, not in a generic pass.
