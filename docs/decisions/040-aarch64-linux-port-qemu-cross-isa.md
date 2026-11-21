# 040 — aarch64.linux.lo: cross-ISA reducer port, qemu-verified

Status: implemented. Commit 7690985.

## What

Third host realization, second ISA. `host/routines_aarch64_linux_lo.py`
ports `routines_x86_64_linux_lo` onto the aarch64 ISA table — same label
graph, same LO semantics, same stdin→NF/stdout + stats/stderr contract.

- ISA additions (oracle-verified, 72/72 vs llvm-mc): `subs_reg`,
  `ands_reg` (cmp/tst via rd=xzr), `udiv_reg`, `msub_reg` (itoa),
  `ldrb_uoff`, `strb_uoff`, `("alo"/"ahi", sym)` operand kinds for
  absolute symbol materialization in movz/movk.
- `target_elf64`: `machine=` parameter (`ELF64_AARCH64`, EM=0xB7) —
  same static two-segment ELF; also `(name,size,init)` data slots now
  (parity with pe64/fasmg).
- Toolchain `aarch64.linux.lo` resolves; `isa.aarch64` placeholder note
  updated (win64 variant still unrealized).

## Register map

x0..x3 args/ret · x19 heap bump · x20 heap end · x21 term · x22/x23
scratch+parse stack · x24 steps · x25/x26 parse cursor/end · x8 syscall
nr · x30 saved by every non-leaf (`_push`/`_pop` helpers, 16B-aligned
frames — aarch64 has no push/pop).

## Verification (qemu-aarch64 via WSL binfmt)

Byte-identical stdout + stderr + rc vs x86-64 linux kernel on every
probe: postfix terms, empty input (→ `I`, rc0), bad byte (rc3),
fuel (rc2), fuse_s variant (byte-identical), and a 327,675-step
doubling-tower burner. Speed: a64-under-qemu-TCG ≈ 3.1× slower than
x64 native on 327K steps — startup-dominated noise at small sizes.

## Traps that bit

- MSUB/UDIV bases must be the **32-bit** forms (`0x1AC00800`,
  `0x1B008000`) — `sf` is set by the field op from the rd name;
  baking sf=1 collides in word32.
- `wsl -- bash -c '...$?...'` eats `$?`/`$rc` through the quoting
  layers — **always run test loops from a script file**, never
  `bash -c` one-liners. Cost an hour chasing a phantom fuel bug that
  was really a shell artifact.
- build_ds: `mov x0,rA; mov x1,x0` clobbers the leaf operand — arg
  order into mkapp must be set before overwriting x0 (mkleaf leaves
  the leaf IN x0; move it to x1 first when x0 must hold an older reg).

## What this proves

encode → invariant layer → decode is now exercised across two ISAs:
the same Realization parameterization emits a *third* observable
witness of the same reduction semantics, and observational equivalence
(not byte-identity — the binaries differ) holds end-to-end under a
foreign ISA + OS ABI.
