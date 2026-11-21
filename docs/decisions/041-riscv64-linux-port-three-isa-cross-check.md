# 041 — riscv64.linux.lo: third ISA, cross-check closes

`host/isa_riscv64.py` + `host/routines_riscv64_linux_lo.py`, committed `687e385`.
Third ISA (RV64IM) on the same `encode → OperEq → decode/run` chain; fourth host
realization of the reducer.

## What the port cost

- ISA table ~700 lines on `enc_core.interpret`, oracle 42/42 vs
  `llvm-mc -triple=riscv64 -mattr=+m` (M needed for `divu`/`remu` in itoa).
  Two-pass assembler; B-type ±4KB / J-type ±1MB fixups; `("ahi"/"alo", sym)`
  operand kinds for `lui`+`addiw` absolute materialization (all kernel
  constants fit 32 bits).
- Oracle quirk: llvm-mc prints fixup-carrying bytes as `0x63'A'` /
  `0bAAAA0000` — `_encbyte` masks any 'A'-containing token to 0; pass 2
  (object mode, resolved targets) verifies the full bytes.
- Routines ~900 lines, same label graph. No flags: `cmp x,imm` becomes
  `addi t6,imm` + fused `beq/bne/blt/bge/bgeu`. `sp` pairs via
  `sd`/`ld sp,off` ±16B frames; `ra` saved by every non-leaf.
- Asm-generic syscall table shared with aarch64 (63/64/222/93), `ecall`.
- `target_elf64` gained `EM_RISCV = 0xF3` — packer untouched.

## Cross-ISA gate (x86_64 / aarch64+qemu / riscv64+qemu)

Byte-identical stdout, `steps`/`alloc` stderr, and rc on: token battery,
fuse_s variant, fuel→rc2, malformed→rc3, empty→I. 327,675-step tower:
x64 142ms, riscv64+qemu 170ms (~1.2×), aarch64+qemu 245ms (~1.7×) —
riscv64 emulates cheaper under TCG (fewer flag side-effects to model).

## Standing lessons

- WSL: files for qemu tests must live under `/mnt/c/...` or WSL-side paths
  that actually exist; Python `os.makedirs('/tmp/x')` on Windows lands on
  `C:\tmp`. Return codes only reliable from script files — `$?` through
  `wsl -- bash -c '...'` gets eaten by quoting layers.
- The routine-shape port is now mechanical: new ISA = table + register map
  + syscall numbers. Realized thrice: x86_64, aarch64, riscv64.

## Next

`.o`/debug-symbol emission, instrumentation layer, `-O3`-style stage opts.
