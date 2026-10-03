<!-- Generated from host/toolchain.json — do not edit. -->

# Emit-target matrix (derived status — never asserted)

| toolchain | dialect | isa | routines | target | path | status |
| --- | --- | --- | --- | --- | --- | --- |
| native.x86_64.pe | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| native.x86_64.pe.ir | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| native.x86_64.pe.ir.mt | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| native.x86_64.fasmg | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| native.x86_64.ir.fasmg | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| native.x86_64.res | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| native.x86_64.res.fasmg | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| xdu.x86_64.pe | ✓ | ✓ | ✓ | ✓ | native | realized |
| isa.aarch64 | ✓ | ✓ | — | ✓ | runtime | declared |
| aarch64.linux.lo | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| riscv64.linux.lo | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| x86_64.linux.o | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| aarch64.linux.o | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| riscv64.linux.o | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| x86_64.win64.cd | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| x86_64.linux.lo | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| x86_64.uefi.lo | ✓ | ✓ | ○ | ○ | runtime | declared |
| elf64 | ✓ | ✓ | ✓ | ✓ | runtime | realized |
| macho64 | ✓ | ✓ | — | ○ | runtime | declared |
| flat | ✓ | ✓ | — | ○ | runtime | declared |
| pe64.uefi | ✓ | ✓ | ○ | ○ | runtime | declared |
| lambda.bracket | — | ✓ | ✓ | ✓ | runtime | declared |
| phi.rel | ○ | ✓ | ✓ | ✓ | runtime | declared |
| native.c | ✓ | ✓ | ✓ | ✓ | runtime | realized |

cell: `✓` realized (module imports), `○` declared (refuses), `—` not a registered component; `status` = the triplet's derived state.

## Gate families × live

| family | obligations | ✓ | ✓* | ✗ | · |
| --- | --- | --- | --- | --- | --- |
| cost | 1 | 1 | 0 | 0 | 0 |
| quotient | 11 | 7 | 0 | 0 | 4 |
| staging | 23 | 6 | 0 | 0 | 17 |

live cells from battery_last.json — `·` = no record (tier/env-gated or not yet run).
