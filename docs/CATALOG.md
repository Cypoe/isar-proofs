<!-- Generated from host/toolchain.json — do not edit. -->

# Catalog (derived status — never asserted)

## Components

| component | name | module.record | status | note |
| --- | --- | --- | --- | --- |
| dialect | bytecode.postfix | bytecode_dialect.bytecode_map | realized |  |
| dialect | lambda.named | lambda_dialect.lambda_turner_map | realized | host QuotientMap exists; no native token alphabet |
| dialect | xdu.json | xdu_dialect.XDU | realized | nibble transducer plex (W3) |
| dialect | phi.rel | — | declared | spec only |
| isa | x86_64 | isa_x86_64.X86_64 | realized |  |
| isa | aarch64 | isa_aarch64.AARCH64 | realized |  |
| isa | riscv64 | — | declared | no riscv64 ISA table |
| routines | x86_64.win64.lo | routines_x86_64_win64.X86_64_WIN64 | realized |  |
| routines | x86_64.win64.xdu | routines_x86_64_win64_xdu.X86_64_WIN64_XDU | realized | nibble transducer plex routines (W3) |
| routines | x86_64.win64.cd | routines_x86_64_win64_cd.X86_64_WIN64_CD | realized | Lean ParStep / host reduce_cd contract |
| routines | x86_64.linux.lo | routines_x86_64_linux_lo.X86_64_LINUX_LO | realized | syscall ABI, no kernel32 IAT |
| routines | x86_64.uefi.lo | — | declared | UEFI boot services ABI |
| target | pe64 | target_pe64.PE64 | realized |  |
| target | elf64 | target_elf64.ELF64 | realized | ELF64 container writer |
| target | macho64 | — | declared | Mach-O 64 container writer |
| target | flat | — | declared | flat binary, no loader |
| target | pe64.uefi | — | declared | PE32+ EFI application subsystem |
| piece | graph.lo | host_pieces.GRAPH_PIECE | realized |  |
| piece | graph.cd | host_pieces.GRAPH_CD_PIECE | realized |  |
| piece | lambda.lstep | lambda_eval.LSTEP_PIECE | realized | weak-beta NExpr evaluator (Lean LStep mirror) + saturated combs |
| regime | operEq | observation_regime.oper_eq_regime | realized |  |
| regime | stdout+rc | xdu_dialect.stdout_rc_regime | realized | declared (W3) |
| regime | syscall-trace | — | declared | declared |

## Toolchains

| name | dialect | isa | routines | target | path | status |
| --- | --- | --- | --- | --- | --- | --- |
| native.x86_64.pe | bytecode.postfix | x86_64 | x86_64.win64.lo | pe64 | runtime | realized |
| xdu.x86_64.pe | xdu.json | x86_64 | x86_64.win64.xdu | pe64 | native | realized |
| isa.aarch64 | bytecode.postfix | aarch64 | aarch64.win64.lo | pe64 | runtime | declared |
| isa.riscv64 | bytecode.postfix | riscv64 | riscv64.linux.lo | elf64 | runtime | declared |
| x86_64.win64.cd | bytecode.postfix | x86_64 | x86_64.win64.cd | pe64 | runtime | realized |
| x86_64.linux.lo | bytecode.postfix | x86_64 | x86_64.linux.lo | elf64 | runtime | realized |
| x86_64.uefi.lo | bytecode.postfix | x86_64 | x86_64.uefi.lo | pe64.uefi | runtime | declared |
| elf64 | bytecode.postfix | x86_64 | x86_64.linux.lo | elf64 | runtime | realized |
| macho64 | bytecode.postfix | x86_64 | x86_64.macho.lo | macho64 | runtime | declared |
| flat | bytecode.postfix | x86_64 | x86_64.baremetal.lo | flat | runtime | declared |
| pe64.uefi | bytecode.postfix | x86_64 | x86_64.uefi.lo | pe64.uefi | runtime | declared |
| lambda.bracket | lambda.bracket | x86_64 | x86_64.win64.lo | pe64 | runtime | declared |
| phi.rel | phi.rel | x86_64 | x86_64.win64.lo | pe64 | runtime | declared |

## Strategy axes

- **order**: lo=realized, cd=realized
- **abi**: win64=realized, linux=realized, uefi=declared
- **fuse_s**: False=realized, True=realized
- **alloc**: bump-chunked=realized, arena=declared
- **reclaim**: none=realized, refcount=declared, mark-sweep=declared
- **stack**: machine=realized, explicit=declared
- **io**: stdin/stdout=realized, memory=declared
- **fuel**: None=realized, int=realized
- **geometry**: chunk_bytes, stack_reserve, read_buf_bytes, node_bytes

## Paths

### native
- meaning: program behaviour compiled to code; no reducer, no tags in the image
- input: bytes (program-declared parser)
- regime: stdout+rc
- covers: xdu.json
- uncovered: bytecode.postfix, lambda.named, counting (unbounded state), byte alphabet (256-way dispatch)

### runtime
- meaning: term reduced live by a host piece
- regime: operEq NF
- pieces: graph.lo, graph.cd, native.x86_64.pe, native.x86_64.pe.fuse_s
