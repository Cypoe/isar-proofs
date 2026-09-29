<!-- Generated from host/toolchain.json — do not edit. -->

# Catalog (derived status — never asserted)

## Components

| component | name | module.record | status | note |
| --- | --- | --- | --- | --- |
| dialect | bytecode.postfix | bytecode_dialect.bytecode_map | realized |  |
| dialect | lambda.named | lambda_dialect.lambda_turner_map | realized | host QuotientMap exists; no native token alphabet |
| dialect | xdu.json | xdu_dialect.XDU | realized | nibble transducer plex (W3) |
| dialect | phi.rel | — | declared | spec only |
| dialect | packed.ir | spec_term.ir_map | realized | ADR-005 canonical packed-IR node stream (multi-root batch); the exe-seam transport |
| isa | x86_64 | isa_x86_64.X86_64 | realized |  |
| isa | aarch64 | isa_aarch64.AARCH64 | realized |  |
| isa | riscv64 | isa_riscv64.RISCV64 | realized |  |
| isa | c | isa_c.C_ISA | realized | C11 statements as data; assemble emits source text |
| isa | x86_64.fasmg | isa_fasmg.FASMG_X86_64 | realized | x86-64 insn items rendered as fasmg source; resolution stays symbolic, fasmg does fixups |
| routines | x86_64.win64.lo | routines_x86_64_win64.X86_64_WIN64 | realized |  |
| routines | x86_64.win64.xdu | routines_x86_64_win64_xdu.X86_64_WIN64_XDU | realized | nibble transducer plex routines (W3) |
| routines | x86_64.win64.cd | routines_x86_64_win64_cd.X86_64_WIN64_CD | realized | Lean ParStep / host reduce_cd contract |
| routines | x86_64.linux.lo | routines_x86_64_linux_lo.X86_64_LINUX_LO | realized | syscall ABI, no kernel32 IAT |
| routines | aarch64.linux.lo | routines_aarch64_linux_lo.AARCH64_LINUX_LO | realized | aarch64 svc ABI port of x86_64.linux.lo — same label graph |
| routines | riscv64.linux.lo | routines_riscv64_linux_lo.RISCV64_LINUX_LO | realized | RV64IM ecall ABI port of x86_64.linux.lo — same label graph |
| routines | x86_64.uefi.lo | — | declared | UEFI boot services ABI |
| routines | c.hosted.lo | routines_c.C_HOSTED_LO | realized | C reducer kernel — the second host (IStepBasis, hosted) |
| routines | x86_64.win64.ir | routines_x86_64_win64.X86_64_WIN64_IR | realized | packed-IR batch front end (depack replaces token parse; per-root arena reset) |
| routines | x86_64.win64.res | routines_x86_64_win64.X86_64_WIN64_RES | realized | residual-application kernel: packed residual in .data, per-root graft + reduce |
| target | pe64 | target_pe64.PE64 | realized |  |
| target | elf64 | target_elf64.ELF64 | realized | ELF64 container writer |
| target | elf64.aarch64 | target_elf64.ELF64_AARCH64 | realized | same static ELF64 container, e_machine=EM_AARCH64 |
| target | elf64.riscv64 | target_elf64.ELF64_RISCV64 | realized | same static ELF64 container, e_machine=EM_RISCV |
| target | elfo64 | target_elf64.ELFO64 | realized | ET_REL symbolized object — .text/.data/.symtab/.rela.text |
| target | elfo64.aarch64 | target_elf64.ELFO64_AARCH64 | realized | ET_REL, e_machine=EM_AARCH64, MOVW_UABS_G0/G1 relocs |
| target | elfo64.riscv64 | target_elf64.ELFO64_RISCV64 | realized | ET_REL, e_machine=EM_RISCV, HI20/LO12_I relocs |
| target | macho64 | — | declared | Mach-O 64 container writer |
| target | flat | — | declared | flat binary, no loader |
| target | pe64.uefi | — | declared | PE32+ EFI application subsystem |
| target | c | target_c.C | realized | C11 source container; compiles via system cc |
| target | fasmg.pe64 | target_fasmg.FASMG_PE64 | realized | PE64 source container for fasmg (format PE64 + manual .idata); compile() runs fasmg.exe |
| piece | graph.lo | host_pieces.GRAPH_PIECE | realized |  |
| piece | graph.cd | host_pieces.GRAPH_CD_PIECE | realized |  |
| piece | lambda.lstep | lambda_eval.LSTEP_PIECE | realized | weak-beta NExpr evaluator (Lean LStep mirror) + saturated combs |
| regime | operEq | observation_regime.oper_eq_regime | realized |  |
| regime | stdout+rc | xdu_dialect.stdout_rc_regime | realized | declared (W3) |
| regime | stdout+stderr+rc | — | declared | NF on stdout + steps/alloc[/rules] stats line on stderr + exit code |
| regime | bytes | — | declared | byte-exact equality of two construction routes (seam) |
| regime | syscall-trace | — | declared | declared |

## Toolchains

| name | dialect | isa | routines | target | path | status |
| --- | --- | --- | --- | --- | --- | --- |
| native.x86_64.pe | bytecode.postfix | x86_64 | x86_64.win64.lo | pe64 | runtime | realized |
| native.x86_64.pe.ir | packed.ir | x86_64 | x86_64.win64.ir | pe64 | runtime | realized |
| native.x86_64.fasmg | bytecode.postfix | x86_64.fasmg | x86_64.win64.lo | fasmg.pe64 | runtime | realized |
| native.x86_64.ir.fasmg | packed.ir | x86_64.fasmg | x86_64.win64.ir | fasmg.pe64 | runtime | realized |
| native.x86_64.res | packed.ir | x86_64 | x86_64.win64.res | pe64 | runtime | realized |
| native.x86_64.res.fasmg | packed.ir | x86_64.fasmg | x86_64.win64.res | fasmg.pe64 | runtime | realized |
| xdu.x86_64.pe | xdu.json | x86_64 | x86_64.win64.xdu | pe64 | native | realized |
| isa.aarch64 | bytecode.postfix | aarch64 | aarch64.win64.lo | pe64 | runtime | declared |
| aarch64.linux.lo | bytecode.postfix | aarch64 | aarch64.linux.lo | elf64.aarch64 | runtime | realized |
| riscv64.linux.lo | bytecode.postfix | riscv64 | riscv64.linux.lo | elf64.riscv64 | runtime | realized |
| x86_64.linux.o | bytecode.postfix | x86_64 | x86_64.linux.lo | elfo64 | runtime | realized |
| aarch64.linux.o | bytecode.postfix | aarch64 | aarch64.linux.lo | elfo64.aarch64 | runtime | realized |
| riscv64.linux.o | bytecode.postfix | riscv64 | riscv64.linux.lo | elfo64.riscv64 | runtime | realized |
| x86_64.win64.cd | bytecode.postfix | x86_64 | x86_64.win64.cd | pe64 | runtime | realized |
| x86_64.linux.lo | bytecode.postfix | x86_64 | x86_64.linux.lo | elf64 | runtime | realized |
| x86_64.uefi.lo | bytecode.postfix | x86_64 | x86_64.uefi.lo | pe64.uefi | runtime | declared |
| elf64 | bytecode.postfix | x86_64 | x86_64.linux.lo | elf64 | runtime | realized |
| macho64 | bytecode.postfix | x86_64 | x86_64.macho.lo | macho64 | runtime | declared |
| flat | bytecode.postfix | x86_64 | x86_64.baremetal.lo | flat | runtime | declared |
| pe64.uefi | bytecode.postfix | x86_64 | x86_64.uefi.lo | pe64.uefi | runtime | declared |
| lambda.bracket | lambda.bracket | x86_64 | x86_64.win64.lo | pe64 | runtime | declared |
| phi.rel | phi.rel | x86_64 | x86_64.win64.lo | pe64 | runtime | declared |
| native.c | bytecode.postfix | c | c.hosted.lo | c | runtime | realized |

## Strategy axes

- **order**: lo=realized, cd=realized
- **abi**: win64=realized, linux=realized, uefi=declared
- **fuse_s**: False=realized, True=realized
- **alloc**: bump-chunked=realized, arena=declared
- **reclaim**: none=realized, refcount=declared, mark-sweep=declared
- **stack**: machine=realized, explicit=declared
- **io**: stdin/stdout=realized, memory=declared
- **fuel**: None=realized, int=realized
- **peephole**: False=realized — default, both routes, True=realized — seed route only; staged chain NotRealized (no peepholeOf stage)
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
- pieces: graph.lo, graph.cd, native.x86_64.pe, native.x86_64.pe.fuse_s, native.x86_64.pe.ir
