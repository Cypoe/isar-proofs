"""
routines_riscv64_linux_lo — the reducer PROGRAM (asm-as-data) for
ISA=riscv64 (RV64IM), ABI=linux (ecall, no imports), order="lo".

FOURTH host realization, third ISA: the reducer algorithm is the
routines_x86_64_linux_lo / routines_aarch64_linux_lo SHAPE — same
labels, same routine order, same lo semantics — re-encoded against
the riscv64 ISA table (isa_riscv64).  Register map (aarch64 port role
-> riscv):

  x0..x3 args/ret        -> a0..a3     x4..x7 scratch -> a4..a7
  x19 heap bump          -> s1         x20 heap end    -> s2
  x21 term/readbuf       -> s3         x22 step-local f -> s4
  x23 x / parse-stack    -> s5         x24 steps        -> s6
  x25/x26 cursor/end     -> s7/s8      x9..x11 scratch  -> t0..t5
  x8  syscall nr         -> a7         x30 link         -> ra
  t6: immediate-compare scratch (riscv has no flags — "cmp x,imm" is
  li t6,imm + beq/bne).

Host-facing layer: asm-generic syscall numbers (same as aarch64):
read=63 write=64 mmap=222 exit=93, ecall, fds 0/1/2,
mmap(NULL,len,RW,PRIV|ANON,-1,0).  Error = negative a0 -> blt a0,zero.

riscv facts the port absorbs: sp 16-aligned (push/pop helper pairs);
jal ra = call, jalr zero,0(ra) = ret — ra saved by every non-leaf;
64-bit constants materialize lui+addiw ("ahi"/"alo" operand kinds for
absolute symbols); B-type branches reach ±4KB (the whole kernel is
~2KB); div/rem need the M extension (qemu +m).
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, List, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
_SEED_DIR = os.path.normpath(os.path.join(_HOST, "..", "seed"))
for _p in (_HOST, _SEED_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import isa_riscv64 as _isa                       # noqa: E402
from isa_riscv64 import I, LBL, Program, encode  # noqa: E402
from toolchain import NotRealized               # noqa: E402
from seed import Tag, Realization               # noqa: E402

# static image: no imports (the elf64 target refuses any non-empty list)
IMPORTS: Tuple[str, ...] = ()

DATA_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("hin", 8), ("hout", 8), ("herr", 8), ("nread", 8), ("nw", 8),
    ("nalloc", 8), ("ds", 8), ("scratch", 64),
)

# riscv64 linux uses the asm-generic syscall table — same numbers as
# aarch64: read=63 write=64 mmap=222 munmap=215 exit=93
SYS_read, SYS_write, SYS_mmap, SYS_exit = 63, 64, 222, 93
PROT_READ_WRITE = 3                    # PROT_READ|PROT_WRITE
MAP_PRIV_ANON = 0x22                   # MAP_PRIVATE|MAP_ANONYMOUS
FD_IN, FD_OUT, FD_ERR = 0, 1, 2
STK_TAG = 7   # native-internal parse-stack cons cell tag (never a term node)

Ctx = Dict[str, object]


def _ctx() -> Ctx:
    return {}


# ----------------------------------------------------------------------
# emission helpers — the instruction-shape primitives the port uses
# ----------------------------------------------------------------------

def _mv(d: str, s: str) -> Tuple:
    return I("addi", d, s, 0)


def _z(r: str) -> Tuple:
    return I("addi", r, "zero", 0)


def _mov64(d: str, v: int) -> List[Tuple]:
    """d = v.  All kernel constants fit 32 bits: lui hi20' + addiw lo12
    (lo12 sign-extends — the +0x800 in ahi folds the borrow)."""
    v &= (1 << 64) - 1
    if -2048 <= v <= 2047:
        return [I("addi", d, "zero", v)]
    assert v < (1 << 32), f"mov64 {v:#x} needs a lui/slli chain"
    hi = (v + 0x800) >> 12
    lo = v - (hi << 12)
    p = [I("lui", d, hi)]
    if lo:
        p.append(I("addiw", d, d, lo))
    return p


def _adr(d: str, sym: str) -> List[Tuple]:
    """d = &sym (absolute VA) via lui+addiw on ahi/alo symbol halves."""
    return [I("lui", d, ("ahi", sym)), I("addiw", d, d, ("alo", sym))]


def _lds(d: str, sym: str) -> List[Tuple]:
    """d = [sym] — load a data slot (address materialized in t0)."""
    return _adr("t0", sym) + [I("ld", d, "t0", 0)]


def _sts(sym: str, r: str) -> List[Tuple]:
    """[sym] = r — store to a data slot."""
    return _adr("t0", sym) + [I("sd", r, "t0", 0)]


def _incs(sym: str) -> List[Tuple]:
    """[sym] += 1."""
    return _adr("t0", sym) + [
        I("ld", "t1", "t0", 0), I("addi", "t1", "t1", 1),
        I("sd", "t1", "t0", 0)]


def _push(*rs: str) -> List[Tuple]:
    """save regs to a fresh 16B-aligned frame."""
    pad = 16 * ((len(rs) + 1) // 2)
    p = [I("addi", "sp", "sp", -pad)]
    for i, r in enumerate(rs):
        p.append(I("sd", r, "sp", i * 8))
    return p


def _pop(*rs: str) -> List[Tuple]:
    """restore in order, drop the frame."""
    pad = 16 * ((len(rs) + 1) // 2)
    p = [I("ld", r, "sp", i * 8) for i, r in enumerate(rs)]
    return p + [I("addi", "sp", "sp", pad)]


def _sys(nr: int) -> List[Tuple]:
    return [I("addi", "a7", "zero", nr), I("ecall")]


def _jmp(l: str) -> Tuple:
    return I("jal", "zero", ("p", l))


def _call(l: str) -> Tuple:
    return I("jal", "ra", ("p", l))


def _beqz(r: str, l: str) -> Tuple:
    return I("beq", r, "zero", ("p", l))


def _bnez(r: str, l: str) -> Tuple:
    return I("bne", r, "zero", ("p", l))


def _beqi(r: str, imm: int, l: str) -> List[Tuple]:
    """beq r, imm, l — immediate materialized in t6."""
    return [I("addi", "t6", "zero", imm), I("beq", r, "t6", ("p", l))]


# ----------------------------------------------------------------------
# routines — same label graph as routines_x86_64_linux_lo
# ----------------------------------------------------------------------

def r_entry(R: Realization, ctx: Ctx) -> Program:
    """_start: streaming read buffer via mmap (granule, not a cap),
    empty parse stack, first heap chunk, derived_s template (expanded)."""
    p: Program = [
        LBL("_start"),
        I("addi", "sp", "sp", -16), I("sd", "ra", "sp", 0),
        # read buffer: mmap(NULL, read_buf_bytes, RW, PRIV|ANON, -1, 0)
        _z("a0"),
    ]
    p += _mov64("a1", R.read_buf_bytes)
    p += [
        I("addi", "a2", "zero", PROT_READ_WRITE),
        I("addi", "a3", "zero", MAP_PRIV_ANON),
        I("addi", "a4", "zero", -1),      # fd = -1
        _z("a5"),
    ]
    p += _sys(SYS_mmap)
    p += [
        I("blt", "a0", "zero", ("p", "exit4")),
        _mv("s3", "a0"),                  # read buffer base
        _z("s5"),                         # parse stack top
        _call("grow_heap"),
    ]
    if not R.fuse_s:
        # build the shared derived_s template (L0-only tree)
        p += [_call("build_ds")]
    return p


def r_parse(R: Realization, ctx: Ctx) -> Program:
    """read_loop/parse_bytes/p_*: streaming parse, heap-cons bytecode stack,
    Lean underflow rules ([]->[I], [t]->[I,t] on `@`)."""
    p: Program = [
        # ---- streaming parse: read granule -> parse bytes -> repeat ----
        # bytecode stack = heap cons cells {tag=STK_TAG, l=value, r=next}
        LBL("read_loop"),
        _z("a0"),                          # fd 0
        _mv("a1", "s3"),
    ]
    p += _mov64("a2", R.read_buf_bytes)
    p += _sys(SYS_read)
    p += [
        # 0 = EOF; negative = -errno — both end input
        _beqz("a0", "parse_done"),
        I("blt", "a0", "zero", ("p", "parse_done")),
        _mv("s7", "s3"),                   # cursor
        I("add", "s8", "s3", "a0"),        # end
        LBL("parse_bytes"),
        I("bgeu", "s7", "s8", ("p", "read_loop")),
        I("lbu", "a0", "s7", 0),
    ]
    p += _beqi("a0", 0x49, "p_i")          # I
    p += _beqi("a0", 0x4B, "p_k")          # K
    p += _beqi("a0", 0x53, "p_s")          # S
    p += _beqi("a0", 0x42, "p_b")          # B
    p += _beqi("a0", 0x57, "p_w")          # W
    p += _beqi("a0", 0x43, "p_c")          # C
    p += _beqi("a0", 0x40, "p_app")        # @
    p += _beqi("a0", 0x20, "p_next")
    p += _beqi("a0", 0x09, "p_next")
    p += _beqi("a0", 0x0A, "p_next")
    p += _beqi("a0", 0x0D, "p_next")
    p += [
        _jmp("exit3"),
        LBL("p_i"), I("addi", "a2", "zero", Tag.norm),
        _call("mkleaf"), _jmp("p_push"),
        LBL("p_k"), I("addi", "a2", "zero", Tag.konst),
        _call("mkleaf"), _jmp("p_push"),
        LBL("p_b"), I("addi", "a2", "zero", Tag.comp),
        _call("mkleaf"), _jmp("p_push"),
        LBL("p_w"), I("addi", "a2", "zero", Tag.dup),
        _call("mkleaf"), _jmp("p_push"),
        LBL("p_c"), I("addi", "a2", "zero", Tag.swap),
        _call("mkleaf"), _jmp("p_push"),
    ]
    if R.fuse_s:
        p += [
            LBL("p_s"), I("addi", "a2", "zero", Tag.s),
            _call("mkleaf"), _jmp("p_push"),
        ]
    else:
        # view expansion: `S` pushes the shared derived_s root
        p += [LBL("p_s")]
        p += _lds("a0", "ds")
        p += [_jmp("p_push")]
    p += [
        LBL("p_push"),
    ]
    p += _push("ra")
    p += [
        _call("mkstk"),                    # a0 already = leaf ptr
    ]
    p += _pop("ra")
    p += [
        _jmp("p_next"),
        LBL("p_app"),
        # depth >= 2 iff top cell and its next exist
        _beqz("s5", "p_under"),
        I("ld", "t0", "s5", 16),
        _beqz("t0", "p_under"),
        # x = top.l, y = next.l; pop both; push app(y, x)
        I("ld", "a4", "s5", 8),            # x
        I("ld", "a5", "t0", 8),            # y
        I("ld", "s5", "t0", 16),           # stack top = next.next
    ]
    p += _push("ra")
    p += [
        _mv("a0", "a5"), _mv("a1", "a4"),
        _call("mkapp"),                    # a0 = app(y, x)
        _call("mkstk"),
    ]
    p += _pop("ra")
    p += [
        _jmp("p_next"),
        LBL("p_under"),
        # depth 0 or 1 -> push I (Lean underflow: []->[I], [t]->[I,t])
        I("addi", "a2", "zero", Tag.norm),
    ]
    p += _push("ra")
    p += [
        _call("mkleaf"),
        _call("mkstk"),
    ]
    p += _pop("ra")
    p += [
        LBL("p_next"), I("addi", "s7", "s7", 1),
        _jmp("parse_bytes"),
        LBL("parse_done"),
        _beqz("s5", "empty"),
        I("ld", "s3", "s5", 8),
        _jmp("do_reduce"),
        LBL("empty"), I("addi", "a2", "zero", Tag.norm),
    ]
    p += _push("ra")
    p += [
        _call("mkleaf"),
        _mv("s3", "a0"),
    ]
    p += _pop("ra")
    return p


def r_reduce(R: Realization, ctx: Ctx) -> Program:
    """do_reduce/red_loop (+ fuel check when R.fuel) -> count_nodes ->
    exact output mmap -> emit_nf -> write(1, ...) stdout."""
    p: Program = [
        LBL("do_reduce"),
    ]
    p += _push("ra")
    p += [
        _z("s6"),
        LBL("red_loop"),
        _mv("a0", "s3"), _call("step"),
        _beqz("a0", "red_done"),
        _mv("s3", "a0"), I("addi", "s6", "s6", 1),
    ]
    if R.fuel is not None:
        p += [
            I("addi", "t6", "zero", R.fuel),
            I("bge", "s6", "t6", ("p", "exit2")),
        ]
    p += [
        _jmp("red_loop"),
        # ---- out: count nodes, mmap exact, postfix emit, write(1,..) ----
        LBL("red_done"),
        _mv("a0", "s3"), _call("count_nodes"),
        _mv("a1", "a0"), I("add", "a1", "a1", "a1"),
        I("addi", "a1", "a1", 16),
        _z("a0"),
        I("addi", "a2", "zero", PROT_READ_WRITE),
        I("addi", "a3", "zero", MAP_PRIV_ANON),
        I("addi", "a4", "zero", -1), _z("a5"),
    ]
    p += _sys(SYS_mmap)
    p += [
        I("blt", "a0", "zero", ("p", "exit4")),
        _mv("s5", "a0"),                   # out base
        _mv("a1", "a0"),                   # out cursor
        _mv("a0", "s3"), _call("emit_nf"),
        I("addi", "t0", "zero", 0x0A), I("sb", "t0", "a1", 0),
        I("addi", "a1", "a1", 1),
        I("sub", "a2", "a1", "s5"),        # len
        _mv("a1", "s5"),
        I("addi", "a0", "zero", FD_OUT),
    ]
    p += _sys(SYS_write)
    p += _pop("ra")
    return p


def _stats_str(p: Program, s: str) -> None:
    for ch in s:
        p.append(I("addi", "t3", "zero", ord(ch)))
        p.append(I("sb", "t3", "a1", 0))
        p.append(I("addi", "a1", "a1", 1))


def r_stats(R: Realization, ctx: Ctx) -> Program:
    """stderr line `steps=N alloc=M` via scratch buffer + itoa."""
    p: Program = []
    p += _push("ra")
    p += _adr("a1", "scratch")
    _stats_str(p, "steps=")
    p += [
        _mv("a0", "s6"), _call("itoa"),
    ]
    _stats_str(p, " alloc=")
    p += _lds("a0", "nalloc")
    p += [
        _call("itoa"),
        I("addi", "t3", "zero", 0x0A), I("sb", "t3", "a1", 0),
        I("addi", "a1", "a1", 1),
        _mv("a2", "a1"),                   # end
    ]
    p += _adr("a1", "scratch")
    p += [
        I("sub", "a2", "a2", "a1"),        # len
        I("addi", "a0", "zero", FD_ERR),
    ]
    p += _sys(SYS_write)
    p += _pop("ra")
    return p


def r_exits(R: Realization, ctx: Ctx) -> Program:
    """exit 0; exit2 fuel exhausted, exit3 bad input, exit4 OOM."""
    p: Program = [_z("a0")]
    p += _sys(SYS_exit)
    p += [LBL("exit2"), I("addi", "a0", "zero", 2)]
    p += _sys(SYS_exit)
    p += [LBL("exit3"), I("addi", "a0", "zero", 3)]
    p += _sys(SYS_exit)
    p += [LBL("exit4"), I("addi", "a0", "zero", 4)]
    p += _sys(SYS_exit)
    return p


def r_grow_heap(R: Realization, ctx: Ctx) -> Program:
    """grow_heap: s1=bump, s2=chunk end (chunked mmap)."""
    p: Program = [
        LBL("grow_heap"),
    ]
    p += _push("ra")
    p += [_z("a0")]
    p += _mov64("a1", R.chunk_bytes)
    p += [
        I("addi", "a2", "zero", PROT_READ_WRITE),
        I("addi", "a3", "zero", MAP_PRIV_ANON),
        I("addi", "a4", "zero", -1), _z("a5"),
    ]
    p += _sys(SYS_mmap)
    p += [
        I("blt", "a0", "zero", ("p", "grow_fail")),
        _mv("s1", "a0"),
    ]
    p += _mov64("t0", R.chunk_bytes)
    p += [
        I("add", "s2", "a0", "t0"),
    ]
    p += _pop("ra")
    p += [
        I("ret"),
        LBL("grow_fail"), I("addi", "a0", "zero", 4),
    ]
    p += _sys(SYS_exit)
    return p


def r_mkleaf(R: Realization, ctx: Ctx) -> Program:
    """mkleaf: a2=tag -> a0 node (counted in nalloc)."""
    p: Program = [
        LBL("mkleaf"),
        I("addi", "t0", "s1", R.node_bytes),
        I("bgeu", "s2", "t0", ("p", "mkleaf_ok")),
    ]
    p += _push("a2", "ra")
    p += [_call("grow_heap")]
    p += _pop("a2", "ra")
    p += [
        LBL("mkleaf_ok"),
        _mv("a0", "s1"), I("addi", "s1", "s1", R.node_bytes),
        I("sd", "a2", "a0", 0),
        I("sd", "zero", "a0", 8), I("sd", "zero", "a0", 16),
    ]
    p += _incs("nalloc")
    p += [I("ret")]
    return p


def r_mkapp(R: Realization, ctx: Ctx) -> Program:
    """mkapp: a0=f, a1=x -> a0 node (counted in nalloc)."""
    p: Program = [
        LBL("mkapp"),
        I("addi", "t0", "s1", R.node_bytes),
        I("bgeu", "s2", "t0", ("p", "mkapp_ok")),
    ]
    p += _push("a0", "a1", "ra")
    p += [_call("grow_heap")]
    p += _pop("a0", "a1", "ra")
    p += [
        LBL("mkapp_ok"),
        _mv("t0", "s1"), I("addi", "s1", "s1", R.node_bytes),
        I("sd", "zero", "t0", 0),
        I("sd", "a0", "t0", 8), I("sd", "a1", "t0", 16),
        _mv("a0", "t0"),
    ]
    p += _incs("nalloc")
    p += [I("ret")]
    return p


def r_mkstk(R: Realization, ctx: Ctx) -> Program:
    """mkstk: a0=value -> a0 cons cell, s5=new stack top.
    Parse-stack cells share the dynamic heap; NOT counted in nalloc."""
    p: Program = [
        LBL("mkstk"),
        I("addi", "t0", "s1", R.node_bytes),
        I("bgeu", "s2", "t0", ("p", "mkstk_ok")),
    ]
    p += _push("a0", "ra")
    p += [_call("grow_heap")]
    p += _pop("a0", "ra")
    p += [
        LBL("mkstk_ok"),
        _mv("t0", "s1"), I("addi", "s1", "s1", R.node_bytes),
        I("addi", "t1", "zero", STK_TAG),
        I("sd", "t1", "t0", 0),
        I("sd", "a0", "t0", 8), I("sd", "s5", "t0", 16),
        _mv("s5", "t0"), _mv("a0", "t0"), I("ret"),
    ]
    return p


def r_step(R: Realization, ctx: Ctx) -> Program:
    """step(a0=t) -> a0: LO single-step dispatch, Lean IStepBasis order
    (normβ, konstβ, dupβ, compβ, swapβ, [sβ], then congruence).
    Saves ra + the s3..s5 locals it borrows (x86 pushed r12-r14)."""
    p: Program = [
        LBL("step"),
    ]
    p += _push("s3", "s4", "s5", "ra")
    p += [
        _mv("s3", "a0"),
        I("ld", "t0", "s3", 0),
        _bnez("t0", "st_none"),            # tag != APP(0)
        I("ld", "s4", "s3", 8),            # f
        I("ld", "s5", "s3", 16),           # x
        I("ld", "t0", "s4", 0),
    ]
    p += _beqi("t0", Tag.norm, "st_norm")
    p += [
        I("ld", "t0", "s4", 0),
        _bnez("t0", "st_left"),            # f not APP
        I("ld", "a0", "s4", 8),            # fl
        I("ld", "a3", "s4", 16),           # fr
        I("ld", "t0", "a0", 0),
    ]
    p += _beqi("t0", Tag.konst, "st_konst")
    p += [
        I("ld", "t0", "a0", 0),
    ]
    p += _beqi("t0", Tag.dup, "st_dup")
    p += [
        I("ld", "t0", "a0", 0),
        _bnez("t0", "st_left"),            # fl not APP
        I("ld", "a2", "a0", 8),            # fll
        I("ld", "a1", "a0", 16),           # flr
        I("ld", "t0", "a2", 0),
    ]
    p += _beqi("t0", Tag.comp, "st_comp")
    p += [
        I("ld", "t0", "a2", 0),
    ]
    p += _beqi("t0", Tag.swap, "st_swap")
    if R.fuse_s:
        p += [
            I("ld", "t0", "a2", 0),
        ]
        p += _beqi("t0", Tag.s, "st_s")
    p += [
        _jmp("st_left"),
    ]
    return p


def r_st_norm(R: Realization, ctx: Ctx) -> Program:
    """normβ: I x -> x."""
    return [
        LBL("st_norm"), _mv("a0", "s5"),
        _jmp("st_out"),
    ]


def r_st_konst(R: Realization, ctx: Ctx) -> Program:
    """konstβ (fused macro): K x y -> x."""
    return [
        LBL("st_konst"), _mv("a0", "a3"),
        _jmp("st_out"),
    ]


def r_st_dup(R: Realization, ctx: Ctx) -> Program:
    """dupβ: W f x -> f x x."""
    return [
        LBL("st_dup"),                                 # W f x -> f x x
        _mv("a0", "a3"), _mv("a1", "s5"),
        _call("mkapp"),                                # a0 = (f x)
        _mv("a1", "s5"),
        _call("mkapp"),                                # a0 = (f x) x
        _jmp("st_out"),
    ]


def r_st_swap(R: Realization, ctx: Ctx) -> Program:
    """swapβ: C f x y -> f y x."""
    p: Program = [
        LBL("st_swap"),                                # C f x y -> f y x
    ]
    p += _push("a3")                                   # save fr (=x)
    p += [
        _mv("a0", "a1"), _mv("a1", "s5"),
        _call("mkapp"),                                # a0 = (f y)
    ]
    p += _pop("a1")                                    # a1 = fr = x
    p += [
        _call("mkapp"),                                # a0 = (f y) x
        _jmp("st_out"),
    ]
    return p


def r_st_comp(R: Realization, ctx: Ctx) -> Program:
    """compβ: B f g x -> f (g x)."""
    p: Program = [
        LBL("st_comp"),                                # B f g x -> f (g x)
    ]
    p += _push("a1", "a3")                             # [sp]=flr=f, [sp+8]=fr=g
    p += [
        _mv("a0", "a3"), _mv("a1", "s5"),
        _call("mkapp"),                                # a0 = (g x)
        _mv("a1", "a0"),                               # a1 = (g x)
    ]
    p += _pop("a0", "t1")                              # a0 = flr = f
    p += [
        _call("mkapp"),                                # a0 = f (g x)
        _jmp("st_out"),
    ]
    return p


def r_st_s(R: Realization, ctx: Ctx) -> Program:
    """sβ (fuse_s=True only): S f g x -> (f x)(g x)."""
    p: Program = [
        LBL("st_s"),                               # S f g x -> (f x)(g x)
    ]
    p += _push("a1", "a3")                         # [sp]=flr=f, [sp+8]=fr=g
    p += [
        _mv("a0", "a1"), _mv("a1", "s5"),
        _call("mkapp"),                            # a0 = (f x)
    ]
    p += _push("a0")                               # [sp]=(f x)
    p += [
        I("ld", "a0", "sp", 24),                   # fr = g
        _mv("a1", "s5"),
        _call("mkapp"),                            # a0 = (g x)
        _mv("a1", "a0"),                           # a1 = (g x)
    ]
    p += _pop("a0")                                # a0 = (f x)
    p += [
        _call("mkapp"),                            # a0 = (f x)(g x)
    ]
    p += _pop("t1", "t2")                          # drop saved f,g
    p += [
        _jmp("st_out"),
    ]
    return p


def r_step_congr(R: Realization, ctx: Ctx) -> Program:
    """appL/appR congruence + st_none/st_out epilogue."""
    return [
        LBL("st_left"),
        _mv("a0", "s4"), _call("step"),
        _beqz("a0", "st_right"),
        _mv("a1", "s5"),
        _call("mkapp"), _jmp("st_out"),
        LBL("st_right"),
        _mv("a0", "s5"), _call("step"),
        _beqz("a0", "st_none"),
        _mv("a1", "a0"), _mv("a0", "s4"),
        _call("mkapp"), _jmp("st_out"),
        LBL("st_none"), _z("a0"),
        LBL("st_out"),
    ] + _pop("s3", "s4", "s5", "ra") + [
        I("ret"),
    ]


def r_count_nodes(R: Realization, ctx: Ctx) -> Program:
    """count_nodes(a0) -> a0."""
    p: Program = [
        LBL("count_nodes"),
    ]
    p += _push("s3", "s4", "ra")
    p += [
        _mv("s3", "a0"),
        I("ld", "t0", "s3", 0),
        _bnez("t0", "cn_leaf"),
        I("ld", "a0", "s3", 8),
        _call("count_nodes"),
        _mv("s4", "a0"),
        I("ld", "a0", "s3", 16),
        _call("count_nodes"),
        I("add", "a0", "a0", "s4"), I("addi", "a0", "a0", 1),
        _jmp("cn_out"),
        LBL("cn_leaf"), I("addi", "a0", "zero", 1),
        LBL("cn_out"),
    ]
    p += _pop("s3", "s4", "ra")
    p += [I("ret")]
    return p


def r_emit_nf(R: Realization, ctx: Ctx) -> Program:
    """emit_nf(a0=node, a1=cur) -> a1: postfix decompile I K S B W C @."""
    p: Program = [
        LBL("emit_nf"),
        I("ld", "t0", "a0", 0),
        _bnez("t0", "en_leaf"),
    ]
    p += _push("a0", "ra")
    p += [
        I("ld", "a0", "a0", 8),
        _call("emit_nf"),
        I("ld", "a0", "sp", 0),            # saved node
        I("ld", "a0", "a0", 16),
        _call("emit_nf"),
    ]
    p += _pop("t3", "ra")
    p += [
        I("addi", "t3", "zero", 0x40), I("sb", "t3", "a1", 0),
        I("addi", "a1", "a1", 1),
        I("addi", "t3", "zero", 0x20), I("sb", "t3", "a1", 0),
        I("addi", "a1", "a1", 1), I("ret"),
        LBL("en_leaf"),
    ]
    p += _beqi("t0", Tag.norm, "en_i")
    p += _beqi("t0", Tag.konst, "en_k")
    p += _beqi("t0", Tag.s, "en_s")
    p += _beqi("t0", Tag.comp, "en_b")
    p += _beqi("t0", Tag.dup, "en_d")
    p += _beqi("t0", Tag.swap, "en_c")
    p += [
        I("addi", "a2", "zero", 0x3F), _jmp("en_w"),
        LBL("en_i"), I("addi", "a2", "zero", 0x49), _jmp("en_w"),
        LBL("en_k"), I("addi", "a2", "zero", 0x4B), _jmp("en_w"),
        LBL("en_s"), I("addi", "a2", "zero", 0x53), _jmp("en_w"),
        LBL("en_b"), I("addi", "a2", "zero", 0x42), _jmp("en_w"),
        LBL("en_d"), I("addi", "a2", "zero", 0x57), _jmp("en_w"),
        LBL("en_c"), I("addi", "a2", "zero", 0x43),
        LBL("en_w"),
        I("sb", "a2", "a1", 0), I("addi", "a1", "a1", 1),
        I("addi", "t3", "zero", 0x20), I("sb", "t3", "a1", 0),
        I("addi", "a1", "a1", 1), I("ret"),
    ]
    return p


def r_itoa(R: Realization, ctx: Ctx) -> Program:
    """itoa(a0=val, a1=cur) -> a1.  divu/remu digit loop (M ext),
    scratch stack buffer at [sp,#0..32)."""
    return [
        LBL("itoa"),
        I("addi", "sp", "sp", -48),
        _mv("a4", "a0"),                   # val
        I("addi", "a5", "sp", 32),         # buf end
        I("addi", "a6", "zero", 10),
        LBL("it_dig"),
        I("divu", "t4", "a4", "a6"),       # q = val / 10
        I("remu", "t5", "a4", "a6"),       # rem = val % 10
        _mv("a4", "t4"),
        I("addi", "t5", "t5", 0x30),
        I("addi", "a5", "a5", -1), I("sb", "t5", "a5", 0),
        _bnez("a4", "it_dig"),
        LBL("it_cp"),
        I("addi", "a6", "sp", 32),
        I("bgeu", "a5", "a6", ("p", "it_done")),
        I("lbu", "t5", "a5", 0),
        I("sb", "t5", "a1", 0),
        I("addi", "a5", "a5", 1), I("addi", "a1", "a1", 1),
        _jmp("it_cp"),
        LBL("it_done"), I("addi", "sp", "sp", 48), I("ret"),
    ]


def r_build_ds(R: Realization, ctx: Ctx) -> Program:
    """build_ds (default build only): construct DERIVED_S once into [ds];
    s4/s5/s6 scratch (s5 re-zeroed — it is the parse-stack top)."""
    p: Program = [
        LBL("build_ds"),
    ]
    p += _push("ra")
    p += [
        I("addi", "a2", "zero", Tag.comp),
        _call("mkleaf"), _mv("s4", "a0"),
        I("addi", "a2", "zero", Tag.dup),
        _call("mkleaf"),
        _mv("a1", "a0"), _mv("a0", "s4"),
        _call("mkapp"), _mv("s4", "a0"),
        I("addi", "a2", "zero", Tag.comp),
        _call("mkleaf"),
        _mv("a1", "s4"),
        _call("mkapp"), _mv("s4", "a0"),
        I("addi", "a2", "zero", Tag.comp),        # s4 = (B (B D))
        _call("mkleaf"), _mv("s6", "a0"),
        I("addi", "a2", "zero", Tag.comp),
        _call("mkleaf"),
        _mv("a1", "a0"), _mv("a0", "s6"),
        _call("mkapp"), _mv("s6", "a0"),
        I("addi", "a2", "zero", Tag.comp),        # s6 = (B B)
        _call("mkleaf"), _mv("s5", "a0"),
        I("addi", "a2", "zero", Tag.comp),
        _call("mkleaf"),
        _mv("a1", "a0"), _mv("a0", "s5"),
        _call("mkapp"), _mv("s5", "a0"),
        I("addi", "a2", "zero", Tag.swap),        # s5 = (B B)
        _call("mkleaf"),                          # a0 = C
        _mv("a1", "a0"), _mv("a0", "s5"),
        _call("mkapp"), _mv("s5", "a0"),          # s5 = ((B B) C)
        _mv("a0", "s6"), _mv("a1", "s5"),
        _call("mkapp"), _mv("s6", "a0"),          # s6 = ((BB)((BB)C))
        I("addi", "a2", "zero", Tag.swap),
        _call("mkleaf"),                          # a0 = C
        _mv("a1", "s6"),                          # mkapp(C, s6)
        _call("mkapp"), _mv("s6", "a0"),          # s6 = (C X)
        I("addi", "a2", "zero", Tag.norm),
        _call("mkleaf"),                          # a0 = I
        _mv("a1", "a0"), _mv("a0", "s6"),
        _call("mkapp"), _mv("s6", "a0"),          # s6 = ((C X) I)
        _mv("a0", "s4"), _mv("a1", "s6"),
        _call("mkapp"),                           # a0 = derived_s
    ]
    p += _sts("ds", "a0")
    p += [
        _z("s5"),
    ]
    p += _pop("ra")
    p += [I("ret")]
    return p


# Ordered routine names = emission order.  "st_s" emits iff R.fuse_s,
# "build_ds" iff not R.fuse_s (handled in program()).
ROUTINES: Tuple[str, ...] = (
    "entry", "parse", "reduce", "stats", "exits",
    "grow_heap", "mkleaf", "mkapp", "mkstk",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

_BUILDERS: Dict[str, Callable[[Realization, Ctx], Program]] = {
    name[2:]: fn for name, fn in list(globals().items())
    if name.startswith("r_")
}


def program(R: Realization) -> Program:
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    if R.abi != "linux":
        raise NotRealized(f"abi={R.abi!r} declared but not realized")
    ctx = _ctx()
    p: Program = []
    for name in ROUTINES:
        if name == "st_s" and not R.fuse_s:
            continue
        if name == "build_ds" and R.fuse_s:
            continue
        p += _BUILDERS[name](R, ctx)
    return p


@dataclass(frozen=True)
class Routines:
    name: str          # "riscv64.linux.lo"
    isa: str           # "riscv64"
    abi: str           # "linux"
    orders: tuple
    routines: tuple    # ROUTINES
    program: Callable  # program(R) -> Program
    imports: tuple     # () — static image, no IAT
    data_slots: tuple


RISCV64_LINUX_LO = Routines(
    name="riscv64.linux.lo",
    isa="riscv64",
    abi="linux",
    orders=("lo",),
    routines=ROUTINES,
    program=program,
    imports=IMPORTS,
    data_slots=DATA_SLOTS,
)


def _dummy_symbols() -> Dict[str, int]:
    import target_elf64
    return target_elf64.symbols(IMPORTS, DATA_SLOTS)


def _routine_sizes(R: Realization) -> Dict[str, int]:
    ctx = _ctx()
    out: Dict[str, int] = {}
    for name in ROUTINES:
        if name == "st_s" and not R.fuse_s:
            continue
        if name == "build_ds" and R.fuse_s:
            continue
        frag = _BUILDERS[name](R, ctx)
        out[name] = sum(len(encode(i[1:])) for i in frag if i[0] != "label")
    return out


def main() -> int:
    ok = True
    for tag, R in (("default", Realization(abi="linux")),
                   ("fuse_s", Realization(abi="linux", fuse_s=True))):
        prog = program(R)
        text, labels = _isa.assemble(prog, _dummy_symbols(),
                                     base=0x4000B0)
        sizes = _routine_sizes(R)
        print(f"  {tag}: {len(text)}B text, routines "
              + " ".join(f"{n}={s}" for n, s in sizes.items()))
        has_ds, has_s = "build_ds" in labels, "st_s" in labels
        if has_ds != (not R.fuse_s) or has_s != R.fuse_s:
            print(f"  FAIL {tag}: build_ds={has_ds} st_s={has_s}")
            ok = False
    for bad in (Realization(order="cd", abi="linux"),
                Realization(abi="win64")):
        try:
            program(bad)
            print(f"  FAIL program({bad!r}) built silently")
            ok = False
        except NotRealized as e:
            print(f"  ok refused: {e}")
    print(f"{'OK' if ok else 'FAIL'} routines_riscv64_linux_lo")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
