"""
routines_aarch64_linux_lo — the reducer PROGRAM (asm-as-data) for
ISA=aarch64, ABI=linux (svc syscall, no imports), order="lo".

THIRD host realization, second ISA: the reducer algorithm is the
routines_x86_64_linux_lo SHAPE — same labels, same routine order, same
lo semantics — re-encoded against the aarch64 ISA table (isa_aarch64).
The cross-ISA claim under test: identical NF/stats/rc output under
qemu-aarch64 is the encode -> invariant -> decode round-trip made
honest.  Register map (x86 role -> aarch64):

  rax/rdi/rsi/rdx/rcx  -> x0..x3   (args + return; our own convention)
  rbx (heap bump)      -> x19      rbp (heap end)       -> x20
  r12 (term/readbuf)   -> x21      r13                  -> x22
  r14 (parse stack)    -> x23      r15 (steps)          -> x24
  r8..r11 scratch      -> x4..x7, x9..x11
  x25/x26              -> parse cursor/end (callee-saved)
  x8 = syscall nr; x30 = link register (saved by every non-leaf).

Host-facing layer: kernel32 IAT -> raw svc; read=63 write=64 mmap=222
munmap=215 exit=93, fds 0/1/2, mmap(NULL,len,RW,PRIV|ANON,-1,0).
Syscall error = negative x0 (ands xzr,x0,x0 -> N -> b.mi), uniform.

aarch64 facts the port absorbs: sp must stay 16-aligned (frames are
multiples of 16, x86's +8 align slots become paired str slots); bl
clobbers x30 so every non-leaf routine saves it; 64-bit constants are
movz/movk pairs ("alo"/"ahi" operand kinds resolve absolute symbols);
cmp/tst are subs/ands with rd=xzr; there is no push/pop — stack
traffic is sub sp + str offsets.
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

import isa_aarch64 as _isa                       # noqa: E402
from isa_aarch64 import I, LBL, Program, encode  # noqa: E402
from toolchain import NotRealized               # noqa: E402
from seed import Tag, Realization               # noqa: E402

# static image: no imports (the elf64 target refuses any non-empty list)
IMPORTS: Tuple[str, ...] = ()

# audit counters: cumulative per-process redex-class histogram —
# incremented only when Realization.audit (dead .data otherwise).
AUDIT_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("c_norm", 8), ("c_konst", 8), ("c_dup", 8), ("c_swap", 8),
    ("c_comp", 8), ("c_s", 8), ("c_left", 8), ("c_right", 8),
)
DATA_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("hin", 8), ("hout", 8), ("herr", 8), ("nread", 8), ("nw", 8),
    ("nalloc", 8), ("ds", 8), ("scratch", 64),
) + AUDIT_SLOTS

# aarch64 linux syscall numbers
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

def _z(r: str) -> Tuple:
    """zero: mov xd, xzr"""
    return I("mov_reg", r, "xzr")


def _mov64(d: str, v: int) -> List[Tuple]:
    """xd = v (64-bit): movz lo16 then movk for each nonzero half."""
    v &= (1 << 64) - 1
    p = [I("movz", d, v & 0xFFFF)]
    for sh in (16, 32, 48):
        h = (v >> sh) & 0xFFFF
        if h:
            p.append(I("movk", d, h, sh))
    return p


def _adr(d: str, sym: str) -> List[Tuple]:
    """xd = &sym (absolute VA — data slots / labels via alo/ahi ops)."""
    return [I("movz", d, ("alo", sym)), I("movk", d, ("ahi", sym), 16)]


def _lds(d: str, sym: str) -> List[Tuple]:
    """xd = [sym] — load a data slot (address materialized in x9)."""
    return _adr("x9", sym) + [I("ldr_uoff", d, "x9", 0)]


def _sts(sym: str, r: str) -> List[Tuple]:
    """[sym] = r — store to a data slot."""
    return _adr("x9", sym) + [I("str_uoff", r, "x9", 0)]


def _incs(sym: str) -> List[Tuple]:
    """[sym] += 1 (inc_mrip)."""
    return _adr("x9", sym) + [
        I("ldr_uoff", "x10", "x9", 0), I("add_imm", "x10", "x10", 1),
        I("str_uoff", "x10", "x9", 0)]


def _push(*rs: str) -> List[Tuple]:
    """save regs to a fresh 16B-aligned frame."""
    pad = 16 * ((len(rs) + 1) // 2)
    p = [I("sub_imm", "sp", "sp", pad)]
    for i, r in enumerate(rs):
        p.append(I("str_uoff", r, "sp", i * 8))
    return p


def _pop(*rs: str) -> List[Tuple]:
    """restore in order, drop the frame."""
    pad = 16 * ((len(rs) + 1) // 2)
    p = [I("ldr_uoff", r, "sp", i * 8) for i, r in enumerate(rs)]
    return p + [I("add_imm", "sp", "sp", pad)]


def _sys(nr: int) -> List[Tuple]:
    return [I("movz", "x8", nr), I("svc_imm16", 0)]


def _cmp(rn: str, rm) -> Tuple:
    """flags = rn - rm (reg or imm): subs xzr, rn, rm."""
    if isinstance(rm, str):
        return I("subs_reg", "xzr", rn, rm)
    return I("subs_imm", "xzr", rn, rm)


def _tst(rn: str) -> Tuple:
    """flags = rn & rn — zero/sign check."""
    return I("ands_reg", "xzr", rn, rn)


# ----------------------------------------------------------------------
# routines — same label graph as routines_x86_64_linux_lo
# ----------------------------------------------------------------------

def r_entry(R: Realization, ctx: Ctx) -> Program:
    """_start: streaming read buffer via mmap (granule, not a cap),
    empty parse stack, first heap chunk, derived_s template (expanded)."""
    p: Program = [
        LBL("_start"),
        I("sub_imm", "sp", "sp", 16), I("str_uoff", "x30", "sp", 0),
        # read buffer: mmap(NULL, read_buf_bytes, RW, PRIV|ANON, -1, 0)
        _z("x0"),
    ]
    p += _mov64("x1", R.read_buf_bytes)
    p += [
        I("movz", "x2", PROT_READ_WRITE), I("movz", "x3", MAP_PRIV_ANON),
        I("movn", "x4", 0),               # fd = -1
        _z("x5"),
    ]
    p += _sys(SYS_mmap)
    p += [
        _tst("x0"), I("bcond_rel", "mi", ("p", "exit4")),
        I("mov_reg", "x21", "x0"),        # read buffer base
        _z("x23"),                        # parse stack top
        I("bl_rel", ("p", "grow_heap")),
    ]
    if not R.fuse_s:
        # build the shared derived_s template (L0-only tree)
        p += [I("bl_rel", ("p", "build_ds"))]
    return p


def r_parse(R: Realization, ctx: Ctx) -> Program:
    """read_loop/parse_bytes/p_*: streaming parse, heap-cons bytecode stack,
    Lean underflow rules ([]->[I], [t]->[I,t] on `@`)."""
    p: Program = [
        # ---- streaming parse: read granule -> parse bytes -> repeat ----
        # bytecode stack = heap cons cells {tag=STK_TAG, l=value, r=next}
        LBL("read_loop"),
        _z("x0"),                          # fd 0
        I("mov_reg", "x1", "x21"),
    ]
    p += _mov64("x2", R.read_buf_bytes)
    p += _sys(SYS_read)
    p += [
        # 0 = EOF; negative = -errno — both end input, like win64's
        # ReadFile FALSE (ERROR_BROKEN_PIPE) -> parse_done
        I("cbz_rel", "x0", ("p", "parse_done")),
        _tst("x0"), I("bcond_rel", "mi", ("p", "parse_done")),
        I("mov_reg", "x25", "x21"),        # cursor
        I("add_reg", "x26", "x21", "x0"),  # end
        LBL("parse_bytes"),
        _cmp("x25", "x26"), I("bcond_rel", "ge", ("p", "read_loop")),
        I("ldrb_uoff", "w0", "x25", 0),
        _cmp("x0", 0x49), I("bcond_rel", "eq", ("p", "p_i")),
        _cmp("x0", 0x4B), I("bcond_rel", "eq", ("p", "p_k")),
        _cmp("x0", 0x53), I("bcond_rel", "eq", ("p", "p_s")),
        _cmp("x0", 0x42), I("bcond_rel", "eq", ("p", "p_b")),
        _cmp("x0", 0x57), I("bcond_rel", "eq", ("p", "p_w")),
        _cmp("x0", 0x43), I("bcond_rel", "eq", ("p", "p_c")),
        _cmp("x0", 0x40), I("bcond_rel", "eq", ("p", "p_app")),
        _cmp("x0", 0x20), I("bcond_rel", "eq", ("p", "p_next")),
        _cmp("x0", 0x09), I("bcond_rel", "eq", ("p", "p_next")),
        _cmp("x0", 0x0A), I("bcond_rel", "eq", ("p", "p_next")),
        _cmp("x0", 0x0D), I("bcond_rel", "eq", ("p", "p_next")),
        I("b_rel", ("p", "exit3")),
        LBL("p_i"), I("movz", "x2", Tag.norm),
        I("bl_rel", ("p", "mkleaf")), I("b_rel", ("p", "p_push")),
        LBL("p_k"), I("movz", "x2", Tag.konst),
        I("bl_rel", ("p", "mkleaf")), I("b_rel", ("p", "p_push")),
        LBL("p_b"), I("movz", "x2", Tag.comp),
        I("bl_rel", ("p", "mkleaf")), I("b_rel", ("p", "p_push")),
        LBL("p_w"), I("movz", "x2", Tag.dup),
        I("bl_rel", ("p", "mkleaf")), I("b_rel", ("p", "p_push")),
        LBL("p_c"), I("movz", "x2", Tag.swap),
        I("bl_rel", ("p", "mkleaf")), I("b_rel", ("p", "p_push")),
    ]
    if R.fuse_s:
        p += [
            LBL("p_s"), I("movz", "x2", Tag.s),
            I("bl_rel", ("p", "mkleaf")), I("b_rel", ("p", "p_push")),
        ]
    else:
        # view expansion: `S` pushes the shared derived_s root
        p += [LBL("p_s")]
        p += _lds("x0", "ds")
        p += [I("b_rel", ("p", "p_push"))]
    p += [
        LBL("p_push"),
    ]
    p += _push("x30")
    p += [
        I("bl_rel", ("p", "mkstk")),       # x0 already = leaf ptr
    ]
    p += _pop("x30")
    p += [
        I("b_rel", ("p", "p_next")),
        LBL("p_app"),
        # depth >= 2 iff top cell and its next exist
        I("cbz_rel", "x23", ("p", "p_under")),
        I("ldr_uoff", "x9", "x23", 16),
        I("cbz_rel", "x9", ("p", "p_under")),
        # x = top.l, y = next.l; pop both; push app(y, x)
        I("ldr_uoff", "x4", "x23", 8),     # x
        I("ldr_uoff", "x5", "x9", 8),      # y
        I("ldr_uoff", "x23", "x9", 16),    # stack top = next.next
    ]
    p += _push("x30")
    p += [
        I("mov_reg", "x0", "x5"), I("mov_reg", "x1", "x4"),
        I("bl_rel", ("p", "mkapp")),       # x0 = app(y, x)
        I("bl_rel", ("p", "mkstk")),
    ]
    p += _pop("x30")
    p += [
        I("b_rel", ("p", "p_next")),
        LBL("p_under"),
        # depth 0 or 1 -> push I (Lean underflow: []->[I], [t]->[I,t])
        I("movz", "x2", Tag.norm),
    ]
    p += _push("x30")
    p += [
        I("bl_rel", ("p", "mkleaf")),
        I("bl_rel", ("p", "mkstk")),
    ]
    p += _pop("x30")
    p += [
        LBL("p_next"), I("add_imm", "x25", "x25", 1),
        I("b_rel", ("p", "parse_bytes")),
        LBL("parse_done"),
        I("cbz_rel", "x23", ("p", "empty")),
        I("ldr_uoff", "x21", "x23", 8),
        I("b_rel", ("p", "do_reduce")),
        LBL("empty"), I("movz", "x2", Tag.norm),
    ]
    p += _push("x30")
    p += [
        I("bl_rel", ("p", "mkleaf")),
        I("mov_reg", "x21", "x0"),
    ]
    p += _pop("x30")
    return p


def r_reduce(R: Realization, ctx: Ctx) -> Program:
    """do_reduce/red_loop (+ fuel check when R.fuel) -> count_nodes ->
    exact output mmap -> emit_nf -> write(1, ...) stdout."""
    p: Program = [
        LBL("do_reduce"),
    ]
    p += _push("x30")
    p += [
        _z("x24"),
        LBL("red_loop"),
        I("mov_reg", "x0", "x21"), I("bl_rel", ("p", "step")),
        I("cbz_rel", "x0", ("p", "red_done")),
        I("mov_reg", "x21", "x0"), I("add_imm", "x24", "x24", 1),
    ]
    if R.fuel is not None:
        p += [
            _cmp("x24", R.fuel), I("bcond_rel", "ge", ("p", "exit2")),
        ]
    p += [
        I("b_rel", ("p", "red_loop")),
        # ---- out: count nodes, mmap exact, postfix emit, write(1,..) ----
        LBL("red_done"),
        I("mov_reg", "x0", "x21"), I("bl_rel", ("p", "count_nodes")),
        I("mov_reg", "x1", "x0"), I("add_reg", "x1", "x1", "x1"),
        I("add_imm", "x1", "x1", 16),
        _z("x0"),
        I("movz", "x2", PROT_READ_WRITE), I("movz", "x3", MAP_PRIV_ANON),
        I("movn", "x4", 0), _z("x5"),
    ]
    p += _sys(SYS_mmap)
    p += [
        _tst("x0"), I("bcond_rel", "mi", ("p", "exit4")),
        I("mov_reg", "x23", "x0"),         # out base
        I("mov_reg", "x1", "x0"),          # out cursor
        I("mov_reg", "x0", "x21"), I("bl_rel", ("p", "emit_nf")),
        I("movz", "w9", 0x0A), I("strb_uoff", "w9", "x1", 0),
        I("add_imm", "x1", "x1", 1),
        I("sub_reg", "x2", "x1", "x23"),   # len
        I("mov_reg", "x1", "x23"),
        I("movz", "x0", FD_OUT),
    ]
    p += _sys(SYS_write)
    p += _pop("x30")
    return p


def _stats_str(p: Program, s: str) -> None:
    for ch in s:
        p.append(I("movz", "w9", ord(ch)))
        p.append(I("strb_uoff", "w9", "x1", 0))
        p.append(I("add_imm", "x1", "x1", 1))


def r_stats(R: Realization, ctx: Ctx) -> Program:
    """stderr line `steps=N alloc=M` via scratch buffer + itoa."""
    p: Program = []
    p += _push("x30")
    p += _adr("x1", "scratch")
    _stats_str(p, "steps=")
    p += [
        I("mov_reg", "x0", "x24"), I("bl_rel", ("p", "itoa")),
    ]
    _stats_str(p, " alloc=")
    p += _lds("x0", "nalloc")
    p += [
        I("bl_rel", ("p", "itoa")),
    ]
    if R.audit:
        _stats_str(p, " rules=I:")
        p += _lds("x0", "c_norm")
        p += [I("bl_rel", ("p", "itoa"))]
        for tag, slot in (("K:", "c_konst"), ("W:", "c_dup"), ("C:", "c_swap"),
                          ("B:", "c_comp"), ("S:", "c_s"),
                          ("L:", "c_left"), ("R:", "c_right")):
            _stats_str(p, "," + tag)
            p += _lds("x0", slot)
            p += [I("bl_rel", ("p", "itoa"))]
    p += [
        I("movz", "w9", 0x0A), I("strb_uoff", "w9", "x1", 0),
        I("add_imm", "x1", "x1", 1),
        I("mov_reg", "x2", "x1"),          # end
    ]
    p += _adr("x1", "scratch")
    p += [
        I("sub_reg", "x2", "x2", "x1"),    # len
        I("movz", "x0", FD_ERR),
    ]
    p += _sys(SYS_write)
    p += _pop("x30")
    return p


def r_exits(R: Realization, ctx: Ctx) -> Program:
    """exit 0; exit2 fuel exhausted, exit3 bad input, exit4 OOM."""
    p: Program = [_z("x0")]
    p += _sys(SYS_exit)
    p += [LBL("exit2"), I("movz", "x0", 2)]
    p += _sys(SYS_exit)
    p += [LBL("exit3"), I("movz", "x0", 3)]
    p += _sys(SYS_exit)
    p += [LBL("exit4"), I("movz", "x0", 4)]
    p += _sys(SYS_exit)
    return p


def r_grow_heap(R: Realization, ctx: Ctx) -> Program:
    """grow_heap: x19=bump, x20=chunk end (chunked mmap)."""
    p: Program = [
        LBL("grow_heap"),
    ]
    p += _push("x30")
    p += [_z("x0")]
    p += _mov64("x1", R.chunk_bytes)
    p += [
        I("movz", "x2", PROT_READ_WRITE), I("movz", "x3", MAP_PRIV_ANON),
        I("movn", "x4", 0), _z("x5"),
    ]
    p += _sys(SYS_mmap)
    p += [
        _tst("x0"), I("bcond_rel", "mi", ("p", "grow_fail")),
        I("mov_reg", "x19", "x0"),
    ]
    p += _mov64("x9", R.chunk_bytes)
    p += [
        I("add_reg", "x20", "x0", "x9"),
    ]
    p += _pop("x30")
    p += [
        I("ret"),
        LBL("grow_fail"), I("movz", "x0", 4),
    ]
    p += _sys(SYS_exit)
    return p


def r_mkleaf(R: Realization, ctx: Ctx) -> Program:
    """mkleaf: x2=tag -> x0 node (counted in nalloc)."""
    p: Program = [
        LBL("mkleaf"),
        I("add_imm", "x9", "x19", R.node_bytes),
        _cmp("x9", "x20"), I("bcond_rel", "ls", ("p", "mkleaf_ok")),
    ]
    p += _push("x2", "x30")
    p += [I("bl_rel", ("p", "grow_heap"))]
    p += _pop("x2", "x30")
    p += [
        LBL("mkleaf_ok"),
        I("mov_reg", "x0", "x19"), I("add_imm", "x19", "x19", R.node_bytes),
        I("str_uoff", "x2", "x0", 0),
        I("movz", "x9", 0),
        I("str_uoff", "x9", "x0", 8), I("str_uoff", "x9", "x0", 16),
    ]
    p += _incs("nalloc")
    p += [I("ret")]
    return p


def r_mkapp(R: Realization, ctx: Ctx) -> Program:
    """mkapp: x0=f, x1=x -> x0 node (counted in nalloc)."""
    p: Program = [
        LBL("mkapp"),
        I("add_imm", "x9", "x19", R.node_bytes),
        _cmp("x9", "x20"), I("bcond_rel", "ls", ("p", "mkapp_ok")),
    ]
    p += _push("x0", "x1", "x30")
    p += [I("bl_rel", ("p", "grow_heap"))]
    p += _pop("x0", "x1", "x30")
    p += [
        LBL("mkapp_ok"),
        I("mov_reg", "x9", "x19"), I("add_imm", "x19", "x19", R.node_bytes),
        I("movz", "x10", 0),
        I("str_uoff", "x10", "x9", 0),
        I("str_uoff", "x0", "x9", 8), I("str_uoff", "x1", "x9", 16),
        I("mov_reg", "x0", "x9"),
    ]
    p += _incs("nalloc")
    p += [I("ret")]
    return p


def r_mkstk(R: Realization, ctx: Ctx) -> Program:
    """mkstk: x0=value -> x0 cons cell, x23=new stack top.
    Parse-stack cells share the dynamic heap; NOT counted in nalloc."""
    p: Program = [
        LBL("mkstk"),
        I("add_imm", "x9", "x19", R.node_bytes),
        _cmp("x9", "x20"), I("bcond_rel", "ls", ("p", "mkstk_ok")),
    ]
    p += _push("x0", "x30")
    p += [I("bl_rel", ("p", "grow_heap"))]
    p += _pop("x0", "x30")
    p += [
        LBL("mkstk_ok"),
        I("mov_reg", "x9", "x19"), I("add_imm", "x19", "x19", R.node_bytes),
        I("movz", "x10", STK_TAG),
        I("str_uoff", "x10", "x9", 0),
        I("str_uoff", "x0", "x9", 8), I("str_uoff", "x23", "x9", 16),
        I("mov_reg", "x23", "x9"), I("mov_reg", "x0", "x9"), I("ret"),
    ]
    return p


def r_step(R: Realization, ctx: Ctx) -> Program:
    """step(x0=t) -> x0: LO single-step dispatch, Lean IStepBasis order
    (normβ, konstβ, dupβ, compβ, swapβ, [sβ], then congruence).
    Saves x30 + the x21..x23 locals it borrows (x86 pushed r12-r14)."""
    p: Program = [
        LBL("step"),
    ]
    p += _push("x21", "x22", "x23", "x30")
    p += [
        I("mov_reg", "x21", "x0"),
        I("ldr_uoff", "x9", "x21", 0),
        I("cbnz_rel", "x9", ("p", "st_none")),      # tag != APP(0)
        I("ldr_uoff", "x22", "x21", 8),             # f
        I("ldr_uoff", "x23", "x21", 16),            # x
        I("ldr_uoff", "x9", "x22", 0),
        _cmp("x9", Tag.norm), I("bcond_rel", "eq", ("p", "st_norm")),
        I("ldr_uoff", "x9", "x22", 0),
        I("cbnz_rel", "x9", ("p", "st_left")),      # f not APP
        I("ldr_uoff", "x0", "x22", 8),              # fl
        I("ldr_uoff", "x3", "x22", 16),             # fr
        I("ldr_uoff", "x9", "x0", 0),
        _cmp("x9", Tag.konst), I("bcond_rel", "eq", ("p", "st_konst")),
        I("ldr_uoff", "x9", "x0", 0),
        _cmp("x9", Tag.dup), I("bcond_rel", "eq", ("p", "st_dup")),
        I("ldr_uoff", "x9", "x0", 0),
        I("cbnz_rel", "x9", ("p", "st_left")),      # fl not APP
        I("ldr_uoff", "x2", "x0", 8),               # fll
        I("ldr_uoff", "x1", "x0", 16),              # flr
        I("ldr_uoff", "x9", "x2", 0),
        _cmp("x9", Tag.comp), I("bcond_rel", "eq", ("p", "st_comp")),
        I("ldr_uoff", "x9", "x2", 0),
        _cmp("x9", Tag.swap), I("bcond_rel", "eq", ("p", "st_swap")),
    ]
    if R.fuse_s:
        p += [
            I("ldr_uoff", "x9", "x2", 0),
            _cmp("x9", Tag.s), I("bcond_rel", "eq", ("p", "st_s")),
        ]
    p += [
        I("b_rel", ("p", "st_left")),
    ]
    return p


def _bump(slot: str) -> Program:
    """counter[slot]++ — x9/x10 are tag scratch, dead at every site."""
    return _incs(slot)


def r_st_norm(R: Realization, ctx: Ctx) -> Program:
    """normβ: I x -> x."""
    p = [LBL("st_norm")]
    if R.audit:
        p += _bump("c_norm")
    return p + [
        I("mov_reg", "x0", "x23"),
        I("b_rel", ("p", "st_out")),
    ]


def r_st_konst(R: Realization, ctx: Ctx) -> Program:
    """konstβ (fused macro): K x y -> x."""
    p = [LBL("st_konst")]
    if R.audit:
        p += _bump("c_konst")
    return p + [
        I("mov_reg", "x0", "x3"),
        I("b_rel", ("p", "st_out")),
    ]


def r_st_dup(R: Realization, ctx: Ctx) -> Program:
    """dupβ: W f x -> f x x."""
    p = [LBL("st_dup")]                                # W f x -> f x x
    if R.audit:
        p += _bump("c_dup")
    return p + [
        I("mov_reg", "x0", "x3"), I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")),                   # x0 = (f x)
        I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")),                   # x0 = (f x) x
        I("b_rel", ("p", "st_out")),
    ]


def r_st_swap(R: Realization, ctx: Ctx) -> Program:
    """swapβ: C f x y -> f y x."""
    p: Program = [
        LBL("st_swap"),                                # C f x y -> f y x
    ]
    if R.audit:
        p += _bump("c_swap")
    p += _push("x3")                                   # save fr (=x)
    p += [
        I("mov_reg", "x0", "x1"), I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")),                   # x0 = (f y)
    ]
    p += _pop("x1")                                    # x1 = fr = x
    p += [
        I("bl_rel", ("p", "mkapp")),                   # x0 = (f y) x
        I("b_rel", ("p", "st_out")),
    ]
    return p


def r_st_comp(R: Realization, ctx: Ctx) -> Program:
    """compβ: B f g x -> f (g x)."""
    p: Program = [
        LBL("st_comp"),                                # B f g x -> f (g x)
    ]
    if R.audit:
        p += _bump("c_comp")
    p += _push("x1", "x3")                             # [sp]=flr=f, [sp+8]=fr=g
    p += [
        I("mov_reg", "x0", "x3"), I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")),                   # x0 = (g x)
        I("mov_reg", "x1", "x0"),                      # x1 = (g x)
    ]
    p += _pop("x0", "x9")                              # x0 = flr = f
    p += [
        I("bl_rel", ("p", "mkapp")),                   # x0 = f (g x)
        I("b_rel", ("p", "st_out")),
    ]
    return p


def r_st_s(R: Realization, ctx: Ctx) -> Program:
    """sβ (fuse_s=True only): S f g x -> (f x)(g x)."""
    p: Program = [
        LBL("st_s"),                               # S f g x -> (f x)(g x)
    ]
    if R.audit:
        p += _bump("c_s")
    p += _push("x1", "x3")                         # [sp]=flr=f, [sp+8]=fr=g
    p += [
        I("mov_reg", "x0", "x1"), I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")),               # x0 = (f x)
    ]
    p += _push("x0")                               # [sp]=(f x)
    p += [
        I("ldr_uoff", "x0", "sp", 24),             # fr = g
        I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")),               # x0 = (g x)
        I("mov_reg", "x1", "x0"),                  # x1 = (g x)
    ]
    p += _pop("x0")                                # x0 = (f x)
    p += [
        I("bl_rel", ("p", "mkapp")),               # x0 = (f x)(g x)
    ]
    p += _pop("x9", "x10")                         # drop saved f,g
    p += [
        I("b_rel", ("p", "st_out")),
    ]
    return p


def r_step_congr(R: Realization, ctx: Ctx) -> Program:
    """appL/appR congruence + st_none/st_out epilogue."""
    p: Program = [
        LBL("st_left"),
    ]
    if R.audit:
        p += _bump("c_left")
    p += [
        I("mov_reg", "x0", "x22"), I("bl_rel", ("p", "step")),
        I("cbz_rel", "x0", ("p", "st_right")),
        I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")), I("b_rel", ("p", "st_out")),
        LBL("st_right"),
    ]
    if R.audit:
        p += _bump("c_right")
    return p + [
        I("mov_reg", "x0", "x23"), I("bl_rel", ("p", "step")),
        I("cbz_rel", "x0", ("p", "st_none")),
        I("mov_reg", "x1", "x0"), I("mov_reg", "x0", "x22"),
        I("bl_rel", ("p", "mkapp")), I("b_rel", ("p", "st_out")),
        LBL("st_none"), _z("x0"),
        LBL("st_out"),
    ] + _pop("x21", "x22", "x23", "x30") + [
        I("ret"),
    ]


def r_count_nodes(R: Realization, ctx: Ctx) -> Program:
    """count_nodes(x0) -> x0."""
    p: Program = [
        LBL("count_nodes"),
    ]
    p += _push("x21", "x22", "x30")
    p += [
        I("mov_reg", "x21", "x0"),
        I("ldr_uoff", "x9", "x21", 0),
        I("cbnz_rel", "x9", ("p", "cn_leaf")),
        I("ldr_uoff", "x0", "x21", 8),
        I("bl_rel", ("p", "count_nodes")),
        I("mov_reg", "x22", "x0"),
        I("ldr_uoff", "x0", "x21", 16),
        I("bl_rel", ("p", "count_nodes")),
        I("add_reg", "x0", "x0", "x22"), I("add_imm", "x0", "x0", 1),
        I("b_rel", ("p", "cn_out")),
        LBL("cn_leaf"), I("movz", "x0", 1),
        LBL("cn_out"),
    ]
    p += _pop("x21", "x22", "x30")
    p += [I("ret")]
    return p


def r_emit_nf(R: Realization, ctx: Ctx) -> Program:
    """emit_nf(x0=node, x1=cur) -> x1: postfix decompile I K S B W C @."""
    p: Program = [
        LBL("emit_nf"),
        I("ldr_uoff", "x9", "x0", 0),
        I("cbnz_rel", "x9", ("p", "en_leaf")),
    ]
    p += _push("x0", "x30")
    p += [
        I("ldr_uoff", "x0", "x0", 8),
        I("bl_rel", ("p", "emit_nf")),
        I("ldr_uoff", "x0", "sp", 0),      # saved node
        I("ldr_uoff", "x0", "x0", 16),
        I("bl_rel", ("p", "emit_nf")),
    ]
    p += _pop("x9", "x30")
    p += [
        I("movz", "w9", 0x40), I("strb_uoff", "w9", "x1", 0),
        I("add_imm", "x1", "x1", 1),
        I("movz", "w9", 0x20), I("strb_uoff", "w9", "x1", 0),
        I("add_imm", "x1", "x1", 1), I("ret"),
        LBL("en_leaf"),
        _cmp("x9", Tag.norm), I("bcond_rel", "eq", ("p", "en_i")),
        _cmp("x9", Tag.konst), I("bcond_rel", "eq", ("p", "en_k")),
        _cmp("x9", Tag.s), I("bcond_rel", "eq", ("p", "en_s")),
        _cmp("x9", Tag.comp), I("bcond_rel", "eq", ("p", "en_b")),
        _cmp("x9", Tag.dup), I("bcond_rel", "eq", ("p", "en_d")),
        _cmp("x9", Tag.swap), I("bcond_rel", "eq", ("p", "en_c")),
        I("movz", "w2", 0x3F), I("b_rel", ("p", "en_w")),
        LBL("en_i"), I("movz", "w2", 0x49), I("b_rel", ("p", "en_w")),
        LBL("en_k"), I("movz", "w2", 0x4B), I("b_rel", ("p", "en_w")),
        LBL("en_s"), I("movz", "w2", 0x53), I("b_rel", ("p", "en_w")),
        LBL("en_b"), I("movz", "w2", 0x42), I("b_rel", ("p", "en_w")),
        LBL("en_d"), I("movz", "w2", 0x57), I("b_rel", ("p", "en_w")),
        LBL("en_c"), I("movz", "w2", 0x43),
        LBL("en_w"),
        I("strb_uoff", "w2", "x1", 0), I("add_imm", "x1", "x1", 1),
        I("movz", "w9", 0x20), I("strb_uoff", "w9", "x1", 0),
        I("add_imm", "x1", "x1", 1), I("ret"),
    ]
    return p


def r_itoa(R: Realization, ctx: Ctx) -> Program:
    """itoa(x0=val, x1=cur) -> x1.  udiv/msub digit loop, scratch stack
    buffer at [sp,#0..32)."""
    return [
        LBL("itoa"),
        I("sub_imm", "sp", "sp", 48),
        I("mov_reg", "x4", "x0"),              # val
        I("add_imm", "x5", "sp", 32),          # buf end
        I("movz", "x6", 10),
        LBL("it_dig"),
        I("udiv_reg", "x7", "x4", "x6"),       # q = val / 10
        I("msub_reg", "x9", "x7", "x6", "x4"), # rem = val - q*10
        I("mov_reg", "x4", "x7"),
        I("add_imm", "w9", "w9", 0x30),
        I("sub_imm", "x5", "x5", 1), I("strb_uoff", "w9", "x5", 0),
        I("cbnz_rel", "x4", ("p", "it_dig")),
        LBL("it_cp"),
        I("add_imm", "x6", "sp", 32),
        _cmp("x5", "x6"), I("bcond_rel", "ge", ("p", "it_done")),
        I("ldrb_uoff", "w9", "x5", 0),
        I("strb_uoff", "w9", "x1", 0),
        I("add_imm", "x5", "x5", 1), I("add_imm", "x1", "x1", 1),
        I("b_rel", ("p", "it_cp")),
        LBL("it_done"), I("add_imm", "sp", "sp", 48), I("ret"),
    ]


def r_build_ds(R: Realization, ctx: Ctx) -> Program:
    """build_ds (default build only): construct DERIVED_S once into [ds];
    x22/x23/x24 scratch (x23 re-zeroed — it is the parse-stack top)."""
    p: Program = [
        LBL("build_ds"),
    ]
    p += _push("x30")
    p += [
        I("movz", "x2", Tag.comp),
        I("bl_rel", ("p", "mkleaf")), I("mov_reg", "x22", "x0"),
        I("movz", "x2", Tag.dup),
        I("bl_rel", ("p", "mkleaf")),
        I("mov_reg", "x1", "x0"), I("mov_reg", "x0", "x22"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x22", "x0"),
        I("movz", "x2", Tag.comp),
        I("bl_rel", ("p", "mkleaf")),
        I("mov_reg", "x1", "x22"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x22", "x0"),
        I("movz", "x2", Tag.comp),         # x22 = (B (B D))
        I("bl_rel", ("p", "mkleaf")), I("mov_reg", "x24", "x0"),
        I("movz", "x2", Tag.comp),
        I("bl_rel", ("p", "mkleaf")),
        I("mov_reg", "x1", "x0"), I("mov_reg", "x0", "x24"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x24", "x0"),
        I("movz", "x2", Tag.comp),         # x24 = (B B)
        I("bl_rel", ("p", "mkleaf")), I("mov_reg", "x23", "x0"),
        I("movz", "x2", Tag.comp),
        I("bl_rel", ("p", "mkleaf")),
        I("mov_reg", "x1", "x0"), I("mov_reg", "x0", "x23"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x23", "x0"),
        I("movz", "x2", Tag.swap),         # x23 = (B B)
        I("bl_rel", ("p", "mkleaf")),      # x0 = C
        I("mov_reg", "x1", "x0"), I("mov_reg", "x0", "x23"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x23", "x0"),
        I("mov_reg", "x0", "x24"), I("mov_reg", "x1", "x23"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x24", "x0"),
        I("movz", "x2", Tag.swap),         # x24 = ((B B)((B B)C))
        I("bl_rel", ("p", "mkleaf")),      # x0 = C
        I("mov_reg", "x1", "x24"),         # mkapp(C, x24)
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x24", "x0"),
        I("movz", "x2", Tag.norm),         # x24 = (C ((B B)((B B)C)))
        I("bl_rel", ("p", "mkleaf")),      # x0 = I
        I("mov_reg", "x1", "x0"), I("mov_reg", "x0", "x24"),
        I("bl_rel", ("p", "mkapp")), I("mov_reg", "x24", "x0"),
        I("mov_reg", "x0", "x22"), I("mov_reg", "x1", "x24"),
        I("bl_rel", ("p", "mkapp")),       # x0 = derived_s
    ]
    p += _sts("ds", "x0")
    p += [
        _z("x23"),
    ]
    p += _pop("x30")
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
    name: str          # "aarch64.linux.lo"
    isa: str           # "aarch64"
    abi: str           # "linux"
    orders: tuple
    routines: tuple    # ROUTINES
    program: Callable  # program(R) -> Program
    imports: tuple     # () — static image, no IAT
    data_slots: tuple


AARCH64_LINUX_LO = Routines(
    name="aarch64.linux.lo",
    isa="aarch64",
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
    print(f"{'OK' if ok else 'FAIL'} routines_aarch64_linux_lo")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
