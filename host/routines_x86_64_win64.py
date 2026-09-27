"""
routines_x86_64_win64 — the reducer PROGRAM (asm-as-data) for
ISA=x86_64, ABI=win64 (kernel32 IAT), order="lo".

Moved verbatim from seed/seed.py §5, refactored into one builder per
routine; program(R) concatenates them in ROUTINES order — byte-identical
to the old monolithic reducer_program (checked by the seed's frozen PE
oracle).  `build_ds` is emitted iff not R.fuse_s, `st_s` iff R.fuse_s.

Imports seed (Tag, Realization) and isa_x86_64 (I, LBL, Program) via
sys.path, same pattern as seed's lazy host import.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
_SEED_DIR = os.path.normpath(os.path.join(_HOST, "..", "seed"))
for _p in (_HOST, _SEED_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import isa_x86_64 as _isa                        # noqa: E402
from isa_x86_64 import I, LBL, Program, encode  # noqa: E402
from toolchain import NotRealized               # noqa: E402
from seed import Tag, Realization               # noqa: E402

IMPORTS: Tuple[str, ...] = (
    "GetStdHandle", "ReadFile", "WriteFile", "VirtualAlloc", "ExitProcess",
)

# .data slots (labels; 8 bytes each unless noted)
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

# packed-IR batch front end (ADR-005): extra .data slots.
# irbuf = current stream region; irnodes/irnroots = stream header counts;
# irroots = root-ptr table; irarena = reserved heap base; irj/irsteps/
# irnstreams = batch state.
DATA_SLOTS_IR: Tuple[Tuple[str, int], ...] = DATA_SLOTS + (
    ("irbuf", 8), ("irhdr", 8), ("irnodes", 8), ("irnroots", 8),
    ("irroots", 8), ("irarena", 8), ("irj", 8), ("irsteps", 8),
    ("irnstreams", 8),
)

# packed-IR constants — pinned by docs/adr/0005; keep in sync with
# spec_term.IR_MAGIC / IR_VERSION / IR_VAR.
IR_MAGIC = 0x30524950                # "PIR0"
IR_VERSION = 1
MEM_RESERVE = 0x2000                 # VirtualAlloc MEM_RESERVE
MEM_COMMIT = 0x1000                  # VirtualAlloc MEM_COMMIT
MEM_DECOMMIT = 0x4000                # VirtualFree MEM_DECOMMIT
MEM_RELEASE = 0x8000                 # VirtualFree MEM_RELEASE
IR_DS_AREA = 1 << 12                 # permanent region for build_ds output

VA_COMMIT_RESERVE = 0x3000
PAGE_RW = 4
STK_TAG = 7   # native-internal parse-stack cons cell tag (never a term node;
              # tags 1..6 are atoms generated from SIGNATURE); excluded from
              # nalloc so `alloc=` counts term nodes only

# ctx shared by builders: iat operand helper for kernel32 imports.
Ctx = Dict[str, object]


def _ctx() -> Ctx:
    return {"iat": lambda n: ("p", f"iat_{n}")}


def r_entry(R: Realization, ctx: Ctx) -> Program:
    """_start: std handles, streaming read buffer (granule, not a cap),
    empty parse stack, first heap chunk, derived_s template (expanded build)."""
    iat = ctx["iat"]
    p: Program = [
        LBL("_start"),
        I("sub_r64_imm", "rsp", 0x28),
        # handles: stdin -10, stdout -11, stderr -12
        I("mov_r32_imm32", "ecx", -10), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "hin"), "rax"),
        I("mov_r32_imm32", "ecx", -11), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "hout"), "rax"),
        I("mov_r32_imm32", "ecx", -12), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "herr"), "rax"),
        # one streaming read buffer (granule, not a cap) + empty parse stack
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "edx", R.read_buf_bytes),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_r64", "r12", "rax"),          # read buffer base
        I("xor_r32_r32", "r14d", "r14d"),        # r14 = parse stack top (0)
        # first heap chunk (sets rbx=bump, rbp=end)
        I("call_rel32", ("l", "grow_heap")),
    ]
    if not R.fuse_s:
        # build the shared derived_s template (L0-only tree); `S` tokens push it
        p += [I("call_rel32", ("l", "build_ds"))]
    return p


def r_parse(R: Realization, ctx: Ctx) -> Program:
    """read_loop/parse_bytes/p_*: streaming parse, heap-cons bytecode stack,
    Lean underflow rules ([]->[I], [t]->[I,t] on `@`)."""
    iat = ctx["iat"]
    p: Program = [
        # ---- streaming parse: ReadFile granule -> parse bytes -> repeat ----
        # bytecode stack = heap cons cells {tag=STK_TAG, l=value, r=next}
        LBL("read_loop"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_r64", "rdx", "r12"),
        I("mov_r32_imm32", "r8d", R.read_buf_bytes),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        # FALSE from an anonymous pipe = EOF (ERROR_BROKEN_PIPE), not an error
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "parse_done")),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "parse_done")),
        I("mov_r64_r64", "rsi", "r12"),          # cursor
        I("mov_r64_r64", "rdi", "r12"),
        I("add_r64_r64", "rdi", "rax"),          # end
        LBL("parse_bytes"),
        I("cmp_r64_r64", "rsi", "rdi"), I("jge_rel32", ("l", "read_loop")),
        I("movzx_r32_m8", "eax", ("m", "rsi", 0)),
        I("cmp_r64_imm", "rax", 0x49), I("je_rel32", ("l", "p_i")),
        I("cmp_r64_imm", "rax", 0x4B), I("je_rel32", ("l", "p_k")),
        I("cmp_r64_imm", "rax", 0x53), I("je_rel32", ("l", "p_s")),
        I("cmp_r64_imm", "rax", 0x42), I("je_rel32", ("l", "p_b")),
        I("cmp_r64_imm", "rax", 0x57), I("je_rel32", ("l", "p_w")),
        I("cmp_r64_imm", "rax", 0x43), I("je_rel32", ("l", "p_c")),
        I("cmp_r64_imm", "rax", 0x40), I("je_rel32", ("l", "p_app")),
        I("cmp_r64_imm", "rax", 0x20), I("je_rel32", ("l", "p_next")),
        I("cmp_r64_imm", "rax", 0x09), I("je_rel32", ("l", "p_next")),
        I("cmp_r64_imm", "rax", 0x0A), I("je_rel32", ("l", "p_next")),
        I("cmp_r64_imm", "rax", 0x0D), I("je_rel32", ("l", "p_next")),
        I("jmp_rel32", ("l", "exit3")),
        LBL("p_i"), I("mov_r32_imm32", "edx", Tag.norm),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        LBL("p_k"), I("mov_r32_imm32", "edx", Tag.konst),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        LBL("p_b"), I("mov_r32_imm32", "edx", Tag.comp),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        LBL("p_w"), I("mov_r32_imm32", "edx", Tag.dup),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        LBL("p_c"), I("mov_r32_imm32", "edx", Tag.swap),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
    ]
    if R.fuse_s:
        p += [
            LBL("p_s"), I("mov_r32_imm32", "edx", Tag.s),
            I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        ]
    else:
        # view expansion: `S` pushes the shared derived_s root (no sβ emitted)
        p += [
            LBL("p_s"), I("mov_r64_rip", "rax", ("p", "ds")),
            I("jmp_rel32", ("l", "p_push")),
        ]
    p += [
        LBL("p_push"),
        I("push_r64", "rdi"), I("sub_r64_imm", "rsp", 8),
        I("mov_r64_r64", "rdi", "rax"), I("call_rel32", ("l", "mkstk")),
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rdi"),
        I("jmp_rel32", ("l", "p_next")),
        LBL("p_app"),
        # depth >= 2 iff top cell and its next exist
        I("test_r64_r64", "r14", "r14"), I("je_rel32", ("l", "p_under")),
        I("mov_r64_m64", "rax", ("m", "r14", 16)),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "p_under")),
        # x = top.l, y = next.l; pop both; push app(y, x)
        I("mov_r64_m64", "rcx", ("m", "r14", 8)),
        I("mov_r64_m64", "rdx", ("m", "rax", 8)),
        I("mov_r64_m64", "r14", ("m", "rax", 16)),
        I("push_r64", "rdi"), I("push_r64", "rsi"),   # save end, cursor
        I("mov_r64_r64", "rdi", "rdx"), I("mov_r64_r64", "rsi", "rcx"),
        I("call_rel32", ("l", "mkapp")),               # rax = app(y, x)
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "mkstk")),
        I("pop_r64", "rsi"), I("pop_r64", "rdi"),
        I("jmp_rel32", ("l", "p_next")),
        LBL("p_under"),
        # depth 0 or 1 -> push I (Lean underflow: []->[I], [t]->[I,t])
        I("mov_r32_imm32", "edx", Tag.norm),
        I("call_rel32", ("l", "mkleaf")),
        I("push_r64", "rdi"), I("sub_r64_imm", "rsp", 8),
        I("mov_r64_r64", "rdi", "rax"), I("call_rel32", ("l", "mkstk")),
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rdi"),
        LBL("p_next"), I("inc_r64", "rsi"), I("jmp_rel32", ("l", "parse_bytes")),
        LBL("parse_done"),
        I("test_r64_r64", "r14", "r14"), I("je_rel32", ("l", "empty")),
        I("mov_r64_m64", "r12", ("m", "r14", 8)),
        I("jmp_rel32", ("l", "do_reduce")),
        LBL("empty"), I("mov_r32_imm32", "edx", Tag.norm),
        I("call_rel32", ("l", "mkleaf")), I("mov_r64_r64", "r12", "rax"),
    ]
    return p


def r_reduce(R: Realization, ctx: Ctx) -> Program:
    """do_reduce/red_loop (+ fuel check when R.fuel) -> count_nodes ->
    exact output alloc -> emit_nf -> WriteFile stdout."""
    iat = ctx["iat"]
    p: Program = [
        # ---- reduce loop (r15 = steps) ----
        LBL("do_reduce"), I("xor_r32_r32", "r15d", "r15d"),
        LBL("red_loop"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "red_done")),
        I("mov_r64_r64", "r12", "rax"), I("inc_r64", "r15"),
    ]
    if R.fuel is not None:
        p += [
            I("cmp_r64_imm", "r15", R.fuel), I("jge_rel32", ("l", "exit2")),
        ]
    p += [
        I("jmp_rel32", ("l", "red_loop")),
        # ---- out: count nodes, VirtualAlloc exact, postfix emit, WriteFile ----
        LBL("red_done"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "count_nodes")),
        I("lea_r64_m64", "rdx", ("m", "rax", 0)), I("add_r64_r64", "rdx", "rdx"),
        I("add_r64_imm", "rdx", 16),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_r64", "r14", "rax"),          # out base
        I("mov_r64_r64", "rsi", "rax"),          # out cursor
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "emit_nf")),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x0A), I("inc_r64", "rsi"),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_r64", "rdx", "r14"),
        I("mov_r64_r64", "r8", "rsi"), I("sub_r64_r64", "r8", "r14"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
    ]
    return p


def _stats_str(p: Program, s: str) -> None:
    for ch in s:
        p.append(I("mov_m8_imm8", ("m", "rsi", 0), ord(ch)))
        p.append(I("inc_r64", "rsi"))


def r_stats(R: Realization, ctx: Ctx) -> Program:
    """stderr line `steps=N alloc=M` via scratch buffer + itoa."""
    iat = ctx["iat"]
    p: Program = [
        I("lea_r64_rip", "rsi", ("p", "scratch")),
    ]
    _stats_str(p, "steps=")
    p += [
        I("mov_r64_r64", "rdi", "r15"), I("call_rel32", ("l", "itoa")),
    ]
    _stats_str(p, " alloc=")
    p += [
        I("mov_r64_rip", "rdi", ("p", "nalloc")), I("call_rel32", ("l", "itoa")),
    ]
    if R.audit:
        _stats_str(p, " rules=I:")
        p += [I("mov_r64_rip", "rdi", ("p", "c_norm")),
              I("call_rel32", ("l", "itoa"))]
        for tag, slot in (("K:", "c_konst"), ("W:", "c_dup"), ("C:", "c_swap"),
                          ("B:", "c_comp"), ("S:", "c_s"),
                          ("L:", "c_left"), ("R:", "c_right")):
            _stats_str(p, "," + tag)
            p += [I("mov_r64_rip", "rdi", ("p", slot)),
                  I("call_rel32", ("l", "itoa"))]
    p += [
        I("mov_m8_imm8", ("m", "rsi", 0), 0x0A), I("inc_r64", "rsi"),
        I("mov_r64_rip", "rcx", ("p", "herr")),
        I("lea_r64_rip", "rdx", ("p", "scratch")),
        I("mov_r64_r64", "r8", "rsi"), I("sub_r64_r64", "r8", "rdx"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
    ]
    return p


def r_exits(R: Realization, ctx: Ctx) -> Program:
    """exit 0; exit2 fuel exhausted, exit3 bad input, exit4 OOM."""
    iat = ctx["iat"]
    return [
        I("xor_r32_r32", "ecx", "ecx"), I("call_mrip", iat("ExitProcess")),
        LBL("exit2"), I("mov_r32_imm32", "ecx", 2), I("call_mrip", iat("ExitProcess")),
        LBL("exit3"), I("mov_r32_imm32", "ecx", 3), I("call_mrip", iat("ExitProcess")),
        LBL("exit4"), I("mov_r32_imm32", "ecx", 4), I("call_mrip", iat("ExitProcess")),
    ]


def r_grow_heap(R: Realization, ctx: Ctx) -> Program:
    """grow_heap: rbx=bump, rbp=chunk end (chunked VirtualAlloc)."""
    iat = ctx["iat"]
    return [
        LBL("grow_heap"),
        I("sub_r64_imm", "rsp", 0x28),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r64_imm", "rdx", R.chunk_bytes),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "grow_fail")),
        I("mov_r64_r64", "rbx", "rax"),
        I("lea_r64_m64", "rbp", ("m", "rax", R.chunk_bytes)),
        I("add_r64_imm", "rsp", 0x28), I("ret"),
        LBL("grow_fail"), I("mov_r32_imm32", "ecx", 4),
        I("call_mrip", iat("ExitProcess")),
    ]


def r_mkleaf(R: Realization, ctx: Ctx) -> Program:
    """mkleaf: rdx=tag -> rax node (counted in nalloc)."""
    return [
        LBL("mkleaf"),
        I("lea_r64_m64", "rax", ("m", "rbx", R.node_bytes)),
        I("cmp_r64_r64", "rax", "rbp"), I("jbe_rel32", ("l", "mkleaf_ok")),
        I("push_r64", "rdx"), I("call_rel32", ("l", "grow_heap")),
        I("pop_r64", "rdx"),
        LBL("mkleaf_ok"),
        I("mov_r64_r64", "rax", "rbx"), I("add_r64_imm", "rbx", R.node_bytes),
        I("mov_m64_r64", ("m", "rax", 0), "rdx"),
        I("mov_m64_imm32", ("m", "rax", 8), 0),
        I("mov_m64_imm32", ("m", "rax", 16), 0),
        I("inc_mrip", ("p", "nalloc")), I("ret"),
    ]


def r_mkapp(R: Realization, ctx: Ctx) -> Program:
    """mkapp: rdi=f, rsi=x -> rax node (counted in nalloc)."""
    return [
        LBL("mkapp"),
        I("lea_r64_m64", "rax", ("m", "rbx", R.node_bytes)),
        I("cmp_r64_r64", "rax", "rbp"), I("jbe_rel32", ("l", "mkapp_ok")),
        I("push_r64", "rdi"), I("push_r64", "rsi"), I("sub_r64_imm", "rsp", 8),
        I("call_rel32", ("l", "grow_heap")),
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rsi"), I("pop_r64", "rdi"),
        LBL("mkapp_ok"),
        I("mov_r64_r64", "rax", "rbx"), I("add_r64_imm", "rbx", R.node_bytes),
        I("mov_m64_imm32", ("m", "rax", 0), 0),
        I("mov_m64_r64", ("m", "rax", 8), "rdi"),
        I("mov_m64_r64", ("m", "rax", 16), "rsi"),
        I("inc_mrip", ("p", "nalloc")), I("ret"),
    ]


def r_mkstk(R: Realization, ctx: Ctx) -> Program:
    """mkstk: rdi=value -> rax cons cell, r14=new stack top.
    Parse-stack cells share the dynamic heap; NOT counted in nalloc."""
    return [
        LBL("mkstk"),
        I("lea_r64_m64", "rax", ("m", "rbx", R.node_bytes)),
        I("cmp_r64_r64", "rax", "rbp"), I("jbe_rel32", ("l", "mkstk_ok")),
        I("push_r64", "rdi"), I("call_rel32", ("l", "grow_heap")),
        I("pop_r64", "rdi"),
        LBL("mkstk_ok"),
        I("mov_r64_r64", "rax", "rbx"), I("add_r64_imm", "rbx", R.node_bytes),
        I("mov_m64_imm32", ("m", "rax", 0), STK_TAG),
        I("mov_m64_r64", ("m", "rax", 8), "rdi"),
        I("mov_m64_r64", ("m", "rax", 16), "r14"),
        I("mov_r64_r64", "r14", "rax"), I("ret"),
    ]


def r_step(R: Realization, ctx: Ctx) -> Program:
    """step(rdi=t) -> rax: LO single-step dispatch, Lean IStepBasis order
    (normβ, konstβ, dupβ, compβ, swapβ, [sβ], then congruence)."""
    p: Program = [
        LBL("step"),
        I("push_r64", "r12"), I("push_r64", "r13"), I("push_r64", "r14"),
        I("mov_r64_r64", "r12", "rdi"),
        I("cmp_m64_imm", ("m", "r12", 0), Tag.APP),
        I("jne_rel32", ("l", "st_none")),
        I("mov_r64_m64", "r13", ("m", "r12", 8)),    # f
        I("mov_r64_m64", "r14", ("m", "r12", 16)),   # x
        I("cmp_m64_imm", ("m", "r13", 0), Tag.norm),
        I("je_rel32", ("l", "st_norm")),
        I("cmp_m64_imm", ("m", "r13", 0), Tag.APP),
        I("jne_rel32", ("l", "st_left")),
        I("mov_r64_m64", "rax", ("m", "r13", 8)),    # fl
        I("mov_r64_m64", "rcx", ("m", "r13", 16)),   # fr
        I("cmp_m64_imm", ("m", "rax", 0), Tag.konst),
        I("je_rel32", ("l", "st_konst")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.dup),
        I("je_rel32", ("l", "st_dup")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.APP),
        I("jne_rel32", ("l", "st_left")),
        I("mov_r64_m64", "rdx", ("m", "rax", 8)),    # fll
        I("mov_r64_m64", "rsi", ("m", "rax", 16)),   # flr
        I("cmp_m64_imm", ("m", "rdx", 0), Tag.comp),
        I("je_rel32", ("l", "st_comp")),
        I("cmp_m64_imm", ("m", "rdx", 0), Tag.swap),
        I("je_rel32", ("l", "st_swap")),
    ]
    if R.fuse_s:
        p += [
            I("cmp_m64_imm", ("m", "rdx", 0), Tag.s),
            I("je_rel32", ("l", "st_s")),
        ]
    p += [
        I("jmp_rel32", ("l", "st_left")),
    ]
    return p


def _bump(slot: str) -> Program:
    """counter[slot]++ — rax is dead at every site this is used."""
    return [
        I("mov_r64_rip", "rax", ("p", slot)), I("inc_r64", "rax"),
        I("mov_rip_r64", ("p", slot), "rax"),
    ]


def r_st_norm(R: Realization, ctx: Ctx) -> Program:
    """normβ: I x -> x."""
    p = [LBL("st_norm")]
    if R.audit:
        p += _bump("c_norm")
    return p + [
        I("mov_r64_r64", "rax", "r14"),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_konst(R: Realization, ctx: Ctx) -> Program:
    """konstβ (fused macro): K x y -> x."""
    p = [LBL("st_konst")]
    if R.audit:
        p += _bump("c_konst")
    return p + [
        I("mov_r64_r64", "rax", "rcx"),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_dup(R: Realization, ctx: Ctx) -> Program:
    """dupβ: W f x -> f x x."""
    p = [LBL("st_dup")]                                # W f x -> f x x
    if R.audit:
        p += _bump("c_dup")
    return p + [
        I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x)
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x) x
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_swap(R: Realization, ctx: Ctx) -> Program:
    """swapβ: C f x y -> f y x."""
    p = [LBL("st_swap")]                               # C f x y -> f y x
    if R.audit:
        p += _bump("c_swap")
    return p + [
        I("push_r64", "rcx"), I("sub_r64_imm", "rsp", 8),  # save fr (=y-side)
        I("mov_r64_r64", "rdi", "rsi"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f y)
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rsi"),
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f y) x
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_comp(R: Realization, ctx: Ctx) -> Program:
    """compβ: B f g x -> f (g x)."""
    p = [LBL("st_comp")]                               # B f g x -> f (g x)
    if R.audit:
        p += _bump("c_comp")
    return p + [
        I("push_r64", "rcx"), I("push_r64", "rsi"),
        I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (g x)
        I("pop_r64", "rdi"), I("pop_r64", "rdx"),      # rdi = flr
        I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")),               # rax = f (g x)
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_s(R: Realization, ctx: Ctx) -> Program:
    """sβ (fuse_s=True only): S f g x -> (f x)(g x)."""
    p = [LBL("st_s")]                            # S f g x -> (f x)(g x)
    if R.audit:
        p += _bump("c_s")
    return p + [
        I("push_r64", "rcx"), I("push_r64", "rsi"),  # [rsp]=flr,[rsp+8]=fr
        I("mov_r64_r64", "rdi", "rsi"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),             # rax = (f x)
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),
        I("mov_r64_m64", "rdi", ("m", "rsp", 24)),   # fr
        I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),             # rax = (g x)
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rdi"),
        I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")),
        I("add_r64_imm", "rsp", 16),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_step_congr(R: Realization, ctx: Ctx) -> Program:
    """appL/appR congruence + st_none/st_out epilogue."""
    p = [LBL("st_left")]
    if R.audit:
        p += _bump("c_left")
    p += [
        I("mov_r64_r64", "rdi", "r13"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "st_right")),
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")), I("jmp_rel32", ("l", "st_out")),
        LBL("st_right"),
    ]
    if R.audit:
        p += _bump("c_right")
    return p + [
        I("mov_r64_r64", "rdi", "r14"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "st_none")),
        I("mov_r64_r64", "rdi", "r13"), I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")), I("jmp_rel32", ("l", "st_out")),
        LBL("st_none"), I("xor_r32_r32", "eax", "eax"),
        LBL("st_out"),
        I("pop_r64", "r14"), I("pop_r64", "r13"), I("pop_r64", "r12"), I("ret"),
    ]


def r_count_nodes(R: Realization, ctx: Ctx) -> Program:
    """count_nodes(rdi) -> rax."""
    return [
        LBL("count_nodes"),
        I("push_r64", "r12"), I("push_r64", "r13"), I("sub_r64_imm", "rsp", 8),
        I("mov_r64_r64", "r12", "rdi"),
        I("cmp_m64_imm", ("m", "r12", 0), Tag.APP),
        I("jne_rel32", ("l", "cn_leaf")),
        I("mov_r64_m64", "rdi", ("m", "r12", 8)),
        I("call_rel32", ("l", "count_nodes")),
        I("mov_r64_r64", "r13", "rax"),
        I("mov_r64_m64", "rdi", ("m", "r12", 16)),
        I("call_rel32", ("l", "count_nodes")),
        I("add_r64_r64", "rax", "r13"), I("inc_r64", "rax"),
        I("jmp_rel32", ("l", "cn_out")),
        LBL("cn_leaf"), I("mov_r32_imm32", "eax", 1),
        LBL("cn_out"),
        I("add_r64_imm", "rsp", 8),
        I("pop_r64", "r13"), I("pop_r64", "r12"), I("ret"),
    ]


def r_emit_nf(R: Realization, ctx: Ctx) -> Program:
    """emit_nf(rdi=node, rsi=cur) -> rsi: postfix decompile I K S B W C @."""
    return [
        LBL("emit_nf"),
        I("mov_r64_m64", "rax", ("m", "rdi", 0)),
        I("test_r64_r64", "rax", "rax"), I("jne_rel32", ("l", "en_leaf")),
        I("push_r64", "rdi"),
        I("mov_r64_m64", "rdi", ("m", "rdi", 8)),
        I("call_rel32", ("l", "emit_nf")),
        I("mov_r64_m64", "rdi", ("m", "rsp", 0)),
        I("mov_r64_m64", "rdi", ("m", "rdi", 16)),
        I("call_rel32", ("l", "emit_nf")),
        I("add_r64_imm", "rsp", 8),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x40), I("inc_r64", "rsi"),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x20), I("inc_r64", "rsi"), I("ret"),
        LBL("en_leaf"),
        I("cmp_r64_imm", "rax", Tag.norm), I("je_rel32", ("l", "en_i")),
        I("cmp_r64_imm", "rax", Tag.konst), I("je_rel32", ("l", "en_k")),
        I("cmp_r64_imm", "rax", Tag.s), I("je_rel32", ("l", "en_s")),
        I("cmp_r64_imm", "rax", Tag.comp), I("je_rel32", ("l", "en_b")),
        I("cmp_r64_imm", "rax", Tag.dup), I("je_rel32", ("l", "en_d")),
        I("cmp_r64_imm", "rax", Tag.swap), I("je_rel32", ("l", "en_c")),
        I("mov_r32_imm32", "ecx", 0x3F), I("jmp_rel32", ("l", "en_w")),
        LBL("en_i"), I("mov_r32_imm32", "ecx", 0x49), I("jmp_rel32", ("l", "en_w")),
        LBL("en_k"), I("mov_r32_imm32", "ecx", 0x4B), I("jmp_rel32", ("l", "en_w")),
        LBL("en_s"), I("mov_r32_imm32", "ecx", 0x53), I("jmp_rel32", ("l", "en_w")),
        LBL("en_b"), I("mov_r32_imm32", "ecx", 0x42), I("jmp_rel32", ("l", "en_w")),
        LBL("en_d"), I("mov_r32_imm32", "ecx", 0x57), I("jmp_rel32", ("l", "en_w")),
        LBL("en_c"), I("mov_r32_imm32", "ecx", 0x43),
        LBL("en_w"),
        I("mov_m8_r8", ("m", "rsi", 0), "cl"), I("inc_r64", "rsi"),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x20), I("inc_r64", "rsi"), I("ret"),
    ]


def r_itoa(R: Realization, ctx: Ctx) -> Program:
    """itoa(rdi=val, rsi=cur) -> rsi."""
    return [
        LBL("itoa"),
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_r64_r64", "rax", "rdi"),
        I("lea_r64_m64", "r9", ("m", "rsp", 0x20)),
        I("mov_r32_imm32", "r8d", 10),
        LBL("it_dig"),
        I("xor_r32_r32", "edx", "edx"), I("div_r64", "r8"),
        I("add_r8_imm8", "dl", 0x30),
        I("dec_r64", "r9"), I("mov_m8_r8", ("m", "r9", 0), "dl"),
        I("test_r64_r64", "rax", "rax"), I("jne_rel32", ("l", "it_dig")),
        LBL("it_cp"),
        I("lea_r64_m64", "rcx", ("m", "rsp", 0x20)),
        I("cmp_r64_r64", "r9", "rcx"), I("jge_rel32", ("l", "it_done")),
        I("mov_r8_m8", "al", ("m", "r9", 0)),
        I("mov_m8_r8", ("m", "rsi", 0), "al"),
        I("inc_r64", "r9"), I("inc_r64", "rsi"),
        I("jmp_rel32", ("l", "it_cp")),
        LBL("it_done"), I("add_r64_imm", "rsp", 0x28), I("ret"),
    ]


def r_build_ds(R: Realization, ctx: Ctx) -> Program:
    """build_ds (default build only): construct DERIVED_S once into [rip+ds];
    r13/r14/r15 scratch (pre-parse; r14 re-zeroed — it is the parse-stack top)."""
    return [
        LBL("build_ds"),
        I("sub_r64_imm", "rsp", 8),
        I("mov_r32_imm32", "edx", Tag.comp),
        I("call_rel32", ("l", "mkleaf")), I("mov_r64_r64", "r13", "rax"),
        I("mov_r32_imm32", "edx", Tag.dup),
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "r13"), I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r13", "rax"),
        I("mov_r32_imm32", "edx", Tag.comp),
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r13"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r13", "rax"),
        I("mov_r32_imm32", "edx", Tag.comp),        # r13 = (B (B D))
        I("call_rel32", ("l", "mkleaf")), I("mov_r64_r64", "r15", "rax"),
        I("mov_r32_imm32", "edx", Tag.comp),
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "r15"), I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r15", "rax"),
        I("mov_r32_imm32", "edx", Tag.comp),        # r15 = (B B)
        I("call_rel32", ("l", "mkleaf")), I("mov_r64_r64", "r14", "rax"),
        I("mov_r32_imm32", "edx", Tag.comp),
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "r14"), I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r14", "rax"),
        I("mov_r32_imm32", "edx", Tag.swap),        # r14 = (B B)
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "r14"), I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r14", "rax"),
        I("mov_r64_r64", "rdi", "r15"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r15", "rax"),
        I("mov_r32_imm32", "edx", Tag.swap),        # r15 = ((B B)(B C))
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r15"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r15", "rax"),
        I("mov_r32_imm32", "edx", Tag.norm),        # r15 = (C ((B B)(B C)))
        I("call_rel32", ("l", "mkleaf")),
        I("mov_r64_r64", "rdi", "r15"), I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")), I("mov_r64_r64", "r15", "rax"),
        I("mov_r64_r64", "rdi", "r13"), I("mov_r64_r64", "rsi", "r15"),
        I("call_rel32", ("l", "mkapp")),            # rax = derived_s
        I("mov_rip_r64", ("p", "ds"), "rax"),
        I("xor_r32_r32", "r14d", "r14d"),
        I("add_r64_imm", "rsp", 8), I("ret"),
    ]


# ======================================================================
# PACKED-IR BATCH FRONT END (ADR-005)
#
# stdin carries one IR stream: header(magic,ver,n_nodes,n_roots) +
# u32 root indices + 9B node records (postorder, children before parents).
# The depack region (nodes*24 + roots*8 + ds area) is its own VirtualAlloc
# and NEVER resets — node i's cell lives at base+i*24, so index resolution
# is address arithmetic and one forward pass suffices.  The reduction heap
# is a single reserved arena committed ahead in chunks; each root starts
# by decommitting the used span (physical pages freed, VA retained) and
# ends by writing one NF line to stdout.
# ======================================================================

def r_ir_entry(R: Realization, ctx: Ctx) -> Program:
    """_start (IR): handles, granule buffer for header reads (r12),
    reserved commit-ahead heap arena (rbx=bump, rbp=committed end),
    zeroed batch state, permanent derived-S region (default mode)."""
    iat = ctx["iat"]
    p: Program = [
        LBL("_start"),
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_r32_imm32", "ecx", -10), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "hin"), "rax"),
        I("mov_r32_imm32", "ecx", -11), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "hout"), "rax"),
        I("mov_r32_imm32", "ecx", -12), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "herr"), "rax"),
        # granule buffer for the header peek + oversize probe
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "edx", R.read_buf_bytes),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "irhdr"), "rax"),
        # heap: one reserved region; rbx=rbp=base means "nothing committed"
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r64_imm", "rdx", R.ir_arena_bytes),
        I("mov_r32_imm32", "r8d", MEM_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "irarena"), "rax"),
        I("mov_r64_r64", "rbx", "rax"),
        I("mov_r64_r64", "rbp", "rax"),
        # batch state (slots may be uninitialised data)
        I("xor_r32_r32", "eax", "eax"),
        I("mov_rip_r64", ("p", "irsteps"), "rax"),
        I("mov_rip_r64", ("p", "irnstreams"), "rax"),
        I("mov_rip_r64", ("p", "irj"), "rax"),
    ]
    if not R.fuse_s:
        # permanent derived-S region: tag-3 cells alias its root across
        # the whole run, so it must outlive the per-stream regions
        p += [
            I("xor_r32_r32", "ecx", "ecx"),
            I("mov_r32_imm32", "edx", IR_DS_AREA),
            I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
            I("mov_r64_r64", "rbx", "rax"),
            I("lea_r64_m64", "rbp", ("m", "rax", IR_DS_AREA)),
            I("call_rel32", ("l", "build_ds")),
            I("mov_r64_rip", "rbx", ("p", "irarena")),
            I("mov_r64_r64", "rbp", "rbx"),
        ]
    return p


def r_ir_read(R: Realization, ctx: Ctx) -> Program:
    """ir_sloop: one packed-IR stream element per iteration — 16B header
    read-exactly (clean EOF -> ir_sdone, partial -> exit3), then the
    4*n_roots + 9*n_nodes body into a per-stream region laid out as
    [root idx | node records | cells | root ptrs].  Concatenated
    streams are the batch unit (ADR-005): each element is
    self-describing, so the same blob feeds a fork-pool chunk today
    and a CUDA grid tile later."""
    iat = ctx["iat"]
    return [
        LBL("ir_sloop"),
        # ---- 16-byte header, read-exactly into the granule buf ----
        I("xor_r32_r32", "r13d", "r13d"),
        LBL("ir_hloop"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "irhdr")),
        I("add_r64_r64", "rdx", "r13"),
        I("mov_r32_imm32", "r8d", 16), I("sub_r64_r64", "r8", "r13"),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        # pipes report EOF as FALSE/ERROR_BROKEN_PIPE, files as nread=0 —
        # clean at a stream boundary (r13==0), truncated otherwise
        I("test_r64_r64", "rax", "rax"), I("jne_rel32", ("l", "ir_hok")),
        I("test_r64_r64", "r13", "r13"), I("je_rel32", ("l", "ir_sdone")),
        I("jmp_rel32", ("l", "exit3")),
        LBL("ir_hok"),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("jne_rel32", ("l", "ir_hgot")),
        I("test_r64_r64", "r13", "r13"), I("je_rel32", ("l", "ir_sdone")),
        I("jmp_rel32", ("l", "exit3")),
        LBL("ir_hgot"),
        I("add_r64_r64", "r13", "rax"),
        I("cmp_r64_imm", "r13", 16), I("jl_rel32", ("l", "ir_hloop")),
        # header: magic u32 @0, ver u32 @4, n_nodes u32 @8, n_roots u32 @12
        I("mov_r64_rip", "r13", ("p", "irhdr")),
        I("mov_r32_m32", "eax", ("m", "r13", 0)),
        I("mov_r32_imm32", "ecx", IR_MAGIC), I("cmp_r64_r64", "rax", "rcx"),
        I("jne_rel32", ("l", "exit3")),
        I("mov_r32_m32", "eax", ("m", "r13", 4)),
        I("cmp_r64_imm", "rax", IR_VERSION), I("jne_rel32", ("l", "exit3")),
        I("mov_r32_m32", "eax", ("m", "r13", 8)),
        I("cmp_r64_imm", "rax", 0x7FFFFFFF), I("jge_rel32", ("l", "exit3")),
        I("mov_rip_r64", ("p", "irnodes"), "rax"),
        I("mov_r32_m32", "ecx", ("m", "r13", 12)),
        I("cmp_r64_imm", "rcx", 0x7FFFFFFF), I("jge_rel32", ("l", "exit3")),
        I("mov_rip_r64", ("p", "irnroots"), "rcx"),
        # stream region = 33*n_nodes + 12*n_roots, laid out as
        #   [4*nr root idx][9*nn node records][24*nn cells][8*nr ptrs]
        I("mov_r64_r64", "rdx", "rax"), I("shl_r64_imm8", "rax", 5),
        I("add_r64_r64", "rax", "rdx"),                      # 33*nn
        I("mov_r64_r64", "rdx", "rcx"), I("shl_r64_imm8", "rdx", 1),
        I("add_r64_r64", "rdx", "rcx"), I("shl_r64_imm8", "rdx", 2),
        I("add_r64_r64", "rax", "rdx"),                      # +12*nr
        I("mov_r64_r64", "rdx", "rax"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "irbuf"), "rax"),
        # ---- body, read-exactly: 4*nr + 9*nn bytes into irbuf ----
        I("mov_r64_rip", "rax", ("p", "irnodes")),
        I("mov_r64_r64", "rdx", "rax"), I("shl_r64_imm8", "rax", 3),
        I("add_r64_r64", "rax", "rdx"),                      # 9*nn
        I("mov_r64_rip", "rcx", ("p", "irnroots")),
        I("shl_r64_imm8", "rcx", 2), I("add_r64_r64", "rax", "rcx"),
        I("mov_r64_r64", "r14", "rax"),                      # body size
        I("test_r64_r64", "r14", "r14"),
        I("je_rel32", ("l", "ir_depack")),                   # empty body
        I("xor_r32_r32", "r13d", "r13d"),
        LBL("ir_brd"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "irbuf")),
        I("add_r64_r64", "rdx", "r13"),
        I("mov_r64_r64", "r8", "r14"), I("sub_r64_r64", "r8", "r13"),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("add_r64_r64", "r13", "rax"),
        I("cmp_r64_r64", "r13", "r14"), I("jl_rel32", ("l", "ir_brd")),
    ]


def _mul24() -> Program:
    """rax = rax*24 (idx -> cell offset; no scaled-mem form in this ISA)."""
    return [
        I("shl_r64_imm8", "rax", 3), I("mov_r64_r64", "rdx", "rax"),
        I("add_r64_r64", "rdx", "rdx"), I("add_r64_r64", "rax", "rdx"),
    ]


def r_ir_depack(R: Realization, ctx: Ctx) -> Program:
    """ir_depack: cells live inside the per-stream region — r13 = irbuf
    + 4*nr + 9*nn, root-ptr table at r13 + 24*nn.  One forward pass
    over the postorder records; tag-3 cells copy the permanent ds root
    triple (built once in entry, children alias it — stable across
    streams and arena resets); fuse_s keeps tag-3 a primitive leaf.
    Tags >= 7 (STK/VAR/junk) and forward/out-of-range indices -> exit3."""
    iat = ctx["iat"]
    p: Program = [
        LBL("ir_depack"),
        # r13 = cells base = irbuf + 4*nr + 9*nn
        I("mov_r64_rip", "rax", ("p", "irnodes")),
        I("mov_r64_r64", "rdx", "rax"), I("shl_r64_imm8", "rax", 3),
        I("add_r64_r64", "rax", "rdx"),                      # 9*nn
        I("mov_r64_rip", "rcx", ("p", "irnroots")),
        I("shl_r64_imm8", "rcx", 2),
        I("add_r64_r64", "rax", "rcx"),                      # +4*nr
        I("mov_r64_rip", "rcx", ("p", "irbuf")),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_r64_r64", "r13", "rax"),
        # irroots = r13 + 24*nn
        I("mov_r64_rip", "rax", ("p", "irnodes")),
    ] + _mul24() + [
        I("add_r64_r64", "rax", "r13"),
        I("mov_rip_r64", ("p", "irroots"), "rax"),
        # source cursor: rsi = irbuf + 4*nr; cell cursor r14; i r15
        I("mov_r64_rip", "rsi", ("p", "irbuf")),
        I("mov_r64_rip", "rax", ("p", "irnroots")),
        I("shl_r64_imm8", "rax", 2),
        I("add_r64_r64", "rsi", "rax"),
        I("mov_r64_r64", "r14", "r13"), I("xor_r32_r32", "r15d", "r15d"),
        LBL("ir_dloop"),
        I("mov_r64_rip", "rax", ("p", "irnodes")),
        I("cmp_r64_r64", "r15", "rax"), I("jge_rel32", ("l", "ir_ddone")),
        I("movzx_r32_m8", "eax", ("m", "rsi", 0)),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "ir_d_app")),
        I("cmp_r64_imm", "rax", 7), I("jge_rel32", ("l", "exit3")),
    ]
    if not R.fuse_s:
        p += [I("cmp_r64_imm", "rax", Tag.s), I("je_rel32", ("l", "ir_d_ds"))]
    p += [
        # leaf cell {tag,0,0}
        LBL("ir_d_leaf"),
        I("mov_m64_r64", ("m", "r14", 0), "rax"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_m64_r64", ("m", "r14", 8), "rcx"),
        I("mov_m64_r64", ("m", "r14", 16), "rcx"),
        I("jmp_rel32", ("l", "ir_d_st")),
    ]
    if not R.fuse_s:
        p += [
            # tag-3 cell := structural copy of the ds root (children alias
            # the region-resident template — stable across arena resets)
            LBL("ir_d_ds"),
            I("mov_m64_imm32", ("m", "r14", 0), Tag.APP),
            I("mov_r64_rip", "rax", ("p", "ds")),
            I("mov_r64_m64", "rcx", ("m", "rax", 8)),
            I("mov_m64_r64", ("m", "r14", 8), "rcx"),
            I("mov_r64_m64", "rcx", ("m", "rax", 16)),
            I("mov_m64_r64", ("m", "r14", 16), "rcx"),
            I("jmp_rel32", ("l", "ir_d_st")),
        ]
    p += [
        # app node: l idx @+1, r idx @+5 (postorder => idx < i)
        LBL("ir_d_app"),
        I("mov_r32_m32", "eax", ("m", "rsi", 1)),
        I("cmp_r64_r64", "rax", "r15"), I("jge_rel32", ("l", "exit3")),
    ] + _mul24() + [
        I("add_r64_r64", "rax", "r13"),
        I("mov_m64_r64", ("m", "r14", 8), "rax"),
        I("mov_r32_m32", "eax", ("m", "rsi", 5)),
        I("cmp_r64_r64", "rax", "r15"), I("jge_rel32", ("l", "exit3")),
    ] + _mul24() + [
        I("add_r64_r64", "rax", "r13"),
        I("mov_m64_r64", ("m", "r14", 16), "rax"),
        I("mov_m64_imm32", ("m", "r14", 0), Tag.APP),
        LBL("ir_d_st"),
        I("inc_r64", "r15"), I("add_r64_imm", "rsi", 9),
        I("add_r64_imm", "r14", 24), I("jmp_rel32", ("l", "ir_dloop")),
        LBL("ir_ddone"),
        # depacked cells counted like parse's mk* allocations
        I("mov_r64_rip", "rax", ("p", "nalloc")),
        I("mov_r64_rip", "rcx", ("p", "irnodes")), I("add_r64_r64", "rax", "rcx"),
        I("mov_rip_r64", ("p", "nalloc"), "rax"),
        # roots: rsi = region base (root idx table at +0), rdi = [irroots]
        I("mov_r64_rip", "rsi", ("p", "irbuf")),
        I("mov_r64_rip", "rdi", ("p", "irroots")),
        I("xor_r32_r32", "r15d", "r15d"),
        LBL("ir_rtloop"),
        I("mov_r64_rip", "rax", ("p", "irnroots")),
        I("cmp_r64_r64", "r15", "rax"), I("jge_rel32", ("l", "ir_binit")),
        I("mov_r32_m32", "eax", ("m", "rsi", 0)),
        I("mov_r64_rip", "rcx", ("p", "irnodes")),
        I("cmp_r64_r64", "rax", "rcx"), I("jge_rel32", ("l", "exit3")),
    ] + _mul24() + [
        I("add_r64_r64", "rax", "r13"),
        I("mov_m64_r64", ("m", "rdi", 0), "rax"),
        I("inc_r64", "r15"), I("add_r64_imm", "rsi", 4),
        I("add_r64_imm", "rdi", 8), I("jmp_rel32", ("l", "ir_rtloop")),
    ]
    return p


def r_ir_reduce(R: Realization, ctx: Ctx) -> Program:
    """ir_binit/ir_bloop: per root — decommit used arena span, fresh fuel
    (per-root fuel semantics), LO loop, one NF line on stdout.  irsteps
    accumulates total steps; stats/alloc report the whole batch."""
    iat = ctx["iat"]
    p: Program = [
        LBL("ir_binit"),
        I("xor_r32_r32", "eax", "eax"),
        I("mov_rip_r64", ("p", "irj"), "rax"),
        LBL("ir_bloop"),
        I("mov_r64_rip", "rax", ("p", "irj")),
        I("mov_r64_rip", "rcx", ("p", "irnroots")),
        I("cmp_r64_r64", "rax", "rcx"), I("jge_rel32", ("l", "ir_bdone")),
        # arena reset: decommit the used span (VA retained)
        I("mov_r64_rip", "rcx", ("p", "irarena")),
        I("cmp_r64_r64", "rbp", "rcx"), I("jbe_rel32", ("l", "ir_nofree")),
        I("mov_r64_r64", "rdx", "rbp"), I("sub_r64_r64", "rdx", "rcx"),
        I("mov_r32_imm32", "r8d", MEM_DECOMMIT),
        I("call_mrip", iat("VirtualFree")),
        LBL("ir_nofree"),
        I("mov_r64_rip", "rbx", ("p", "irarena")),
        I("mov_r64_r64", "rbp", "rbx"),
        # r12 = roots[j]; r15 = this root's step counter
        I("mov_r64_rip", "rax", ("p", "irj")), I("shl_r64_imm8", "rax", 3),
        I("mov_r64_rip", "rcx", ("p", "irroots")), I("add_r64_r64", "rax", "rcx"),
        I("mov_r64_m64", "r12", ("m", "rax", 0)),
        I("xor_r32_r32", "r15d", "r15d"),
        LBL("ir_rloop"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "ir_red_done")),
        I("mov_r64_r64", "r12", "rax"), I("inc_r64", "r15"),
    ]
    if R.fuel is not None:
        p += [I("cmp_r64_imm", "r15", R.fuel), I("jge_rel32", ("l", "exit2"))]
    p += [
        I("jmp_rel32", ("l", "ir_rloop")),
        # ---- per-root NF line (same emit block as the token path) ----
        LBL("ir_red_done"),
        I("mov_r64_rip", "rax", ("p", "irsteps")),
        I("add_r64_r64", "rax", "r15"),
        I("mov_rip_r64", ("p", "irsteps"), "rax"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "count_nodes")),
        I("lea_r64_m64", "rdx", ("m", "rax", 0)), I("add_r64_r64", "rdx", "rdx"),
        I("add_r64_imm", "rdx", 16),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_r64", "r14", "rax"),
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "emit_nf")),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x0A), I("inc_r64", "rsi"),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_r64", "rdx", "r14"),
        I("mov_r64_r64", "r8", "rsi"), I("sub_r64_r64", "r8", "r14"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        I("mov_r64_rip", "rax", ("p", "irj")), I("inc_r64", "rax"),
        I("mov_rip_r64", ("p", "irj"), "rax"),
        I("jmp_rel32", ("l", "ir_bloop")),
        # stream done: release its region, count it, next stream
        LBL("ir_bdone"),
        I("mov_r64_rip", "rcx", ("p", "irbuf")),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "r8d", MEM_RELEASE),
        I("call_mrip", iat("VirtualFree")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_rip", "rax", ("p", "irnstreams")), I("inc_r64", "rax"),
        I("mov_rip_r64", ("p", "irnstreams"), "rax"),
        I("jmp_rel32", ("l", "ir_sloop")),
        LBL("ir_sdone"),
        I("mov_r64_rip", "rax", ("p", "irnstreams")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "r15", ("p", "irsteps")),
    ]
    return p


# residual-application front end: the residual term's packed-IR blob is
# initialized .data (R.payload); VAR records (tag 0xFE — legal inside
# the payload, still rejected on the wire) depack to hole cells which
# the per-root graft substitutes with the current argument root.
IR_HOLE = 8   # hole-cell tag in the residual's depacked cells


def r_res_entry(R: Realization, ctx: Ctx) -> Program:
    """res_entry: ir_entry + permanent region for the residual's
    depacked cells + res_depack.  Layout of the residual payload:
    pack_ir(residual) verbatim — 16B header, root table, 9B records."""
    iat = ctx["iat"]
    return r_ir_entry(R, ctx) + [
        # permanent cell region for the residual: 24*nres bytes
        I("lea_r64_rip", "rax", ("p", "resblob")),
        I("mov_r32_m32", "ecx", ("m", "rax", 0)),
        I("mov_r32_imm32", "edx", IR_MAGIC), I("cmp_r64_r64", "rcx", "rdx"),
        I("jne_rel32", ("l", "exit3")),
        I("mov_r32_m32", "ecx", ("m", "rax", 8)),
        I("test_r64_r64", "rcx", "rcx"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_r64", "rax", "rcx"),
    ] + _mul24() + [
        I("mov_r64_r64", "rdx", "rax"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "rescells"), "rax"),
        I("call_rel32", ("l", "res_depack")),
        # residual depack cells count like stream depack cells
        I("mov_r64_rip", "rax", ("p", "nalloc")),
        I("mov_r64_rip", "rcx", ("p", "resn")), I("add_r64_r64", "rax", "rcx"),
        I("mov_rip_r64", ("p", "nalloc"), "rax"),
        I("jmp_rel32", ("l", "ir_sloop")),
    ]


def r_res_depack(R: Realization, ctx: Ctx) -> Program:
    """res_depack: resblob (.data) -> pointer cells in the permanent
    region.  Same record walk as ir_depack; tag 0xFE -> hole cell
    {IR_HOLE, varidx, 0}; tag 3 -> ds-root copy (default build).
    Roots table first entry -> resroot (cell INDEX, graft resolves it
    per argument)."""
    p: Program = [
        LBL("res_depack"),
        I("lea_r64_rip", "rsi", ("p", "resblob")),
        I("mov_r32_m32", "eax", ("m", "rsi", 4)),
        I("cmp_r64_imm", "rax", IR_VERSION), I("jne_rel32", ("l", "exit3")),
        I("mov_r32_m32", "eax", ("m", "rsi", 12)),
        I("cmp_r64_imm", "rax", 1), I("jne_rel32", ("l", "exit3")),
        I("mov_r32_m32", "eax", ("m", "rsi", 8)),
        I("mov_rip_r64", ("p", "resn"), "rax"),
        I("mov_r32_m32", "eax", ("m", "rsi", 16)),
        I("mov_rip_r64", ("p", "resroot"), "rax"),
        I("add_r64_imm", "rsi", 20),                # records @ +16+4*nr
        I("mov_r64_rip", "rdi", ("p", "rescells")),
        I("mov_r64_r64", "r14", "rdi"),
        I("xor_r32_r32", "r15d", "r15d"),
        LBL("res_dloop"),
        I("mov_r64_rip", "rax", ("p", "resn")),
        I("cmp_r64_r64", "r15", "rax"), I("jge_rel32", ("l", "res_ddone")),
        I("movzx_r32_m8", "eax", ("m", "rsi", 0)),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "res_d_app")),
        I("cmp_r64_imm", "rax", 0xFE), I("je_rel32", ("l", "res_d_hole")),
        I("cmp_r64_imm", "rax", 7), I("jge_rel32", ("l", "exit3")),
    ]
    if not R.fuse_s:
        p += [I("cmp_r64_imm", "rax", Tag.s), I("je_rel32", ("l", "res_d_ds"))]
    p += [
        LBL("res_d_leaf"),
        I("mov_m64_r64", ("m", "r14", 0), "rax"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_m64_r64", ("m", "r14", 8), "rcx"),
        I("mov_m64_r64", ("m", "r14", 16), "rcx"),
        I("jmp_rel32", ("l", "res_d_st")),
        LBL("res_d_hole"),
        I("mov_m64_imm32", ("m", "r14", 0), IR_HOLE),
        I("mov_r32_m32", "eax", ("m", "rsi", 1)),
        I("mov_m64_r64", ("m", "r14", 8), "rax"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_m64_r64", ("m", "r14", 16), "rcx"),
        I("jmp_rel32", ("l", "res_d_st")),
    ]
    if not R.fuse_s:
        p += [
            LBL("res_d_ds"),
            I("mov_m64_imm32", ("m", "r14", 0), Tag.APP),
            I("mov_r64_rip", "rax", ("p", "ds")),
            I("mov_r64_m64", "rcx", ("m", "rax", 8)),
            I("mov_m64_r64", ("m", "r14", 8), "rcx"),
            I("mov_r64_m64", "rcx", ("m", "rax", 16)),
            I("mov_m64_r64", ("m", "r14", 16), "rcx"),
            I("jmp_rel32", ("l", "res_d_st")),
        ]
    p += [
        LBL("res_d_app"),
        I("mov_r32_m32", "eax", ("m", "rsi", 1)),
        I("cmp_r64_r64", "rax", "r15"), I("jge_rel32", ("l", "exit3")),
    ] + _mul24() + [
        I("add_r64_r64", "rax", "rdi"),
        I("mov_m64_r64", ("m", "r14", 8), "rax"),
        I("mov_r32_m32", "eax", ("m", "rsi", 5)),
        I("cmp_r64_r64", "rax", "r15"), I("jge_rel32", ("l", "exit3")),
    ] + _mul24() + [
        I("add_r64_r64", "rax", "rdi"),
        I("mov_m64_r64", ("m", "r14", 16), "rax"),
        I("mov_m64_imm32", ("m", "r14", 0), Tag.APP),
        LBL("res_d_st"),
        I("inc_r64", "r15"), I("add_r64_imm", "rsi", 9),
        I("add_r64_imm", "r14", 24), I("jmp_rel32", ("l", "res_dloop")),
        LBL("res_ddone"), I("ret"),
    ]
    return p


def r_res_reduce(R: Realization, ctx: Ctx) -> Program:
    """ir_binit/ir_bloop with graft: per arg root — arena reset, then a
    postorder copy of the residual into the arena where hole children
    remap to the arg pointer (residual[1 := arg] at cell level), reduce
    the grafted root, one NF line.  remap(child): if child is inside
    [rescells, rescells+24*resn) it is a residual cell — hole -> arg,
    else rescells + delta (contiguous mkapp run); outside stays as-is
    (ds template pointers)."""
    iat = ctx["iat"]
    p: Program = [
        LBL("ir_binit"),
        I("xor_r32_r32", "eax", "eax"),
        I("mov_rip_r64", ("p", "irj"), "rax"),
        LBL("ir_bloop"),
        I("mov_r64_rip", "rax", ("p", "irj")),
        I("mov_r64_rip", "rcx", ("p", "irnroots")),
        I("cmp_r64_r64", "rax", "rcx"), I("jge_rel32", ("l", "ir_bdone")),
        # arena reset: decommit the used span (VA retained)
        I("mov_r64_rip", "rcx", ("p", "irarena")),
        I("cmp_r64_r64", "rbp", "rcx"), I("jbe_rel32", ("l", "ir_nofree")),
        I("mov_r64_r64", "rdx", "rbp"), I("sub_r64_r64", "rdx", "rcx"),
        I("mov_r32_imm32", "r8d", MEM_DECOMMIT),
        I("call_mrip", iat("VirtualFree")),
        I("mov_r64_rip", "rbp", ("p", "irarena")),
        I("mov_r64_r64", "rbx", "rbp"),
        LBL("ir_nofree"),
        I("mov_r64_rip", "rbx", ("p", "irarena")),
        I("mov_r64_r64", "rbp", "rbx"),
        # ---- graft: residual[hole := arg] into fresh arena cells ----
        # r14 = arg root ptr; r13 = rescell cursor; r15 = src end
        I("mov_r64_rip", "rax", ("p", "irj")), I("shl_r64_imm8", "rax", 3),
        I("mov_r64_rip", "rcx", ("p", "irroots")), I("add_r64_r64", "rax", "rcx"),
        I("mov_r64_m64", "r14", ("m", "rax", 0)),
        I("mov_rip_r64", ("p", "resarg"), "r14"),
        I("mov_r64_rip", "r13", ("p", "rescells")),
        I("mov_r64_r64", "r12", "r13"),    # hoisted: residual block base
        I("mov_r64_rip", "rax", ("p", "resn")),
    ] + _mul24() + [
        I("mov_r64_r64", "r15", "r13"), I("add_r64_r64", "r15", "rax"),
        # resdelta = rbx - rescells (out_base - src_base)
        I("mov_r64_r64", "rax", "rbx"), I("sub_r64_r64", "rax", "r13"),
        I("mov_rip_r64", ("p", "resdelta"), "rax"),
        LBL("res_gloop"),
        I("cmp_r64_r64", "r13", "r15"), I("jge_rel32", ("l", "res_gdone")),
        I("mov_r64_m64", "rax", ("m", "r13", 0)),
        I("test_r64_r64", "rax", "rax"), I("jne_rel32", ("l", "res_gleaf")),
        # APP cell: remap l (then r) INLINED — child below rescells or at/
        # beyond resend -> verbatim; in range: hole -> r14 (resarg),
        # else +resdelta.  invariants in r12/r15/r14 across mkapp calls.
        I("mov_r64_m64", "rax", ("m", "r13", 8)),
        I("cmp_r64_r64", "rax", "r12"), I("jb_rel32", ("l", "res_g_l")),
        I("cmp_r64_r64", "rax", "r15"), I("jge_rel32", ("l", "res_g_l")),
        I("cmp_m64_imm", ("m", "rax", 0), IR_HOLE),
        I("jne_rel32", ("l", "res_g_ld")),
        I("mov_r64_r64", "rax", "r14"), I("jmp_rel32", ("l", "res_g_l")),
        LBL("res_g_ld"),
        I("mov_r64_rip", "rdx", ("p", "resdelta")), I("add_r64_r64", "rax", "rdx"),
        LBL("res_g_l"),
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_m64", "rax", ("m", "r13", 16)),
        I("cmp_r64_r64", "rax", "r12"), I("jb_rel32", ("l", "res_g_r")),
        I("cmp_r64_r64", "rax", "r15"), I("jge_rel32", ("l", "res_g_r")),
        I("cmp_m64_imm", ("m", "rax", 0), IR_HOLE),
        I("jne_rel32", ("l", "res_g_rd")),
        I("mov_r64_r64", "rax", "r14"), I("jmp_rel32", ("l", "res_g_r")),
        LBL("res_g_rd"),
        I("mov_r64_rip", "rdx", ("p", "resdelta")), I("add_r64_r64", "rax", "rdx"),
        LBL("res_g_r"),
        I("mov_r64_r64", "rsi", "rax"),
        I("jmp_rel32", ("l", "res_gmk")),
        LBL("res_gleaf"),          # leaf or hole: copy tag verbatim
        I("mov_r64_r64", "rdx", "rax"),
        I("call_rel32", ("l", "mkleaf")),
        I("jmp_rel32", ("l", "res_gstep")),
        LBL("res_gmk"),
        I("call_rel32", ("l", "mkapp")),
        LBL("res_gstep"),
        I("add_r64_imm", "r13", 24), I("jmp_rel32", ("l", "res_gloop")),
        LBL("res_gdone"),
        # graft root: out_base + 24*resroot — out_base = rbx0 =
        # rescells + resdelta; if the root record is a hole the whole
        # residual IS the argument
        I("mov_r64_rip", "rax", ("p", "resroot")),
    ] + _mul24() + [
        I("mov_r64_r64", "rcx", "rax"),
        I("mov_r64_rip", "rax", ("p", "rescells")), I("add_r64_r64", "rcx", "rax"),
        # r12 = out twin of the residual root cell; flags-free before cmp
        I("mov_r64_rip", "r12", ("p", "resdelta")), I("add_r64_r64", "r12", "rcx"),
        I("mov_r64_m64", "rax", ("m", "rcx", 0)),
        I("cmp_r64_imm", "rax", IR_HOLE),
        I("jne_rel32", ("l", "res_rooted")),
        I("mov_r64_rip", "r12", ("p", "resarg")),
        LBL("res_rooted"),
        I("xor_r32_r32", "r15d", "r15d"),
        LBL("ir_rloop"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "ir_red_done")),
        I("mov_r64_r64", "r12", "rax"), I("inc_r64", "r15"),
    ]
    if R.fuel is not None:
        p += [I("cmp_r64_imm", "r15", R.fuel), I("jge_rel32", ("l", "exit2"))]
    p += [
        I("jmp_rel32", ("l", "ir_rloop")),
        LBL("ir_red_done"),
        I("mov_r64_rip", "rax", ("p", "irsteps")),
        I("add_r64_r64", "rax", "r15"),
        I("mov_rip_r64", ("p", "irsteps"), "rax"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "count_nodes")),
        I("lea_r64_m64", "rdx", ("m", "rax", 0)), I("add_r64_r64", "rdx", "rdx"),
        I("add_r64_imm", "rdx", 16),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_r64", "r14", "rax"),
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "emit_nf")),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x0A), I("inc_r64", "rsi"),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_r64", "rdx", "r14"),
        I("mov_r64_r64", "r8", "rsi"), I("sub_r64_r64", "r8", "r14"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        I("mov_r64_rip", "rax", ("p", "irj")), I("inc_r64", "rax"),
        I("mov_rip_r64", ("p", "irj"), "rax"),
        I("jmp_rel32", ("l", "ir_bloop")),
        LBL("ir_bdone"),
        I("mov_r64_rip", "rcx", ("p", "irbuf")),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "r8d", MEM_RELEASE),
        I("call_mrip", iat("VirtualFree")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_rip", "rax", ("p", "irnstreams")), I("inc_r64", "rax"),
        I("mov_rip_r64", ("p", "irnstreams"), "rax"),
        I("jmp_rel32", ("l", "ir_sloop")),
        LBL("ir_sdone"),
        I("mov_r64_rip", "rax", ("p", "irnstreams")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "r15", ("p", "irsteps")),
    ]
    return p


def r_grow_heap_ir(R: Realization, ctx: Ctx) -> Program:
    """grow_heap (IR): commit-ahead inside the reserved arena —
    VirtualAlloc(rbp, chunk, MEM_COMMIT, RW); rbp += chunk on success.
    Also bounds the depack-region ds build (its rbp = region end)."""
    iat = ctx["iat"]
    return [
        LBL("grow_heap"),
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_r64_r64", "rcx", "rbp"),
        I("mov_r64_imm", "rdx", R.chunk_bytes),
        I("mov_r32_imm32", "r8d", MEM_COMMIT),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "grow_fail")),
        I("mov_r64_imm", "rax", R.chunk_bytes), I("add_r64_r64", "rbp", "rax"),
        I("add_r64_imm", "rsp", 0x28), I("ret"),
        LBL("grow_fail"), I("mov_r32_imm32", "ecx", 4),
        I("call_mrip", iat("ExitProcess")),
    ]


# Ordered routine names = emission order.  "st_s" emits iff R.fuse_s,
# "build_ds" iff not R.fuse_s (handled in program()).
ROUTINES: Tuple[str, ...] = (
    "entry", "parse", "reduce", "stats", "exits",
    "grow_heap", "mkleaf", "mkapp", "mkstk",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

# IR variant: same reducer core, different front end — no token parser,
# no parse stack (mkstk/mkstk unused); entry/read/depack/reduce replace
# entry/parse/reduce.  "ir_reduce" is the batch loop.
ROUTINES_IR: Tuple[str, ...] = (
    "ir_entry", "ir_read", "ir_depack", "ir_reduce", "stats", "exits",
    "grow_heap_ir", "mkleaf", "mkapp",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

IMPORTS_IR: Tuple[str, ...] = IMPORTS + ("VirtualFree",)

_BUILDERS: Dict[str, Callable[[Realization, Ctx], Program]] = {
    name[2:]: fn for name, fn in list(globals().items())
    if name.startswith("r_")
}


def _emit(R: Realization, names: Tuple[str, ...]) -> Program:
    ctx = _ctx()
    p: Program = []
    for name in names:
        if name == "st_s" and not R.fuse_s:
            continue
        if name == "build_ds" and R.fuse_s:
            continue
        p += _BUILDERS[name](R, ctx)
    return p


def program(R: Realization) -> Program:
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    return _emit(R, ROUTINES)


def program_ir(R: Realization) -> Program:
    """Packed-IR batch kernel: depack replaces the token parse; the
    reducer core is shared verbatim."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    return _emit(R, ROUTINES_IR)


@dataclass(frozen=True)
class Routines:
    name: str          # "x86_64.win64.lo"
    isa: str           # "x86_64"
    abi: str           # "win64"
    orders: tuple      # ("lo",)  — cd NOT here; declared in toolchain.py
    routines: tuple    # ROUTINES
    program: Callable  # program(R) -> Program
    imports: tuple
    data_slots: tuple


X86_64_WIN64 = Routines(
    name="x86_64.win64.lo",
    isa="x86_64",
    abi="win64",
    orders=("lo",),
    routines=ROUTINES,
    program=program,
    imports=IMPORTS,
    data_slots=DATA_SLOTS,
)


X86_64_WIN64_IR = Routines(
    name="x86_64.win64.ir",
    isa="x86_64",
    abi="win64",
    orders=("lo",),
    routines=ROUTINES_IR,
    program=program_ir,
    imports=IMPORTS_IR,
    data_slots=DATA_SLOTS_IR,
)


# Residual-application variant (Futamura-2 artifact): R.payload holds
# pack_ir(residual) — the specialized program's static part — baked
# into .data.  At entry the kernel depacks it once into a permanent
# region (VAR records become hole cells); each input stream supplies
# dynamic arguments as packed-IR roots, grafted into the residual's
# holes before reduction.  Same wire contract as the IR kernel.
ROUTINES_RES: Tuple[str, ...] = (
    "res_entry", "ir_read", "ir_depack", "res_reduce", "stats", "exits",
    "grow_heap_ir", "mkleaf", "mkapp", "res_depack",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)


def data_slots_res(R: Realization) -> tuple:
    if not R.payload:
        raise NotRealized("residual realization requires R.payload")
    return DATA_SLOTS_IR + (
        ("resblob", len(R.payload), R.payload),
        ("rescells", 8), ("resn", 8), ("resroot", 8),
        ("resarg", 8), ("resdelta", 8),
    )


def program_res(R: Realization) -> Program:
    """Residual-application kernel: graft loop + shared reducer core."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    return _emit(R, ROUTINES_RES)


X86_64_WIN64_RES = Routines(
    name="x86_64.win64.res",
    isa="x86_64",
    abi="win64",
    orders=("lo",),
    routines=ROUTINES_RES,
    program=program_res,
    imports=IMPORTS_IR,
    data_slots=data_slots_res,
)


def _dummy_symbols(slots=DATA_SLOTS,
                   imports: Tuple[str, ...] = IMPORTS) -> Dict[str, int]:
    syms = {f"iat_{n}": 0x2000 + i * 8 for i, n in enumerate(imports)}
    off = 0x3000
    for slot in slots:
        syms[slot[0]] = off
        off += slot[1]
    return syms


def _routine_sizes(R: Realization, names: Tuple[str, ...] = ROUTINES
                   ) -> Dict[str, int]:
    ctx = _ctx()
    out: Dict[str, int] = {}
    for name in names:
        if name == "st_s" and not R.fuse_s:
            continue
        if name == "build_ds" and R.fuse_s:
            continue
        frag = _BUILDERS[name](R, ctx)
        out[name] = sum(len(encode(i[1:])) for i in frag if i[0] != "label")
    return out


def main() -> int:
    ok = True
    for tag, R in (("default", Realization()), ("fuse_s", Realization(fuse_s=True))):
        prog = program(R)
        text, labels = _isa.assemble(prog, _dummy_symbols())
        sizes = _routine_sizes(R)
        print(f"  {tag}: {len(text)}B text, routines "
              + " ".join(f"{n}={s}" for n, s in sizes.items()))
        has_ds, has_s = "build_ds" in labels, "st_s" in labels
        if has_ds != (not R.fuse_s) or has_s != R.fuse_s:
            print(f"  FAIL {tag}: build_ds={has_ds} st_s={has_s}")
            ok = False
        prog = program_ir(R)
        text, labels = _isa.assemble(
            prog, _dummy_symbols(DATA_SLOTS_IR, IMPORTS_IR))
        sizes = _routine_sizes(R, ROUTINES_IR)
        print(f"  {tag}.ir: {len(text)}B text, routines "
              + " ".join(f"{n}={s}" for n, s in sizes.items()))
        has_ds, has_s = "build_ds" in labels, "st_s" in labels
        if has_ds != (not R.fuse_s) or has_s != R.fuse_s:
            print(f"  FAIL {tag}.ir: build_ds={has_ds} st_s={has_s}")
            ok = False
    print(f"{'OK' if ok else 'FAIL'} routines_x86_64_win64")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
