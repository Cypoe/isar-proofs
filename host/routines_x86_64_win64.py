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
DATA_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("hin", 8), ("hout", 8), ("herr", 8), ("nread", 8), ("nw", 8),
    ("nalloc", 8), ("ds", 8), ("scratch", 64),
)

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


def r_st_norm(R: Realization, ctx: Ctx) -> Program:
    """normβ: I x -> x."""
    return [
        LBL("st_norm"), I("mov_r64_r64", "rax", "r14"),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_konst(R: Realization, ctx: Ctx) -> Program:
    """konstβ (fused macro): K x y -> x."""
    return [
        LBL("st_konst"), I("mov_r64_r64", "rax", "rcx"),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_dup(R: Realization, ctx: Ctx) -> Program:
    """dupβ: W f x -> f x x."""
    return [
        LBL("st_dup"),                                 # W f x -> f x x
        I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x)
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x) x
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_swap(R: Realization, ctx: Ctx) -> Program:
    """swapβ: C f x y -> f y x."""
    return [
        LBL("st_swap"),                                # C f x y -> f y x
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
    return [
        LBL("st_comp"),                                # B f g x -> f (g x)
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
    return [
        LBL("st_s"),                               # S f g x -> (f x)(g x)
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
    return [
        LBL("st_left"),
        I("mov_r64_r64", "rdi", "r13"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "st_right")),
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")), I("jmp_rel32", ("l", "st_out")),
        LBL("st_right"),
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


def _dummy_symbols() -> Dict[str, int]:
    syms = {f"iat_{n}": 0x2000 + i * 8 for i, n in enumerate(IMPORTS)}
    off = 0x3000
    for name, sz in DATA_SLOTS:
        syms[name] = off
        off += sz
    return syms


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
    print(f"{'OK' if ok else 'FAIL'} routines_x86_64_win64")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
