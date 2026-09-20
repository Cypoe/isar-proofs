"""
routines_x86_64_win64_cd — the reducer PROGRAM (asm-as-data) for
ISA=x86_64, ABI=win64 (kernel32 IAT), order="cd" (complete development).

SECOND routines module — the lo reducer lives untouched in
routines_x86_64_win64.py; strategies stay separate data.  The shared
machinery SHAPE is copied verbatim (entry/parse/exits/heap/allocators/
count/emit/itoa/build_ds — these are strategy-independent); only the
reducer core differs: `step` + `st_*` (one leftmost-outermost redex per
call) is replaced by `cd` + `cd_*` (every round-start redex per call).

Semantics — oracle is graph_runtime.reduce_tree_cd (the `graph.cd`
piece) / reduce.py `reduce_cd`.  Complete development as recursion:

  cd(t): t atom            -> t
         I x               -> cd(x)
         K a b             -> cd(a)
         W f x             -> (cd f)(cd x)(cd x)   (zx shared: dag)
         B f g x           -> (cd f)((cd g)(cd x))
         C f x y           -> ((cd f)(cd y))(cd x)
         [fuse_s] S f g x  -> ((cd f)(cd x))((cd g)(cd x))
         app f x           -> (cd f)(cd x)          (congruence)

MARKING SCHEME — none, by design (documented choice over the two-phase
mark/contract walk): the input term is immutable during a round, so the
redex dispatch above IS the round-start marking — every node whose
pattern matches at dispatch time is a marked redex, and its contractum
is built from already-developed parts.  Contractum app nodes are FRESH
allocations and are never re-dispatched inside the same call, so redexes
created by contraction wait for the next round.  The tag field stays a
clean u64 (0..6) — no mark bit, nothing for tag dispatch to filter.
Round fixpoint is detected by `cdhit` (.data u64): every contraction arm
increments it, `red_loop` zeroes it per round; a round that leaves it 0
contracted nothing => NF reached (a term with any redex always contracts
it — flag==0 <=> fixpoint, no structural compare needed).

Rounds (r15) — NOT steps.  The unit is the cd pass: r15 counts every cd
call including the final no-contraction round, matching reduce_tree_cd's
`rounds` exactly (parity, not ±offset).  stderr reports `rounds=N
alloc=M` — never `steps=`.  R.fuel limits ROUNDS -> exit 2 (same code as
lo fuel); exit 3 bad input, exit 4 OOM.

Shares the lo module's call-site mod-16 discipline: every `call` site
keeps rsp == 0 mod 16 (callee entry rsp == 8; kernel32 wrappers do
sub rsp,0x28).  cd's frame pushes r12/r13/r14 (entry rsp==8 -> body==0);
arm temporaries go through push+sub-8 pairs (16B, parity-preserving).
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

# .data slots (labels; 8 bytes each unless noted).  Same shape as the lo
# module plus `cdhit` — the per-round "a contraction happened" flag that
# `red_loop` uses for fixpoint detection (see header).
DATA_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("hin", 8), ("hout", 8), ("herr", 8), ("nread", 8), ("nw", 8),
    ("nalloc", 8), ("ds", 8), ("cdhit", 8), ("scratch", 64),
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


# ----------------------------------------------------------------------
# strategy-independent machinery — verbatim shape from the lo module
# ----------------------------------------------------------------------

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
    """do_reduce/red_loop (+ fuel check when R.fuel — fuel counts ROUNDS)
    -> count_nodes -> exact output alloc -> emit_nf -> WriteFile stdout.

    One iteration = one complete-development round: clear cdhit, cd(root),
    count the round, then fixpoint iff nothing contracted."""
    iat = ctx["iat"]
    p: Program = [
        # ---- reduce loop (r15 = rounds) ----
        LBL("do_reduce"), I("xor_r32_r32", "r15d", "r15d"),
        LBL("red_loop"),
        I("xor_r32_r32", "eax", "eax"),
        I("mov_rip_r64", ("p", "cdhit"), "rax"),  # clear round flag
        I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "cd")),
        I("mov_r64_r64", "r12", "rax"), I("inc_r64", "r15"),
        I("mov_r64_rip", "rax", ("p", "cdhit")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "red_done")),
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
    """stderr line `rounds=N alloc=M` via scratch buffer + itoa.
    Rounds, NEVER `steps=` — the units differ (see header)."""
    iat = ctx["iat"]
    p: Program = [
        I("lea_r64_rip", "rsi", ("p", "scratch")),
    ]
    _stats_str(p, "rounds=")
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
    """exit 0; exit2 fuel (rounds) exhausted, exit3 bad input, exit4 OOM."""
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


# ----------------------------------------------------------------------
# cd reducer core — replaces step/st_*.  cd(rdi=t) -> rax = the complete
# development of t: every round-start redex contracted exactly once, new
# redexes deferred (contractum nodes are fresh and never re-dispatched).
#
# Frame: push r12/r13/r14 (entry rsp==8 mod16 -> body==0, every internal
# call site stays at ==0).  r12=t, r13=t.l (f), r14=t.r (x).  Deeper
# selectors are reloaded from the immutable input term per arm:
#   fl = [r13+8], fr = [r13+16], fll = [fl+8], flr = [fl+16].
# Every contraction arm does `inc [rip+cdhit]` — the round flag.
# ----------------------------------------------------------------------

def r_cd(R: Realization, ctx: Ctx) -> Program:
    """cd dispatch — same redex-shape walk as the lo `step` head
    (norm, konst, dup, comp, swap, [s]), but every arm builds the fully
    developed contractum instead of the one-step contractum."""
    p: Program = [
        LBL("cd"),
        I("push_r64", "r12"), I("push_r64", "r13"), I("push_r64", "r14"),
        I("mov_r64_r64", "r12", "rdi"),
        I("cmp_m64_imm", ("m", "r12", 0), Tag.APP),
        I("jne_rel32", ("l", "cd_atom")),
        I("mov_r64_m64", "r13", ("m", "r12", 8)),    # f
        I("mov_r64_m64", "r14", ("m", "r12", 16)),   # x
        I("cmp_m64_imm", ("m", "r13", 0), Tag.norm),
        I("je_rel32", ("l", "cd_norm")),
        I("cmp_m64_imm", ("m", "r13", 0), Tag.APP),
        I("jne_rel32", ("l", "cd_cong")),
        I("mov_r64_m64", "rax", ("m", "r13", 8)),    # fl
        I("cmp_m64_imm", ("m", "rax", 0), Tag.konst),
        I("je_rel32", ("l", "cd_konst")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.dup),
        I("je_rel32", ("l", "cd_dup")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.APP),
        I("jne_rel32", ("l", "cd_cong")),
        I("mov_r64_m64", "rdx", ("m", "rax", 8)),    # fll
        I("cmp_m64_imm", ("m", "rdx", 0), Tag.comp),
        I("je_rel32", ("l", "cd_comp")),
        I("cmp_m64_imm", ("m", "rdx", 0), Tag.swap),
        I("je_rel32", ("l", "cd_swap")),
    ]
    if R.fuse_s:
        p += [
            I("cmp_m64_imm", ("m", "rdx", 0), Tag.s),
            I("je_rel32", ("l", "cd_s")),
        ]
    p += [
        I("jmp_rel32", ("l", "cd_cong")),
    ]
    return p


def r_cd_norm(R: Realization, ctx: Ctx) -> Program:
    """I x => cd x."""
    return [
        LBL("cd_norm"), I("inc_mrip", ("p", "cdhit")),
        I("mov_r64_r64", "rdi", "r14"), I("call_rel32", ("l", "cd")),
        I("jmp_rel32", ("l", "cd_out")),
    ]


def r_cd_konst(R: Realization, ctx: Ctx) -> Program:
    """K a b => cd a   (a = fr = [r13+16]; b is dropped undeveloped)."""
    return [
        LBL("cd_konst"), I("inc_mrip", ("p", "cdhit")),
        I("mov_r64_m64", "rdi", ("m", "r13", 16)),
        I("call_rel32", ("l", "cd")),
        I("jmp_rel32", ("l", "cd_out")),
    ]


def r_cd_dup(R: Realization, ctx: Ctx) -> Program:
    """W f x => (cd f)(cd x)(cd x); fr=[r13+16]=f, r14=x.
    zx = cd(x) computed once and shared — the contractum is a dag, like
    the oracle's interned mk_app."""
    return [
        LBL("cd_dup"), I("inc_mrip", ("p", "cdhit")),
        I("mov_r64_r64", "rdi", "r14"), I("call_rel32", ("l", "cd")),
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),   # zx @ [rsp+8]
        I("mov_r64_m64", "rdi", ("m", "r13", 16)),          # fr = f
        I("call_rel32", ("l", "cd")),                       # cd(f)
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_m64", "rsi", ("m", "rsp", 8)),           # zx
        I("call_rel32", ("l", "mkapp")),                    # (cd f) zx
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_m64", "rsi", ("m", "rsp", 8)),           # zx
        I("add_r64_imm", "rsp", 16),
        I("call_rel32", ("l", "mkapp")),                    # ((cd f) zx) zx
        I("jmp_rel32", ("l", "cd_out")),
    ]


def r_cd_comp(R: Realization, ctx: Ctx) -> Program:
    """B f g x => (cd f)((cd g)(cd x)); flr=[fl+16]=f, fr=[r13+16]=g, r14=x."""
    return [
        LBL("cd_comp"), I("inc_mrip", ("p", "cdhit")),
        I("mov_r64_m64", "rax", ("m", "r13", 8)),           # fl
        I("mov_r64_m64", "rdi", ("m", "rax", 16)),          # flr = f
        I("call_rel32", ("l", "cd")),
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),   # cd(f) @ [rsp+8]
        I("mov_r64_m64", "rdi", ("m", "r13", 16)),          # fr = g
        I("call_rel32", ("l", "cd")),
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),   # cd(g) @ [rsp+8]
                                                            # cd(f) @ [rsp+24]
        I("mov_r64_r64", "rdi", "r14"),
        I("call_rel32", ("l", "cd")),                       # cd(x)
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 8)),           # cd(g)
        I("call_rel32", ("l", "mkapp")),                    # (cd g)(cd x)
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 24)),          # cd(f)
        I("add_r64_imm", "rsp", 32),
        I("call_rel32", ("l", "mkapp")),                    # (cd f)((cd g)(cd x))
        I("jmp_rel32", ("l", "cd_out")),
    ]


def r_cd_swap(R: Realization, ctx: Ctx) -> Program:
    """C f x y => ((cd f)(cd y))(cd x); flr=[fl+16]=f, r14=y, fr=[r13+16]=x."""
    return [
        LBL("cd_swap"), I("inc_mrip", ("p", "cdhit")),
        I("mov_r64_m64", "rax", ("m", "r13", 8)),           # fl
        I("mov_r64_m64", "rdi", ("m", "rax", 16)),          # flr = f
        I("call_rel32", ("l", "cd")),
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),   # cd(f) @ [rsp+8]
        I("mov_r64_r64", "rdi", "r14"),                     # y
        I("call_rel32", ("l", "cd")),
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 8)),
        I("call_rel32", ("l", "mkapp")),                    # (cd f)(cd y)
        I("mov_m64_r64", ("m", "rsp", 8), "rax"),           # save partial
        I("mov_r64_m64", "rdi", ("m", "r13", 16)),          # fr = x
        I("call_rel32", ("l", "cd")),
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 8)),
        I("add_r64_imm", "rsp", 16),
        I("call_rel32", ("l", "mkapp")),                    # ((cd f)(cd y))(cd x)
        I("jmp_rel32", ("l", "cd_out")),
    ]


def r_cd_s(R: Realization, ctx: Ctx) -> Program:
    """sβ development (fuse_s=True only):
    S f g x => ((cd f)(cd x))((cd g)(cd x)); flr=[fl+16]=f, fr=[r13+16]=g."""
    return [
        LBL("cd_s"), I("inc_mrip", ("p", "cdhit")),
        I("mov_r64_r64", "rdi", "r14"),
        I("call_rel32", ("l", "cd")),                       # zx = cd(x)
        I("push_r64", "rax"), I("push_r64", "rax"),         # zx @ [rsp],[rsp+8]
        I("mov_r64_m64", "rax", ("m", "r13", 8)),           # fl
        I("mov_r64_m64", "rdi", ("m", "rax", 16)),          # flr = f
        I("call_rel32", ("l", "cd")),
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_m64", "rsi", ("m", "rsp", 8)),           # zx
        I("call_rel32", ("l", "mkapp")),                    # left = (cd f)(cd x)
        I("mov_m64_r64", ("m", "rsp", 8), "rax"),           # left @ [rsp+8]
        I("mov_r64_m64", "rdi", ("m", "r13", 16)),          # fr = g
        I("call_rel32", ("l", "cd")),
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_m64", "rsi", ("m", "rsp", 0)),           # zx
        I("call_rel32", ("l", "mkapp")),                    # (cd g)(cd x)
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 8)),           # left
        I("add_r64_imm", "rsp", 16),
        I("call_rel32", ("l", "mkapp")),
        I("jmp_rel32", ("l", "cd_out")),
    ]


def r_cd_tail(R: Realization, ctx: Ctx) -> Program:
    """cd_atom/cd_cong/cd_out: atoms return themselves; the congruence
    case rebuilds app(cd f, cd x); epilogue restores the frame."""
    return [
        LBL("cd_atom"), I("mov_r64_r64", "rax", "r12"),
        I("jmp_rel32", ("l", "cd_out")),
        LBL("cd_cong"),
        I("mov_r64_r64", "rdi", "r13"), I("call_rel32", ("l", "cd")),
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),   # cd(f) @ [rsp+8]
        I("mov_r64_r64", "rdi", "r14"), I("call_rel32", ("l", "cd")),
        I("mov_r64_r64", "rsi", "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 8)),
        I("add_r64_imm", "rsp", 16),
        I("call_rel32", ("l", "mkapp")),                    # (cd f)(cd x)
        LBL("cd_out"),
        I("pop_r64", "r14"), I("pop_r64", "r13"), I("pop_r64", "r12"), I("ret"),
    ]


# ----------------------------------------------------------------------
# output helpers + derived_s template — verbatim shape from the lo module
# ----------------------------------------------------------------------

def r_count_nodes(R: Realization, ctx: Ctx) -> Program:
    """count_nodes(rdi) -> rax.  Counts dag-shared children once per
    occurrence — that is exactly the emit size (emit_nf prints the same
    shared subtree at each occurrence)."""
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


# Ordered routine names = emission order.  "cd_s" emits iff R.fuse_s,
# "build_ds" iff not R.fuse_s (handled in program()).
ROUTINES: Tuple[str, ...] = (
    "entry", "parse", "reduce", "stats", "exits",
    "grow_heap", "mkleaf", "mkapp", "mkstk",
    "cd", "cd_norm", "cd_konst", "cd_dup", "cd_comp", "cd_swap", "cd_s",
    "cd_tail", "count_nodes", "emit_nf", "itoa", "build_ds",
)

_BUILDERS: Dict[str, Callable[[Realization, Ctx], Program]] = {
    name[2:]: fn for name, fn in list(globals().items())
    if name.startswith("r_")
}


def program(R: Realization) -> Program:
    if R.order != "cd":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    ctx = _ctx()
    p: Program = []
    for name in ROUTINES:
        if name == "cd_s" and not R.fuse_s:
            continue
        if name == "build_ds" and R.fuse_s:
            continue
        p += _BUILDERS[name](R, ctx)
    return p


@dataclass(frozen=True)
class Routines:
    name: str          # "x86_64.win64.cd"
    isa: str           # "x86_64"
    abi: str           # "win64"
    orders: tuple      # ("cd",)
    routines: tuple    # ROUTINES
    program: Callable  # program(R) -> Program
    imports: tuple
    data_slots: tuple


X86_64_WIN64_CD = Routines(
    name="x86_64.win64.cd",
    isa="x86_64",
    abi="win64",
    orders=("cd",),
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
        if name == "cd_s" and not R.fuse_s:
            continue
        if name == "build_ds" and R.fuse_s:
            continue
        frag = _BUILDERS[name](R, ctx)
        out[name] = sum(len(encode(i[1:])) for i in frag if i[0] != "label")
    return out


# ----------------------------------------------------------------------
# self-test: assemble both builds, verify refusal discipline, emit a real
# exe through the spec toolchain chain, probe it against the oracles
# (graph_runtime.reduce_tree_cd / reduce_tree_lo for the expanded build;
# reduce.py reduce_cd for the fused build — its round count is one less,
# it does not count the final fixpoint-detection round).
# ----------------------------------------------------------------------

def _emit_exe(R: Realization, path: str) -> str:
    """emit(R, tc="x86_64.win64.cd") -> write exe — the real chain
    (toolchain.resolve -> isa.assemble -> target.pack)."""
    import seed
    import toolchain
    pe = seed.emit(R, tc=toolchain.by_name("x86_64.win64.cd"))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(pe)
    return path


def _cd_mirror(t):
    """Tree complete development — the exact spec the asm `cd` routine
    implements (basis rules incl. dup/swap + fused sβ).  This is the
    round-count oracle: graph.cd on the same terms can report FEWER
    rounds because its repr()/fwd redirect chasing and interned mk_app
    re-develop an already-contracted node reached again in the same
    round (a slice of the next round absorbed early).  The native heap
    has no redirects/interning: one pass = one literal development."""
    from reduce import app
    if t.k.name != "APP":
        return t
    f, x = t.l, t.r
    if f.k.name == "NORM":
        return _cd_mirror(x)
    if f.k.name == "APP":
        fl, fr = f.l, f.r
        if fl.k.name == "KONST":
            return _cd_mirror(fr)
        if fl.k.name == "DUP":
            zx = _cd_mirror(x)
            return app(app(_cd_mirror(fr), zx), zx)
        if fl.k.name == "APP":
            fll, flr = fl.l, fl.r
            if fll.k.name == "COMP":
                return app(_cd_mirror(flr),
                           app(_cd_mirror(fr), _cd_mirror(x)))
            if fll.k.name == "SWAP":
                return app(app(_cd_mirror(flr), _cd_mirror(x)),
                           _cd_mirror(fr))
            if fll.k.name == "S":
                return app(app(_cd_mirror(flr), _cd_mirror(x)),
                           app(_cd_mirror(fr), _cd_mirror(x)))
    return app(_cd_mirror(f), _cd_mirror(x))


def _mirror_reduce(t, fuel: int = 10_000):
    """Iterate _cd_mirror to fixpoint; rounds counted like the exe and
    graph.cd (the final no-contraction pass included)."""
    cur, n = t, 0
    while n < fuel:
        nxt = _cd_mirror(cur)
        n += 1
        if nxt == cur:
            break
        cur = nxt
    return cur, n


def _probes(hreduce, fused: bool):
    """(label, token_text, host_term).  Text covers the whole input
    alphabet; W/C terms are built as host trees and tokenized by hand
    (bcd.parse_prog only knows I K S @).  The fused (surface) oracle
    alphabet is I/K/B/S — dup/swap have no rule in the IStep mirror."""
    from reduce import app, I as HI, KK, S as HS, B as HB, D as HD, C as HC

    def toks(t):
        if t.k.name == "APP":
            return toks(t.l) + " " + toks(t.r) + " @"
        return {"NORM": "I", "KONST": "K", "S": "S",
                "COMP": "B", "DUP": "W", "SWAP": "C"}[t.k.name]

    church2 = app(app(HS, app(app(HS, app(KK, HS)), KK)), app(app(HS, app(
        app(HS, app(KK, HS)), KK)), app(KK, HI)))  # small applied church term
    cases = [
        ("atom I", "I", None),
        ("I K -> K", "I K @", None),
        ("K S I -> S", "K S @ I @", None),
        ("S K K I -> I", "S K @ K @ I @", None),
        ("disjoint redexes (I K)(I S): 1 contraction round", None,
         app(app(HI, KK), app(HI, HS))),
        ("nested redexes I(I(I K)): 1 contraction round", None,
         app(HI, app(HI, app(HI, KK)))),
        ("B comp: B K I S -> K (I S) -> K S", None,
         app(app(app(HB, KK), HI), HS)),
        ("church (2 2) applied", None, church2),
    ]
    if not fused:
        cases += [
            ("W dup: W K I -> K I I -> I", None,
             app(app(HD, KK), HI)),
            ("C swap: C K I B -> K B I -> B", None,
             app(app(app(HC, KK), HI), HB)),
        ]
    out = []
    for label, text, t in cases:
        if t is not None:
            text = toks(t)
        out.append((label, text, t))
    return out


def _run_probes(R: Realization, exe: str, hreduce, bcd) -> bool:
    """Run the built exe on every probe; NF must equal the cd oracle NF
    and the lo NF class; rounds must equal the tree-cd mirror (exact —
    see _cd_mirror on why graph.cd can read one lower)."""
    import re
    import subprocess
    import seed
    import tower
    import graph_runtime

    ok = True
    for label, text, t in _probes(hreduce, R.fuse_s):
        term = t if t is not None else bcd.compile_bytecode(bcd.parse_prog(text))
        cp = subprocess.run([exe], input=text.encode(),
                            capture_output=True, timeout=600)
        out, err, rc = (cp.stdout.decode("utf-8", "replace"),
                        cp.stderr.decode("utf-8", "replace"), cp.returncode)
        m = re.search(r"rounds=(\d+)", err)
        rounds_native = int(m.group(1)) if m else -1
        good = rc == 0 and m is not None
        detail = ""
        if good:
            got = seed._parse_native_out(out)
            if R.fuse_s:
                nf_cd, rounds_ref = _mirror_reduce(term)
                nf_lo, _ = hreduce.reduce(term, fuel=1_000_000)
                # reduce.py counts without the fixpoint pass: mirror-1
                rounds_graph = hreduce.reduce_cd(term, fuel=10_000)[1] + 1
                nf_ref = nf_cd
            else:
                base = tower.translate_to_basis(term)
                nf_cd, rounds_ref = _mirror_reduce(base)
                nf_cd = tower.quote_surface(nf_cd)
                nf_g, rounds_graph, _ = graph_runtime.reduce_tree_cd(
                    term, fuel=10_000)
                nf_lo, _steps_lo, _ = graph_runtime.reduce_tree_lo(
                    term, fuel=1_000_000)
                nf_ref = nf_cd
                got = tower.quote_surface(got)
            good = (got == nf_ref) and (nf_cd == nf_lo) \
                and (rounds_native == rounds_ref)
            if not good:
                detail = (f" nf={got!r} ref={nf_ref!r} lo={nf_lo!r} "
                          f"rounds={rounds_native} mirror={rounds_ref} "
                          f"graph={rounds_graph}")
            if not good:
                print(f"  FAIL {label}: rc={rc} out={out.strip()!r} "
                      f"err={err.strip()!r}{detail}")
                ok = False
            else:
                alt = "graph.cd" if not R.fuse_s else "hreduce.cd"
                print(f"  ok {label}: nf={out.strip()[:80]!r} "
                      f"rounds={rounds_native} ({alt}={rounds_graph})")
        else:
            print(f"  FAIL {label}: rc={rc} out={out.strip()!r} "
                  f"err={err.strip()!r}")
            ok = False
    return ok


def main() -> int:
    ok = True
    for tag, R in (("default", Realization(order="cd")),
                   ("fuse_s", Realization(order="cd", fuse_s=True))):
        prog = program(R)
        text, labels = _isa.assemble(prog, _dummy_symbols())
        sizes = _routine_sizes(R)
        print(f"  {tag}: {len(text)}B text, routines "
              + " ".join(f"{n}={s}" for n, s in sizes.items()))
        has_ds, has_s = "build_ds" in labels, "cd_s" in labels
        if has_ds != (not R.fuse_s) or has_s != R.fuse_s:
            print(f"  FAIL {tag}: build_ds={has_ds} cd_s={has_s}")
            ok = False
    # honest refusal: the cd module refuses any other order
    try:
        program(Realization(order="lo"))
        print("  FAIL program(order='lo') built silently")
        ok = False
    except NotRealized as e:
        print(f"  ok refused order='lo': {e}")

    sys.setrecursionlimit(200_000)
    _seed_dir = os.path.normpath(os.path.join(_HOST, "..", "seed"))
    import seed
    import reduce as hreduce
    import bytecode_dialect as bcd
    for tag, R in (("default", Realization(order="cd")),
                   ("fuse_s", Realization(order="cd", fuse_s=True))):
        exe = _emit_exe(R, os.path.join(
            _seed_dir, "build",
            "reducer_cd.exe" if tag == "default" else "reducer_cd_fuse.exe"))
        print(f" build {tag}: {exe} ({os.path.getsize(exe)}B)")
        ok = _run_probes(R, exe, hreduce, bcd) and ok
    print(f"{'OK' if ok else 'FAIL'} routines_x86_64_win64_cd")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
