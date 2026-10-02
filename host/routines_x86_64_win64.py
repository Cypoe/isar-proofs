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
from typing import Callable, Dict, Optional, Tuple

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
    # redirect store: era-ordered arena — cells below permend are
    # immutable template/vocab (never a write target), cells at or
    # above are writable; depacked input cells occupy [permend,
    # irstart) and survive per-root arena resets (pay-once).
    ("permend", 8), ("irstart", 8),
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
# redirect-only: persist zone cursor+limit — cells in [pcur0, pend)
# sit below irstart so input cells may FWD/write-back into them
# (pay-once for shared input redexes)
DATA_SLOTS_PS: Tuple[Tuple[str, int], ...] = (("pcur", 8), ("pend", 8))

# packed-IR constants — pinned by docs/adr/0005; keep in sync with
# spec_term.IR_MAGIC / IR_VERSION / IR_VAR.
IR_MAGIC = 0x30524950                # "PIR0"
IR_VERSION = 1
MEM_RESERVE = 0x2000                 # VirtualAlloc MEM_RESERVE
MEM_COMMIT = 0x1000                  # VirtualAlloc MEM_COMMIT
MEM_DECOMMIT = 0x4000                # VirtualFree MEM_DECOMMIT
MEM_RELEASE = 0x8000                 # VirtualFree MEM_RELEASE
IR_DS_AREA = 1 << 12                 # permanent region for build_ds output

# byte-egress mode (io=("stdin","bytes")): the kernel decodes the
# byte-list NF itself — spec_term._decode_bytecells mirrored in asm.
EG_MARK = 9     # marker leaf tag — never a term tag (depack refuses
                # >=7), head-inert under every rule, l=k payload.
                # sel·m0..m15 -> m_k reads the nibble off .l
EG_PROBE_FUEL = 2048        # per-probe step cap; a legit decode probe is
                            # <100 steps — exhaustion -> exit5
EG_OUT_BYTES = 16 << 20     # committed stdout frame buffer; also the
                            # malformed-spine bound (each iteration
                            # writes a byte or exits) — overflow -> exit5

VA_COMMIT_RESERVE = 0x3000
PAGE_RW = 4
STK_TAG = 7   # native-internal parse-stack cons cell tag (never a term node;
              # tags 1..6 are atoms generated from SIGNATURE); excluded from
              # nalloc so `alloc=` counts term nodes only
FWD_TAG = 10  # redirect store (R.reclaim="redirect"): a collapsed redex
              # cell becomes {tag=FWD, l=reduct} — the heap model of
              # HeapDev.lean (`redirect`/`repr`).  Native-internal like
              # STK_TAG/IR_HOLE/EG_MARK: never on the wire.

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
    ]
    if R.reclaim == "redirect":
        p += [
            # one reserved arena (commit-ahead): era ordering needs all
            # cells in a single address-ordered region
            I("xor_r32_r32", "ecx", "ecx"),
            I("mov_r64_imm", "rdx", R.ir_arena_bytes),
            I("mov_r32_imm32", "r8d", MEM_RESERVE),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
            I("mov_r64_r64", "rbx", "rax"),
            I("mov_r64_r64", "rbp", "rax"),
        ]
    else:
        # first heap chunk (sets rbx=bump, rbp=end)
        p += [I("call_rel32", ("l", "grow_heap"))]
    if not R.fuse_s:
        # build the shared derived_s template (L0-only tree); `S` tokens push it
        p += [I("call_rel32", ("l", "build_ds"))]
    p += [
        # immutable prefix ends here — everything allocated after this
        # point is a writable redirect target; token mode never resets,
        # so irstart == permend (no input tier)
        I("mov_rip_r64", ("p", "permend"), "rbx"),
        I("mov_rip_r64", ("p", "irstart"), "rbx"),
    ]
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
    if R.io[1] == "bytes":
        # decode-probe step total, reported separately — `steps=`
        # stays the query reduction count (term-mode comparable)
        _stats_str(p, " dec=")
        p += [I("mov_r64_rip", "rdi", ("p", "eb_dec")),
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
    """exit 0; exit2 fuel exhausted, exit3 bad input, exit4 OOM,
    exit5 (bytes mode) malformed byte-list NF / decode probe."""
    iat = ctx["iat"]
    p: Program = [
        I("xor_r32_r32", "ecx", "ecx"), I("call_mrip", iat("ExitProcess")),
        LBL("exit2"), I("mov_r32_imm32", "ecx", 2), I("call_mrip", iat("ExitProcess")),
        LBL("exit3"), I("mov_r32_imm32", "ecx", 3), I("call_mrip", iat("ExitProcess")),
        LBL("exit4"), I("mov_r32_imm32", "ecx", 4), I("call_mrip", iat("ExitProcess")),
    ]
    if R.io[1] == "bytes":
        p += [LBL("exit5"), I("mov_r32_imm32", "ecx", 5),
              I("call_mrip", iat("ExitProcess"))]
    return p


def r_grow_heap(R: Realization, ctx: Ctx) -> Program:
    """grow_heap: rbx=bump, rbp=chunk end.  reclaim="redirect" commits
    inside the one reserved arena (allocation order must equal address
    order for the v<C acyclicity check); "none" keeps per-chunk VAs."""
    iat = ctx["iat"]
    if R.reclaim == "redirect":
        return [
            LBL("grow_heap"),
            I("sub_r64_imm", "rsp", 0x28),
            I("mov_r64_r64", "rcx", "rbp"),
            I("mov_r64_imm", "rdx", R.chunk_bytes),
            I("mov_r32_imm32", "r8d", MEM_COMMIT),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "grow_fail")),
            I("mov_r64_imm", "rax", R.chunk_bytes),
            I("add_r64_r64", "rbp", "rax"),
            I("add_r64_imm", "rsp", 0x28), I("ret"),
            LBL("grow_fail"), I("mov_r32_imm32", "ecx", 4),
            I("call_mrip", iat("ExitProcess")),
        ]
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


def r_mkapp_p(R: Realization, ctx: Ctx) -> Program:
    """mkapp_p: rdi=f, rsi=x -> rax node in the persist zone
    [pcur, pend) — survives arena resets, so input cells (below
    irstart) may point at it.  IR builds bump pcur bounded by pend;
    token mode never resets so it aliases the ordinary bump (mkapp).
    Counted in nalloc."""
    if ctx.get("ir") and R.reclaim == "redirect":
        return [
            LBL("mkapp_p"),
            I("mov_r64_rip", "r9", ("p", "pcur")),
            I("lea_r64_m64", "rax", ("m", "r9", R.node_bytes)),
            I("mov_r64_rip", "r8", ("p", "pend")),
            I("cmp_r64_r64", "rax", "r8"),
            I("jbe_rel32", ("l", "mkp_ok")),
            I("jmp_rel32", ("l", "exit4")),         # persist zone full
            LBL("mkp_ok"),
            I("mov_rip_r64", ("p", "pcur"), "rax"),
            I("mov_r64_r64", "rax", "r9"),
            I("mov_m64_imm32", ("m", "rax", 0), Tag.APP),
            I("mov_m64_r64", ("m", "rax", 8), "rdi"),
            I("mov_m64_r64", ("m", "rax", 16), "rsi"),
            I("inc_mrip", ("p", "nalloc")), I("ret"),
        ]
    return [LBL("mkapp_p"), I("jmp_rel32", ("l", "mkapp"))]


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


def r_repr(R: Realization, ctx: Ctx) -> Program:
    """repr(rdi=t) -> rax: resolve a FWD chain (redirect store only).
    `Heap.repr` — every reader resolves on entry.  FWD cells always
    store a rep at creation, so chains only grow when a rep later
    collapses itself; clobbers rax+rdi only (rcx holds `fr` across the
    step dispatch)."""
    return [
        LBL("repr"),
        I("mov_r64_r64", "rax", "rdi"),
        LBL("repr_l"),
        I("cmp_m64_imm", ("m", "rax", 0), FWD_TAG),
        I("jne_rel32", ("l", "repr_d")),
        I("mov_r64_m64", "rax", ("m", "rax", 8)),
        I("jmp_rel32", ("l", "repr_l")),
        LBL("repr_d"), I("ret"),
    ]


def r_step(R: Realization, ctx: Ctx) -> Program:
    """step(rdi=t) -> rax: LO single-step dispatch, Lean IStepBasis order
    (normβ, konstβ, dupβ, compβ, swapβ, [sβ], then congruence).

    reclaim="redirect": every node fetched for a tag check is resolved
    first (`repr`) and parent slots get the rep written back — a child
    that collapsed since it was stored is seen through once."""
    fwd = R.reclaim == "redirect"

    def rep(reg: str) -> Program:
        return [I("mov_r64_r64", "rdi", reg),
                I("call_rel32", ("l", "repr")),
                I("mov_r64_r64", reg, "rax")]

    p: Program = [
        LBL("step"),
        I("push_r64", "r12"), I("push_r64", "r13"), I("push_r64", "r14"),
        I("mov_r64_r64", "r12", "rdi"),
    ]
    if fwd:
        p += rep("r12")
    p += [
        I("cmp_m64_imm", ("m", "r12", 0), Tag.APP),
        I("jne_rel32", ("l", "st_none")),
        I("mov_r64_m64", "r13", ("m", "r12", 8)),    # f
        I("mov_r64_m64", "r14", ("m", "r12", 16)),   # x
    ]
    if fwd:
        p += rep("r13") + [
            # O.l := rep(f) when the write survives its root — a FWD
            # rep below irstart may also land in an input cell
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_wb_f")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jge_rel32", ("l", "st_wb_w")),
            I("cmp_r64_r64", "r13", "r9"),
            I("jge_rel32", ("l", "st_wb_f")),
            LBL("st_wb_w"),
            I("mov_m64_r64", ("m", "r12", 8), "r13"),
            LBL("st_wb_f"),
        ]
    p += [
        I("cmp_m64_imm", ("m", "r13", 0), Tag.norm),
        I("je_rel32", ("l", "st_norm")),
        I("cmp_m64_imm", ("m", "r13", 0), Tag.APP),
        I("jne_rel32", ("l", "st_left")),
        I("mov_r64_m64", "rax", ("m", "r13", 8)),    # fl
        I("mov_r64_m64", "rcx", ("m", "r13", 16)),   # fr
    ]
    if fwd:
        p += rep("rax") + [
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r13", "r9"),
            I("jb_rel32", ("l", "st_wb_fl")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r13", "r9"),
            I("jge_rel32", ("l", "st_wb_w2")),
            I("cmp_r64_r64", "rax", "r9"),
            I("jge_rel32", ("l", "st_wb_fl")),
            LBL("st_wb_w2"),
            I("mov_m64_r64", ("m", "r13", 8), "rax"),
            LBL("st_wb_fl"),
        ]
    p += [
        I("cmp_m64_imm", ("m", "rax", 0), Tag.konst),
        I("je_rel32", ("l", "st_konst")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.dup),
        I("je_rel32", ("l", "st_dup")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.APP),
        I("jne_rel32", ("l", "st_left")),
        I("mov_r64_m64", "rdx", ("m", "rax", 8)),    # fll
        I("mov_r64_m64", "rsi", ("m", "rax", 16)),   # flr
    ]
    if fwd:
        p += [I("mov_r64_r64", "r8", "rax")]   # repr clobbers rax; keep fl
        p += rep("rdx") + [
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r8", "r9"),
            I("jb_rel32", ("l", "st_wb_fll")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r8", "r9"),
            I("jge_rel32", ("l", "st_wb_w3")),
            I("cmp_r64_r64", "rdx", "r9"),
            I("jge_rel32", ("l", "st_wb_fll")),
            LBL("st_wb_w3"),
            I("mov_m64_r64", ("m", "r8", 8), "rdx"),
            LBL("st_wb_fll"),
        ]
    p += [
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
    """normβ: I x -> x.  redirect: the redex root becomes FWD→rep(x)
    (the reduct is an existing cell — indirection, HeapDev `redirect`)."""
    p = [LBL("st_norm")]
    if R.audit:
        p += _bump("c_norm")
    if R.reclaim == "redirect":
        return p + [
            I("mov_r64_r64", "rdi", "r14"),
            I("call_rel32", ("l", "repr")),          # rax = rep(x)
            # consume O iff the FWD's rep outlives its root: always for
            # a reduction cell, only for a rep below irstart otherwise
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_out")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jge_rel32", ("l", "st_n_fwd")),
            I("cmp_r64_r64", "rax", "r9"),
            I("jge_rel32", ("l", "st_out")),
            LBL("st_n_fwd"),
            I("mov_m64_imm32", ("m", "r12", 0), FWD_TAG),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_m64_imm32", ("m", "r12", 16), 0),
            I("jmp_rel32", ("l", "st_out")),
        ]
    return p + [
        I("mov_r64_r64", "rax", "r14"),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_konst(R: Realization, ctx: Ctx) -> Program:
    """konstβ (fused macro): K x y -> x.  redirect: root -> FWD→rep(x)
    with the same rep-lifetime guard as st_norm."""
    p = [LBL("st_konst")]
    if R.audit:
        p += _bump("c_konst")
    if R.reclaim == "redirect":
        return p + [
            I("mov_r64_r64", "rdi", "rcx"),          # rcx = fr = x
            I("call_rel32", ("l", "repr")),          # rax = rep(x)
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_out")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jge_rel32", ("l", "st_k_fwd")),
            I("cmp_r64_r64", "rax", "r9"),
            I("jge_rel32", ("l", "st_out")),
            LBL("st_k_fwd"),
            I("mov_m64_imm32", ("m", "r12", 0), FWD_TAG),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_m64_imm32", ("m", "r12", 16), 0),
            I("jmp_rel32", ("l", "st_out")),
        ]
    return p + [
        I("mov_r64_r64", "rax", "rcx"),
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_dup(R: Realization, ctx: Ctx) -> Program:
    """dupβ: W f x -> f x x.  redirect: the ROOT cell is rewritten to
    the reduct shape — one mkapp for (f x), two stores — never a spine
    cell (a shared inner cell must keep its term for every referrer).
    Consumption only when O is a reduction cell (>= irstart): a fresh
    reduct would dangle inside an input or perm cell."""
    p = [LBL("st_dup")]                                # W f x -> f x x
    if R.audit:
        p += _bump("c_dup")
    if R.reclaim == "redirect":
        return p + [
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_dup_fr")),         # O below irstart
            I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp")),           # rax = (f x)
            I("mov_m64_r64", ("m", "r12", 8), "rax"),    # O.l := (f x)
            I("mov_m64_r64", ("m", "r12", 16), "r14"),   # O.r := x
            I("mov_r64_r64", "rax", "r12"),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_dup_fr"),                           # O < irstart:
            I("mov_r64_r64", "rdi", "rcx"),               # persist-zone
            I("mov_r64_r64", "rsi", "r14"),               # reduct + FWD
            I("call_rel32", ("l", "mkapp_p")),            # for input O
            I("mov_r64_r64", "rdi", "rax"),
            I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp_p")),           # rax = (f x) x
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_out")),              # perm: unconsumed
            I("mov_m64_imm32", ("m", "r12", 0), FWD_TAG),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_m64_imm32", ("m", "r12", 16), 0),
            I("jmp_rel32", ("l", "st_out")),
        ]
    return p + [
        I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x)
        I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x) x
        I("jmp_rel32", ("l", "st_out")),
    ]


def r_st_swap(R: Realization, ctx: Ctx) -> Program:
    """swapβ: C f x y -> f y x.  redirect: root rewritten to
    ((f y) x) — 1 alloc, 2 stores — only when O >= irstart."""
    p = [LBL("st_swap")]                               # C f x y -> f y x
    if R.audit:
        p += _bump("c_swap")
    if R.reclaim == "redirect":
        return p + [
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_swap_fr")),
            I("mov_r64_r64", "rdi", "rsi"), I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp")),           # rax = (f y)
            I("mov_m64_r64", ("m", "r12", 8), "rax"),    # O.l := (f y)
            I("mov_m64_r64", ("m", "r12", 16), "rcx"),   # O.r := x
            I("mov_r64_r64", "rax", "r12"),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_swap_fr"),
            I("mov_r64_r64", "rdi", "rsi"), I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp_p")),           # rax = (f y)
            I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "rcx"),
            I("call_rel32", ("l", "mkapp_p")),           # rax = (f y) x
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_out")),
            I("mov_m64_imm32", ("m", "r12", 0), FWD_TAG),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_m64_imm32", ("m", "r12", 16), 0),
            I("jmp_rel32", ("l", "st_out")),
        ]
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
    """compβ: B f g x -> f (g x).  redirect: root rewritten to
    (f (g x)) — 1 alloc, 2 stores — only when O >= irstart."""
    p = [LBL("st_comp")]                               # B f g x -> f (g x)
    if R.audit:
        p += _bump("c_comp")
    if R.reclaim == "redirect":
        return p + [
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_comp_fr")),
            I("push_r64", "rsi"), I("sub_r64_imm", "rsp", 8),
            I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp")),           # rax = (g x)
            I("add_r64_imm", "rsp", 8), I("pop_r64", "rsi"),
            I("mov_m64_r64", ("m", "r12", 8), "rsi"),    # O.l := f
            I("mov_m64_r64", ("m", "r12", 16), "rax"),   # O.r := (g x)
            I("mov_r64_r64", "rax", "r12"),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_comp_fr"),
            I("push_r64", "rsi"),                         # save f — rsi is
            I("mov_r64_r64", "rdi", "rcx"),                #   reused for x
            I("mov_r64_r64", "rsi", "r14"),                #   below
            I("call_rel32", ("l", "mkapp_p")),            # rax = (g x)
            I("pop_r64", "rdi"), I("mov_r64_r64", "rsi", "rax"),
            I("call_rel32", ("l", "mkapp_p")),            # rax = f (g x)
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_out")),
            I("mov_m64_imm32", ("m", "r12", 0), FWD_TAG),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_m64_imm32", ("m", "r12", 16), 0),
            I("jmp_rel32", ("l", "st_out")),
        ]
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
    """sβ (fuse_s=True only): S f g x -> (f x)(g x).  redirect: the
    root is rewritten to the reduct pair — 2 allocs, 2 stores — only
    when O >= irstart; below it a fully fresh pair (nothing consumed)."""
    p = [LBL("st_s")]                            # S f g x -> (f x)(g x)
    if R.audit:
        p += _bump("c_s")
    if R.reclaim == "redirect":
        return p + [
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jl_rel32", ("l", "st_s_fr")),
            I("push_r64", "rcx"),                        # g
            I("push_r64", "rsi"),                        # f
            I("mov_r64_r64", "rdi", "rsi"),
            I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp")),             # rax = (f x)
            I("pop_r64", "rsi"),                         # f (dead)
            I("pop_r64", "rcx"),                         # g
            I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),
            I("mov_r64_r64", "rdi", "rcx"),
            I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp")),             # rax = (g x)
            I("add_r64_imm", "rsp", 8), I("pop_r64", "rcx"),  # (f x)
            I("mov_m64_r64", ("m", "r12", 8), "rcx"),    # O.l := (f x)
            I("mov_m64_r64", ("m", "r12", 16), "rax"),   # O.r := (g x)
            I("mov_r64_r64", "rax", "r12"),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_s_fr"),                           # O < irstart:
            I("push_r64", "rcx"),                        #   persist pair +
            I("push_r64", "rsi"),                        #   FWD for input O
            I("mov_r64_r64", "rdi", "rsi"),
            I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp_p")),            # rax = (f x)
            I("pop_r64", "rsi"),
            I("pop_r64", "rcx"),
            I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),
            I("mov_r64_r64", "rdi", "rcx"),
            I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp_p")),            # rax = (g x)
            I("add_r64_imm", "rsp", 8), I("pop_r64", "rdi"),
            I("mov_r64_r64", "rsi", "rax"),
            I("call_rel32", ("l", "mkapp_p")),            # rax = (f x)(g x)
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_out")),
            I("mov_m64_imm32", ("m", "r12", 0), FWD_TAG),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_m64_imm32", ("m", "r12", 16), 0),
            I("jmp_rel32", ("l", "st_out")),
        ]
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
    """appL/appR congruence + st_none/st_out epilogue.  redirect: the
    parent slot takes the child's rep — one store, no spine churn; a
    shared subtree's collapse is paid once by every referrer.  A perm
    parent can't be rewritten: its one-step result is a fresh node with
    rep-resolved children and nothing is consumed."""
    p = [LBL("st_left")]
    if R.audit:
        p += _bump("c_left")
    p += [
        I("mov_r64_r64", "rdi", "r13"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "st_right")),
    ]
    if R.reclaim == "redirect":
        p += [
            # in-place iff O survives the write: reduction cell, or an
            # input cell whose new child stays below irstart
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_l_fr")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jge_rel32", ("l", "st_l_ip")),
            I("cmp_r64_r64", "rax", "r9"),
            I("jge_rel32", ("l", "st_l_fr")),
            LBL("st_l_ip"),
            I("mov_m64_r64", ("m", "r12", 8), "rax"),
            I("mov_r64_r64", "rax", "r12"),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_l_fr"),
            I("push_r64", "rax"),
            I("mov_r64_r64", "rdi", "r14"),
            I("call_rel32", ("l", "repr")),
            I("mov_r64_r64", "rsi", "rax"),
            I("pop_r64", "rdi"),
            # persist the copy when both children live below irstart —
            # an input parent may store it; reduction children force rbx
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "rdi", "r9"),
            I("jge_rel32", ("l", "st_l_rb")),
            I("cmp_r64_r64", "rsi", "r9"),
            I("jge_rel32", ("l", "st_l_rb")),
            I("call_rel32", ("l", "mkapp_p")),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_l_rb"),
            I("call_rel32", ("l", "mkapp")),           # app(l', rep(r))
            I("jmp_rel32", ("l", "st_out")),
        ]
    else:
        p += [
            I("mov_r64_r64", "rdi", "rax"), I("mov_r64_r64", "rsi", "r14"),
            I("call_rel32", ("l", "mkapp")), I("jmp_rel32", ("l", "st_out")),
        ]
    p += [LBL("st_right")]
    if R.audit:
        p += _bump("c_right")
    p += [
        I("mov_r64_r64", "rdi", "r14"), I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "st_none")),
    ]
    if R.reclaim == "redirect":
        p += [
            I("mov_r64_rip", "r9", ("p", "permend")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jb_rel32", ("l", "st_r_fr")),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "r12", "r9"),
            I("jge_rel32", ("l", "st_r_ip")),
            I("cmp_r64_r64", "rax", "r9"),
            I("jge_rel32", ("l", "st_r_fr")),
            LBL("st_r_ip"),
            I("mov_m64_r64", ("m", "r12", 16), "rax"),
            I("mov_r64_r64", "rax", "r12"),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_r_fr"),
            I("push_r64", "rax"),
            I("mov_r64_r64", "rdi", "r13"),
            I("call_rel32", ("l", "repr")),
            I("mov_r64_r64", "rdi", "rax"),
            I("pop_r64", "rsi"),
            I("mov_r64_rip", "r9", ("p", "irstart")),
            I("cmp_r64_r64", "rdi", "r9"),
            I("jge_rel32", ("l", "st_r_rb")),
            I("cmp_r64_r64", "rsi", "r9"),
            I("jge_rel32", ("l", "st_r_rb")),
            I("call_rel32", ("l", "mkapp_p")),
            I("jmp_rel32", ("l", "st_out")),
            LBL("st_r_rb"),
            I("call_rel32", ("l", "mkapp")),           # app(rep(l), r')
            I("jmp_rel32", ("l", "st_out")),
        ]
    else:
        p += [
            I("mov_r64_r64", "rdi", "r13"), I("mov_r64_r64", "rsi", "rax"),
            I("call_rel32", ("l", "mkapp")), I("jmp_rel32", ("l", "st_out")),
        ]
    return p + [
        LBL("st_none"), I("xor_r32_r32", "eax", "eax"),
        LBL("st_out"),
        I("pop_r64", "r14"), I("pop_r64", "r13"), I("pop_r64", "r12"), I("ret"),
    ]


def r_count_nodes(R: Realization, ctx: Ctx) -> Program:
    """count_nodes(rdi) -> rax."""
    p: Program = [
        LBL("count_nodes"),
        I("push_r64", "r12"), I("push_r64", "r13"), I("sub_r64_imm", "rsp", 8),
    ]
    if R.reclaim == "redirect":
        p += [I("call_rel32", ("l", "repr")),
              I("mov_r64_r64", "r12", "rax")]
    else:
        p += [I("mov_r64_r64", "r12", "rdi")]
    return p + [
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
    """emit_nf(rdi=node, rsi=cur) -> rsi: postfix decompile I K S B W C @.
    redirect: resolve on entry — a slot may still hold a consumed
    cell; its rep is the NF node."""
    p: Program = [
        LBL("emit_nf"),
    ]
    if R.reclaim == "redirect":
        p += [I("call_rel32", ("l", "repr")),
              I("mov_r64_r64", "rdi", "rax")]
    return p + [
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
        # derived-S template: oldest arena cells (below permend), so a
        # reclaim="redirect" step can never rewrite it in place; tag-3
        # nodes still copy its root triple and alias the template
        p += [I("call_rel32", ("l", "build_ds"))]
    if R.io[1] == "bytes":
        # egress vocab in the same permanent prefix: I/K leaves, the KI
        # cell, and 16 inert marker leaves {tag EG_MARK, l=k} — every
        # decode probe references them, so they sit below permend too
        p += [
            I("mov_r64_rip", "rax", ("p", "nalloc")),    # vocab allocs
            I("mov_rip_r64", ("p", "scratch"), "rax"),   # uncounted
            I("mov_r32_imm32", "edx", Tag.norm),
            I("call_rel32", ("l", "mkleaf")),
            I("mov_rip_r64", ("p", "eb_i"), "rax"),
            I("mov_r32_imm32", "edx", Tag.konst),
            I("call_rel32", ("l", "mkleaf")),
            I("mov_rip_r64", ("p", "eb_k"), "rax"),
            I("mov_r64_r64", "rdi", "rax"),
            I("mov_r64_rip", "rsi", ("p", "eb_i")),
            I("call_rel32", ("l", "mkapp")),             # KI = (K I)
            I("mov_rip_r64", ("p", "eb_ki"), "rax"),
            I("mov_rip_r64", ("p", "eb_marks"), "rbx"),  # contiguous below
            I("xor_r32_r32", "r15d", "r15d"),
            LBL("eb_mkloop"),
            I("mov_r32_imm32", "edx", EG_MARK),
            I("call_rel32", ("l", "mkleaf")),
            I("mov_m64_r64", ("m", "rax", 8), "r15"),    # l = k
            I("inc_r64", "r15"),
            I("cmp_r64_imm", "r15", 16),
            I("jl_rel32", ("l", "eb_mkloop")),
            I("mov_r64_rip", "rax", ("p", "scratch")),
            I("mov_rip_r64", ("p", "nalloc"), "rax"),
            # committed frame buffer: [bytes] per root (u32 len prefix
            # lives in .data — no 32-bit store in the ISA), cap doubles
            # as the malformed-spine termination bound
            I("xor_r32_r32", "ecx", "ecx"),
            I("mov_r64_imm", "rdx", EG_OUT_BYTES),
            I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
            I("mov_rip_r64", ("p", "eb_out"), "rax"),
            I("mov_r64_imm", "rdx", EG_OUT_BYTES),
            I("add_r64_r64", "rax", "rdx"),
            I("mov_rip_r64", ("p", "eb_lim"), "rax"),
        ]
    p += [
        # end of the immutable prefix — depacked input cells occupy
        # [permend, irstart), the reduction bump starts at irstart
        I("mov_rip_r64", ("p", "permend"), "rbx"),
        I("mov_rip_r64", ("p", "irstart"), "rbx"),
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
    """ir_depack: cells live in the arena input prefix — r13 = permend,
    root-ptr table at r13 + 24*nn, irstart = r13 + 24*nn + 8*nr.
    One forward pass over the postorder records (children before
    parents, so address order = allocation era); tag-3 cells copy the
    permanent ds root triple (built once in entry, children alias it —
    stable across streams and arena resets); fuse_s keeps tag-3 a
    primitive leaf.  Tags >= 7 (STK/VAR/junk) and forward/out-of-range
    indices -> exit3."""
    iat = ctx["iat"]
    p: Program = [
        LBL("ir_depack"),
        # r13 = cells base = arena input prefix
        I("mov_r64_rip", "r13", ("p", "permend")),
        # rax = r13 + 24*nn + 8*nr = end of input cells + root table.
        # redirect: the persist zone [pcur, pend) sits here — cells
        # allocated for input-tier reducts, then irstart = pagealign
        # (pend).  Otherwise irstart = pagealign(rax).  DECOMMIT at an
        # unaligned boundary rounds down and would free the page
        # holding the input tail, hence the page align.
        I("mov_r64_rip", "rax", ("p", "irnodes")),
    ] + _mul24() + [
        I("mov_r64_rip", "rcx", ("p", "irnroots")),
        I("shl_r64_imm8", "rcx", 3),
        I("add_r64_r64", "rax", "rcx"),
        I("add_r64_r64", "rax", "r13"),
    ] + ([
        I("add_r64_imm", "rax", R.node_bytes - 1),
        I("and_r64_imm", "rax", -R.node_bytes),
        I("mov_rip_r64", ("p", "pcur"), "rax"),        # pcur = align24(end)
        I("mov_r64_r64", "rcx", "rax"),
        I("add_r64_imm", "rcx", R.persist_bytes),
        I("mov_rip_r64", ("p", "pend"), "rcx"),        # pend = pcur + cap
        I("mov_r64_r64", "rax", "rcx"),
    ] if R.reclaim == "redirect" else []) + [
        I("add_r64_imm", "rax", 0xfff),
        I("and_r64_imm", "rax", -4096),
        I("mov_rip_r64", ("p", "irstart"), "rax"),
        # commit the input span [rbp, irstart) — depack writes cells
        # directly, bypassing grow_heap's commit-ahead.  No rsp adjust:
        # depack is jumped into, _start's 0x28 shadow frame covers the call
        I("cmp_r64_r64", "rax", "rbp"),
        I("jbe_rel32", ("l", "ir_d_comm")),
        I("mov_r64_r64", "rcx", "rbp"),
        I("mov_r64_r64", "rdx", "rax"),
        I("sub_r64_r64", "rdx", "rbp"),
        I("mov_r32_imm32", "r8d", MEM_COMMIT),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_rip", "rbp", ("p", "irstart")),
        LBL("ir_d_comm"),
        I("mov_r64_rip", "rbx", ("p", "irstart")),
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
        # arena reset: decommit the used span past the input prefix
        # (depacked cells + root table in [permend, irstart) persist —
        # a shared subtree's collapse is paid once per stream)
        I("mov_r64_rip", "rcx", ("p", "irstart")),
        I("cmp_r64_r64", "rbp", "rcx"), I("jbe_rel32", ("l", "ir_nofree")),
        I("mov_r64_r64", "rdx", "rbp"), I("sub_r64_r64", "rdx", "rcx"),
        I("mov_r32_imm32", "r8d", MEM_DECOMMIT),
        I("call_mrip", iat("VirtualFree")),
        LBL("ir_nofree"),
        I("mov_r64_rip", "rbx", ("p", "irstart")),
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
        # ---- per-root output: NF line (term) or byte frame (bytes) ----
        LBL("ir_red_done"),
        I("mov_r64_rip", "rax", ("p", "irsteps")),
        I("add_r64_r64", "rax", "r15"),
        I("mov_rip_r64", ("p", "irsteps"), "rax"),
    ]
    if R.io[1] == "bytes":
        # the kernel decodes the byte-list NF itself: one
        # [u32le len][bytes] frame per root, in root order
        p += [I("call_rel32", ("l", "emit_bytes"))]
    elif R.io[1] == "ir":
        # the NF leaves the kernel as its own PIR blob: one
        # [u32le len][PIR] frame per root — a stage output that the
        # next stage can depack verbatim, no Python in between
        p += [I("call_rel32", ("l", "emit_ir"))]
    else:
        p += [
            I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "count_nodes")),
            I("lea_r64_m64", "rdx", ("m", "rax", 0)),
            I("add_r64_r64", "rdx", "rdx"),
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
        ]
    p += [
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


# ======================================================================
# BYTE EGRESS (io=("stdin","bytes"))
#
# emit_bytes walks the root NF exactly as spec_term._decode_bytecells
# does: `while tag(s) != KONST` the cell is a cons.  _cell_parts'
# structural path is the fixed NF shape `K (D ((B (C (D ((B (C I))
# (K h))))) (K t)))` — head at s.r.r.l.r.r.r.r.r, tail at s.r.r.r.r —
# with the same probe fallback (`s I K` -> head, `s I KI` -> tail) for
# any other-but-equal NF.  A byte cell decodes as `b K` -> lo sel,
# `b KI` -> hi sel, each sel applied to the 16 permanent tag-9 markers
# -> m_k.  Probes are ordinary LO reductions (peval wraps the step
# loop) allocating in the main arena — freed by the next root's reset;
# nalloc is snapshot/restored so `alloc=` stays the query's (like
# `steps=`).  Frame wire: [u32le len][bytes] per root, order preserved.
# Malformed spine/byte, non-terminating probe, or frame overflow ->
# exit5 (the kernel has no exception channel — decode failure IS rc5).
# ======================================================================

def r_peval(R: Realization, ctx: Ctx) -> Program:
    """peval: rdi=term -> rax=NF — the red loop as a subroutine.
    r13=cur, r15=fuel (EG_PROBE_FUEL cap -> exit5); steps accumulate
    into [eb_dec] — `dec=` on stderr, kept out of `steps=`."""
    p: Program = [
        LBL("peval"),
        I("sub_r64_imm", "rsp", 8),                # call-site parity
        I("mov_r64_r64", "r13", "rdi"),
        I("mov_r32_imm32", "r15d", EG_PROBE_FUEL),
        LBL("pe_loop"),
        I("mov_r64_r64", "rdi", "r13"),
        I("call_rel32", ("l", "step")),
        I("test_r64_r64", "rax", "rax"),
        I("je_rel32", ("l", "pe_done")),
        I("mov_r64_r64", "r13", "rax"),
        I("dec_r64", "r15"),
        I("je_rel32", ("l", "exit2")),             # probe fuel exhausted
        I("jmp_rel32", ("l", "pe_loop")),
        LBL("pe_done"),
        I("mov_r32_imm32", "eax", EG_PROBE_FUEL),
        I("sub_r64_r64", "rax", "r15"),
        I("mov_r64_rip", "rcx", ("p", "eb_dec")),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_rip_r64", ("p", "eb_dec"), "rax"),
    ]
    if R.reclaim == "redirect":
        # the returned root may be a consumed cell — hand back its rep
        p += [I("mov_r64_r64", "rdi", "r13"),
              I("call_rel32", ("l", "repr")),
              I("mov_r64_r64", "r13", "rax")]
    p += [
        I("mov_r64_r64", "rax", "r13"),
        I("add_r64_imm", "rsp", 8),
        I("ret"),
    ]
    return p


def r_selidx(R: Realization, ctx: Ctx) -> Program:
    """selidx: rdi=selector term -> rax=k — sel m0..m15 peval'd; the NF
    must BE a tag-9 marker leaf (a real 16-way selector returns one of
    its args), anything else means the head wasn't a selector -> exit5."""
    p: Program = [
        LBL("selidx"),
        I("sub_r64_imm", "rsp", 8),
        I("mov_r64_r64", "r13", "rdi"),
    ]
    for k in range(16):
        p += [I("mov_r64_rip", "rsi", ("p", "eb_marks"))]
        if k:
            p += [I("add_r64_imm", "rsi", 24 * k)]
        p += [
            I("mov_r64_r64", "rdi", "r13"),
            I("call_rel32", ("l", "mkapp")),
            I("mov_r64_r64", "r13", "rax"),
        ]
    p += [
        I("mov_r64_r64", "rdi", "r13"),
        I("call_rel32", ("l", "peval")),
        I("cmp_m64_imm", ("m", "rax", 0), EG_MARK),
        I("jne_rel32", ("l", "exit5")),
        I("mov_r64_m64", "rax", ("m", "rax", 8)),
        I("cmp_r64_imm", "rax", 16),
        I("jge_rel32", ("l", "exit5")),
        I("add_r64_imm", "rsp", 8),
        I("ret"),
    ]
    return p


def r_emit_bytes(R: Realization, ctx: Ctx) -> Program:
    """emit_bytes: r12=NF -> WriteFile one [u32le len][bytes] frame.
    r12=s (spine cursor), r14=out cursor; h/lo/hi live at [rsp+0..16].
    Null-deref on the structural path = malformed spine -> exit5."""
    iat = ctx["iat"]
    p: Program = [
        LBL("emit_bytes"),
        I("sub_r64_imm", "rsp", 0x28),
        # probes allocate out of the arena like any reduction; snapshot
        # nalloc so `alloc=` reports the query's nodes only
        I("mov_r64_rip", "rax", ("p", "nalloc")),
        I("mov_rip_r64", ("p", "eb_save"), "rax"),
        I("mov_r64_rip", "r14", ("p", "eb_out")),
        LBL("eb_loop"),
    ]
    if R.reclaim == "redirect":
        # s may be a consumed cell; resolve, then take the probe path —
        # peval resolves internally, the structural path's derefs could
        # land on FWD cells mid-spine
        p += [
            I("mov_r64_r64", "rdi", "r12"),
            I("call_rel32", ("l", "repr")),
            I("mov_r64_r64", "r12", "rax"),
        ]
    p += [
        I("cmp_m64_imm", ("m", "r12", 0), Tag.konst),
        I("je_rel32", ("l", "eb_flush")),            # nil -> flush frame
    ]
    if R.reclaim == "redirect":
        p += [I("jmp_rel32", ("l", "eb_pcons"))]
    p += [
        # --- _cell_parts fast path: s = K (D (B(C(DW)) (K t))) ---
        I("cmp_m64_imm", ("m", "r12", 0), Tag.APP),
        I("jne_rel32", ("l", "eb_pcons")),
        I("mov_r64_m64", "rax", ("m", "r12", 8)),    # s.l
        I("cmp_m64_imm", ("m", "rax", 0), Tag.konst),
        I("jne_rel32", ("l", "eb_pcons")),
        I("mov_r64_m64", "rcx", ("m", "r12", 16)),   # s.r
        I("cmp_m64_imm", ("m", "rcx", 0), Tag.APP),
        I("jne_rel32", ("l", "eb_pcons")),
        I("mov_r64_m64", "rax", ("m", "rcx", 8)),    # s.r.l
        I("cmp_m64_imm", ("m", "rax", 0), Tag.dup),
        I("jne_rel32", ("l", "eb_pcons")),
        I("mov_r64_m64", "rcx", ("m", "rcx", 16)),   # s.r.r
        I("test_r64_r64", "rcx", "rcx"),
        I("je_rel32", ("l", "eb_pcons")),
        I("mov_r64_m64", "rax", ("m", "rcx", 8)),    # s.r.r.l
        I("test_r64_r64", "rax", "rax"),
        I("je_rel32", ("l", "eb_pcons")),
        I("mov_r64_m64", "rdx", ("m", "rcx", 16)),   # s.r.r.r (same guard
        I("test_r64_r64", "rdx", "rdx"),             # as _cell_parts)
        I("je_rel32", ("l", "eb_pcons")),
    ]
    # head = s.r.r.l .r .r .r .r .r (five derefs into the fixed spine)
    for _ in range(5):
        p += [
            I("mov_r64_m64", "rax", ("m", "rax", 16)),
            I("test_r64_r64", "rax", "rax"),
            I("je_rel32", ("l", "exit5")),
        ]
    p += [
        I("mov_m64_r64", ("m", "rsp", 0), "rax"),    # h
        # tail = s.r.r .r .r
        I("mov_r64_m64", "r12", ("m", "rcx", 16)),
        I("test_r64_r64", "r12", "r12"),
        I("je_rel32", ("l", "exit5")),
        I("mov_r64_m64", "r12", ("m", "r12", 16)),
        I("test_r64_r64", "r12", "r12"),
        I("je_rel32", ("l", "exit5")),
        I("jmp_rel32", ("l", "eb_cell")),
        # --- probe fallback: h = (s I) K, t = (s I) KI ---
        LBL("eb_pcons"),
        I("mov_r64_r64", "rdi", "r12"),
        I("mov_r64_rip", "rsi", ("p", "eb_i")),
        I("call_rel32", ("l", "mkapp")),
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_rip", "rsi", ("p", "eb_k")),
        I("call_rel32", ("l", "mkapp")),
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "peval")),
        I("mov_m64_r64", ("m", "rsp", 0), "rax"),    # h
        I("mov_r64_r64", "rdi", "r12"),
        I("mov_r64_rip", "rsi", ("p", "eb_i")),
        I("call_rel32", ("l", "mkapp")),
        I("mov_r64_r64", "rdi", "rax"),
        I("mov_r64_rip", "rsi", ("p", "eb_ki")),
        I("call_rel32", ("l", "mkapp")),
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "peval")),
        I("mov_r64_r64", "r12", "rax"),              # s := t
        # --- byte cell h: lo = sel(h K), hi = sel(h KI) ---
        LBL("eb_cell"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 0)),
        I("mov_r64_rip", "rsi", ("p", "eb_k")),
        I("call_rel32", ("l", "mkapp")),
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "peval")),
        I("mov_m64_r64", ("m", "rsp", 8), "rax"),    # lo sel
        I("mov_r64_m64", "rdi", ("m", "rsp", 0)),
        I("mov_r64_rip", "rsi", ("p", "eb_ki")),
        I("call_rel32", ("l", "mkapp")),
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "peval")),
        I("mov_r64_r64", "rdi", "rax"),
        I("call_rel32", ("l", "selidx")),
        I("shl_r64_imm8", "rax", 4),                 # hi nibble
        I("mov_m64_r64", ("m", "rsp", 16), "rax"),
        I("mov_r64_m64", "rdi", ("m", "rsp", 8)),
        I("call_rel32", ("l", "selidx")),            # rax = lo nibble
        I("mov_r64_m64", "rcx", ("m", "rsp", 16)),
        I("add_r64_r64", "rax", "rcx"),              # byte = hi<<4 | lo
        I("mov_r64_rip", "rcx", ("p", "eb_lim")),
        I("cmp_r64_r64", "r14", "rcx"),
        I("jge_rel32", ("l", "exit5")),              # frame overflow
        I("mov_m8_r8", ("m", "r14", 0), "al"),
        I("inc_r64", "r14"),
        I("jmp_rel32", ("l", "eb_loop")),
        # ---- flush: u32le len (in .data — no 32-bit store form) + bytes
        LBL("eb_flush"),
        I("mov_r64_rip", "rax", ("p", "eb_out")),
        I("mov_r64_r64", "rdx", "r14"), I("sub_r64_r64", "rdx", "rax"),
        I("mov_rip_r64", ("p", "eb_len"), "rdx"),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("lea_r64_rip", "rdx", ("p", "eb_len")),
        I("mov_r32_imm32", "r8d", 4),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_rip", "rdx", ("p", "eb_out")),
        I("mov_r64_r64", "r8", "r14"), I("sub_r64_r64", "r8", "rdx"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        I("mov_r64_rip", "rax", ("p", "eb_save")),
        I("mov_rip_r64", ("p", "nalloc"), "rax"),    # probe cells uncounted
        I("add_r64_imm", "rsp", 0x28), I("ret"),
    ]
    return p


# ======================================================================
# IR EGRESS (io=("stdin","ir"))
#
# emit_ir serializes the NF graph itself to a PIR blob (ADR-005):
# a stage's output IS the next stage's input — no text token line,
# no Python reparse.  Identity dedup via cell-number table is enough:
# Merkle digests are dedup-insensitive (dig(node) = sha over child
# digests), so the blob's canonical root digest equals what Python's
# structural hash-cons computes — verifiable one linear pass over
# the records, spec_term.digest_ir_blob.


def r_emit_ir(R: Realization, ctx: Ctx) -> Program:
    """emit_ir: r12=NF -> WriteFile one [u32le len][PIR blob] frame.
    ei_walk(rdi=node) -> eax=emit idx: repr-resolved postorder
    left-then-right — the same order _pack_ir_all's stack produces —
    with ei_tab[cell_no] = idx+1 deduping on cell identity.  Table and
    output buffer are fresh VirtualAllocs per root: zeroed pages are
    the dedup-init, and cell addresses legitimately rebind across
    roots after the arena reset."""
    iat = ctx["iat"]
    p: Program = [
        LBL("emit_ir"),
        I("sub_r64_imm", "rsp", 0x28),
    ]
    if R.reclaim == "redirect":
        p += [I("mov_r64_r64", "rdi", "r12"),
              I("call_rel32", ("l", "repr")),
              I("mov_r64_r64", "r12", "rax")]
    p += [
        # ncells = (rbp - irarena)/24 — every NF cell sits in the span
        I("mov_r64_r64", "rax", "rbp"),
        I("mov_r64_rip", "rcx", ("p", "irarena")),
        I("sub_r64_r64", "rax", "rcx"),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "ecx", 24),
        I("div_r64", "rcx"),
        I("mov_rip_r64", ("p", "ei_cells"), "rax"),
        # ei_tab = VA(ncells*8, COMMIT|RESERVE, RW) — zeroed
        I("shl_r64_imm8", "rax", 3),
        I("add_r64_imm", "rax", 0xfff), I("and_r64_imm", "rax", -4096),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r64_r64", "rdx", "rax"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "ei_tab"), "rax"),
        # ei_out = VA(ncells*9 + 24 rounded, ...) — emitted nodes <=
        # reachable cells <= span cells
        I("mov_r64_rip", "rax", ("p", "ei_cells")),
        I("mov_r64_r64", "rdx", "rax"), I("shl_r64_imm8", "rdx", 3),
        I("add_r64_r64", "rdx", "rax"),
        I("add_r64_imm", "rdx", 24 + 0xfff),
        I("and_r64_imm", "rdx", -4096),
        I("mov_rip_r64", ("p", "ei_outz"), "rdx"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "ei_out"), "rax"),
        I("mov_r64_rip", "rcx", ("p", "ei_outz")),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_rip_r64", ("p", "ei_lim"), "rax"),
        # header: magic|ver qword (buf+0); nn|nroots + root patched
        # after the walk; records stream from buf+20
        I("mov_r64_rip", "r14", ("p", "ei_out")),
        I("mov_r64_imm", "rax", (1 << 32) | IR_MAGIC),
        I("mov_m64_r64", ("m", "r14", 0), "rax"),
        I("xor_r32_r32", "eax", "eax"),
        I("mov_rip_r64", ("p", "ei_idx"), "rax"),
        I("lea_r64_m64", "rsi", ("m", "r14", 20)),
        I("mov_r64_r64", "rdi", "r12"),
        I("call_rel32", ("l", "ei_walk")),
        # eax = root emit idx — byte stores at buf+16..19 (no dword
        # reg-store form; div-chain extracts the four bytes)
        I("mov_r64_r64", "r12", "rax"),
        I("mov_m8_r8", ("m", "r14", 16), "al"),
        I("xor_r32_r32", "edx", "edx"), I("mov_r32_imm32", "ecx", 0x100),
        I("div_r64", "rcx"),
        I("mov_m8_r8", ("m", "r14", 17), "al"),
        I("xor_r32_r32", "edx", "edx"), I("mov_r32_imm32", "ecx", 0x100),
        I("div_r64", "rcx"),
        I("mov_m8_r8", ("m", "r14", 18), "al"),
        I("xor_r32_r32", "edx", "edx"), I("mov_r32_imm32", "ecx", 0x100),
        I("div_r64", "rcx"),
        I("mov_m8_r8", ("m", "r14", 19), "al"),
        # qword at buf+8 = nn | (nroots=1 << 32)
        I("mov_r64_rip", "rcx", ("p", "ei_idx")),
        I("mov_r64_imm", "rax", 1 << 32),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_m64_r64", ("m", "r14", 8), "rax"),
        # frame: u32 len (in .data — no dword store) + payload
        I("mov_r64_r64", "rdx", "rsi"), I("sub_r64_r64", "rdx", "r14"),
        I("mov_rip_r64", ("p", "ei_len"), "rdx"),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("lea_r64_rip", "rdx", ("p", "ei_len")),
        I("mov_r32_imm32", "r8d", 4),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_rip", "rdx", ("p", "ei_out")),
        I("mov_r64_r64", "r8", "rsi"), I("sub_r64_r64", "r8", "rdx"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        # release table + buffer (MEM_RELEASE: size operand is 0)
        I("mov_r64_rip", "rcx", ("p", "ei_tab")),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "r8d", MEM_RELEASE),
        I("call_mrip", iat("VirtualFree")),
        I("mov_r64_rip", "rcx", ("p", "ei_out")),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "r8d", MEM_RELEASE),
        I("call_mrip", iat("VirtualFree")),
        I("add_r64_imm", "rsp", 0x28), I("ret"),

        # ---- ei_walk: rdi=node, rsi=cursor -> eax=emit idx ----
        LBL("ei_walk"),
    ]
    if R.reclaim == "redirect":
        # interior children can be FWD mid-spine (emit_bytes' probe
        # note) — resolve at every visit, then dedup on the rep
        p += [I("call_rel32", ("l", "repr")),
              I("mov_r64_r64", "rdi", "rax")]
    p += [
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_m64_r64", ("m", "rsp", 0), "rdi"),      # node
        # entry = ei_tab + cell_no*8, cell_no = (node - irarena)/24
        I("mov_r64_r64", "rax", "rdi"),
        I("mov_r64_rip", "rcx", ("p", "irarena")),
        I("sub_r64_r64", "rax", "rcx"),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "ecx", 24),
        I("div_r64", "rcx"),
        I("shl_r64_imm8", "rax", 3),
        I("mov_r64_rip", "rcx", ("p", "ei_tab")),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_m64_r64", ("m", "rsp", 8), "rax"),      # entry ptr
        I("mov_r32_m32", "ecx", ("m", "rax", 0)),
        I("test_r64_r64", "rcx", "rcx"),
        I("jne_rel32", ("l", "ei_hit")),
        # bound: cursor+9 <= ei_lim else exit4 (OOM class)
        I("lea_r64_m64", "rax", ("m", "rsi", 9)),
        I("mov_r64_rip", "rdx", ("p", "ei_lim")),
        I("cmp_r64_r64", "rax", "rdx"),
        I("jge_rel32", ("l", "exit4")),
        I("mov_r64_m64", "rax", ("m", "rdi", 0)),      # tag field
        I("test_r64_r64", "rax", "rax"),
        I("jne_rel32", ("l", "ei_leaf")),
        # app: postorder left then right — _pack_ir_all's order
        I("mov_r64_m64", "rdi", ("m", "rdi", 8)),
        I("call_rel32", ("l", "ei_walk")),
        I("mov_m64_r64", ("m", "rsp", 16), "rax"),     # li
        I("mov_r64_m64", "rdi", ("m", "rsp", 0)),
        I("mov_r64_m64", "rdi", ("m", "rdi", 16)),
        I("call_rel32", ("l", "ei_walk")),             # eax = ri
        # record at rsi: byte tag=0, u32 li@1, u32 ri@5 — composed as
        # one qword store at rsi+1 = li | ri<<32 (clean u32 halves)
        I("mov_r64_r64", "rcx", "rax"),
        I("shl_r64_imm8", "rcx", 32),
        I("mov_r64_m64", "rax", ("m", "rsp", 16)),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_m64_r64", ("m", "rsi", 1), "rax"),
        I("mov_m8_imm8", ("m", "rsi", 0), 0),
        I("jmp_rel32", ("l", "ei_emit")),
        LBL("ei_leaf"),
        # leaf: wire tag = cell tag (1..6); anything else is not an
        # NF node — STK/FWD/EG_MARK/junk refuse as bad IR
        I("cmp_r64_imm", "rax", 1), I("jl_rel32", ("l", "exit3")),
        I("cmp_r64_imm", "rax", 7), I("jge_rel32", ("l", "exit3")),
        I("mov_m8_r8", ("m", "rsi", 0), "al"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_m64_r64", ("m", "rsi", 1), "rcx"),
        LBL("ei_emit"),
        # register: entry = (idx+1); ei_idx++ ; rax = idx
        I("mov_r64_rip", "rax", ("p", "ei_idx")),
        I("mov_r64_m64", "rcx", ("m", "rsp", 8)),
        I("lea_r64_m64", "rdx", ("m", "rax", 1)),
        I("mov_m64_r64", ("m", "rcx", 0), "rdx"),
        I("mov_rip_r64", ("p", "ei_idx"), "rdx"),
        I("add_r64_imm", "rsi", 9),
        I("add_r64_imm", "rsp", 0x28), I("ret"),
        LBL("ei_hit"),
        I("mov_r64_r64", "rax", "rcx"),                # ecx = idx+1
        I("dec_r64", "rax"),
        I("add_r64_imm", "rsp", 0x28), I("ret"),
    ]
    return p


# Ordered routine names = emission order.  "st_s" emits iff R.fuse_s,
# "build_ds" iff not R.fuse_s (handled in program()).
ROUTINES: Tuple[str, ...] = (
    "entry", "parse", "reduce", "stats", "exits",
    "grow_heap", "mkleaf", "mkapp", "mkapp_p", "mkstk", "repr",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

# IR variant: same reducer core, different front end — no token parser,
# no parse stack (mkstk/mkstk unused); entry/read/depack/reduce replace
# entry/parse/reduce.  "ir_reduce" is the batch loop.
ROUTINES_IR: Tuple[str, ...] = (
    "ir_entry", "ir_read", "ir_depack", "ir_reduce", "stats", "exits",
    "grow_heap_ir", "mkleaf", "mkapp", "mkapp_p", "repr",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

# bytes egress adds the NF->bytes decoder (emit_bytes + its two probe
# helpers); emit_nf stays — a bytes-mode kernel could still serve term
# frames if a future io mode asked for it
ROUTINES_IR_BYTES: Tuple[str, ...] = ROUTINES_IR + (
    "emit_bytes", "peval", "selidx",
)

# IR egress adds the NF->PIR-blob serializer: a stage's output leaves
# the kernel already depackable (emit_ir only — no probe vocab needed)
ROUTINES_IR_IR: Tuple[str, ...] = ROUTINES_IR + ("emit_ir",)

IMPORTS_IR: Tuple[str, ...] = IMPORTS + ("VirtualFree",)

# egress .data (bytes mode only — callable below keeps term-mode .data
# byte-identical): probe vocab ptrs, frame buffer bounds, u32 len slot,
# nalloc snapshot, decode-step counter
DATA_SLOTS_EB: Tuple[Tuple[str, int], ...] = (
    ("eb_i", 8), ("eb_k", 8), ("eb_ki", 8), ("eb_marks", 8),
    ("eb_out", 8), ("eb_lim", 8), ("eb_len", 8), ("eb_save", 8),
    ("eb_dec", 8),
)


# egress .data (ir mode only): dedup table + blob buffer bounds,
# emit index, cell count, sizes, u32 len slot
DATA_SLOTS_EI: Tuple[Tuple[str, int], ...] = (
    ("ei_tab", 8), ("ei_out", 8), ("ei_lim", 8), ("ei_idx", 8),
    ("ei_cells", 8), ("ei_len", 8), ("ei_outz", 8),
)


def data_slots_ir(R: Realization) -> tuple:
    """IR slots; io=("stdin","bytes"/"ir") appends the egress block."""
    s = DATA_SLOTS_IR
    if R.reclaim == "redirect":
        s = s + DATA_SLOTS_PS
    if R.io[1] == "bytes":
        s = s + DATA_SLOTS_EB
    if R.io[1] == "ir":
        s = s + DATA_SLOTS_EI
    return s

_BUILDERS: Dict[str, Callable[[Realization, Ctx], Program]] = {
    name[2:]: fn for name, fn in list(globals().items())
    if name.startswith("r_")
}


def _emit(R: Realization, names: Tuple[str, ...]) -> Program:
    ctx = _ctx()
    ctx["ir"] = any(n.startswith("ir_") for n in names)
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
    if R.reclaim not in ("none", "redirect"):
        raise NotRealized(f"reclaim={R.reclaim!r} not realized")
    if R.io != ("stdin", "stdout"):
        raise NotRealized(f"io={R.io!r} not realized by {ROUTINES}")
    return _emit(R, ROUTINES)


def routine_names_ir(R: Realization) -> Tuple[str, ...]:
    """the record's routine list for R — the io specialization is the
    record's own data: bytes egress adds emit_bytes/peval/selidx, ir
    egress adds emit_ir."""
    if R.io == ("stdin", "bytes"):
        return ROUTINES_IR_BYTES
    if R.io == ("stdin", "ir"):
        return ROUTINES_IR_IR
    if R.io != ("stdin", "stdout"):
        raise NotRealized(f"io={R.io!r} not realized by {ROUTINES_IR}")
    return ROUTINES_IR


def program_ir(R: Realization) -> Program:
    """Packed-IR batch kernel: depack replaces the token parse; the
    reducer core is shared verbatim.  io=("stdin","bytes") swaps the
    per-root NF line for a decoded [u32le len][bytes] frame."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    if R.reclaim not in ("none", "redirect"):
        raise NotRealized(f"reclaim={R.reclaim!r} not realized")
    return _emit(R, routine_names_ir(R))


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
    ios: tuple = (("stdin", "stdout"),)   # io modes the record realizes
    # routine list as a function of R — records whose routine set
    # depends on a realization axis (io selects the egress block)
    # declare it here; None means `routines` for every R.
    names_for: Optional[Callable] = None


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
    data_slots=data_slots_ir,
    ios=(("stdin", "stdout"), ("stdin", "bytes"), ("stdin", "ir")),
    names_for=routine_names_ir,
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
    if R.reclaim != "none":
        raise NotRealized(
            f"reclaim={R.reclaim!r} not realized by {ROUTINES_RES}")
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    if R.io != ("stdin", "stdout"):
        raise NotRealized(f"io={R.io!r} not realized by {ROUTINES_RES}")
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
    # byte-egress IR kernel: emits the decoder routines, keeps the
    # reducer core identical
    Rb = Realization(io=("stdin", "bytes"))
    prog_b = program_ir(Rb)
    text_b, labels_b = _isa.assemble(
        prog_b, _dummy_symbols(data_slots_ir(Rb), IMPORTS_IR))
    has = "emit_bytes" in labels_b and "peval" in labels_b
    print(f"  bytes.ir: {len(text_b)}B text "
          f"(emit_bytes={'y' if has else 'MISSING'})")
    if not has:
        ok = False
    print(f"{'OK' if ok else 'FAIL'} routines_x86_64_win64")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
