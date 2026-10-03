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
import layers                                   # noqa: E402
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

# dialect="plex.v3" (ADR-0006 ingest): the kernel depacks the archive
# itself — directory buffer, selected PIR span, KIND_PIR row count,
# and plexleft = payload bytes remaining (the stream's bounded EOF)
DATA_SLOTS_PX: Tuple[Tuple[str, int], ...] = (
    ("plexdir", 8), ("plexoff", 8), ("plexlen", 8), ("plexnp", 8),
    ("plexleft", 8),
)

# packed-IR constants — pinned by docs/adr/0005; keep in sync with
# spec_term.IR_MAGIC / IR_VERSION / IR_VAR.
IR_MAGIC = 0x30524950                # "PIR0"
IR_VERSION = 1
# .plex v3 archive (ADR-0006) — pinned by host/plex_bundle.py
PLEX_MAGIC = 0x58454C50              # "PLEX" little-endian u32
PLEX_VERSION = 3
PLEX_HEADER = 12                     # magic+ver+flags+hsize+nsec
PLEX_DIR_ENT = 32                    # fixed-width directory row
PLEX_KIND_PIR = 10                   # packed-IR program stream payload
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
        # MT: the reservation scales by T — each worker's slab claims get
        # the full single-thread budget, so T threads is not a smaller
        # per-stream arena than the ST kernel's (VA-only until commit).
        I("mov_r64_imm", "rdx", R.ir_arena_bytes * R.threads),
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
    if R.threads > 1:
        # r10 = the main thread's ctx block — mtctxs[threads].  Every
        # threaded helper (mkapp/mkleaf for the vocab below) keeps its
        # mutable state r10-relative; main's own ctx keeps pre-spawn
        # bookkeeping valid and makes it reachable at aggregation.
        p += [
            I("lea_r64_rip", "r10", ("p", "mtctxs")),
            I("mov_r64_imm", "rax", R.threads * MT_CTX_BYTES),
            I("add_r64_r64", "r10", "rax"),
            # first chunk committed for the template/vocab prefix —
            # grow_heap's claim path needs mtslab, which is per-stream
            I("mov_r64_r64", "rcx", "rbp"),
            I("mov_r64_imm", "rdx", R.chunk_bytes),
            I("mov_r32_imm32", "r8d", MEM_COMMIT),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
            I("mov_r64_imm", "rax", R.chunk_bytes),
            I("add_r64_r64", "rbp", "rax"),
            # ctx[T] span = the whole reservation — the vocab build's
            # grow_heap stays on the commit path and never reaches the
            # per-stream slabtop claim.  r10 reload: kernel32's syscall
            # path clobbers it (mov r10,rcx).
            I("lea_r64_rip", "r10", ("p", "mtctxs")),
            I("mov_r64_imm", "rax", R.threads * MT_CTX_BYTES),
            I("add_r64_r64", "r10", "rax"),
            I("mov_r64_rip", "rax", ("p", "irarena")),
            I("mov_r64_imm", "rcx", R.ir_arena_bytes * R.threads),
            I("add_r64_r64", "rax", "rcx"),
            I("mov_m64_r64", ("m", "r10", MT_CTX["myend"]), "rax"),
            I("mov_m64_r64", ("m", "r10", MT_CTX["homeend"]), "rax"),
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
        vocab = [
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
        ]
        p += vocab
        if R.threads == 1:
            # committed frame buffer: [bytes] per root (u32 len prefix
            # lives in .data — no 32-bit store in the ISA), cap doubles
            # as the malformed-spine termination bound.  MT: per-thread
            # buffers are VA'd at spawn instead.
            p += [
                I("xor_r32_r32", "ecx", "ecx"),
                I("mov_r64_imm", "rdx", EG_OUT_BYTES),
                I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
                I("mov_r32_imm32", "r9d", PAGE_RW),
                I("call_mrip", iat("VirtualAlloc")),
                I("test_r64_r64", "rax", "rax"),
                I("je_rel32", ("l", "exit4")),
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


def r_plex_read(R: Realization, ctx: Ctx) -> Program:
    """plex_read (dialect="plex.v3", ADR-0006 ingest): the kernel
    depacks the archive itself — stdin stays a byte stream, the
    container walk is index arithmetic over fixed-width rows.

    12B header ('PLEX' magic, u8 ver==3, u8 flags, u16 hsize, u32
    n_sections) -> n*32B directory -> validate every row:
    cell type in {1,4,8}, arity >= 1, length == rows*arity*type
    (by DIVISION — no mul in this ISA: (ln/m).quot == rows and
    rem == 0), offset 8-aligned and >= hsize.  Exactly one
    KIND_PIR (10) row is required — its payload span is the
    packed-IR stream.  The tail then skips to the span and jumps
    into ir_sloop; `plexleft` bounds every later stdin read so
    trailing bytes after the declared span are never consumed
    (bounded-EOF, mirroring read_bundle's span check — a section
    lying about its length refuses as a truncated read).

    Refusals (exit3) mirror read_bundle: bad magic/version,
    hsize < dir_end or misaligned, truncated header/dir/payload,
    bad cell type, arity 0, length != rows*arity*type, unaligned
    or < hsize offset, no or duplicate KIND_PIR section.  A span
    beyond the file is caught when the bounded read hits real EOF.

    Registers: r12 row cursor, r13 hsize, r14 dirbytes then skip
    delta, r15 row count, rsi read progress, rdi scratch.  rbx/rbp
    (heap) untouched — this runs before irstart is consumed."""
    iat = ctx["iat"]
    p: Program = [
        LBL("plex_read"),
        # ---- 12B header into irhdr ----
        I("xor_r32_r32", "r13d", "r13d"),
        LBL("px_hdr"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "irhdr")),
        I("add_r64_r64", "rdx", "r13"),
        I("mov_r32_imm32", "r8d", PLEX_HEADER),
        I("sub_r64_r64", "r8", "r13"),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("add_r64_r64", "r13", "rax"),
        I("cmp_r64_imm", "r13", PLEX_HEADER),
        I("jl_rel32", ("l", "px_hdr")),
        # ---- header fields ----
        I("mov_r64_rip", "r13", ("p", "irhdr")),
        I("mov_r32_m32", "eax", ("m", "r13", 0)),
        I("mov_r32_imm32", "ecx", PLEX_MAGIC),
        I("cmp_r64_r64", "rax", "rcx"),
        I("jne_rel32", ("l", "exit3")),
        I("movzx_r32_m8", "eax", ("m", "r13", 4)),
        I("cmp_r64_imm", "rax", PLEX_VERSION),
        I("jne_rel32", ("l", "exit3")),
        # nsec u32 @8 -> r15 (0 -> refuse); hsize u16 @6 -> r13
        # (nsec first — r13 is about to stop being the buf pointer)
        I("mov_r32_m32", "ecx", ("m", "r13", 8)),
        I("test_r64_r64", "rcx", "rcx"), I("je_rel32", ("l", "exit3")),
        I("mov_r32_m32", "eax", ("m", "r13", 6)),
        I("and_r64_imm", "rax", 0xFFFF),
        I("mov_r64_r64", "r13", "rax"),
        I("mov_r64_r64", "r15", "rcx"),
        I("mov_r64_r64", "r14", "rcx"), I("shl_r64_imm8", "r14", 5),
        # dir_end = 12 + 32n must fit hsize, hsize 8-aligned
        I("lea_r64_m64", "rax", ("m", "r14", PLEX_HEADER)),
        I("cmp_r64_r64", "r13", "rax"), I("jl_rel32", ("l", "exit3")),
        I("mov_r64_r64", "rax", "r13"), I("and_r64_imm", "rax", 7),
        I("jne_rel32", ("l", "exit3")),
        # ---- directory buffer + read-exactly 32n ----
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r64_r64", "rdx", "r14"),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "plexdir"), "rax"),
        I("xor_r32_r32", "esi", "esi"),
        LBL("px_drd"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "plexdir")),
        I("add_r64_r64", "rdx", "rsi"),
        I("mov_r64_r64", "r8", "r14"), I("sub_r64_r64", "r8", "rsi"),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("add_r64_r64", "rsi", "rax"),
        I("cmp_r64_r64", "rsi", "r14"), I("jl_rel32", ("l", "px_drd")),
        # ---- scan rows: r12 cursor, r15 count ----
        I("mov_r64_rip", "r12", ("p", "plexdir")),
        I("xor_r32_r32", "eax", "eax"),
        I("mov_rip_r64", ("p", "plexnp"), "rax"),
        LBL("px_row"),
        # cell type in {1,4,8}
        I("movzx_r32_m8", "eax", ("m", "r12", 0)),
        I("cmp_r64_imm", "rax", 1), I("je_rel32", ("l", "px_tok")),
        I("cmp_r64_imm", "rax", 4), I("je_rel32", ("l", "px_tok")),
        I("cmp_r64_imm", "rax", 8), I("jne_rel32", ("l", "exit3")),
        LBL("px_tok"),
        I("mov_r64_r64", "r8", "rax"),            # r8 = cell type
        I("movzx_r32_m8", "ecx", ("m", "r12", 1)),
        I("test_r64_r64", "rcx", "rcx"), I("je_rel32", ("l", "exit3")),
        # m = arity * type via shift (type is a power of two)
        I("cmp_r64_imm", "r8", 4), I("je_rel32", ("l", "px_m4")),
        I("cmp_r64_imm", "r8", 8), I("je_rel32", ("l", "px_m8")),
        I("jmp_rel32", ("l", "px_mset")),          # type 1: m = ar
        LBL("px_m4"), I("shl_r64_imm8", "rcx", 2),
        I("jmp_rel32", ("l", "px_mset")),
        LBL("px_m8"), I("shl_r64_imm8", "rcx", 3),
        LBL("px_mset"),
        # length == rows*m  <=>  (ln/m).quot == rows && rem == 0
        I("mov_r64_m64", "rax", ("m", "r12", 16)),   # ln
        I("xor_r32_r32", "edx", "edx"),
        I("div_r64", "rcx"),                          # rax=q, rdx=r
        I("test_r64_r64", "rdx", "rdx"),
        I("jne_rel32", ("l", "exit3")),
        I("mov_r64_m64", "rsi", ("m", "r12", 24)),    # rows
        I("cmp_r64_r64", "rax", "rsi"),
        I("jne_rel32", ("l", "exit3")),
        # offset: 8-aligned and >= hsize(r13)
        I("mov_r64_m64", "rax", ("m", "r12", 8)),
        I("mov_r64_r64", "rdx", "rax"), I("and_r64_imm", "rdx", 7),
        I("jne_rel32", ("l", "exit3")),
        I("cmp_r64_r64", "rax", "r13"),
        I("jl_rel32", ("l", "exit3")),
        # KIND_PIR row: record span, count occurrences
        I("mov_r32_m32", "edi", ("m", "r12", 2)),
        I("and_r64_imm", "rdi", 0xFFFF),
        I("cmp_r64_imm", "rdi", PLEX_KIND_PIR),
        I("jne_rel32", ("l", "px_next")),
        I("inc_mrip", ("p", "plexnp")),
        I("mov_rip_r64", ("p", "plexoff"), "rax"),
        I("mov_r64_m64", "rdx", ("m", "r12", 16)),
        I("mov_rip_r64", ("p", "plexlen"), "rdx"),
        LBL("px_next"),
        I("add_r64_imm", "r12", PLEX_DIR_ENT),
        I("dec_r64", "r15"), I("jne_rel32", ("l", "px_row")),
        # exactly one PIR section
        I("mov_r64_rip", "rax", ("p", "plexnp")),
        I("cmp_r64_imm", "rax", 1), I("jne_rel32", ("l", "exit3")),
        # bounded-EOF for the payload span, then skip to plexoff:
        # stdin pos = PLEX_HEADER + 32n = PLEX_HEADER + r14 (r14 still
        # holds dirbytes — the scan never touches it), and plexoff >=
        # hsize >= pos so the delta is non-negative
        I("mov_r64_rip", "rax", ("p", "plexlen")),
        I("mov_rip_r64", ("p", "plexleft"), "rax"),
        I("mov_r64_rip", "rax", ("p", "plexoff")),
        I("sub_r64_imm", "rax", PLEX_HEADER),
        I("sub_r64_r64", "rax", "r14"),
        I("mov_r64_r64", "r14", "rax"),
        # n = min(r14, granule); read+discard into irhdr
        LBL("px_skiploop"),
        I("test_r64_r64", "r14", "r14"),
        I("je_rel32", ("l", "ir_sloop")),
        I("mov_r64_r64", "r8", "r14"),
        I("mov_r32_imm32", "eax", R.read_buf_bytes),
        I("cmp_r64_r64", "r8", "rax"),
        I("jbe_rel32", ("l", "px_sk_n")),
        I("mov_r64_r64", "r8", "rax"),
        LBL("px_sk_n"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "irhdr")),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("sub_r64_r64", "r14", "rax"),
        I("jne_rel32", ("l", "px_skiploop")),
        I("jmp_rel32", ("l", "ir_sloop")),
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
    plex = R.dialect == "plex.v3"

    def _clamp(lbl: str) -> Program:
        # bounded source: r8 (read request) <= plexleft — at 0 the
        # kernel reads 0 bytes -> nread=0 -> clean EOF at the span
        if not plex:
            return []
        return [I("mov_r64_rip", "rax", ("p", "plexleft")),
                I("cmp_r64_r64", "r8", "rax"),
                I("jbe_rel32", ("l", lbl)),
                I("mov_r64_r64", "r8", "rax"),
                LBL(lbl)]

    def _dec() -> Program:
        if not plex:
            return []
        return [I("mov_r64_rip", "rcx", ("p", "plexleft")),
                I("mov_r64_rip", "rax", ("p", "nread")),
                I("sub_r64_r64", "rcx", "rax"),
                I("mov_rip_r64", ("p", "plexleft"), "rcx")]

    return [
        LBL("ir_sloop"),
        # ---- 16-byte header, read-exactly into the granule buf ----
        I("xor_r32_r32", "r13d", "r13d"),
        LBL("ir_hloop"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "irhdr")),
        I("add_r64_r64", "rdx", "r13"),
        I("mov_r32_imm32", "r8d", 16), I("sub_r64_r64", "r8", "r13"),
        *_clamp("px_hcl"),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        # pipes report EOF as FALSE/ERROR_BROKEN_PIPE, files as nread=0 —
        # clean at a stream boundary (r13==0), truncated otherwise
        I("test_r64_r64", "rax", "rax"), I("jne_rel32", ("l", "ir_hok")),
        I("test_r64_r64", "r13", "r13"), I("je_rel32", ("l", "ir_sdone")),
        I("jmp_rel32", ("l", "exit3")),
        LBL("ir_hok"),
        *_dec(),
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
        # MT: next stage is ir_spawn (workers depack); ST: ir_depack
        I("je_rel32", ("l", ctx.get("irnext", "ir_depack"))),
        I("xor_r32_r32", "r13d", "r13d"),
        LBL("ir_brd"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_rip", "rdx", ("p", "irbuf")),
        I("add_r64_r64", "rdx", "r13"),
        I("mov_r64_r64", "r8", "r14"), I("sub_r64_r64", "r8", "r13"),
        *_clamp("px_bcl"),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        *_dec(),
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


def r_ir_spawn(R: Realization, ctx: Ctx) -> Program:
    """MT stream driver (falls through from ir_read): slabtop reset,
    mtslab = depack span + headroom, ctx blocks zeroed, static root
    chunks, T CreateThreads, WaitForMultipleObjects join, stats
    aggregation, then ordered frame flush — thread t holds the
    contiguous chunk [j0,j1) so concatenating buffers in t order IS
    root order.  Owns the ir_sdone tail (falls to stats)."""
    iat = ctx["iat"]
    T = R.threads
    CTXB = MT_CTX_BYTES
    p: Program = [
        LBL("ir_spawn"),
        # own frame: arg5/arg6 live at [rsp+0x20/0x28]; locals 0x30+
        I("sub_r64_imm", "rsp", 0x50),
        # fresh claim frontier per stream: slabs start past the template
        I("mov_r64_rip", "rax", ("p", "permend")),
        I("mov_rip_r64", ("p", "slabtop"), "rax"),
        # mtslab = pagealign(24*nn + 8*nr [+ persist] + headroom)
        I("mov_r64_rip", "rax", ("p", "irnodes")),
    ] + _mul24() + [
        I("mov_r64_rip", "rcx", ("p", "irnroots")),
        I("shl_r64_imm8", "rcx", 3),
        I("add_r64_r64", "rax", "rcx"),
    ]
    if R.reclaim == "redirect":
        p += [I("mov_r64_imm", "rcx", R.persist_bytes),
              I("add_r64_r64", "rax", "rcx")]
    p += [
        I("mov_r64_imm", "rcx", MT_HEADROOM),
        I("add_r64_r64", "rax", "rcx"),
        I("add_r64_imm", "rax", 0xfff),
        I("and_r64_imm", "rax", -4096),
        I("mov_rip_r64", ("p", "mtslab"), "rax"),
        # zero the ctx array ((T+1) blocks; ctx[T] is main's)
        I("lea_r64_rip", "rdi", ("p", "mtctxs")),
        I("mov_r64_imm", "rcx", (T + 1) * CTXB // 8),
        I("xor_r32_r32", "eax", "eax"),
        LBL("mt_z"),
        I("mov_m64_r64", ("m", "rdi", 0), "rax"),
        I("add_r64_imm", "rdi", 8), I("dec_r64", "rcx"),
        I("jne_rel32", ("l", "mt_z")),
        # per-thread ordered frame buffers — one VA, T partitions
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r64_imm", "rdx", T * EG_MT_OUT),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_r64", "r13", "rax"),                  # outbase
        # chunk geometry: c = nr // T, rem = nr % T
        I("mov_r64_rip", "rax", ("p", "irnroots")),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "ecx", T),
        I("div_r64", "rcx"),
        I("mov_r64_r64", "r12", "rax"),                  # c
        I("mov_m64_r64", ("m", "rsp", 0x30), "rdx"),     # rem
        # spawn loop: r14=ctxptr, r15=t, rbx=running chunk start
        I("lea_r64_rip", "r14", ("p", "mtctxs")),
        I("xor_r32_r32", "r15d", "r15d"),
        I("xor_r32_r32", "ebx", "ebx"),
        LBL("mt_sploop"),
        I("mov_m64_r64", ("m", "r14", MT_CTX["irj"]), "rbx"),
        I("mov_r64_r64", "rax", "r12"),                  # take = c
        I("mov_r64_m64", "rcx", ("m", "rsp", 0x30)),
        I("cmp_r64_r64", "r15", "rcx"),                  # t < rem?
        I("jge_rel32", ("l", "mt_noext")),
        I("inc_r64", "rax"),
        LBL("mt_noext"),
        I("add_r64_r64", "rax", "rbx"),                  # jend
        I("mov_m64_r64", ("m", "r14", MT_CTX["jend"]), "rax"),
        I("mov_r64_r64", "rbx", "rax"),
        # outbuf = outbase + t*EG_MT_OUT (EG_MT_OUT is 1<<24)
        I("mov_r64_r64", "rax", "r15"),
        I("shl_r64_imm8", "rax", 24),
        I("add_r64_r64", "rax", "r13"),
        I("mov_m64_r64", ("m", "r14", MT_CTX["outbuf"]), "rax"),
        I("mov_m64_r64", ("m", "r14", MT_CTX["outcur"]), "rax"),
        I("mov_r64_imm", "rcx", EG_MT_OUT),
        I("add_r64_r64", "rax", "rcx"),
        I("mov_m64_r64", ("m", "r14", MT_CTX["outlim"]), "rax"),
        # CreateThread(0,0,mt_worker,ctx,0,0) -> handles[t]
        I("xor_r32_r32", "ecx", "ecx"),
        I("xor_r32_r32", "edx", "edx"),
        I("lea_r64_rip", "r8", ("p", "mt_worker")),
        I("mov_r64_r64", "r9", "r14"),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("mov_m64_imm32", ("m", "rsp", 0x28), 0),
        I("call_mrip", iat("CreateThread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("lea_r64_rip", "rcx", ("p", "mthandles")),
        I("mov_r64_r64", "rdx", "r15"), I("shl_r64_imm8", "rdx", 3),
        I("add_r64_r64", "rcx", "rdx"),
        I("mov_m64_r64", ("m", "rcx", 0), "rax"),
        I("add_r64_imm", "r14", CTXB),
        I("inc_r64", "r15"),
        I("cmp_r64_imm", "r15", T), I("jl_rel32", ("l", "mt_sploop")),
        # WaitForMultipleObjects(T, handles, TRUE, INFINITE)
        I("mov_r32_imm32", "ecx", T),
        I("lea_r64_rip", "rdx", ("p", "mthandles")),
        I("mov_r32_imm32", "r8d", 1),
        I("mov_r32_imm32", "r9d", -1),
        I("call_mrip", iat("WaitForMultipleObjects")),
        I("mov_r64_imm", "rcx", 0xFFFFFFFF),             # WAIT_FAILED
        I("cmp_r64_r64", "rax", "rcx"), I("je_rel32", ("l", "exit4")),
        # aggregate + flush, thread order: r14=ctxptr, r15=t
        I("lea_r64_rip", "r14", ("p", "mtctxs")),
        I("xor_r32_r32", "r15d", "r15d"),
        LBL("mt_join"),
        # Σctx[t].nalloc / .irsteps (+ .eb_dec in bytes mode) — the
        # T+1st block (main's vocab) rides the loop's last step
        I("mov_r64_m64", "rax", ("m", "r14", MT_CTX["nalloc"])),
        I("mov_r64_rip", "rdx", ("p", "nalloc")),
        I("add_r64_r64", "rdx", "rax"),
        I("mov_rip_r64", ("p", "nalloc"), "rdx"),
        I("mov_r64_m64", "rax", ("m", "r14", MT_CTX["irsteps"])),
        I("mov_r64_rip", "rdx", ("p", "irsteps")),
        I("add_r64_r64", "rdx", "rax"),
        I("mov_rip_r64", ("p", "irsteps"), "rdx"),
    ]
    if R.io[1] == "bytes":
        p += [
            I("mov_r64_m64", "rax", ("m", "r14", MT_CTX["eb_dec"])),
            I("mov_r64_rip", "rdx", ("p", "eb_dec")),
            I("add_r64_r64", "rdx", "rax"),
            I("mov_rip_r64", ("p", "eb_dec"), "rdx"),
        ]
    p += [
        # flush this thread's frames: WriteFile(hout, outbuf, outcur-buf)
        I("cmp_r64_imm", "r15", T), I("jge_rel32", ("l", "mt_jnext")),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_m64", "rdx", ("m", "r14", MT_CTX["outbuf"])),
        I("mov_r64_m64", "r8", ("m", "r14", MT_CTX["outcur"])),
        I("sub_r64_r64", "r8", "rdx"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        # CloseHandle(handles[t])
        I("lea_r64_rip", "rcx", ("p", "mthandles")),
        I("mov_r64_r64", "rdx", "r15"), I("shl_r64_imm8", "rdx", 3),
        I("add_r64_r64", "rcx", "rdx"),
        I("mov_r64_m64", "rcx", ("m", "rcx", 0)),
        I("call_mrip", iat("CloseHandle")),
        LBL("mt_jnext"),
        I("add_r64_imm", "r14", CTXB),
        I("inc_r64", "r15"),
        I("cmp_r64_imm", "r15", T + 1),
        I("jl_rel32", ("l", "mt_join")),
        # ---- bdone tail: release the stream region, next stream ----
        I("mov_r64_rip", "rcx", ("p", "irbuf")),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "r8d", MEM_RELEASE),
        I("call_mrip", iat("VirtualFree")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_rip", "rax", ("p", "irnstreams")), I("inc_r64", "rax"),
        I("mov_rip_r64", ("p", "irnstreams"), "rax"),
        I("add_r64_imm", "rsp", 0x50),
        I("jmp_rel32", ("l", "ir_sloop")),
        LBL("ir_sdone"),
        I("mov_r64_rip", "rax", ("p", "irnstreams")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit3")),
        I("mov_r64_rip", "r15", ("p", "irsteps")),
    ]
    return p


def r_mt_worker(R: Realization, ctx: Ctx) -> Program:
    """mt_worker(rcx=ctxptr): claim a slab span (lock xadd slabtop),
    depack the shared input into it, then the per-root loop over the
    static chunk [irj, jend): arena reset, reduce, egress to the
    thread's ordered frame buffer.  Nothing shared-mutable is written:
    slab cells are thread-private, template/vocab are read-only."""
    iat = ctx["iat"]
    p: Program = [
        LBL("mt_worker"),
        # CreateThread entry; save the callee-saved regs the body uses
        I("push_r64", "rbx"), I("push_r64", "rbp"),
        I("push_r64", "rsi"), I("push_r64", "rdi"),
        I("push_r64", "r12"), I("push_r64", "r13"),
        I("push_r64", "r14"), I("push_r64", "r15"),
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_r64_r64", "r10", "rcx"),                  # ctx base
        # claim [slabtop, +mtslab)
        I("mov_r64_rip", "rax", ("p", "mtslab")),
        I("lock_xadd_rip", ("p", "slabtop"), "rax"),
        I("mov_r64_rip", "rcx", ("p", "mtslab")),
        I("add_r64_r64", "rcx", "rax"),                  # span end
        I("mov_r64_rip", "rdx", ("p", "irarena")),
        I("mov_r64_imm", "r8", R.ir_arena_bytes * R.threads),
        I("add_r64_r64", "rdx", "r8"),
        I("cmp_r64_r64", "rdx", "rcx"),
        I("jl_rel32", ("l", "exit4")),
        I("mov_m64_r64", ("m", "r10", MT_CTX["cellbase"]), "rax"),
        I("mov_m64_r64", ("m", "r10", MT_CTX["myend"]), "rcx"),
        I("mov_m64_r64", ("m", "r10", MT_CTX["homeend"]), "rcx"),
        I("mov_r64_r64", "rbx", "rax"),                  # bump cursors
        I("mov_r64_r64", "rbp", "rax"),                  # = uncommitted
    ]
    if R.io[1] == "bytes":
        # frame payload bound = this thread's out buffer end
        p += [
            I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["outlim"])),
            I("mov_m64_r64", ("m", "r10", MT_CTX["eb_lim"]), "rax"),
        ]
    p += [
        I("jmp_rel32", ("l", "ir_depack")),
        # ---- depack tail lands here: per-root loop over [irj, jend)
        LBL("ir_binit"),
        LBL("ir_bloop"),
        I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["irj"])),
        I("mov_r64_m64", "rcx", ("m", "r10", MT_CTX["jend"])),
        I("cmp_r64_r64", "rax", "rcx"),
        I("jge_rel32", ("l", "mt_wdone")),
        # arena reset: bump back to irstart inside the home span —
        # pages stay committed (reset is a cursor move; MEM_COMMIT
        # re-arming by grow_heap is idempotent) and never decommitted
        # mid-stream: span claims interleave, so no free-range is
        # exclusively this thread's to release.
        I("mov_r64_m64", "rbx", ("m", "r10", MT_CTX["irstart"])),
        I("mov_r64_r64", "rbp", "rbx"),
        I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["homeend"])),
        I("mov_m64_r64", ("m", "r10", MT_CTX["myend"]), "rax"),
        # r12 = irroots[irj]; r15 = per-root steps
        I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["irj"])),
        I("shl_r64_imm8", "rax", 3),
        I("mov_r64_m64", "rcx", ("m", "r10", MT_CTX["irroots"])),
        I("add_r64_r64", "rax", "rcx"),
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
        LBL("ir_red_done"),
        I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["irsteps"])),
        I("add_r64_r64", "rax", "r15"),
        I("mov_m64_r64", ("m", "r10", MT_CTX["irsteps"]), "rax"),
    ]
    if R.io[1] == "bytes":
        # payload window begins past the u32 len slot at outcur
        p += [
            I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["outcur"])),
            I("add_r64_imm", "rax", 4),
            I("mov_m64_r64", ("m", "r10", MT_CTX["eb_out"]), "rax"),
            I("call_rel32", ("l", "emit_bytes")),
        ]
    elif R.io[1] == "ir":
        p += [I("call_rel32", ("l", "emit_ir"))]
    else:
        # text NF line straight into the frame buffer
        p += [
            I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "count_nodes")),
            I("mov_r64_m64", "rsi", ("m", "r10", MT_CTX["outcur"])),
            I("add_r64_r64", "rax", "rax"),
            I("add_r64_imm", "rax", 16),
            I("add_r64_r64", "rax", "rsi"),
            I("mov_r64_m64", "rcx", ("m", "r10", MT_CTX["outlim"])),
            I("cmp_r64_r64", "rcx", "rax"),
            I("jl_rel32", ("l", "exit4")),
            I("mov_r64_r64", "rdi", "r12"), I("call_rel32", ("l", "emit_nf")),
            I("mov_m8_imm8", ("m", "rsi", 0), 0x0A), I("inc_r64", "rsi"),
            I("mov_m64_r64", ("m", "r10", MT_CTX["outcur"]), "rsi"),
        ]
    p += [
        I("mov_r64_m64", "rax", ("m", "r10", MT_CTX["irj"])),
        I("inc_r64", "rax"),
        I("mov_m64_r64", ("m", "r10", MT_CTX["irj"]), "rax"),
        I("jmp_rel32", ("l", "ir_bloop")),
        LBL("mt_wdone"),
        I("xor_r32_r32", "ecx", "ecx"),
        I("call_mrip", iat("ExitThread")),
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
    Also bounds the depack-region ds build (its rbp = region end).
    MT: commit-ahead within the thread's claimed span; at myend the
    worker claims the next slab span (lock xadd on slabtop), commits
    its first chunk, and the bump cursors jump to it."""
    iat = ctx["iat"]
    if R.threads > 1:
        return [
            LBL("grow_heap"),
            I("sub_r64_imm", "rsp", 0x28),
            # in-span room?  rbp+chunk <= ctx.myend -> commit [rbp,chunk)
            I("lea_r64_m64", "rax", ("m", "rbp", R.chunk_bytes)),
            I("mov_r64_m64", "rcx", ("m", "r10", MT_CTX["myend"])),
            I("cmp_r64_r64", "rcx", "rax"),
            I("jl_rel32", ("l", "gh_claim")),
            I("mov_r64_r64", "rcx", "rbp"),
            I("mov_r64_imm", "rdx", R.chunk_bytes),
            I("mov_r32_imm32", "r8d", MEM_COMMIT),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"),
            I("je_rel32", ("l", "grow_fail")),
            I("mov_r64_imm", "rax", R.chunk_bytes),
            I("add_r64_r64", "rbp", "rax"),
            I("add_r64_imm", "rsp", 0x28), I("ret"),
            # ---- span exhausted: claim [slabtop, +mtslab) ----
            LBL("gh_claim"),
            I("mov_r64_rip", "rax", ("p", "mtslab")),
            I("lock_xadd_rip", ("p", "slabtop"), "rax"),
            # rax = claimed base; bound: base+mtslab <= arena end
            I("mov_r64_rip", "rcx", ("p", "mtslab")),
            I("add_r64_r64", "rcx", "rax"),              # rcx = new myend
            I("mov_r64_rip", "rdx", ("p", "irarena")),
            I("mov_r64_imm", "r8", R.ir_arena_bytes * R.threads),
            I("add_r64_r64", "rdx", "r8"),
            I("cmp_r64_r64", "rdx", "rcx"),
            I("jl_rel32", ("l", "grow_fail")),
            I("mov_m64_r64", ("m", "r10", MT_CTX["myend"]), "rcx"),
            I("mov_r64_r64", "rbx", "rax"),
            I("mov_r64_r64", "rbp", "rax"),
            I("mov_r64_r64", "rcx", "rbp"),
            I("mov_r64_imm", "rdx", R.chunk_bytes),
            I("mov_r32_imm32", "r8d", MEM_COMMIT),
            I("mov_r32_imm32", "r9d", PAGE_RW),
            I("call_mrip", iat("VirtualAlloc")),
            I("test_r64_r64", "rax", "rax"),
            I("je_rel32", ("l", "grow_fail")),
            I("mov_r64_imm", "rax", R.chunk_bytes),
            I("add_r64_r64", "rbp", "rax"),
            I("add_r64_imm", "rsp", 0x28), I("ret"),
            LBL("grow_fail"), I("mov_r32_imm32", "ecx", 4),
            I("call_mrip", iat("ExitProcess")),
        ]
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
        # ---- flush: u32le len + bytes ----
        LBL("eb_flush"),
        I("mov_r64_rip", "rax", ("p", "eb_out")),
        I("mov_r64_r64", "rdx", "r14"), I("sub_r64_r64", "rdx", "rax"),
    ]
    if R.threads > 1:
        # MT: append [u32 len][payload] to this thread's frame buffer —
        # the worker set eb_out = outcur+4, so the len slot is outcur
        # itself and the payload already sits where it belongs.
        p += [
            I("mov_m32_r32", ("m", "rax", -4), "edx"),
            I("mov_rip_r64", ("p", "outcur"), "r14"),
        ]
    else:
        p += [
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
        ]
    p += [
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
        # frame: u32 len + payload
        I("mov_r64_r64", "rdx", "rsi"), I("sub_r64_r64", "rdx", "r14"),
    ]
    if R.threads > 1:
        # MT: append [u32 len][blob] to this thread's frame buffer —
        # bound by outlim, then rep movsb the staging blob across.
        p += [
            I("mov_r64_rip", "rax", ("p", "outcur")),
            I("lea_r64_m64", "rcx", ("m", "rax", 4)),
            I("add_r64_r64", "rcx", "rdx"),            # end-of-frame
            I("mov_r64_rip", "r8", ("p", "outlim")),
            I("cmp_r64_r64", "r8", "rcx"),
            I("jl_rel32", ("l", "exit4")),             # frame overflow
            I("mov_m32_r32", ("m", "rax", 0), "edx"),
            I("lea_r64_m64", "rdi", ("m", "rax", 4)),
            I("mov_r64_rip", "rsi", ("p", "ei_out")),
            I("mov_r64_r64", "rcx", "rdx"),
            I("rep_movsb"),
            I("mov_rip_r64", ("p", "outcur"), "rdi"),
        ]
    else:
        p += [
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
        ]
    p += [
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


# Routine vocabulary per kernel family — the catalog of candidates a
# record's legs compose FROM (both basis variants live here; the
# fuse_s legs select per-R).  What a given R actually emits is
# composed below in LEGS_*/routine_names_ir — these tuples are the
# declared vocabulary used by program_query_rt enumeration, routine
# size accounting, and the Routines records' `routines` field.
ROUTINES: Tuple[str, ...] = (
    "entry", "parse", "reduce", "stats", "exits",
    "grow_heap", "mkleaf", "mkapp", "mkapp_p", "mkstk", "repr",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

# IR variant: same reducer core, different front end — no token parser,
# no parse stack (mkstk unused); entry/read/depack/reduce replace
# entry/parse/reduce.  "ir_reduce" is the batch loop.
ROUTINES_IR: Tuple[str, ...] = (
    "ir_entry", "ir_read", "ir_depack", "ir_reduce", "stats", "exits",
    "grow_heap_ir", "mkleaf", "mkapp", "mkapp_p", "repr",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp", "st_s",
    "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

# MT variant (R.threads>1): ir_reduce's per-root loop becomes
# ir_spawn (driver) + mt_worker (per-thread depack+reduce+egress);
# ir_depack emits last — the worker jumps into it, its tail lands on
# mt_worker's ir_binit.  Ordering constraints: ir_spawn must follow
# ir_read (fallthrough) and precede stats (ir_sdone tail fallthrough).
ROUTINES_IR_MT: Tuple[str, ...] = (
    "ir_entry", "ir_read", "ir_spawn", "stats", "exits", "mt_worker",
    "ir_depack", "grow_heap_ir", "mkleaf", "mkapp", "mkapp_p", "repr",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp",
    "st_s", "step_congr", "count_nodes", "emit_nf", "itoa", "build_ds",
)

IMPORTS_IR: Tuple[str, ...] = IMPORTS + ("VirtualFree",)
IMPORTS_IR_MT: Tuple[str, ...] = IMPORTS_IR + (
    "CreateThread", "WaitForMultipleObjects", "CloseHandle",
    "ExitThread",
)

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


# ======================================================================
# KERNEL LAYER LEGS — the composition contract, declared (layers.py)
#
# The kernel image is an ordered sequence of legs, each gated by ONE
# realization axis.  An axis value with no row refuses — the table is
# the complete declaration of what this family realizes.  slot_rank
# orders .data contributions independently of emission position
# (.data layout is image contract): 10 reclaim, 20 container,
# 30 threads, 40 egress.
#
# MT slot block: ctx fields sized by R.threads — a callable
# contribution, parameter-shaped data.
def _slots_mt(R: Realization) -> tuple:
    return (("slabtop", 8), ("mtslab", 8),
            ("mtctxs", (R.threads + 1) * MT_CTX_BYTES),
            ("mthandles", R.threads * 8))


# bytes-egress .data under MT: the cursors live in per-thread ctx
# fields — only the shared probe vocab + counters land in .data
_DATA_SLOTS_EB_MT: Tuple[Tuple[str, int], ...] = (
    ("eb_i", 8), ("eb_k", 8), ("eb_ki", 8), ("eb_marks", 8),
    ("eb_dec", 8),
)


def _slots_eb(R: Realization) -> tuple:
    return _DATA_SLOTS_EB_MT if R.threads > 1 else DATA_SLOTS_EB


# ir-egress .data under MT: all ei_* state is ctx fields (emit_ir's
# ei_len frame-write path is ST-only — never emitted under threads>1)
def _slots_ei(R: Realization) -> tuple:
    return () if R.threads > 1 else DATA_SLOTS_EI


_LEGS_IR: Tuple[layers.Leg, ...] = (
    layers.Leg("head",      None,      ("ir_entry",)),
    layers.Leg("container", "dialect", {
        "pir":     layers.Impl(),
        "plex.v3": layers.Impl(("plex_read",),
                               slots=DATA_SLOTS_PX, slot_rank=20),
    }),
    layers.Leg("encoding",  None,      ("ir_read",)),
    layers.Leg("driver",    "threads", {
        "st": layers.Impl(("ir_depack", "ir_reduce")),
        "mt": layers.Impl(("ir_spawn",),
                          slots=_slots_mt, slot_rank=30),
    }),
    layers.Leg("stats",     None,      ("stats", "exits")),
    layers.Leg("worker",    "threads", {
        "st": layers.Impl(), "mt": layers.Impl(("mt_worker",)),
    }),
    layers.Leg("depack",    "threads", {
        "st": layers.Impl(), "mt": layers.Impl(("ir_depack",)),
    }),
    layers.Leg("core_a",    None,      (
        "grow_heap_ir", "mkleaf", "mkapp", "mkapp_p", "repr",
        "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp",
    )),
    layers.Leg("s_prim",    "fuse_s",  {
        False: layers.Impl(), True: layers.Impl(("st_s",)),
    }),
    layers.Leg("core_b",    None,      (
        "step_congr", "count_nodes", "emit_nf", "itoa",
    )),
    layers.Leg("persist",   "reclaim", {
        "none":     layers.Impl(),
        "redirect": layers.Impl(slots=DATA_SLOTS_PS, slot_rank=10),
    }),
    layers.Leg("basis_tpl", "fuse_s",  {
        False: layers.Impl(("build_ds",)), True: layers.Impl(),
    }),
    layers.Leg("egress",    "io",      {
        ("stdin", "stdout"): layers.Impl(),
        ("stdin", "bytes"):  layers.Impl(
            ("emit_bytes", "peval", "selidx"),
            slots=_slots_eb, slot_rank=40),
        ("stdin", "ir"):     layers.Impl(
            ("emit_ir",), slots=_slots_ei, slot_rank=40),
    }),
)

_LEGS_TOKEN: Tuple[layers.Leg, ...] = (
    layers.Leg("head",      None,      ("entry",)),
    layers.Leg("container", "dialect", {"pir": layers.Impl()}),
    layers.Leg("encoding",  None,      ("parse",)),
    layers.Leg("driver",    "threads", {"st": layers.Impl(("reduce",))}),
    layers.Leg("stats",     None,      ("stats", "exits")),
    layers.Leg("core_a",    None,      (
        "grow_heap", "mkleaf", "mkapp", "mkapp_p", "mkstk", "repr",
        "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp",
    )),
    layers.Leg("s_prim",    "fuse_s",  {
        False: layers.Impl(), True: layers.Impl(("st_s",)),
    }),
    layers.Leg("core_b",    None,      (
        "step_congr", "count_nodes", "emit_nf", "itoa",
    )),
    layers.Leg("persist",   "reclaim", {
        "none": layers.Impl(), "redirect": layers.Impl(),
    }),
    layers.Leg("basis_tpl", "fuse_s",  {
        False: layers.Impl(("build_ds",)), True: layers.Impl(),
    }),
    layers.Leg("egress",    "io",      {
        ("stdin", "stdout"): layers.Impl(),
    }),
)


# ======================================================================
# MT KERNEL (threads>1 — toolchain native.x86_64.pe.ir.mt)
#
# Model (the g_slabtop/SLAB_CELLS discipline of ir_cuda.cu): the shared
# arena reservation is partitioned by atomic claims — a worker's slab is
# [lock-xadd bump, +slab) — and every mutable slot the reducer touches
# becomes a field of a per-thread context block, addressed through r10
# (unused kernel-wide; volatile across WinAPI, so call_mrip sites in
# threaded routines save/restore it on their own frame).
#
# Isolation: each worker depacks the shared input bytes into ITS OWN
# slab cells — redirect's FWD write-backs then mutate only thread-local
# memory; the sub-permend template/vocab region is the only shared data
# and it is immutable by construction.  Root partition is static
# contiguous chunks, so concatenating per-thread frame buffers in thread
# order reproduces root order byte-for-byte.  Stats aggregate at join.
#
# Rewrite: _mt_xform maps ("p",slot) operands of threaded routines to
# ("m","r10",off) — every routine keeps ONE source; the MT program is
# the same builders, post-passed.  Main thread gets ctx[T] so xform'd
# helpers (mkapp for the vocab) are valid pre-spawn too.

MT_CTX_FIELDS: Tuple[str, ...] = (
    "cellbase", "myend", "homeend",           # claimed span geometry
    "irj", "jend",                            # this worker's root chunk
    "irsteps", "nalloc",                      # per-thread stats
    "pcur", "pend",                           # persist zone (redirect)
    "irstart", "irroots",                     # depack products
    "outbuf", "outcur", "outlim",             # ordered frame buffer
    "eb_save", "eb_out", "eb_lim", "eb_dec",  # bytes-egress cursors
    "ei_tab", "ei_out", "ei_lim", "ei_idx",   # ir-egress state
    "ei_cells", "ei_outz",
)
MT_CTX: Dict[str, int] = {n: i * 8 for i, n in enumerate(MT_CTX_FIELDS)}
MT_CTX_BYTES = len(MT_CTX_FIELDS) * 8

# ("p",slot) -> ctx field, applied to thread-executed routines —
# covers every ctx field name so threaded builders stay slot-shaped.
_MT_REN: Dict[str, str] = {n: n for n in MT_CTX_FIELDS}
# depack is the one routine where "permend" means "my cells base", not
# the global immutable bound — same slot name, different semantics
_MT_DEPACK_REN = {"permend": "cellbase"}

# routines whose p-slots rewrite to ctx fields (the worker's world).
_MT_THREADED = frozenset({
    "ir_depack", "grow_heap_ir", "mkleaf", "mkapp", "mkapp_p", "repr",
    "step", "st_norm", "st_konst", "st_dup", "st_swap", "st_comp",
    "st_s", "step_congr", "count_nodes", "emit_nf", "itoa",
    "emit_bytes", "emit_ir", "peval", "selidx",
})


def _mt_xform(prog: Program, extra: Optional[Dict[str, str]] = None
              ) -> Program:
    """Rewrite ("p",slot) operands of a threaded routine to r10-ctx
    memory operands, and bracket every call_mrip (WinAPI clobbers r10)
    with a frame-local save/restore — the inserted 0x10 keeps rsp
    16-aligned at the call site."""
    ren = dict(_MT_REN)
    ren.update(extra or {})
    out: Program = []
    for ins in prog:
        if ins[0] != "i":
            out.append(ins)
            continue
        form, ops = ins[1], ins[2:]
        if form == "call_mrip":
            out += [
                I("sub_r64_imm", "rsp", 0x30),
                I("mov_m64_r64", ("m", "rsp", 0x20), "r10"),
                ins,
                I("mov_r64_m64", "r10", ("m", "rsp", 0x20)),
                I("add_r64_imm", "rsp", 0x30),
            ]
            continue
        # one p-operand at most per insn in these routines
        pi = [i for i, o in enumerate(ops)
              if isinstance(o, tuple) and o and o[0] == "p"
              and o[1] in ren]
        if not pi:
            out.append(ins)
            continue
        i = pi[0]
        off = MT_CTX[ren[ops[i][1]]]
        mem = ("m", "r10", off)
        if form == "mov_r64_rip":                       # load
            out.append(I("mov_r64_m64", ops[0], mem))
        elif form == "mov_rip_r64":                     # store
            out.append(I("mov_m64_r64", mem, ops[1]))
        elif form == "lea_r64_rip":                     # address-take
            out += [I("mov_r64_r64", ops[0], "r10"),
                    I("lea_r64_m64", ops[0], ("m", ops[0], off))]
        elif form == "inc_mrip":
            out.append(I("add_m64_imm", mem, 1))
        else:                                           # generic mem op
            ops2 = list(ops)
            ops2[i] = mem
            out.append(I(form, *ops2))
    return out


MT_HEADROOM = 32 << 20          # reduction space inside the first claim
EG_MT_OUT = 16 << 20            # per-thread ordered frame buffer


def data_slots_ir(R: Realization) -> tuple:
    """IR base slots + every selected leg's declared contribution,
    ordered by slot_rank (reclaim, container, threads, egress) —
    the .data layout is image contract, so it is declared, not
    derived from leg position."""
    return layers.compose_slots(R, _LEGS_IR, DATA_SLOTS_IR)

_BUILDERS: Dict[str, Callable[[Realization, Ctx], Program]] = {
    name[2:]: fn for name, fn in list(globals().items())
    if name.startswith("r_")
}


def _emit(R: Realization, names: Tuple[str, ...]) -> Program:
    ctx = _ctx()
    ctx["ir"] = any(n.startswith("ir_") for n in names)
    ctx["irnext"] = "ir_spawn" if R.threads > 1 else "ir_depack"
    p: Program = []
    for name in names:
        prog = _BUILDERS[name](R, ctx)
        if R.threads > 1 and name in _MT_THREADED:
            prog = _mt_xform(prog, _MT_DEPACK_REN if name == "ir_depack"
                             else None)
        p += prog
    return p


def program(R: Realization) -> Program:
    """Token-surface kernel: compose the record's legs — every axis
    with no row refuses at its leg (dialect/io/reclaim are legs now,
    not ad-hoc checks)."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    return _emit(R, layers.compose(R, _LEGS_TOKEN))


def routine_names_ir(R: Realization) -> Tuple[str, ...]:
    """the record's routine list for R — composed from _LEGS_IR:
    container leg picks the ingest front end (plex.v3 inserts
    plex_read after ir_entry), driver legs pick st/mt, egress leg
    picks io[1], fuse_s legs pick the basis tail.  Every axis value
    the family doesn't realize refuses at its leg, named."""
    return layers.compose(R, _LEGS_IR)


def program_ir(R: Realization) -> Program:
    """Packed-IR batch kernel: depack replaces the token parse; the
    reducer core is shared verbatim.  io=("stdin","bytes") swaps the
    per-root NF line for a decoded [u32le len][bytes] frame."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    if R.threads != 1:
        raise NotRealized(
            f"threads={R.threads} needs record x86_64.win64.ir.mt")
    return _emit(R, routine_names_ir(R))


def program_ir_mt(R: Realization) -> Program:
    """Multithreaded IR kernel — R.threads>1.  Same builder corpus; the
    per-thread world is _mt_xform'd to r10-relative ctx fields."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    if R.threads <= 1:
        raise NotRealized("mt record requires threads>1")
    if R.threads > 64:
        raise NotRealized("WaitForMultipleObjects caps at 64 handles")
    if R.audit:
        raise NotRealized("audit counters not realized under threads>1")
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


# Multithreaded variant (threads>1): T workers depack the shared
# stream into private claimed slabs — nothing shared-mutable exists,
# which is what redirect's FWD write-backs require.  Same reducer
# source; per-thread state is r10-ctx-rewritten.  Thread imports are
# the record's added capabilities.
X86_64_WIN64_IR_MT = Routines(
    name="x86_64.win64.ir.mt",
    isa="x86_64",
    abi="win64",
    orders=("lo",),
    routines=ROUTINES_IR_MT,
    program=program_ir_mt,
    imports=IMPORTS_IR_MT,
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
