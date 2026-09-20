"""
routines_x86_64_win64_xdu — nibble transducer PROGRAM (asm-as-data) for
ISA=x86_64, ABI=win64 (kernel32 IAT), path=native: the XDU table is
compiled to straight-line/jump code — program behaviour, NOT a reducer.

No Tag, no heap nodes, no β routine, no derived_s — this module imports
nothing from seed and reuses none of the runtime-path routines'
semantics.  It borrows only the ISA I/LBL/Program API and the target's
import/data-slot mechanism, driven by the same Realization fields it
needs: read_buf_bytes (input granule — the bytechunk rule's unit),
stack_reserve/io/abi (via the target pack).  State count is a
compile-time constant (finite transducers only — counting is uncovered).

Flow (all code runs at the _start rsp level; per-nibble dispatch is a
computed goto: r14 = continuation address, arms end `push r14; ret`):
  _start      handles, in-buf (read_buf_bytes), out-buf (OUT_BUF_BYTES),
              pend=-1, r13d=start state
  read_loop   ReadFile granule -> per byte: div 16 -> hi nibble then lo
              nibble, each `jmp dispatch` with r14=continuation
  dispatch    cmp r13d per state -> xst_<s>: cmp r15d per literal key ->
              xarm_<s>_<k>; "*" arm is the fallthrough
  xarm_*      emit items -> emit_nib (dl=nibble; "$in" = r15d, literals
              are immediates), then r13d=next, push r14;ret
  emit_nib    packs pairs: pend byte = nib<<4, else *cursor++ =
              pend|nib; buffer full -> flush_out
  xeof_dispatch per state: eof emits -> flush_out -> pend>=0 ? rc 3 :
              ExitProcess(halt)   (odd pending nibble dropped, rc 3 —
              the declared convention, same as the term-side output map)
Called routines (emit_nib, flush_out) follow the grow_heap discipline:
sub rsp,0x28 keeps every kernel32 call site at the same mod-16 offset as
the _start body.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
for _p in (_HOST,):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import isa_x86_64 as _isa                        # noqa: E402
from isa_x86_64 import I, LBL, Program, encode  # noqa: E402
from toolchain import NotRealized               # noqa: E402

IMPORTS: Tuple[str, ...] = (
    "GetStdHandle", "ReadFile", "WriteFile", "VirtualAlloc", "ExitProcess",
)

# .data slots (labels; 8 bytes each)
DATA_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("hin", 8), ("hout", 8), ("nread", 8), ("nw", 8),
    ("obase", 8), ("pend", 8),
)

VA_COMMIT_RESERVE = 0x3000
PAGE_RW = 4
OUT_BUF_BYTES = 64 << 10      # output granule — flush boundary, not a cap

Ctx = Dict[str, object]


def _ctx() -> Ctx:
    return {"iat": lambda n: ("p", f"iat_{n}")}


def _emit_call(p: Program, item: str) -> None:
    """One emit item: dl <- nibble, call emit_nib."""
    if item == "$in":
        p.append(I("mov_r64_r64", "rdx", "r15"))
    else:
        p.append(I("mov_r32_imm32", "edx", int(item, 16)))
    p.append(I("call_rel32", ("l", "emit_nib")))


def r_entry(xdu, idx: Dict[str, int], R, ctx: Ctx) -> Program:
    iat = ctx["iat"]
    return [
        LBL("_start"),
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_r32_imm32", "ecx", -10), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "hin"), "rax"),
        I("mov_r32_imm32", "ecx", -11), I("call_mrip", iat("GetStdHandle")),
        I("mov_rip_r64", ("p", "hout"), "rax"),
        # streaming read buffer (granule, not a cap)
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "edx", R.read_buf_bytes),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_r64_r64", "r12", "rax"),          # in buffer base
        # output buffer (fixed granule)
        I("xor_r32_r32", "ecx", "ecx"),
        I("mov_r32_imm32", "edx", OUT_BUF_BYTES),
        I("mov_r32_imm32", "r8d", VA_COMMIT_RESERVE),
        I("mov_r32_imm32", "r9d", PAGE_RW),
        I("call_mrip", iat("VirtualAlloc")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "exit4")),
        I("mov_rip_r64", ("p", "obase"), "rax"),
        I("mov_r64_r64", "rbx", "rax"),          # out cursor
        I("lea_r64_m64", "rbp", ("m", "rax", OUT_BUF_BYTES)),  # out end
        # ("p",...) resolves only in dedicated rip forms (rel fields) —
        # an imm-to-slot store goes through a register
        I("mov_r64_imm", "rax", -1),
        I("mov_rip_r64", ("p", "pend"), "rax"),  # no pending nibble
        I("mov_r32_imm32", "r13d", idx[xdu.start]),
    ]


def r_read(R, ctx: Ctx) -> Program:
    """read_loop / byte_loop: per byte, div 16 -> hi nibble (r15d) then lo
    nibble; each `jmp dispatch` carries its continuation in r14."""
    iat = ctx["iat"]
    return [
        LBL("read_loop"),
        I("mov_r64_rip", "rcx", ("p", "hin")),
        I("mov_r64_r64", "rdx", "r12"),
        I("mov_r32_imm32", "r8d", R.read_buf_bytes),
        I("lea_r64_rip", "r9", ("p", "nread")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("ReadFile")),
        # FALSE from an anonymous pipe = EOF, not an error
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "xeof_dispatch")),
        I("mov_r64_rip", "rax", ("p", "nread")),
        I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "xeof_dispatch")),
        I("mov_r64_r64", "rsi", "r12"),
        I("mov_r64_r64", "rdi", "r12"),
        I("add_r64_r64", "rdi", "rax"),
        LBL("byte_loop"),
        I("cmp_r64_r64", "rsi", "rdi"), I("jge_rel32", ("l", "read_loop")),
        I("movzx_r32_m8", "eax", ("m", "rsi", 0)),
        I("xor_r32_r32", "edx", "edx"),
        I("mov_r32_imm32", "r8d", 16),
        I("div_r64", "r8"),                      # rax=hi nibble, rdx=lo
        I("mov_r64_r64", "r15", "rax"),          # current nibble = hi
        I("lea_r64_rip", "r14", ("p", "after_hi")),
        I("jmp_rel32", ("l", "dispatch")),
        LBL("after_hi"),
        I("movzx_r32_m8", "eax", ("m", "rsi", 0)),
        I("and_r64_imm", "rax", 15),
        I("mov_r64_r64", "r15", "rax"),          # current nibble = lo
        I("lea_r64_rip", "r14", ("p", "byte_next")),
        I("jmp_rel32", ("l", "dispatch")),
        LBL("byte_next"),
        I("inc_r64", "rsi"),
        I("jmp_rel32", ("l", "byte_loop")),
    ]


def r_dispatch(xdu, idx: Dict[str, int], ctx: Ctx) -> Program:
    """dispatch: r13d = state index -> xst_<s>.  Per-state cmp/je chain on
    r15d for literal keys; '*' arm is the fallthrough.  The x*- prefixes
    keep program labels out of the reducer's label families (st_/en_/
    it_/p_/cn_/red_/mk*/grow_*) so the ISAR-free gate can forbid them
    wholesale."""
    p: Program = [LBL("dispatch")]
    for s, i in idx.items():
        p += [I("cmp_r64_imm", "r13", i), I("je_rel32", ("l", f"xst_{s}"))]
    return p


def r_state(xdu, s: str, idx: Dict[str, int], ctx: Ctx) -> Program:
    """xst_<s> + xarm_<s>_<key>: literal-key cmp chain, '*' fallthrough arm.
    Each arm emits then r13d=next, push r14;ret (continuation)."""
    on = xdu.states[s]["on"]
    p: Program = [LBL(f"xst_{s}")]
    for key, rule in on.items():
        if key == "*":
            continue
        p += [I("cmp_r64_imm", "r15", int(key, 16)),
              I("je_rel32", ("l", f"xarm_{s}_{key}"))]
    if "*" in on:
        p += [I("jmp_rel32", ("l", f"xarm_{s}_star"))]
    # no '*' and 16 literal keys: validated coverage, fall-through dead
    for key, rule in on.items():
        lbl = f"xarm_{s}_{key}" if key != "*" else f"xarm_{s}_star"
        p += [LBL(lbl)]
        for item in rule["emit"]:
            _emit_call(p, item)
        p += [
            I("mov_r32_imm32", "r13d", idx[rule["next"]]),
            I("push_r64", "r14"), I("ret"),
        ]
    return p


def r_eof_dispatch(xdu, idx: Dict[str, int], ctx: Ctx) -> Program:
    """xeof_dispatch: r13d -> xeof_<s>."""
    p: Program = [LBL("xeof_dispatch")]
    for s, i in idx.items():
        p += [I("cmp_r64_imm", "r13", i), I("je_rel32", ("l", f"xeof_{s}"))]
    return p


def r_eof_state(xdu, s: str, ctx: Ctx) -> Program:
    """xeof_<s>: final emits, flush, odd pending nibble -> rc 3, else
    ExitProcess(halt)."""
    iat = ctx["iat"]
    eof = xdu.states[s]["eof"]
    p: Program = [LBL(f"xeof_{s}")]
    for item in eof["emit"]:
        _emit_call(p, item)
    p += [
        I("call_rel32", ("l", "flush_out")),
        I("mov_r64_rip", "rax", ("p", "pend")),
        I("test_r64_r64", "rax", "rax"),
        I("jge_rel32", ("l", f"xeof_rc3_{s}")),
        I("mov_r32_imm32", "ecx", eof["halt"]),
        I("call_mrip", iat("ExitProcess")),
        LBL(f"xeof_rc3_{s}"),
        I("mov_r32_imm32", "ecx", 3),
        I("call_mrip", iat("ExitProcess")),
    ]
    return p


def r_emit_nib(ctx: Ctx) -> Program:
    """emit_nib: dl = nibble.  pend<0 -> pend = nib<<4; else *cursor++ =
    pend|nib, pend=-1, flush on full buffer."""
    return [
        LBL("emit_nib"),
        I("mov_r64_rip", "rax", ("p", "pend")),
        I("test_r64_r64", "rax", "rax"),
        I("jge_rel32", ("l", "xn_pack")),
        I("mov_r64_r64", "rax", "rdx"),
        I("shl_r64_imm8", "rax", 4),
        I("mov_rip_r64", ("p", "pend"), "rax"),
        I("ret"),
        LBL("xn_pack"),
        I("add_r64_r64", "rax", "rdx"),          # pend(hi) | nib(lo)
        I("mov_m8_r8", ("m", "rbx", 0), "al"),
        I("inc_r64", "rbx"),
        I("mov_r64_imm", "rax", -1),             # pend = -1 (rip-slot store
        I("mov_rip_r64", ("p", "pend"), "rax"),  # needs a register)
        I("cmp_r64_r64", "rbx", "rbp"),
        I("jb_rel32", ("l", "xn_done")),
        # keep the call-site mod-16 convention: emit_nib is entered one
        # call-level deep, so pad before the nested call (mkleaf->grow_heap
        # discipline in the runtime-path routines)
        I("sub_r64_imm", "rsp", 0x28),
        I("call_rel32", ("l", "flush_out")),
        I("add_r64_imm", "rsp", 0x28),
        LBL("xn_done"), I("ret"),
    ]


def r_flush(ctx: Ctx) -> Program:
    """flush_out: WriteFile(hout, obase, cursor-obase); reset cursor."""
    iat = ctx["iat"]
    return [
        LBL("flush_out"),
        I("sub_r64_imm", "rsp", 0x28),
        I("mov_r64_rip", "rcx", ("p", "hout")),
        I("mov_r64_rip", "rdx", ("p", "obase")),
        I("mov_r64_r64", "r8", "rbx"),
        I("sub_r64_r64", "r8", "rdx"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        I("mov_r64_rip", "rbx", ("p", "obase")),
        I("add_r64_imm", "rsp", 0x28),
        I("ret"),
    ]


def r_exits(ctx: Ctx) -> Program:
    """exit4: allocation failure."""
    iat = ctx["iat"]
    return [
        LBL("exit4"), I("mov_r32_imm32", "ecx", 4),
        I("call_mrip", iat("ExitProcess")),
    ]


def program(xdu, R) -> Program:
    """XDU + Realization -> asm-as-data Program.  `xdu` is the loaded
    dialect record (native path: the program is the input, not a term)."""
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    if xdu is None:
        raise ValueError("native path: program(xdu, R) needs an XDU record")
    ctx = _ctx()
    states = list(xdu.states)
    idx = {s: i for i, s in enumerate(states)}
    p: Program = []
    p += r_entry(xdu, idx, R, ctx)
    p += r_read(R, ctx)
    p += r_dispatch(xdu, idx, ctx)
    for s in states:
        p += r_state(xdu, s, idx, ctx)
    p += r_eof_dispatch(xdu, idx, ctx)
    for s in states:
        p += r_eof_state(xdu, s, ctx)
    p += r_emit_nib(ctx)
    p += r_flush(ctx)
    p += r_exits(ctx)
    return p


@dataclass(frozen=True)
class Routines:
    name: str          # "x86_64.win64.xdu"
    isa: str           # "x86_64"
    abi: str           # "win64"
    orders: tuple      # ("lo",)  — order-free path, keeps the refusal shape
    routines: tuple    # builder names
    program: Callable  # program(xdu, R) -> Program
    imports: tuple
    data_slots: tuple


_ROUTINE_NAMES: Tuple[str, ...] = (
    "entry", "read", "dispatch", "state", "eof_dispatch", "eof_state",
    "emit_nib", "flush", "exits",
)

X86_64_WIN64_XDU = Routines(
    name="x86_64.win64.xdu",
    isa="x86_64",
    abi="win64",
    orders=("lo",),
    routines=_ROUTINE_NAMES,
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


def main() -> int:
    _seed = os.path.normpath(os.path.join(_HOST, "..", "seed"))
    if _seed not in sys.path:
        sys.path.insert(0, _seed)
    import xdu_dialect as xd
    ok = True
    for probe in ("echo", "hexdump", "drop0", "toggle"):
        xdu = xd.load(xd.probe_path(probe))
        for tag, R in (("default", None),):
            from seed import Realization
            Rv = Realization()
            prog = program(xdu, Rv)
            text, labels = _isa.assemble(prog, _dummy_symbols())
            forbidden = {"step", "mkleaf", "mkapp", "build_ds", "count_nodes",
                         "emit_nf", "grow_heap", "mkstk", "do_reduce",
                         "red_loop", "parse_bytes", "itoa"}
            bad = forbidden & set(labels)
            good = not bad
            print(f"  {probe}: {len(text)}B text, "
                  f"{sum(1 for i in prog if i[0] == 'label')} labels, "
                  f"forbidden={sorted(bad) if bad else 'none'}")
            ok = ok and good
    print(f"{'OK' if ok else 'FAIL'} routines_x86_64_win64_xdu")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
