"""
SEED — native x86-64 realization of the Lean `step?` kernel as a real PE.

Invariant : IStep = Lean `step?` (normβ, konstβ, compβ, sβ + appL/appR,
            leftmost-outermost).  The Python mirror in §1 is a reference
            transcription of `src/ISAR/Reduce.lean` / `host/reduce.py`.
Strategy  : `Realization` (§2) — a frozen data record: evaluation order,
            node layout, allocation discipline, fuel policy, stack reserve,
            ABI.  `order="cd"` is a declared parameter value but is
            *refused* (NotRealized) — mine_adopt semantics, never a fallback.
Data      : the ISA table (§3), the reducer program as asm-data (§5),
            the PE layout table (§6), the import table (§6).
Mechanism : encode() (ISA-intrinsic), assemble() (two-pass fixups),
            build_pe() (header construction).
Oracles   : fasmg.exe (byte equality, env ISAR_FASMG), host reduce.py and
            graph.lo piece (NF equality) — imported lazily in §7/§8 only.

Gates: G1 encoder vs fasmg | G2 kernel vs host reduce | G3 native exe
end-to-end | G4 strategy variations + cd refusal + fuel | G5 host
registration (cogen.choose -> cpu, native_realize, piece adoption).

Hard rules: no fixed heap (chunked VirtualAlloc growth), fuel optional
(default off — run to NF), cd refused, no cross-repo *code* (oracle
binaries and host oracle modules only), §1–§6 import nothing from host.

Note: B has a step rule (compβ) for step? fidelity but no input token —
unreachable from BytecodeView by construction; a B-containing NF cannot
arise from the {I,K,S,@} input alphabet.
"""
from __future__ import annotations

import os
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass, fields
from enum import IntEnum
from typing import Dict, List, Optional, Sequence, Tuple, Union

SEED_DIR = os.path.dirname(os.path.abspath(__file__))
BUILD_DIR = os.path.join(SEED_DIR, "build")

DEFAULT_FASMG = os.path.normpath(os.path.join(
    SEED_DIR, "..", "..", "isa-physics", "boostrap", "fasmg", "fasmg.exe"))
FASMG = os.environ.get("ISAR_FASMG", DEFAULT_FASMG)
FASMG_INC = os.path.join(os.path.dirname(FASMG), "examples", "x86", "include")


class NotRealized(Exception):
    """Declared-but-unrealized strategy value (refusal, never fallback)."""


# ======================================================================
# §1  KERNEL MIRROR (reference, Python) — self-contained
# ======================================================================

class Tag(IntEnum):
    APP = 0
    I = 1
    K = 2
    S = 3
    B = 4   # no input token; compβ unreachable from BytecodeView


class T:
    __slots__ = ("tag", "l", "r")

    def __init__(self, tag: int, l: "Optional[T]" = None, r: "Optional[T]" = None):
        self.tag = tag
        self.l = l
        self.r = r

    def __eq__(self, o) -> bool:
        return (isinstance(o, T) and self.tag == o.tag
                and self.l == o.l and self.r == o.r)

    def __repr__(self) -> str:
        if self.tag == Tag.APP:
            return f"({self.l} {self.r})"
        return {Tag.I: "I", Tag.K: "K", Tag.S: "S", Tag.B: "B"}[Tag(self.tag)]

    def __hash__(self):
        return hash((self.tag, id(self.l), id(self.r)))


TI = T(Tag.I)
TK = T(Tag.K)
TS = T(Tag.S)


def app(f: T, x: T) -> T:
    return T(Tag.APP, f, x)


# Pattern table as documentation-as-data (Lean IStep rule order).
RULES = (
    ("normβ",  "I x        -> x"),
    ("konstβ", "K a b      -> a"),
    ("compβ",  "B f g x    -> f (g x)"),
    ("sβ",     "S f g x    -> (f x)(g x)"),
)


def step(t: T) -> Optional[T]:
    """LO single step = Lean `step?` (normβ, konstβ, compβ, sβ, appL, appR)."""
    if t.tag != Tag.APP:
        return None
    f, x = t.l, t.r
    if f.tag == Tag.I:                      # normβ: I x -> x
        return x
    if f.tag == Tag.APP:
        fl, fr = f.l, f.r
        if fl.tag == Tag.K:                 # konstβ: K a b -> a
            return fr
        if fl.tag == Tag.APP:
            fll, flr = fl.l, fl.r
            if fll.tag == Tag.B:            # compβ: B f g x -> f (g x)
                return app(flr, app(fr, x))
            if fll.tag == Tag.S:            # sβ: S f g x -> (f x)(g x)
                return app(app(flr, x), app(fr, x))
    sf = step(f)                            # appL
    if sf is not None:
        return app(sf, x)
    sx = step(x)                            # appR
    if sx is not None:
        return app(f, sx)
    return None


def reduce(t: T, fuel: Optional[int] = None) -> Tuple[T, int]:
    """Iterate LO step until NF (fuel=None) or exhaustion."""
    cur, n = t, 0
    while fuel is None or n < fuel:
        nxt = step(cur)
        if nxt is None:
            break
        cur = nxt
        n += 1
    return cur, n


def bc_compile(tokens: str) -> T:
    """Lean BytecodeView.run incl. underflow rules, then head of stack."""
    st: List[T] = []
    for ch in tokens:
        if ch == "I":
            st.insert(0, TI)
        elif ch == "K":
            st.insert(0, TK)
        elif ch == "S":
            st.insert(0, TS)
        elif ch == "@":
            if len(st) >= 2:
                x, y = st[0], st[1]
                st = [app(y, x)] + st[2:]
            elif len(st) == 1:
                st = [TI, st[0]]
            else:
                st = [TI]
        elif ch in " \t\r\n,":
            continue
        else:
            raise ValueError(f"bad input byte: {ch!r}")
    return st[0] if st else TI


def bc_decompile(t: T) -> str:
    """Postfix single-char tokens 'I','K','S','@' + '\\n'; raises on B."""
    if t.tag == Tag.I:
        return "I"
    if t.tag == Tag.K:
        return "K"
    if t.tag == Tag.S:
        return "S"
    if t.tag == Tag.APP:
        return bc_decompile(t.l) + bc_decompile(t.r) + "@"
    raise ValueError(f"decompile: unexpected tag {t.tag}")


def t_to_host(t: T, H):
    """Convert seed T -> host reduce.T (H = host reduce module)."""
    if t.tag == Tag.I:
        return H.I
    if t.tag == Tag.K:
        return H.KK
    if t.tag == Tag.S:
        return H.S
    if t.tag == Tag.APP:
        return H.app(t_to_host(t.l, H), t_to_host(t.r, H))
    raise ValueError("B has no host surface token")


def t_from_host(h) -> T:
    """Convert host reduce.T -> seed T."""
    from_host = {
        "NORM": Tag.I, "KONST": Tag.K, "S": Tag.S, "COMP": Tag.B,
    }
    if h.k.name == "APP":
        return app(t_from_host(h.l), t_from_host(h.r))
    return T(from_host[h.k.name])


# ======================================================================
# §2  REALIZATION (strategy as data)
# ======================================================================

@dataclass(frozen=True)
class Realization:
    order: str = "lo"                 # "lo" realized | "cd" declared, REFUSED
    node_bytes: int = 24              # {tag:u64 @0, l:ptr @8, r:ptr @16}
    alloc: str = "bump-chunked"       # VirtualAlloc(chunk) on exhaustion
    chunk_bytes: int = 1 << 20
    fuel: Optional[int] = None        # None = run to NF; int = exit 2 on exhaustion
    stack_reserve: int = 64 << 20     # PE SizeOfStackReserve
    read_buf_bytes: int = 64 << 10    # read granule, NOT a cap: input streams
                                    # through one buffer of this size, parsed
                                    # chunk-by-chunk; total input is unbounded
    io: tuple = ("stdin", "stdout")
    abi: str = "win64"
    reclaim: str = "none"             # GC slot — explicitly none this wave


DEFAULT = Realization()


# ======================================================================
# §3  ISA DATA (x86-64, authored from ISA; each row oracle-checked)
# ======================================================================

REG64: Dict[str, int] = {
    "rax": 0, "rcx": 1, "rdx": 2, "rbx": 3, "rsp": 4, "rbp": 5, "rsi": 6,
    "rdi": 7, "r8": 8, "r9": 9, "r10": 10, "r11": 11, "r12": 12, "r13": 13,
    "r14": 14, "r15": 15,
}
REG32: Dict[str, int] = {"eax": 0, "ecx": 1, "edx": 2, "ebx": 3, "esp": 4,
                         "ebp": 5, "esi": 6, "edi": 7}
REG32.update({f"r{i}d": i for i in range(8, 16)})
REG8: Dict[str, int] = {"al": 0, "cl": 1, "dl": 2, "bl": 3, "spl": 4, "bpl": 5,
                        "sil": 6, "dil": 7}
REG8.update({f"r{i}b": i for i in range(8, 16)})

# INSN rows: (form, mnemonic, opcode, rex_w, modrm_reg_ext|'+'=opcode+rd, imm_kind)
# imm_kind: 0 none | io imm64 | i4 imm32 | i1r imm8 after reg-modrm
#           | i1m/i4m imm after mem-modrm | g grp1 (83/81/acc sel) | gm grp1 mem
#           | l rel32 label | p rip-rel32
INSN: Tuple[Tuple[str, str, int, int, object, object], ...] = (
    ("mov_r64_imm",   "mov",   0xB8,   1, "+",   "io"),
    ("mov_r64_r64",   "mov",   0x89,   1, None,  0),
    ("mov_r64_m64",   "mov",   0x8B,   1, None,  0),
    ("mov_m64_r64",   "mov",   0x89,   1, None,  0),
    ("mov_r64_rip",   "mov",   0x8B,   1, None,  "p"),
    ("mov_rip_r64",   "mov",   0x89,   1, None,  "p"),
    ("movzx_r32_m8",  "movzx", 0x0FB6, 0, None,  0),
    ("mov_r8_m8",     "mov",   0x8A,   0, None,  0),
    ("mov_m8_r8",     "mov",   0x88,   0, None,  0),
    ("mov_m8_imm8",   "mov",   0xC6,   0, 0,     "i1m"),
    ("mov_m64_imm32", "mov",   0xC7,   1, 0,     "i4m"),
    ("mov_r32_imm32", "mov",   0xB8,   0, "+",   "i4"),
    ("lea_r64_m64",   "lea",   0x8D,   1, None,  0),
    ("lea_r64_rip",   "lea",   0x8D,   1, None,  "p"),
    ("add_r64_imm",   "add",   0x81,   1, 0,     "g"),
    ("and_r64_imm",   "and",   0x81,   1, 4,     "g"),
    ("sub_r64_imm",   "sub",   0x81,   1, 5,     "g"),
    ("cmp_r64_imm",   "cmp",   0x81,   1, 7,     "g"),
    ("cmp_m64_imm",   "cmp",   0x81,   1, 7,     "gm"),
    ("add_r64_r64",   "add",   0x01,   1, None,  0),
    ("sub_r64_r64",   "sub",   0x29,   1, None,  0),
    ("cmp_r64_r64",   "cmp",   0x39,   1, None,  0),
    ("test_r64_r64",  "test",  0x85,   1, None,  0),
    ("xor_r32_r32",   "xor",   0x31,   0, None,  0),
    ("add_r8_imm8",   "add",   0x80,   0, 0,     "i1r"),
    ("shl_r64_imm8",  "shl",   0xC1,   1, 4,     "i1r"),
    ("push_r64",      "push",  0x50,   0, "+",   0),
    ("pop_r64",       "pop",   0x58,   0, "+",   0),
    ("call_rel32",    "call",  0xE8,   0, None,  "l"),
    ("call_mrip",     "call",  0xFF,   0, 2,     "p"),
    ("jmp_rel32",     "jmp",   0xE9,   0, None,  "l"),
    ("je_rel32",      "je",    0x0F84, 0, None,  "l"),
    ("jne_rel32",     "jne",   0x0F85, 0, None,  "l"),
    ("jl_rel32",      "jl",    0x0F8C, 0, None,  "l"),
    ("jge_rel32",     "jge",   0x0F8D, 0, None,  "l"),
    ("jb_rel32",      "jb",    0x0F82, 0, None,  "l"),
    ("jbe_rel32",     "jbe",   0x0F86, 0, None,  "l"),
    ("ret",           "ret",   0xC3,   0, None,  0),
    ("inc_r64",       "inc",   0xFF,   1, 0,     0),
    ("dec_r64",       "dec",   0xFF,   1, 1,     0),
    ("inc_mrip",      "inc",   0xFF,   1, 0,     "p"),
    ("div_r64",       "div",   0xF7,   1, 6,     0),
)
FORMS: Dict[str, Tuple[str, int, int, object, object]] = {r[0]: r[1:] for r in INSN}

_ACC_OP = {"add": 0x05, "and": 0x25, "sub": 0x2D, "cmp": 0x3D}


def _opbytes(op: int) -> bytes:
    if op > 0xFFFF:
        return bytes(((op >> 16) & 0xFF, (op >> 8) & 0xFF, op & 0xFF))
    if op > 0xFF:
        return bytes(((op >> 8) & 0xFF, op & 0xFF))
    return bytes((op,))


def _i8s(v: int) -> bool:
    return -128 <= v <= 127


def _i32s(v: int) -> bool:
    return -(1 << 31) <= v <= (1 << 31) - 1


def _mem_modrm(reg_field: int, memop) -> Tuple[int, bytes, bytes]:
    """Return (rex_b, modrm+sib, disp) for ('m', base, disp) or ('p', disp/label)."""
    kind = memop[0]
    if kind == "p":
        return 0, bytes((((reg_field & 7) << 3) | 5,)), b"\x00\x00\x00\x00"
    _, base, disp = memop
    b = REG64[base]
    lo = b & 7
    if disp == 0 and lo != 5:
        mod = 0
        db = b""
    elif _i8s(disp):
        mod = 1
        db = struct.pack("<b", disp)
    else:
        mod = 2
        db = struct.pack("<i", disp)
    if lo == 4:
        rm, sib = 4, bytes((4 << 3 | lo,))        # index=100 none
    else:
        rm, sib = lo, b""
    return b >> 3, bytes((mod << 6 | (reg_field & 7) << 3 | rm,)) + sib, db


def _reg_code(name: str) -> int:
    if name in REG64:
        return REG64[name]
    if name in REG32:
        return REG32[name]
    if name in REG8:
        return REG8[name]
    raise ValueError(f"bad register {name}")


# Insn datum: (form, *operands).  Label operand: ("l", name|disp).
# Rip operand: ("p", name|disp).  Mem operand: ("m", base_reg, disp).
Insn = Tuple


def _rexb(v: int) -> bytes:
    """Emit a REX prefix only when needed (W set, or any ext bit)."""
    return bytes((v,)) if v != 0x40 else b""


def encode(insn: Insn, resolve=None) -> bytes:
    """ISA-intrinsic encoding: REX/ModRM/SIB/disp/imm assembly."""
    form, ops = insn[0], insn[1:]
    mnem, op, w, ext, immk = FORMS[form]
    rex = 0x40 | (0x08 if w else 0)
    opcode = _opbytes(op)

    def rel(opnd) -> bytes:
        if isinstance(opnd[1], int):
            return struct.pack("<i", opnd[1])
        if resolve is None:
            return b"\x00\x00\x00\x00"
        return struct.pack("<i", resolve(opnd[1]))

    if immk == "l":                                 # call/jmp/jcc rel32
        return opcode + rel(ops[0])

    if form in ("call_mrip", "inc_mrip"):
        rex_b, modrm, _ = _mem_modrm(ext, ops[0])
        return _rexb(rex | rex_b) + opcode + modrm + rel(ops[0])

    if immk == "p":                                 # rip mem forms
        if form in ("mov_r64_rip", "lea_r64_rip"):
            regf, memop = _reg_code(ops[0]), ops[1]
        else:                                       # mov_rip_r64
            regf, memop = _reg_code(ops[1]), ops[0]
        rex_b, modrm, _ = _mem_modrm(regf, memop)
        return _rexb(rex | (regf >> 3) << 2 | rex_b) + opcode + modrm + rel(memop)

    if ext == "+":                                  # push/pop/mov imm (+rd)
        rd = _reg_code(ops[0])
        if form == "mov_r64_imm":
            v = ops[1]
            if _i32s(v):
                return bytes((rex | (rd >> 3),)) + b"\xC7" \
                    + bytes((0xC0 | (rd & 7),)) + struct.pack("<i", v)
            return bytes((rex | (rd >> 3),)) + bytes((0xB8 + (rd & 7),)) \
                + struct.pack("<q", v)
        if immk == "i4":                            # mov r32,imm32
            return _rexb(0x40 | (rd >> 3)) + bytes((op + (rd & 7),)) \
                + struct.pack("<i", ops[1])
        return _rexb(0x40 | (rd >> 3)) + bytes((op + (rd & 7),))

    if immk in ("g", "gm"):                         # grp1 r64/mem, imm
        dst, v = ops
        ib = _i8s(v)
        opb = 0x83 if ib else op
        imm = struct.pack("<b" if ib else "<i", v)
        if immk == "gm":
            rex_b, modrm, disp = _mem_modrm(ext, dst)
            return _rexb(rex | rex_b) + bytes((opb,)) + modrm + disp + imm
        rd = _reg_code(dst)
        if not ib and rd == 0:                      # accumulator special
            return bytes((rex,)) + bytes((_ACC_OP[mnem],)) + struct.pack("<i", v)
        modrm = bytes((0xC0 | (ext << 3) | (rd & 7),))
        return bytes((rex | (rd >> 3),)) + bytes((opb,)) + modrm + imm

    if immk == "i1r":                               # shl r64 / add r8, imm8
        dst, v = ops
        rd = _reg_code(dst)
        modrm = bytes((0xC0 | (ext << 3) | (rd & 7),))
        if form == "add_r8_imm8":
            return _rexb(0x40 | (rd >> 3) | (1 if rd >= 4 else 0)) \
                + opcode + modrm + struct.pack("<b", v)
        return bytes((rex | (rd >> 3),)) + opcode + modrm + struct.pack("<b", v)

    if immk in ("i1m", "i4m"):                      # mov m,imm
        memop, v = ops
        rex_b, modrm, disp = _mem_modrm(ext, memop)
        imm = struct.pack("<b" if immk == "i1m" else "<i", v)
        return _rexb(rex | rex_b) + opcode + modrm + disp + imm

    if ext is not None:                             # inc/dec/div reg, mod=11
        rd = _reg_code(ops[0])
        modrm = bytes((0xC0 | (ext << 3) | (rd & 7),))
        return bytes((rex | (rd >> 3),)) + opcode + modrm

    if len(ops) == 2 and isinstance(ops[0], str) and isinstance(ops[1], str):
        dst, src = _reg_code(ops[0]), _reg_code(ops[1])
        modrm = bytes((0xC0 | (src & 7) << 3 | (dst & 7),))
        return _rexb(rex | (src >> 3) << 2 | (dst >> 3)) + opcode + modrm

    if len(ops) == 2:                               # reg<->mem
        if isinstance(ops[0], str):                 # reg, mem
            regf, memop = _reg_code(ops[0]), ops[1]
        else:                                       # mem, reg
            memop, regf = ops[0], _reg_code(ops[1])
        rex_b, modrm, disp = _mem_modrm(regf, memop)
        need = w or (regf >> 3) or rex_b or _reg8_ext(ops[0]) or _reg8_ext(ops[1])
        return _rexb(rex | (regf >> 3) << 2 | rex_b) + opcode + modrm + disp \
            if need else opcode + modrm + disp

    return opcode                                   # ret


def _reg8_ext(o) -> bool:
    return isinstance(o, str) and o in REG8 and REG8[o] >= 4


def render_fasm(insn: Insn, resolve=None) -> str:
    """Mnemonic text for the oracle (one line, 'near' forced on branches)."""
    form, ops = insn[0], insn[1:]
    mnem = FORMS[form][0]

    def mem(m) -> str:
        if m[0] == "p":
            d = m[1] if isinstance(m[1], int) else (resolve(m[1]) if resolve else 0)
            return f"[rip{'+' if d >= 0 else ''}{d}]"
        _, base, d = m
        if d == 0:
            return f"[{base}]"
        return f"[{base}{'+' if d > 0 else ''}{d}]"

    if FORMS[form][4] == "l":
        return f"{mnem} near {ops[0][1]}"
    if form in ("call_mrip", "inc_mrip"):
        m = ops[0]
        d = m[1] if isinstance(m[1], int) else (resolve(m[1]) if resolve else 0)
        sz = "qword "
        return f"{mnem} {sz}[rip{'+' if d >= 0 else ''}{d}]"
    if form in ("mov_r64_rip", "lea_r64_rip"):
        return f"{mnem} {ops[0]}, {mem(ops[1])}"
    if form == "mov_rip_r64":
        return f"mov {mem(ops[0])}, {ops[1]}"
    if form == "mov_r64_imm":
        return f"mov {ops[0]}, {ops[1]}"
    if form == "mov_r32_imm32":
        return f"mov {ops[0]}, {ops[1]}"
    if form == "movzx_r32_m8":
        return f"movzx {ops[0]}, byte {mem(ops[1])}"
    if form == "mov_r8_m8":
        return f"mov {ops[0]}, byte {mem(ops[1])}"
    if form == "mov_m8_r8":
        return f"mov byte {mem(ops[0])}, {ops[1]}"
    if form == "mov_m8_imm8":
        return f"mov byte {mem(ops[0])}, {ops[1]}"
    if form == "mov_m64_imm32":
        return f"mov qword {mem(ops[0])}, {ops[1]}"
    if form in ("mov_r64_m64", "lea_r64_m64"):
        return f"{mnem} {ops[0]}, {mem(ops[1])}"
    if form in ("mov_m64_r64",):
        return f"mov {mem(ops[0])}, {ops[1]}"
    if form == "cmp_m64_imm":
        return f"cmp qword {mem(ops[0])}, {ops[1]}"
    if form == "add_r8_imm8":
        return f"add {ops[0]}, {ops[1]}"
    if len(ops) == 0:
        return mnem
    if len(ops) == 1:
        return f"{mnem} {ops[0]}"
    return f"{mnem} {ops[0]}, {ops[1]}"


# ======================================================================
# §4  ASSEMBLER (two-pass, labels)
# ======================================================================

Program = List[Tuple]


def LBL(name: str) -> Tuple:
    return ("label", name)


def I(form: str, *ops) -> Tuple:
    return ("i", form, *ops)


def assemble(program: Program, symbols: Dict[str, int]) -> Tuple[bytes, Dict[str, int]]:
    """Two-pass assembly; labels + rip/rel32 fixups to `symbols` + local labels."""
    local: Dict[str, int] = {}
    offs: List[int] = []
    pos = 0
    for item in program:
        if item[0] == "label":
            local[item[1]] = pos
            offs.append(pos)
        else:
            offs.append(pos)
            pos += len(encode(item[1:]))
    out = bytearray()
    for item, off in zip(program, offs):
        if item[0] == "label":
            continue
        insn = item[1:]
        end = off + len(encode(insn))
        resolver = lambda name, _e=end: (
            symbols[name] if name in symbols else local[name]) - _e
        out += encode(insn, resolve=resolver)
    return bytes(out), local


# ======================================================================
# §5  REDUCER PROGRAM (asm-as-data, built from Realization)
# ======================================================================

IMPORTS: Tuple[str, ...] = (
    "GetStdHandle", "ReadFile", "WriteFile", "VirtualAlloc", "ExitProcess",
)

# .data slots (labels; 8 bytes each unless noted)
DATA_SLOTS: Tuple[Tuple[str, int], ...] = (
    ("hin", 8), ("hout", 8), ("herr", 8), ("nread", 8), ("nw", 8),
    ("nalloc", 8), ("scratch", 64),
)

VA_COMMIT_RESERVE = 0x3000
PAGE_RW = 4
STK_TAG = 5   # native-internal parse-stack cons cell tag (never a term node);
              # excluded from nalloc so `alloc=` counts term nodes only


def reducer_program(R: Realization) -> Program:
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    iat = lambda n: ("p", f"iat_{n}")
    p: Program = []

    def stats_str(s: str) -> None:
        for ch in s:
            p.append(I("mov_m8_imm8", ("m", "rsi", 0), ord(ch)))
            p.append(I("inc_r64", "rsi"))

    p += [
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
        I("cmp_r64_imm", "rax", 0x40), I("je_rel32", ("l", "p_app")),
        I("cmp_r64_imm", "rax", 0x20), I("je_rel32", ("l", "p_next")),
        I("cmp_r64_imm", "rax", 0x09), I("je_rel32", ("l", "p_next")),
        I("cmp_r64_imm", "rax", 0x0A), I("je_rel32", ("l", "p_next")),
        I("cmp_r64_imm", "rax", 0x0D), I("je_rel32", ("l", "p_next")),
        I("jmp_rel32", ("l", "exit3")),
        LBL("p_i"), I("mov_r32_imm32", "edx", Tag.I),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        LBL("p_k"), I("mov_r32_imm32", "edx", Tag.K),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
        LBL("p_s"), I("mov_r32_imm32", "edx", Tag.S),
        I("call_rel32", ("l", "mkleaf")), I("jmp_rel32", ("l", "p_push")),
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
        I("mov_r32_imm32", "edx", Tag.I),
        I("call_rel32", ("l", "mkleaf")),
        I("push_r64", "rdi"), I("sub_r64_imm", "rsp", 8),
        I("mov_r64_r64", "rdi", "rax"), I("call_rel32", ("l", "mkstk")),
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rdi"),
        LBL("p_next"), I("inc_r64", "rsi"), I("jmp_rel32", ("l", "parse_bytes")),
        LBL("parse_done"),
        I("test_r64_r64", "r14", "r14"), I("je_rel32", ("l", "empty")),
        I("mov_r64_m64", "r12", ("m", "r14", 8)),
        I("jmp_rel32", ("l", "do_reduce")),
        LBL("empty"), I("mov_r32_imm32", "edx", Tag.I),
        I("call_rel32", ("l", "mkleaf")), I("mov_r64_r64", "r12", "rax"),
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
    # ---- stats: "steps=N alloc=M\n" to stderr ----
    p += [
        I("lea_r64_rip", "rsi", ("p", "scratch")),
    ]
    stats_str("steps=")
    p += [
        I("mov_r64_r64", "rdi", "r15"), I("call_rel32", ("l", "itoa")),
    ]
    stats_str(" alloc=")
    p += [
        I("mov_r64_rip", "rdi", ("p", "nalloc")), I("call_rel32", ("l", "itoa")),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x0A), I("inc_r64", "rsi"),
        I("mov_r64_rip", "rcx", ("p", "herr")),
        I("lea_r64_rip", "rdx", ("p", "scratch")),
        I("mov_r64_r64", "r8", "rsi"), I("sub_r64_r64", "r8", "rdx"),
        I("lea_r64_rip", "r9", ("p", "nw")),
        I("mov_m64_imm32", ("m", "rsp", 0x20), 0),
        I("call_mrip", iat("WriteFile")),
        # ---- exit ----
        I("xor_r32_r32", "ecx", "ecx"), I("call_mrip", iat("ExitProcess")),
        LBL("exit2"), I("mov_r32_imm32", "ecx", 2), I("call_mrip", iat("ExitProcess")),
        LBL("exit3"), I("mov_r32_imm32", "ecx", 3), I("call_mrip", iat("ExitProcess")),
        LBL("exit4"), I("mov_r32_imm32", "ecx", 4), I("call_mrip", iat("ExitProcess")),
        # ---- grow_heap: rbx=bump, rbp=chunk end (chunked VirtualAlloc) ----
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
        # ---- mkleaf: rdx=tag -> rax node ----
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
        # ---- mkapp: rdi=f, rsi=x -> rax node ----
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
        # ---- mkstk: rdi=value -> rax cons cell, r14=new stack top ----
        # parse-stack cells share the dynamic heap; NOT counted in nalloc
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
        # ---- step(rdi=t) -> rax : LO single step, Lean order ----
        LBL("step"),
        I("push_r64", "r12"), I("push_r64", "r13"), I("push_r64", "r14"),
        I("mov_r64_r64", "r12", "rdi"),
        I("cmp_m64_imm", ("m", "r12", 0), Tag.APP),
        I("jne_rel32", ("l", "st_none")),
        I("mov_r64_m64", "r13", ("m", "r12", 8)),    # f
        I("mov_r64_m64", "r14", ("m", "r12", 16)),   # x
        I("cmp_m64_imm", ("m", "r13", 0), Tag.I),
        I("je_rel32", ("l", "st_norm")),
        I("cmp_m64_imm", ("m", "r13", 0), Tag.APP),
        I("jne_rel32", ("l", "st_left")),
        I("mov_r64_m64", "rax", ("m", "r13", 8)),    # fl
        I("mov_r64_m64", "rcx", ("m", "r13", 16)),   # fr
        I("cmp_m64_imm", ("m", "rax", 0), Tag.K),
        I("je_rel32", ("l", "st_konst")),
        I("cmp_m64_imm", ("m", "rax", 0), Tag.APP),
        I("jne_rel32", ("l", "st_left")),
        I("mov_r64_m64", "rdx", ("m", "rax", 8)),    # fll
        I("mov_r64_m64", "rsi", ("m", "rax", 16)),   # flr
        I("cmp_m64_imm", ("m", "rdx", 0), Tag.B),
        I("je_rel32", ("l", "st_comp")),
        I("cmp_m64_imm", ("m", "rdx", 0), Tag.S),
        I("je_rel32", ("l", "st_s")),
        I("jmp_rel32", ("l", "st_left")),
        LBL("st_norm"), I("mov_r64_r64", "rax", "r14"),
        I("jmp_rel32", ("l", "st_out")),
        LBL("st_konst"), I("mov_r64_r64", "rax", "rcx"),
        I("jmp_rel32", ("l", "st_out")),
        LBL("st_comp"),                                # B f g x -> f (g x)
        I("push_r64", "rcx"), I("push_r64", "rsi"),
        I("mov_r64_r64", "rdi", "rcx"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (g x)
        I("pop_r64", "rdi"), I("pop_r64", "rdx"),      # rdi = flr
        I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")),               # rax = f (g x)
        I("jmp_rel32", ("l", "st_out")),
        LBL("st_s"),                                   # S f g x -> (f x)(g x)
        I("push_r64", "rcx"), I("push_r64", "rsi"),    # [rsp]=flr,[rsp+8]=fr
        I("mov_r64_r64", "rdi", "rsi"), I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (f x)
        I("push_r64", "rax"), I("sub_r64_imm", "rsp", 8),
        I("mov_r64_m64", "rdi", ("m", "rsp", 24)),     # fr
        I("mov_r64_r64", "rsi", "r14"),
        I("call_rel32", ("l", "mkapp")),               # rax = (g x)
        I("add_r64_imm", "rsp", 8), I("pop_r64", "rdi"),
        I("mov_r64_r64", "rsi", "rax"),
        I("call_rel32", ("l", "mkapp")),
        I("add_r64_imm", "rsp", 16),
        I("jmp_rel32", ("l", "st_out")),
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
        # ---- count_nodes(rdi) -> rax ----
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
        # ---- emit(rdi=node, rsi=cur) -> rsi : postfix decompile ----
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
        I("cmp_r64_imm", "rax", Tag.I), I("je_rel32", ("l", "en_i")),
        I("cmp_r64_imm", "rax", Tag.K), I("je_rel32", ("l", "en_k")),
        I("cmp_r64_imm", "rax", Tag.S), I("je_rel32", ("l", "en_s")),
        I("mov_r32_imm32", "ecx", 0x3F), I("jmp_rel32", ("l", "en_w")),
        LBL("en_i"), I("mov_r32_imm32", "ecx", 0x49), I("jmp_rel32", ("l", "en_w")),
        LBL("en_k"), I("mov_r32_imm32", "ecx", 0x4B), I("jmp_rel32", ("l", "en_w")),
        LBL("en_s"), I("mov_r32_imm32", "ecx", 0x53),
        LBL("en_w"),
        I("mov_m8_r8", ("m", "rsi", 0), "cl"), I("inc_r64", "rsi"),
        I("mov_m8_imm8", ("m", "rsi", 0), 0x20), I("inc_r64", "rsi"), I("ret"),
        # ---- itoa(rdi=val, rsi=cur) -> rsi ----
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
    return p


# ======================================================================
# §6  PE64 WRITER (layout as table)
# ======================================================================

TEXT_RVA = 0x1000
IDATA_RVA = 0x2000
DATA_RVA = 0x3000
FILE_ALIGN = 0x200
SECT_ALIGN = 0x1000
IMAGE_BASE = 0x140000000


def build_idata() -> Tuple[bytes, Dict[str, int]]:
    """Import directory + ILT + IAT + hint/names; returns bytes and iat symbols."""
    n = len(IMPORTS)
    idt_sz, ilt_sz = (n // n + 1) * 20, (n + 1) * 8   # 1 dll desc + null; n+1 thunks
    idt_sz = 40
    ilt_off = idt_sz
    iat_off = ilt_off + ilt_sz
    names_off = iat_off + ilt_sz
    recs: List[Tuple[str, bytes]] = []
    off = names_off
    hn_rvas: List[int] = []
    for name in IMPORTS:
        hn = struct.pack("<H", 0) + name.encode() + b"\x00"
        if len(hn) & 1:
            hn += b"\x00"
        hn_rvas.append(IDATA_RVA + off)
        off += len(hn)
    dll_rva = IDATA_RVA + off
    dll = b"kernel32.dll\x00"
    off += len(dll)
    ilt = b"".join(struct.pack("<Q", r) for r in hn_rvas) + b"\x00" * 8
    idt = struct.pack("<IIIII", IDATA_RVA + ilt_off, 0, 0, dll_rva,
                      IDATA_RVA + iat_off) + b"\x00" * 20
    body = idt + ilt + ilt  # ILT and IAT identical content
    names = b"".join(
        struct.pack("<H", 0) + nm.encode() + b"\x00"
        + (b"\x00" if (2 + len(nm) + 1) & 1 else b"")
        for nm in IMPORTS)
    body += names + dll
    syms = {f"iat_{nm}": IDATA_RVA + iat_off + i * 8
            for i, nm in enumerate(IMPORTS)}
    return body, syms


def build_data() -> Tuple[bytes, Dict[str, int]]:
    syms: Dict[str, int] = {}
    off = 0
    for name, sz in DATA_SLOTS:
        syms[name] = DATA_RVA + off
        off += sz
    return b"\x00" * off, syms


def build_pe(R: Realization = DEFAULT) -> bytes:
    prog = reducer_program(R)
    idata, iat_syms = build_idata()
    data, data_syms = build_data()
    base_rva = TEXT_RVA
    all_syms = dict(iat_syms)
    all_syms.update(data_syms)

    # assemble with symbols resolved as absolute RVAs; labels local offsets
    local: Dict[str, int] = {}
    pos = 0
    offs = []
    for item in prog:
        if item[0] == "label":
            local[item[1]] = base_rva + pos
        offs.append(pos)
        if item[0] != "label":
            pos += len(encode(item[1:]))
    code = bytearray()
    for item, off in zip(prog, offs):
        if item[0] == "label":
            continue
        insn = item[1:]
        end = base_rva + off + len(encode(insn))
        resolver = lambda name, _e=end: (
            all_syms[name] if name in all_syms else local[name]) - _e
        code += encode(insn, resolve=resolver)
    code = bytes(code)

    def sect(name: bytes, vsize: int, vaddr: int, raw: bytes, chars: int,
             rawptr: int) -> bytes:
        return struct.pack("<8sIIIIIIHHI", name, vsize, vaddr,
                           _align(len(raw), FILE_ALIGN), rawptr, 0, 0, 0, 0,
                           chars)

    text_raw = code + b"\x00" * (_align(len(code), FILE_ALIGN) - len(code))
    idata_raw = idata + b"\x00" * (_align(len(idata), FILE_ALIGN) - len(idata))
    data_raw = data + b"\x00" * (_align(len(data), FILE_ALIGN) - len(data))
    text_ptr = FILE_ALIGN
    idata_ptr = text_ptr + len(text_raw)
    data_ptr = idata_ptr + len(idata_raw)
    size_image = _align(DATA_RVA + len(data), SECT_ALIGN)

    dos = bytearray(0x40)
    dos[0:2] = b"MZ"
    struct.pack_into("<I", dos, 0x3C, 0x40)
    coff = struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0, 0x0022)
    dd = [(0, 0)] * 16
    dd[1] = (IDATA_RVA, len(idata))
    opt = struct.pack(
        "<HBBIIIIIQIIHHHHHHIIIIHHQQQQII",
        0x20B, 0, 0,                      # magic, linker ver
        len(text_raw), len(idata_raw) + len(data_raw), 0,
        TEXT_RVA, TEXT_RVA,               # entry, base of code
        IMAGE_BASE, SECT_ALIGN, FILE_ALIGN,
        6, 0, 0, 0, 6, 0,                 # OS/img/subsys ver
        0, size_image, FILE_ALIGN, 0,     # win32ver, img, hdrs, checksum
        3, 0x8100,                        # subsystem CUI, dllchars (no DYNAMIC_BASE)
        R.stack_reserve, 0x1000,          # stack reserve/commit
        0x100000, 0x1000,                 # heap reserve/commit
        0, 16,                            # loader flags, #rva+size
    ) + b"".join(struct.pack("<II", r, s) for r, s in dd)
    assert len(opt) == 0xF0, len(opt)
    sh = (sect(b".text\x00\x00\x00", len(code), TEXT_RVA, text_raw, 0x60000020,
               text_ptr)
          + sect(b".idata\x00\x00", len(idata), IDATA_RVA, idata_raw, 0x40000040,
                 idata_ptr)
          + sect(b".data\x00\x00\x00", len(data), DATA_RVA, data_raw, 0xC0000040,
                 data_ptr))
    headers = bytes(dos) + b"PE\x00\x00" + coff + opt + sh
    headers += b"\x00" * (FILE_ALIGN - len(headers))
    return headers + text_raw + idata_raw + data_raw


def _align(v: int, a: int) -> int:
    return (v + a - 1) // a * a


def write_exe(path: str, R: Realization = DEFAULT) -> str:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(build_pe(R))
    return path


# ======================================================================
# §7  HOST-FACING API (lazy host imports via sys.path ../host)
# ======================================================================

def _host():
    hdir = os.path.normpath(os.path.join(SEED_DIR, "..", "host"))
    if hdir not in sys.path:
        sys.path.insert(0, hdir)
    import reduce as hreduce        # noqa: E402
    import bytecode_dialect as bcd  # noqa: E402
    import host_pieces as hp        # noqa: E402
    return hreduce, bcd, hp


def run_native(exe: str, tokens_text: str) -> Tuple[str, str, int]:
    cp = subprocess.run([exe], input=tokens_text.encode(),
                        capture_output=True, timeout=600)
    return cp.stdout.decode("utf-8", "replace"), \
        cp.stderr.decode("utf-8", "replace"), cp.returncode


_EXE_CACHE: Dict[str, str] = {}


def _exe_for(R: Realization = DEFAULT) -> str:
    key = repr(R)
    if key not in _EXE_CACHE:
        _EXE_CACHE[key] = write_exe(os.path.join(BUILD_DIR, "reducer.exe"), R)
    return _EXE_CACHE[key]


def reduce_native(t, fuel: Optional[int] = None):
    """HostPiece.reduce signature: (T_host, fuel) -> (nf, steps, alloc).

    The `fuel` argument is intentionally ignored: it is a graph-piece
    parameter, while native fuel is governed by Realization.fuel baked
    into the generated executable.
    """
    hreduce, bcd, hp = _host()
    prog = bcd.decompile(t)
    text = " ".join(
        {bcd.Instr.PUSH_I: "I", bcd.Instr.PUSH_K: "K",
         bcd.Instr.PUSH_S: "S", bcd.Instr.APP: "@"}[i] for i in prog)
    out, err, rc = run_native(_exe_for(DEFAULT), text)
    if rc != 0:
        raise RuntimeError(f"native reducer rc={rc} stderr={err!r}")
    nf = bcd.compile_bytecode(bcd.parse_prog(out))
    steps = alloc = 0
    import re
    m = re.search(r"steps=(\d+)\s+alloc=(\d+)", err)
    if m:
        steps, alloc = int(m.group(1)), int(m.group(2))
    return nf, steps, alloc


def piece():
    _, _, hp = _host()
    return hp.HostPiece(name="native.x86_64.pe", kind="cpu",
                        reduce=reduce_native)


# ======================================================================
# §8  ORACLES + GATES
# ======================================================================

def _fasmg(src: str) -> bytes:
    if not os.path.exists(FASMG):
        raise FileNotFoundError(f"fasmg oracle missing: {FASMG}")
    with tempfile.TemporaryDirectory() as td:
        asm = os.path.join(td, "in.asm")
        binp = os.path.join(td, "out.bin")
        with open(asm, "w", newline="\n") as f:
            f.write(src)
        cp = subprocess.run([FASMG, asm, binp], capture_output=True, text=True)
        if cp.returncode != 0 or not os.path.exists(binp):
            raise RuntimeError(f"fasmg failed rc={cp.returncode}: "
                               f"{cp.stdout}{cp.stderr}")
        with open(binp, "rb") as f:
            return f.read()


_FASM_HDR = (
    f"include '{FASMG_INC}/format/format.inc'\n"
    f"include '{FASMG_INC}/x64.inc'\n"
    "use64\nformat binary\n"
)


def _g1() -> bool:
    ok = True
    samples: List[Tuple[str, Insn]] = [
        ("mov_r64_imm", ("mov_r64_imm", "rax", 0x1122334455667788)),
        ("mov_r64_imm", ("mov_r64_imm", "r15", 1)),
        ("mov_r64_imm", ("mov_r64_imm", "rcx", -10)),
        ("mov_r64_r64", ("mov_r64_r64", "rax", "rbx")),
        ("mov_r64_r64", ("mov_r64_r64", "r14", "r13")),
        ("mov_r64_m64", ("mov_r64_m64", "r14", ("m", "r13", 8))),
        ("mov_r64_m64", ("mov_r64_m64", "rax", ("m", "rsp", 0x20))),
        ("mov_r64_m64", ("mov_r64_m64", "rax", ("m", "rbp", 0))),
        ("mov_r64_m64", ("mov_r64_m64", "r12", ("m", "r15", -8))),
        ("mov_m64_r64", ("mov_m64_r64", ("m", "r13", 16), "r14")),
        ("mov_m64_r64", ("mov_m64_r64", ("m", "r15", 0), "rax")),
        ("mov_r64_rip", ("mov_r64_rip", "rcx", ("p", 0x1234))),
        ("mov_rip_r64", ("mov_rip_r64", ("p", 0x1234), "rax")),
        ("movzx_r32_m8", ("movzx_r32_m8", "eax", ("m", "rsi", 0))),
        ("movzx_r32_m8", ("movzx_r32_m8", "ecx", ("m", "rsi", 3))),
        ("mov_r8_m8", ("mov_r8_m8", "al", ("m", "r9", 0))),
        ("mov_m8_r8", ("mov_m8_r8", ("m", "rsi", 0), "cl")),
        ("mov_m8_imm8", ("mov_m8_imm8", ("m", "rsi", 0), 0x40)),
        ("mov_m64_imm32", ("mov_m64_imm32", ("m", "rsp", 0x20), 0)),
        ("mov_m64_imm32", ("mov_m64_imm32", ("m", "rax", 8), 0)),
        ("mov_r32_imm32", ("mov_r32_imm32", "ecx", -10)),
        ("mov_r32_imm32", ("mov_r32_imm32", "r8d", 0x3000)),
        ("lea_r64_m64", ("lea_r64_m64", "r14", ("m", "rax", 0x100000))),
        ("lea_r64_m64", ("lea_r64_m64", "r9", ("m", "rsp", 0x20))),
        ("lea_r64_rip", ("lea_r64_rip", "rsi", ("p", 0x400))),
        ("add_r64_imm", ("add_r64_imm", "rax", 5)),
        ("add_r64_imm", ("add_r64_imm", "r14", 0x100000)),
        ("add_r64_imm", ("add_r64_imm", "rax", 200)),
        ("and_r64_imm", ("and_r64_imm", "r14", 0xFF)),
        ("sub_r64_imm", ("sub_r64_imm", "rsp", 0x28)),
        ("sub_r64_imm", ("sub_r64_imm", "r15", 8)),
        ("cmp_r64_imm", ("cmp_r64_imm", "rax", 0x49)),
        ("cmp_r64_imm", ("cmp_r64_imm", "r15", 1000)),
        ("cmp_m64_imm", ("cmp_m64_imm", ("m", "r12", 0), 3)),
        ("cmp_m64_imm", ("cmp_m64_imm", ("m", "rax", 0), 0)),
        ("add_r64_r64", ("add_r64_r64", "rax", "rcx")),
        ("sub_r64_r64", ("sub_r64_r64", "rax", "r13")),
        ("cmp_r64_r64", ("cmp_r64_r64", "r13", "r14")),
        ("test_r64_r64", ("test_r64_r64", "rax", "rax")),
        ("xor_r32_r32", ("xor_r32_r32", "eax", "eax")),
        ("xor_r32_r32", ("xor_r32_r32", "r15d", "r15d")),
        ("add_r8_imm8", ("add_r8_imm8", "dl", 0x30)),
        ("shl_r64_imm8", ("shl_r64_imm8", "rdx", 3)),
        ("push_r64", ("push_r64", "r14")),
        ("push_r64", ("push_r64", "rsi")),
        ("pop_r64", ("pop_r64", "r12")),
        ("call_rel32", ("call_rel32", ("l", 0x40))),
        ("call_mrip", ("call_mrip", ("p", 0x2000))),
        ("jmp_rel32", ("jmp_rel32", ("l", 0x30))),
        ("je_rel32", ("je_rel32", ("l", 0x20))),
        ("jne_rel32", ("jne_rel32", ("l", 0x20))),
        ("jl_rel32", ("jl_rel32", ("l", 0x20))),
        ("jge_rel32", ("jge_rel32", ("l", 0x20))),
        ("jb_rel32", ("jb_rel32", ("l", 0x20))),
        ("jbe_rel32", ("jbe_rel32", ("l", 0x20))),
        ("ret", ("ret",)),
        ("inc_r64", ("inc_r64", "r15")),
        ("dec_r64", ("dec_r64", "r9")),
        ("inc_mrip", ("inc_mrip", ("p", 0x3000))),
        ("div_r64", ("div_r64", "r8")),
    ]
    for form, insn in samples:
        if FORMS[form][4] == "l":
            d = insn[1][1]
            src = f"{FORMS[form][0]} near lbl\nrb {d}\nlbl: ret\n"
        else:
            src = render_fasm(insn) + "\n"
        try:
            want = _fasmg(_FASM_HDR + src)
        except Exception as e:
            print(f"  FAIL {src!r}: oracle {e}")
            ok = False
            continue
        got = encode(insn)
        if FORMS[form][4] == "l":
            match = want[:len(got)] == got and len(want) == len(got) + d + 1
        else:
            match = got == want
        if not match:
            print(f"  FAIL {src!r}: got {got.hex()} want {want.hex()}")
            ok = False
    # whole-program: assemble reducer .text, compare with fasmg on the same
    # rendered listing (rel32 via labels, rip via computed displacements).
    prog = reducer_program(DEFAULT)
    idata, iat_syms = build_idata()
    data, data_syms = build_data()
    all_syms = dict(iat_syms)
    all_syms.update(data_syms)
    local: Dict[str, int] = {}
    pos = 0
    offs = []
    for item in prog:
        if item[0] == "label":
            local[item[1]] = TEXT_RVA + pos
        offs.append(pos)
        if item[0] != "label":
            pos += len(encode(item[1:]))
    src_lines = []
    for item, off in zip(prog, offs):
        if item[0] == "label":
            src_lines.append(f"{item[1]}:")
            continue
        insn = item[1:]
        end = TEXT_RVA + off + len(encode(insn))
        resolver = lambda name, _e=end: (
            all_syms[name] if name in all_syms else local[name]) - _e
        src_lines.append("  " + render_fasm(insn, resolve=resolver))
    try:
        want = _fasmg(_FASM_HDR + "\n".join(src_lines) + "\n")
        got2 = bytearray()
        for item, off in zip(prog, offs):
            if item[0] == "label":
                continue
            insn = item[1:]
            end = TEXT_RVA + off + len(encode(insn))
            resolver = lambda name, _e=end: (
                all_syms[name] if name in all_syms else local[name]) - _e
            got2 += encode(insn, resolve=resolver)
        if bytes(got2) != want:
            for i, (a, b) in enumerate(zip(bytes(got2), want)):
                if a != b:
                    print(f"  FAIL whole-program: first diff at 0x{i:x}: "
                          f"{a:02x} != {b:02x}")
                    break
            else:
                print(f"  FAIL whole-program: len {len(got2)} != {len(want)}")
            ok = False
    except Exception as e:
        print(f"  FAIL whole-program oracle: {e}")
        ok = False
    return ok


def _random_progs(n: int, seed_: int = 83) -> List[str]:
    import random
    rng = random.Random(seed_)
    out = []
    for _ in range(n):
        k = rng.randint(1, 14)
        out.append(" ".join(rng.choice("IKS@") for _ in range(k)))
    return out


def _deep_terms():
    """≥3 SKI Church-arithmetic terms with >1000 host steps (fuel 1e6)."""
    hreduce, bcd, hp = _host()
    zero = hreduce.app(hreduce.KK, hreduce.I)
    succ = hreduce.app(hreduce.S, hreduce.app(
        hreduce.app(hreduce.S, hreduce.app(hreduce.KK, hreduce.S)), hreduce.KK))

    def num(n):
        t = zero
        for _ in range(n):
            t = hreduce.app(succ, t)
        return t
    return [
        ("church mul 25 10", hreduce.app(
            hreduce.app(num(25), hreduce.app(num(10), succ)), zero)),
        ("church exp 3 5", hreduce.app(hreduce.app(
            hreduce.app(num(5), num(3)), succ), zero)),
        ("church mul 20 15", hreduce.app(
            hreduce.app(num(20), hreduce.app(num(15), succ)), zero)),
    ]


def _tokens_of_prog(prog) -> str:
    _, bcd, _ = _host()
    m = {bcd.Instr.PUSH_I: "I", bcd.Instr.PUSH_K: "K",
         bcd.Instr.PUSH_S: "S", bcd.Instr.APP: "@"}
    return " ".join(m[i] for i in prog)


def _g2() -> bool:
    hreduce, bcd, hp = _host()
    ok = True
    cases: List[Tuple[str, T]] = []
    for label, term, _exp in hreduce.GOLDENS:
        cases.append((label, t_from_host(term)))
    for text in _random_progs(24):
        try:
            cases.append((text, bc_compile(text)))
        except ValueError:
            pass
    for label, prog, _exp in bcd.GOLDENS:
        cases.append(("bc:" + label, bc_compile(_tokens_of_prog(prog))))
    for label, sterm in cases:
        nf_s, st_s = reduce(sterm, fuel=1_000_000)
        nf_h, st_h = hreduce.reduce(t_to_host(sterm, hreduce), fuel=1_000_000)
        good = (nf_s == t_from_host(nf_h)) and st_s == st_h
        if not good:
            print(f"  FAIL {label}: seed {nf_s}/{st_s} vs host {nf_h}/{st_h}")
            ok = False
    return ok


def _g3() -> bool:
    hreduce, bcd, hp = _host()
    exe = _exe_for(DEFAULT)
    exe_bytes = open(exe, "rb").read()
    ok = True
    probes: List[Tuple[str, str, object]] = []
    for label, prog, _exp in bcd.GOLDENS:
        probes.append((label, _tokens_of_prog(prog), None))
    import mine_adopt as ma
    for i, t in enumerate(ma.default_probes()):
        probes.append((f"probe{i}", _tokens_of_prog(bcd.decompile(t)), t))
    for label, t in _deep_terms():
        probes.append((label, _tokens_of_prog(bcd.decompile(t)), t))
    # streaming-boundary probe: token text > read_buf_bytes (64 KiB granule)
    probes.append(("stream>64KiB", "I K @ " * 20000, None))
    for label, text, t in probes:
        try:
            term = t if t is not None else bcd.compile_bytecode(
                bcd.parse_prog(text))
            nf_host, steps_host = hreduce.reduce(term, fuel=1_000_000)
            bcd.decompile(nf_host)  # must be decompilable
            nf_seed, steps_seed = reduce(t_from_host(term))
            out, err, rc = run_native(exe, text)
            line = out.strip()
            good = rc == 0
            detail = ""
            if good:
                import fasm_dialect as fd
                got = bcd.compile_bytecode(fd.parse_fasm(line))
                good = (got == nf_host) and (nf_seed == t_from_host(nf_host))
                import re
                m = re.search(r"steps=(\d+)", err)
                steps_native = int(m.group(1)) if m else -1
                if steps_native != steps_host:
                    good = False
                    detail += f" steps {steps_native}!={steps_host}"
                squashed = text.replace(" ", "")
                if len(squashed) > 4 and squashed.encode() in exe_bytes:
                    good = False
                    detail += " probe-text-in-exe"
            if not good:
                print(f"  FAIL {label}: rc={rc} out={line!r} err={err!r}{detail}")
                ok = False
            else:
                print(f"  ok {label}: nf={line!r} steps={steps_host}")
        except Exception as e:
            print(f"  FAIL {label}: {e}")
            ok = False
    return ok


def _program_diffs(Ra: Realization, Rb: Realization):
    """Entry-by-entry structural diff: same shape; operands may differ only
    where they equal a Realization field of the respective R."""
    pa, pb = reducer_program(Ra), reducer_program(Rb)
    assert len(pa) == len(pb), (len(pa), len(pb))
    fnames = [f.name for f in fields(Realization)]
    diffs = []

    def walk(x, y, path):
        if x == y:
            return
        if isinstance(x, tuple) and isinstance(y, tuple) and len(x) == len(y):
            for k, (u, v) in enumerate(zip(x, y)):
                walk(u, v, path + (k,))
            return
        hit = [n for n in fnames if getattr(Ra, n) == x and getattr(Rb, n) == y]
        assert hit, f"operand diff not a Realization field: {path} {x!r} {y!r}"
        diffs.append((path, hit[0], x, y))

    for i, (a, b) in enumerate(zip(pa, pb)):
        if a == b:
            continue
        assert a[0] == b[0], (i, a, b)                      # same item kind
        if a[0] == "label":
            assert a[1] == b[1]
            continue
        assert a[1] == b[1], (i, a, b)                    # same insn form
        assert len(a) == len(b)
        for j, (x, y) in enumerate(zip(a[2:], b[2:])):
            walk(x, y, (i, j))
    return diffs


def _text_offsets(pe: bytes) -> bytes:
    """Extract .text section bytes from a built PE image."""
    raw_ptr = struct.unpack_from("<I", pe, 0x40 + 4 + 20 + 0xF0 + 0x10 + 4)[0]
    raw_sz = struct.unpack_from("<I", pe, 0x40 + 4 + 20 + 0xF0 + 0x10)[0]
    return pe[raw_ptr:raw_ptr + raw_sz]


def _variant_exe(tag: str, R: Realization) -> str:
    return write_exe(os.path.join(BUILD_DIR, f"reducer_{tag}.exe"), R)


def _g4() -> bool:
    hreduce, bcd, hp = _host()
    ok = True
    # medium-term probe crossing many 4KiB chunks + streaming boundary
    deep_text = _tokens_of_prog(bcd.decompile(_deep_terms()[0][1]))
    probes = ["I K @", "S K @ K @ I @", "K S @ I @",
              deep_text, "I K @ " * 2000]

    variants = [
        ("chunk4k", Realization(chunk_bytes=4096)),
        ("stack8m", Realization(stack_reserve=8 << 20)),
        ("buf16", Realization(read_buf_bytes=16)),
    ]
    for tag, Rv in variants:
        exe = _variant_exe(tag, Rv)
        for text in probes:
            term = bcd.compile_bytecode(bcd.parse_prog(text))
            nf_host, steps_host = hreduce.reduce(term, fuel=1_000_000)
            out, err, rc = run_native(exe, text)
            good = rc == 0
            if good:
                import fasm_dialect as fd
                got = bcd.compile_bytecode(fd.parse_fasm(out.strip()))
                import re
                m = re.search(r"steps=(\d+)", err)
                good = (got == nf_host
                        and m and int(m.group(1)) == steps_host)
            if not good:
                print(f"  FAIL {tag} probe: rc={rc} out={out[:60]!r}")
                ok = False
        print(f"  ok {tag}: {len(probes)} probes NF+steps match")

    # structural diffs: operands may differ only in Realization fields
    for tag, Rv in variants:
        diffs = _program_diffs(DEFAULT, Rv)
        if diffs:
            print(f"  diffs {tag}: {[(d[0], d[1]) for d in diffs]}")
    # .text byte offsets that differ (chunk4k)
    ta, tb = _text_offsets(build_pe(DEFAULT)), _text_offsets(
        build_pe(Realization(chunk_bytes=4096)))
    byte_diffs = [hex(i) for i, (a, b) in enumerate(zip(ta, tb)) if a != b]
    print(f"  .text diff offsets chunk4k: {byte_diffs}")

    # cd refusal
    try:
        build_pe(Realization(order="cd"))
        print("  FAIL order='cd' built silently (fallback)")
        ok = False
    except NotRealized as e:
        print(f"  ok cd refused: {e}")

    # fuel variants on church exp 3 5 (3148 steps)
    exp_text = _tokens_of_prog(bcd.decompile(_deep_terms()[1][1]))
    exe_f = _variant_exe("fuel50", Realization(fuel=50))
    out, err, rc = run_native(exe_f, exp_text)
    good = rc == 2 and out.strip() == ""
    print(f"  {'ok' if good else 'FAIL'} fuel=50 -> rc={rc} out={out[:40]!r}")
    ok = ok and good
    exe_f2 = _variant_exe("fuel10k", Realization(fuel=10000))
    out2, err2, rc2 = run_native(exe_f2, exp_text)
    term = bcd.compile_bytecode(bcd.parse_prog(exp_text))
    nf_host, steps_host = hreduce.reduce(term, fuel=1_000_000)
    import fasm_dialect as fd
    good2 = (rc2 == 0
             and bcd.compile_bytecode(fd.parse_fasm(out2.strip())) == nf_host)
    print(f"  {'ok' if good2 else 'FAIL'} fuel=10000 -> rc={rc2}")
    ok = ok and good2
    return ok


def _g5() -> bool:
    hreduce, bcd, hp = _host()
    import cogen
    import mine_adopt as ma
    from observation_regime import oper_eq_regime
    ok = True
    hp.register_piece(piece())
    c = cogen.MachineContext.detect()
    plan = cogen.choose(hp.catalog(), cogen.Budget.SERIAL, c)
    good = plan.family == "cpu" and plan.source_piece == "native.x86_64.pe"
    print(f"  {'ok' if good else 'FAIL'} choose SERIAL+x86_64 -> "
          f"{plan.family}/{plan.source_piece}")
    ok = ok and good

    spec, nplan, npiece = cogen.native_realize()
    good = cogen.preserves_spec(spec, npiece)
    print(f"  {'ok' if good else 'FAIL'} native_realize preserves_spec "
          f"({len(spec.probes)} probes)")
    ok = ok and good

    progs = [p for _, p, _ in bcd.GOLDENS]
    r = ma.try_adopt(bcd.compile_bytecode, surfaces=progs,
                     known=[bcd.bytecode_map()])
    good = r.accepted and r.matched_map == "bytecode"
    print(f"  {'ok' if good else 'FAIL'} try_adopt compile_bytecode -> {r}")
    ok = ok and good

    # try_adopt has no piece hook: inline check that native NF ~_O graph.lo NF
    R = oper_eq_regime()
    graph = hp.by_name("graph.lo")
    for p in progs:
        term = bcd.compile_bytecode(p)
        nfn, _, _ = npiece.reduce(term, 100_000)
        nfg, _, _ = graph.reduce(term, 100_000)
        if not R.sim(nfn, nfg):
            print(f"  FAIL native NF != graph.lo NF on {p}")
            ok = False
    print(f"  ok native NF ~_O graph.lo on {len(progs)} probes "
          "(inline; try_adopt has no piece hook)")
    return ok


def main() -> int:
    results = []
    print("G1 encoder vs fasmg")
    try:
        g1 = _g1()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g1 = False
    print(f"{'OK' if g1 else 'FAIL'} G1")
    results.append(g1)

    print("G2 kernel mirror vs host reduce")
    try:
        g2 = _g2()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g2 = False
    print(f"{'OK' if g2 else 'FAIL'} G2")
    results.append(g2)

    print("G3 native exe probes")
    try:
        g3 = _g3()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g3 = False
    print(f"{'OK' if g3 else 'FAIL'} G3")
    results.append(g3)

    print("G4 strategy variations")
    try:
        g4 = _g4()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g4 = False
    print(f"{'OK' if g4 else 'FAIL'} G4")
    results.append(g4)

    print("G5 host registration")
    try:
        g5 = _g5()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g5 = False
    print(f"{'OK' if g5 else 'FAIL'} G5")
    results.append(g5)
    return 0 if all(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
