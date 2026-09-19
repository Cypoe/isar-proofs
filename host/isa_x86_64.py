"""
isa_x86_64 — pure x86-64 ISA data + encoder + two-pass assembler.

Moved verbatim from seed/seed.py §3/§4 (the seed only seeds; the ISA is
host data the toolchain catalog can list/choose/refuse).  `assemble`
gained a `base` parameter (default 0): with base=TEXT_RVA the resolver
math is identical to the old inline build_pe assembly.

Oracle: fasmg.exe (env ISAR_FASMG) byte-equality per INSN row — see
check_rows() / main().  Missing oracle = FAIL, never SKIP.
"""
from __future__ import annotations

import os
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

DEFAULT_FASMG = os.path.normpath(os.path.join(
    _HOST, "..", "..", "isa-physics", "boostrap", "fasmg", "fasmg.exe"))
FASMG = os.environ.get("ISAR_FASMG", DEFAULT_FASMG)
FASMG_INC = os.path.join(os.path.dirname(FASMG), "examples", "x86", "include")

_FASM_HDR = (
    f"include '{FASMG_INC}/format/format.inc'\n"
    f"include '{FASMG_INC}/x64.inc'\n"
    "use64\nformat binary\n"
)


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


# ======================================================================
# ISA DATA (x86-64, authored from ISA; each row oracle-checked)
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
# ASSEMBLER (two-pass, labels)
# ======================================================================

Program = List[Tuple]


def LBL(name: str) -> Tuple:
    return ("label", name)


def I(form: str, *ops) -> Tuple:
    return ("i", form, *ops)


def assemble(program: Program, symbols: Dict[str, int],
             base: int = 0) -> Tuple[bytes, Dict[str, int]]:
    """Two-pass assembly; labels + rip/rel32 fixups to `symbols` + local labels.
    `base` shifts label/insn addresses (e.g. TEXT_RVA) without changing the
    relative displacements — symbols must already be absolute."""
    local: Dict[str, int] = {}
    offs: List[int] = []
    pos = 0
    for item in program:
        if item[0] == "label":
            local[item[1]] = base + pos
            offs.append(pos)
        else:
            offs.append(pos)
            pos += len(encode(item[1:]))
    out = bytearray()
    for item, off in zip(program, offs):
        if item[0] == "label":
            continue
        insn = item[1:]
        end = base + off + len(encode(insn))
        resolver = lambda name, _e=end: (
            symbols[name] if name in symbols else local[name]) - _e
        out += encode(insn, resolve=resolver)
    return bytes(out), local


@dataclass(frozen=True)
class ISA:
    name: str            # "x86_64"
    bits: int            # 64
    insn: tuple          # INSN rows
    encode: Callable     # encode(insn, resolve=None) -> bytes
    assemble: Callable   # assemble(program, symbols, base=0) -> (bytes, labels)
    render: Callable     # render_fasm


X86_64 = ISA(
    name="x86_64",
    bits=64,
    insn=INSN,
    encode=encode,
    assemble=assemble,
    render=render_fasm,
)


# ======================================================================
# Oracle: fasmg per-row byte equality
# ======================================================================

# (form, insn) samples covering every INSN row (~60 operand variations).
ROW_SAMPLES: List[Tuple[str, Insn]] = [
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


def check_rows() -> bool:
    """fasmg byte oracle on every ROW_SAMPLES entry (per-row only; the
    whole-.text oracle needs the routines and stays in the seed's G1)."""
    ok = True
    for form, insn in ROW_SAMPLES:
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
    return ok


def main() -> int:
    ok = check_rows()
    print(f"{'OK' if ok else 'FAIL'} isa_x86_64 "
          f"({len(ROW_SAMPLES)} samples vs fasmg)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
