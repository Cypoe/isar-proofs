"""
isa_riscv64 — pure RV64IM ISA data + table-driven encoder + assembler.

Third consumer of enc_core.interpret.  Fixed-width like aarch64: every
insn is exactly 4 bytes (no C extension in this table); each row's
"bits" contributes the opcode/funct3/funct7 template and the fields
fill its holes.

Register model: x0..x31 by ABI name — zero, ra, sp, gp, tp, t0..t6,
s0..s11, a0..a7.  No flags: compares are fused into branches
(beq/bne/blt/bge/bltu/bgeu take two registers); "cmp x, imm" is
materialize-then-branch at the routines layer.  No sf split: every
register is 64-bit; addiw exists for 32-bit-signed addi (the lui+addiw
pair materializes any 32-bit constant; wider via slli/addi chains at
the call site).

Formats:
  R  funct7|rs2|rs1|f3|rd|0110011     add/sub/and/or/xor/sltu/divu/remu
  I  imm[11:0]|rs1|f3|rd|op           addi/addiw/slli/srli/ld/lbu/jalr
  S  imm[11:5]|rs2|rs1|f3|imm[4:0]|0100011   sd/sb
  B  imm[12|10:5]|rs2|rs1|f3|imm[4:1|11]|1100011   branches
  U  imm[31:12]|rd|0110111            lui
  J  imm[20|10:1|11|19:12]|rd|1101111 jal

Branch/jal displacement is target - insn_addr, counted at the insn's
own address (same anchor convention as aarch64 — assemble()'s resolver
handles it; B imm is a signed 13-bit offset<<1, J is signed 21<<1).
Both stay inside the emitted kernel's ~2KB text: B range is ±4KB.

Symbol operands for absolute addresses (the lui+addiw materialization):
("ahi", s) = (a + 0x800) >> 12  (lui field),  ("alo", s) = signed low
12 bits of a - (hi<<12) (addi field) — same pair role as aarch64's
alo/ahi but for the riscv lo12-sign-extends convention.

Oracle: llvm-mc -triple=riscv64 -mattr=+m (env ISAR_LLVM_MC).  Missing
oracle = FAIL, never SKIP.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from enc_core import interpret, word32  # noqa: E402

_LLVM_BIN = r"C:\Program Files\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin"
DEFAULT_LLVM_MC = shutil.which("llvm-mc") or os.path.join(
    _LLVM_BIN, "llvm-mc.exe")
LLVM_MC = os.environ.get("ISAR_LLVM_MC", DEFAULT_LLVM_MC)
DEFAULT_LLVM_OBJCOPY = shutil.which("llvm-objcopy") or os.path.join(
    os.path.dirname(LLVM_MC), "llvm-objcopy.exe")
LLVM_OBJCOPY = os.environ.get("ISAR_LLVM_OBJCOPY", DEFAULT_LLVM_OBJCOPY)


def _exists(tool: str) -> bool:
    return os.path.exists(tool) or shutil.which(tool) is not None


def _llvm_mc(src: str):
    """llvm-mc -triple=riscv64 -mattr=+m -show-encoding on stdin asm.

    Same bytespec contract as isa_aarch64: four (mask, value) pairs —
    concrete '0xHH' gives (0xFF, HH), a symbolic fixup slot 'A' gives
    (0, 0) — plus (fixup_kind, value) when annotated."""
    if not _exists(LLVM_MC):
        raise FileNotFoundError(f"llvm-mc oracle missing: {LLVM_MC}")
    cp = subprocess.run(
        [LLVM_MC, "-triple=riscv64", "-mattr=+m", "-show-encoding"],
        input=src, capture_output=True, text=True)
    if cp.returncode != 0:
        raise RuntimeError(f"llvm-mc failed rc={cp.returncode}: "
                           f"{cp.stdout}{cp.stderr}")
    out = []
    for line in cp.stdout.splitlines():
        m = re.search(r"encoding: \[([^\]]+)\]", line)
        if m:
            out.append([[_encbyte(t.strip()) for t in m.group(1).split(",")],
                        None])
            continue
        m = re.search(r"fixup \w - offset: \d+, value: (.+), kind: (\S+)",
                      line)
        if m and out:
            out[-1][1] = (m.group(2), m.group(1).strip())
    return out


def _encbyte(tok: str) -> Tuple[int, int]:
    """oracle token -> (mask, value); 'A'-containing slots mask out
    (llvm-mc riscv prints e.g. 0x63'A' — the byte carries fixup bits
    whose positions aren't shown; pass 2 verifies resolved bytes)."""
    if "A" in tok:
        return (0, 0)
    if tok.startswith("0b"):
        return (int(tok[2:], 2), 0) if False else (
            int("".join("0" if c == "A" else "1" for c in tok[2:]), 2),
            int("".join("0" if c == "A" else c for c in tok[2:]), 2))
    return (0xFF, int(tok, 16))


def _llvm_mc_obj(src: str) -> bytes:
    """llvm-mc -filetype=obj, then llvm-objcopy .text -> raw bytes."""
    if not _exists(LLVM_OBJCOPY):
        raise FileNotFoundError(f"llvm-objcopy missing: {LLVM_OBJCOPY}")
    with tempfile.TemporaryDirectory() as td:
        op = os.path.join(td, "o.o")
        tp = os.path.join(td, "t.bin")
        cp = subprocess.run(
            [LLVM_MC, "-triple=riscv64", "-mattr=+m",
             "-filetype=obj", "-o", op],
            input=src, capture_output=True, text=True)
        if cp.returncode != 0:
            raise RuntimeError(f"llvm-mc obj failed: "
                               f"{cp.stdout}{cp.stderr}")
        cp = subprocess.run(
            [LLVM_OBJCOPY, "-O", "binary", "--only-section=.text",
             op, tp],
            capture_output=True, text=True)
        if cp.returncode != 0:
            raise RuntimeError(f"llvm-objcopy failed: {cp.stderr}")
        return open(tp, "rb").read()


# ======================================================================
# REGISTER + INSN TABLES (the row data)
# ======================================================================

REGS: Dict[str, int] = {
    "zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4,
    "t0": 5, "t1": 6, "t2": 7,
    "s0": 8, "s1": 9,
    "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15,
    "a6": 16, "a7": 17,
    "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23,
    "s8": 24, "s9": 25, "s10": 26, "s11": 27,
    "t3": 28, "t4": 29, "t5": 30, "t6": 31,
}

# INSN rows: (form, mnemonic, base) — base is the row's constant bit
# template; its zero bits are the holes the ENCS fields fill.
INSN: Tuple[Tuple[str, str, int], ...] = (
    ("nop",       "nop",   0x00000013),   # addi zero, zero, 0
    ("ret",       "ret",   0x00008067),   # jalr zero, 0(ra)
    ("ecall",     "ecall", 0x00000073),
    ("lui",       "lui",   0x00000037),
    ("addi",      "addi",  0x00000013),   # also mv (imm=0) / li (rs1=zero)
    ("addiw",     "addiw", 0x0000001B),
    ("slli",      "slli",  0x00001013),
    ("srli",      "srli",  0x00005013),
    ("add",       "add",   0x00000033),
    ("sub",       "sub",   0x40000033),
    ("and",       "and",   0x00007033),
    ("or",        "or",    0x00006033),
    ("xor",       "xor",   0x00004033),
    ("sltu",      "sltu",  0x00003033),
    ("ld",        "ld",    0x00003003),
    ("lbu",       "lbu",   0x00004003),
    ("sd",        "sd",    0x00003023),
    ("sb",        "sb",    0x00000023),
    ("beq",       "beq",   0x00000063),
    ("bne",       "bne",   0x00001063),
    ("blt",       "blt",   0x00004063),
    ("bge",       "bge",   0x00005063),
    ("bltu",      "bltu",  0x00006063),
    ("bgeu",      "bgeu",  0x00007063),
    ("jal",       "jal",   0x0000006F),
    ("jalr",      "jalr",  0x00000067),
    ("divu",      "divu",  0x02005033),   # M ext
    ("remu",      "remu",  0x02007033),   # M ext
)
FORMS: Dict[str, Tuple[str, int]] = {r[0]: r[1:] for r in INSN}

# Insn datum: (form, *operands).  Branch/jal target: ("p", label|int) —
# int is the byte offset target - insn_addr.  I/S immediates are ints;
# "ahi"/"alo" tuple operands resolve absolute symbols.
Insn = Tuple


# ======================================================================
# ENCODING TEMPLATES (riscv row data)
#
# ENCS[form] = ordered alternatives; the first whose PREDS all hold is
# emitted as the word32-fold of its FIELDS ops.  riscv has no flag/
# width split — most forms carry a single alternative; the preds exist
# for range checks that must FAIL loudly (branch reach, imm12 range)
# rather than truncate.
# ======================================================================

_IT = (("bits",), ("iimm", 2), ("rs1", 1), ("rd", 0))
_RT = (("bits",), ("rs2", 2), ("rs1", 1), ("rd", 0))
_ST = (("bits",), ("shi", 2), ("rs2", 0), ("rs1", 1), ("slo", 2))
_BT = (("bits",), ("bhi12", 2), ("bhi105", 2), ("rs2", 1), ("rs1", 0),
       ("blo41", 2), ("blo11", 2))
_UT = (("bits",), ("uimm", 1), ("rd", 0))
_JT = (("bits",), ("jhi20", 1), ("jhi101", 1), ("jhi11", 1),
       ("jhi1912", 1), ("rd", 0))
_SH = (("bits",), ("sh6", 2), ("rs1", 1), ("rd", 0))

ENCS: Dict[str, Tuple] = {
    "nop":    (((), (("bits",),)),),
    "ret":    (((), (("bits",),)),),   # jalr zero,0(ra) — constant
    "ecall":  (((), (("bits",),)),),
    "lui":    (((("ufit", 1),), _UT),),
    "addi":   (((("ifit", 2),), _IT),),
    "addiw":  (((("ifit", 2),), _IT),),
    "slli":   (((("sfit", 2),), _SH),),
    "srli":   (((("sfit", 2),), _SH),),
    "add":    (((), _RT),),
    "sub":    (((), _RT),),
    "and":    (((), _RT),),
    "or":     (((), _RT),),
    "xor":    (((), _RT),),
    "sltu":   (((), _RT),),
    "ld":     (((("ifit", 2),), _IT),),
    "lbu":    (((("ifit", 2),), _IT),),
    "sd":     (((("ifit", 2),), _ST),),
    "sb":     (((("ifit", 2),), _ST),),
    "beq":    (((("bfit", 2),), _BT),),
    "bne":    (((("bfit", 2),), _BT),),
    "blt":    (((("bfit", 2),), _BT),),
    "bge":    (((("bfit", 2),), _BT),),
    "bltu":   (((("bfit", 2),), _BT),),
    "bgeu":   (((("bfit", 2),), _BT),),
    "jal":    (((("jfit", 1),), _JT),),
    "jalr":   (((("ifit", 2),), _IT),),
    "divu":   (((), _RT),),
    "remu":   (((), _RT),),
}


# ======================================================================
# FIELD + PREDICATE VOCABULARY (riscv) — the named ops ENCS references.
# Every field returns (value, lsb, width) for enc_core.word32.
# ======================================================================

class _Ctx:
    """Field-interpreter scratch: row data + operands + label resolver."""
    __slots__ = ("mnem", "base", "ops", "resolve")

    def __init__(self, row: tuple, ops: tuple, resolve) -> None:
        self.mnem, self.base = row
        self.ops, self.resolve = ops, resolve


def _op(ctx: _Ctx, i: int, default=None):
    return ctx.ops[i] if i < len(ctx.ops) else default


def _reg(x) -> int:
    return REGS[x]


def _f_bits(ctx: _Ctx) -> Tuple[int, int, int]:
    return ctx.base, 0, 32


def _f_rd(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i)), 7, 5


def _f_rs1(ctx: _Ctx, i: int, default=None) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i, default)), 15, 5


def _f_rs2(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i)), 20, 5


def _symbits(v, kind: str, ctx: _Ctx) -> int:
    """("ahi"/"alo", s) tuple operand -> the resolved riscv value.
    The resolver sees the full tuple — it owns the hi/lo split (and
    reloc recording under assemble_obj)."""
    if not isinstance(v, tuple):
        return v
    return ctx.resolve(v) if ctx.resolve else 0


def _f_iimm(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    v = _symbits(_op(ctx, i, 0), "i", ctx)
    assert -2048 <= v <= 2047, f"imm12 {v} out of range"
    return v & 0xFFF, 20, 12


def _f_iimm0(ctx: _Ctx) -> Tuple[int, int, int]:
    return 0, 20, 12


def _f_uimm(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    v = _symbits(_op(ctx, i), "u", ctx)
    assert 0 <= v < (1 << 20), f"uimm20 {v} out of range"
    return v, 12, 20


def _f_sh6(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    v = _op(ctx, i)
    assert 0 <= v < 64, f"shamt {v} out of range"
    return v, 20, 6


def _f_shi(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    v = _symbits(_op(ctx, i), "s", ctx)
    return (v >> 5) & 0x7F, 25, 7


def _f_slo(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    v = _symbits(_op(ctx, i), "s", ctx)
    return v & 0x1F, 7, 5


def _reld(ctx: _Ctx, i: int) -> int:
    """Branch operand -> byte offset target - insn_addr."""
    o = _op(ctx, i)
    assert o[0] == "p", o
    if isinstance(o[1], int):
        return o[1]
    return ctx.resolve(o[1]) if ctx.resolve else 0


def _bimm(ctx: _Ctx, i: int) -> int:
    d = _reld(ctx, i)
    assert d % 2 == 0 and -4096 <= d <= 4094, \
        f"b-offset {d} out of ±4KB range"
    return d


def _jimm(ctx: _Ctx, i: int) -> int:
    d = _reld(ctx, i)
    assert d % 2 == 0 and -(1 << 20) <= d < (1 << 20), \
        f"j-offset {d} out of ±1MB range"
    return d


def _f_bhi12(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_bimm(ctx, i) >> 12) & 1, 31, 1


def _f_bhi105(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_bimm(ctx, i) >> 5) & 0x3F, 25, 6


def _f_blo41(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_bimm(ctx, i) >> 1) & 0xF, 8, 4


def _f_blo11(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_bimm(ctx, i) >> 11) & 1, 7, 1


def _f_jhi20(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_jimm(ctx, i) >> 20) & 1, 31, 1


def _f_jhi101(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_jimm(ctx, i) >> 1) & 0x3FF, 21, 10


def _f_jhi11(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_jimm(ctx, i) >> 11) & 1, 20, 1


def _f_jhi1912(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return (_jimm(ctx, i) >> 12) & 0xFF, 12, 8


FIELDS: Dict[str, Callable[..., Tuple[int, int, int]]] = {
    "bits":    _f_bits,
    "rd":      _f_rd,
    "rs1":     _f_rs1,
    "rs2":     _f_rs2,
    "iimm":    _f_iimm,
    "iimm0":   _f_iimm0,
    "uimm":    _f_uimm,
    "sh6":     _f_sh6,
    "shi":     _f_shi,
    "slo":     _f_slo,
    "bhi12":   _f_bhi12,
    "bhi105":  _f_bhi105,
    "blo41":   _f_blo41,
    "blo11":   _f_blo11,
    "jhi20":   _f_jhi20,
    "jhi101":  _f_jhi101,
    "jhi11":   _f_jhi11,
    "jhi1912": _f_jhi1912,
}


# ======================================================================
# PREDICATES — range checks that must fail loudly, never truncate.
# ======================================================================

def _p_ifit(ctx: _Ctx, i: int) -> bool:
    v = _op(ctx, i)
    if isinstance(v, tuple):
        return True                        # resolved later, asserted in field
    return -2048 <= v <= 2047


def _p_bfit(ctx: _Ctx, i: int) -> bool:
    o = _op(ctx, i)
    if not isinstance(o[1], int):
        return True                        # label: resolved later
    return o[1] % 2 == 0 and -4096 <= o[1] <= 4094


def _p_jfit(ctx: _Ctx, i: int) -> bool:
    o = _op(ctx, i)
    if not isinstance(o[1], int):
        return True
    return o[1] % 2 == 0 and -(1 << 20) <= o[1] < (1 << 20)


PREDS: Dict[str, Callable[..., bool]] = {
    "ifit": _p_ifit,
    "sfit": lambda ctx, i: 0 <= _op(ctx, i) < 64,
    "ufit": lambda ctx, i: isinstance(_op(ctx, i), tuple)
           or 0 <= _op(ctx, i) < (1 << 20),
    "bfit": _p_bfit,
    "jfit": _p_jfit,
}


# ======================================================================
# ENCODE — enc_core.interpret with the bit-slice combiner.
# ======================================================================

def encode(insn: Insn, resolve=None) -> bytes:
    """ISA-intrinsic encoding: ENCS row data through the field engine."""
    form, ops = insn[0], insn[1:]
    return interpret(FIELDS, PREDS, ENCS[form],
                     _Ctx(FORMS[form], ops, resolve), word32)


def render_mc(insn: Insn, resolve=None) -> str:
    """Mnemonic text for the oracle (one line of riscv64 asm).
    Branch/jal targets render '.+d'/'.-d' or the label name."""
    form, ops = insn[0], insn[1:]
    m = FORMS[form][0]

    def tgt(o) -> str:
        return f".{o[1]:+d}" if isinstance(o[1], int) else o[1]

    def immv(o) -> str:
        return f"0x{o[1]:x}" if isinstance(o, tuple) else str(o)

    if form in ("nop", "ret", "ecall"):
        return m
    if form in ("addi", "addiw", "slli", "srli"):
        return f"{m} {ops[0]}, {ops[1]}, {immv(ops[2])}"
    if form in ("add", "sub", "and", "or", "xor", "sltu", "divu", "remu"):
        return f"{m} {ops[0]}, {ops[1]}, {ops[2]}"
    if form in ("ld", "lbu"):
        return f"{m} {ops[0]}, {ops[2]}({ops[1]})"
    if form in ("sd", "sb"):
        return f"{m} {ops[0]}, {immv(ops[2])}({ops[1]})"
    if form in ("beq", "bne", "blt", "bge", "bltu", "bgeu"):
        return f"{m} {ops[0]}, {ops[1]}, {tgt(ops[2])}"
    if form == "jal":
        return f"jal {ops[0]}, {tgt(ops[1])}"
    if form == "jalr":
        return f"{m} {ops[0]}, {ops[2]}({ops[1]})"
    if form == "lui":
        return f"lui {ops[0]}, {immv(ops[1])}"
    raise ValueError(f"no render for form {form}")


# ======================================================================
# ASSEMBLER (two-pass, labels; 4-byte stride)
# ======================================================================

Program = List[Tuple]


def LBL(name: str) -> Tuple:
    return ("label", name)


def I(form: str, *ops) -> Tuple:
    return ("i", form, *ops)


def assemble(program: Program, symbols: Dict[str, int],
             base: int = 0) -> Tuple[bytes, Dict[str, int]]:
    """Two-pass assembly; ("p", name) fixups resolve against `symbols` +
    local labels.  The resolver returns target - insn_addr (riscv counts
    branch displacement from the branch's own address, like aarch64 —
    unlike x86 rip which counts from insn end)."""
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
        at = base + off
        def resolver(name, _a=at):
            if isinstance(name, tuple):
                # ("ahi", s)/("alo", s): resolver owns the split
                s = name[1]
                a = symbols[s] if s in symbols else local[s]
                if name[0] == "ahi":
                    return ((a + 0x800) >> 12) & 0xFFFFF
                if name[0] == "alo":
                    return a - ((a + 0x800) & ~0xFFF)
                return a
            return (symbols[name] if name in symbols
                    else local[name]) - _a
        out += encode(insn, resolve=resolver)
    return bytes(out), local


R_RISCV_HI20 = 26         # lui field — absolute hi20 of S+A
R_RISCV_LO12_I = 27       # i-imm field — signed lo12 of S+A


def assemble_obj(program: Program, syms=frozenset()) -> Tuple[
        bytes, Dict[str, int], List[Tuple[int, str, int, int]]]:
    """Relocatable assembly (ET_REL .o): branches/jal resolve inline
    (pc-relative intra-.text is link-safe); ("ahi"/"alo", sym) refs to
    non-local symbols become HI20/LO12_I relocations on the insn word —
    reloc offset = insn offset, field zeroed.  The lui+addiw pair is the
    standard absolute-address idiom the linker folds (+0x800) itself."""
    local: Dict[str, int] = {}
    offs: List[int] = []
    pos = 0
    for item in program:
        if item[0] == "label":
            if item[1] in local:
                raise ValueError(f"duplicate label {item[1]!r}")
            local[item[1]] = pos
            offs.append(pos)
        else:
            offs.append(pos)
            pos += len(encode(item[1:]))
    _RTYPE = {"ahi": R_RISCV_HI20, "alo": R_RISCV_LO12_I}
    relocs: List[Tuple[int, str, int, int]] = []
    out = bytearray()
    for item, off in zip(program, offs):
        if item[0] == "label":
            continue
        insn = item[1:]

        def resolver(name, _a=off, _o=off):
            if isinstance(name, tuple):
                s = name[1]
                if s not in local:
                    assert s in syms, f"undeclared symbol {s!r}"
                    relocs.append((_o, s, _RTYPE[name[0]], 0))
                    return 0
                a = local[s]
                if name[0] == "ahi":
                    return ((a + 0x800) >> 12) & 0xFFFFF
                if name[0] == "alo":
                    return a - ((a + 0x800) & ~0xFFF)
                return a
            return local[name] - _a

        out += encode(insn, resolve=resolver)
    return bytes(out), local, relocs


@dataclass(frozen=True)
class ISA:
    name: str            # "riscv64"
    bits: int            # 64
    insn: tuple          # INSN rows
    fields: dict         # FIELDS — per-ISA field vocabulary
    templates: dict      # ENCS — per-form encoding alternatives
    encode: Callable     # encode(insn, resolve=None) -> bytes
    assemble: Callable   # assemble(program, symbols, base=0) -> (bytes, labels)
    render: Callable     # render_mc
    assemble_obj: Callable = None  # assemble_obj(prog, syms) -> (text, labels, relocs)


RISCV64 = ISA(
    name="riscv64",
    bits=64,
    insn=INSN,
    fields=FIELDS,
    templates=ENCS,
    encode=encode,
    assemble=assemble,
    render=render_mc,
    assemble_obj=assemble_obj,
)


# ======================================================================
# Oracle: llvm-mc per-row byte equality
# ======================================================================

# (form, insn[, resolve]) — resolve maps label operands to the byte
# offset the check_rows label frame places them at.
ROW_SAMPLES: List[Tuple] = [
    ("nop",   ("nop",)),
    ("ret",   ("ret",)),
    ("ecall", ("ecall",)),
    ("lui",   ("lui", "t0", 0x12345)),
    ("lui",   ("lui", "s1", 0x500)),
    ("addi",  ("addi", "a0", "a1", 5)),
    ("addi",  ("addi", "sp", "sp", -16)),
    ("addi",  ("addi", "t0", "zero", 0x49)),
    ("addi",  ("addi", "s3", "s4", -2048)),
    ("addiw", ("addiw", "a3", "a4", 7)),
    ("addiw", ("addiw", "s1", "s1", -2048)),
    ("slli",  ("slli", "t0", "t0", 12)),
    ("slli",  ("slli", "a0", "a1", 63)),
    ("srli",  ("srli", "t1", "t2", 32)),
    ("add",   ("add", "a0", "a1", "a2")),
    ("sub",   ("sub", "t0", "t1", "t2")),
    ("and",   ("and", "s1", "s2", "s3")),
    ("or",    ("or", "a4", "a5", "a6")),
    ("xor",   ("xor", "a7", "a7", "a7")),
    ("sltu",  ("sltu", "t0", "t1", "t2")),
    ("ld",    ("ld", "a0", "sp", 8)),
    ("ld",    ("ld", "s1", "t0", -8)),
    ("ld",    ("ld", "t5", "s3", 2047)),
    ("lbu",   ("lbu", "t3", "t4", 3)),
    ("sd",    ("sd", "ra", "sp", 8)),
    ("sd",    ("sd", "t2", "s3", -16)),
    ("sb",    ("sb", "t5", "sp", 7)),
    ("beq",   ("beq", "a0", "a1", ("p", 8))),
    ("beq",   ("beq", "s1", "zero", ("p", -4))),
    ("bne",   ("bne", "a0", "zero", ("p", 12))),
    ("bne",   ("bne", "t0", "t6", ("p", "Lb")), {"Lb": -16}),
    ("blt",   ("blt", "s1", "s2", ("p", 4094))),
    ("bge",   ("bge", "a0", "zero", ("p", -4096))),
    ("bltu",  ("bltu", "s1", "s2", ("p", 0))),
    ("bgeu",  ("bgeu", "s2", "t0", ("p", 20))),
    ("jal",   ("jal", "ra", ("p", 16))),
    ("jal",   ("jal", "zero", ("p", -8))),
    ("jal",   ("jal", "ra", ("p", "Lf")), {"Lf": 24}),
    ("jalr",  ("jalr", "zero", "ra", 0)),
    ("jalr",  ("jalr", "t0", "a0", 24)),
    ("divu",  ("divu", "a0", "a1", "a2")),
    ("remu",  ("remu", "t5", "a4", "a6")),
]

_REL_OPS = {"beq": 2, "bne": 2, "blt": 2, "bge": 2, "bltu": 2,
            "bgeu": 2, "jal": 1}
_FIXUP_KIND = {f: "fixup_riscv_branch" for f in
               ("beq", "bne", "blt", "bge", "bltu", "bgeu")}
_FIXUP_KIND["jal"] = "fixup_riscv_jal"


def _rel_target(insn) -> Tuple:
    return insn[1 + _REL_OPS[insn[0]]]


def _resolve_of(sample) -> Optional[Callable]:
    if len(sample) > 2:
        rmap = sample[2]
        return lambda name: rmap[name]
    return None


def check_rows() -> bool:
    """llvm-mc oracle on every ROW_SAMPLES entry — same contract as
    isa_aarch64.check_rows: concrete-bit equality in pass 1, fully
    resolved branch/jal immediates proven in pass 2 (-filetype=obj)."""
    ok = True
    missing = [r[0] for r in INSN if r[0] not in ENCS]
    if missing:
        print(f"  FAIL ENCS missing rows: {missing}")
        ok = False

    # ---- pass 1: -show-encoding batch, one insn line per sample ----
    lines = []
    for i, s in enumerate(ROW_SAMPLES):
        insn = s[1]
        lines.append(render_mc(insn))
        o = insn[1 + _REL_OPS[insn[0]]] if insn[0] in _REL_OPS else None
        if o is not None and not isinstance(o[1], int):
            lines.append(f"{o[1]}:")        # label operand: define it
    try:
        encs = _llvm_mc("\n".join(lines) + "\n")
    except Exception as e:
        print(f"  FAIL oracle: {e}")
        return False
    if len(encs) != len(ROW_SAMPLES):
        print(f"  FAIL oracle count {len(encs)} != "
              f"{len(ROW_SAMPLES)} samples")
        return False
    for i, s in enumerate(ROW_SAMPLES):
        form, insn = s[0], s[1]
        got = encode(insn, resolve=_resolve_of(s))
        spec, fix = encs[i]
        bad = [k for k, (mask, val) in enumerate(spec)
               if got[k] & mask != val]
        if bad:
            print(f"  FAIL {lines[i]!r}: got {got.hex()} "
                  f"spec {spec} bytes {bad}")
            ok = False
        if form in _REL_OPS:
            o = _rel_target(insn)
            if fix is None:
                print(f"  FAIL {lines[i]!r}: no fixup annotated")
                ok = False
                continue
            kind, val = fix
            if kind != _FIXUP_KIND[form]:
                print(f"  FAIL {lines[i]!r}: fixup kind {kind} != "
                      f"{_FIXUP_KIND[form]}")
                ok = False
            if isinstance(o[1], int):
                m = re.match(r"\.Ltmp\d+([+-]\d+)$", val)
                if not m or int(m.group(1)) != o[1]:
                    print(f"  FAIL {lines[i]!r}: fixup value {val!r} "
                          f"!= delta {o[1]}")
                    ok = False
            elif val != o[1]:
                print(f"  FAIL {lines[i]!r}: fixup value {val!r} "
                      f"!= label {o[1]!r}")
                ok = False

    # ---- pass 2: object mode, rel samples only (imm value resolved) ----
    rel = [(i, s) for i, s in enumerate(ROW_SAMPLES)
           if s[0] in _REL_OPS]
    lines2, at = [], {}
    pos = 0
    for i, s in rel:
        insn = s[1]
        o = _rel_target(insn)
        d = o[1] if isinstance(o[1], int) else _resolve_of(s)(o[1])
        name = o[1] if not isinstance(o[1], int) else None
        if name is None:                    # '.±d' anchors itself
            lines2.append(render_mc(insn))
            at[i] = pos
            pos += 4
        elif d <= 0:                        # label at/before the insn
            lines2.append(f"{name}:")
            if d:
                lines2.append(f".space {-d}")
            lines2.append(render_mc(insn))
            at[i] = pos - d
            pos += -d + 4
        else:                               # label d bytes ahead
            lines2.append(render_mc(insn))
            if d > 4:
                lines2.append(f".space {d - 4}")
            lines2.append(f"{name}:")
            at[i] = pos
            pos += max(4, d)
    if rel:
        try:
            text = _llvm_mc_obj("\n".join(lines2) + "\n")
        except Exception as e:
            print(f"  FAIL obj oracle: {e}")
            return False
        for i, s in rel:
            got = encode(s[1], resolve=_resolve_of(s))
            want = text[at[i]:at[i] + 4]
            if got != want:
                print(f"  FAIL obj {render_mc(s[1])!r}: got {got.hex()} "
                      f"want {want.hex()}")
                ok = False
    return ok


def main() -> int:
    ok = check_rows()
    print(f"{'OK' if ok else 'FAIL'} isa_riscv64 "
          f"({len(ROW_SAMPLES)} samples vs llvm-mc)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
