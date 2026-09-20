"""
isa_aarch64 — pure AArch64 ISA data + table-driven encoder + assembler.

Second consumer of the enc_core.interpret loop (G10): where isa_x86_64
fields emit byte chunks joined by b"".join, aarch64 fields emit
(value, lsb, width) bit-slices folded by enc_core.word32.  Fixed-width:
every insn is exactly 4 bytes; a row's "bits" field contributes the
constant opcode template and the named fields fill its zero-holes.

Register model: x0..x30 / w0..w30 plus sp and xzr/wzr operand strings.
Encoding 31 is shared — SP for rn/rd of add/sub-immediate and the
load/store base register, XZR/WZR everywhere else (moves, shifted-
register operands, and rd of the flag-setting adds/subs — the cmn/cmp
aliases).  The operand string names the role; _reg() maps "sp" and
"xzr"/"wzr" to 31 alike and each form documents which role its 31
means.  Missing optional operands default: ret -> x30, shifts -> lsl#0,
load/store offset -> 0.

Branch displacement is target - branch_addr (aarch64 counts from the
branch's own address, unlike x86 rip which counts from insn end) —
assemble()'s resolver reflects that; the "rel" field scales >>2.

Oracle: llvm-mc -triple=aarch64 (env ISAR_LLVM_MC) — see check_rows() /
main().  -show-encoding prints concrete bytes for non-branch encodings;
for rel fields it prints symbolic fixup slots, so check_rows masks to
the concrete bits, asserts the fixup kind/delta, and adds a second
-filetype=obj pass (llvm-objcopy .text) where same-section targets
resolve — true byte equality on the immediate value too.  Missing
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
    """llvm-mc -triple=aarch64 -show-encoding on stdin asm text.

    Returns one entry per instruction line: (bytespec, fixup) where
    bytespec is four (mask, value) pairs — concrete '0xHH' contributes
    (0xFF, HH), a symbolic fixup slot 'A' contributes (0, 0), a mixed
    '0bAAA00000' contributes its concrete-bit mask/value — and fixup is
    (kind, value-string) or None."""
    if not _exists(LLVM_MC):
        raise FileNotFoundError(f"llvm-mc oracle missing: {LLVM_MC}")
    cp = subprocess.run([LLVM_MC, "-triple=aarch64", "-show-encoding"],
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
    """One encoding-list entry -> (concrete-bit mask, concrete value)."""
    if tok.startswith("0x"):
        return 0xFF, int(tok, 16)
    if tok == "A":
        return 0, 0
    if tok.startswith("0b"):
        mask = val = 0
        for ch in tok[2:]:
            mask, val = mask << 1, val << 1
            if ch in "01":
                mask |= 1
                val |= int(ch)
            elif ch != "A":
                raise ValueError(f"bad encoding byte {tok!r}")
        return mask, val
    raise ValueError(f"bad encoding byte {tok!r}")


def _llvm_mc_obj(src: str) -> bytes:
    """Assemble src to an ELF object and return its .text bytes.

    -show-encoding leaves PC-relative fields as symbolic fixups even
    when the target is in the same section; the object pass resolves
    them, giving the oracle's ground truth for the rel immediate value
    (the >>2 scaling and two's-complement packing the text pass cannot
    see)."""
    for tool in (LLVM_MC, LLVM_OBJCOPY):
        if not _exists(tool):
            raise FileNotFoundError(f"llvm oracle tool missing: {tool}")
    with tempfile.TemporaryDirectory() as td:
        obj = os.path.join(td, "in.o")
        binp = os.path.join(td, "out.bin")
        cp = subprocess.run([LLVM_MC, "-triple=aarch64", "-filetype=obj",
                             "-o", obj], input=src, capture_output=True,
                            text=True)
        if cp.returncode != 0 or not os.path.exists(obj):
            raise RuntimeError(f"llvm-mc obj failed rc={cp.returncode}: "
                               f"{cp.stdout}{cp.stderr}")
        cp = subprocess.run([LLVM_OBJCOPY, "--only-section=.text",
                             "-O", "binary", obj, binp],
                            capture_output=True, text=True)
        if cp.returncode != 0 or not os.path.exists(binp):
            raise RuntimeError(f"llvm-objcopy failed rc={cp.returncode}: "
                               f"{cp.stdout}{cp.stderr}")
        with open(binp, "rb") as f:
            return f.read()


# ======================================================================
# ISA DATA (aarch64, authored from ARM ARM; each row oracle-checked)
# ======================================================================

# Encoding 31 is shared: SP in rn/rd of add/sub-immediate and the
# load/store base; XZR/WZR elsewhere.  See the module docstring.
def _reg(name: str) -> int:
    if name in ("sp", "xzr", "wzr"):
        return 31
    if name[:1] in ("x", "w") and name[1:].isdigit():
        n = int(name[1:])
        if 0 <= n <= 30:
            return n
    raise ValueError(f"bad register {name!r}")


CONDS: Dict[str, int] = {
    "eq": 0, "ne": 1, "cs": 2, "hs": 2, "cc": 3, "lo": 3, "mi": 4,
    "pl": 5, "vs": 6, "vc": 7, "hi": 8, "ls": 9, "ge": 10, "lt": 11,
    "gt": 12, "le": 13, "al": 14, "nv": 15,
}

SHIFTS: Dict[str, int] = {"lsl": 0, "lsr": 1, "asr": 2}

# INSN rows: (form, mnemonic, base) — base is the row's constant bit
# template; its zero bits are the holes the ENCS fields fill.  Rendered
# mnemonic for bcond_rel gains a ".<cond>" suffix.
INSN: Tuple[Tuple[str, str, int], ...] = (
    ("nop",       "nop",  0xD503201F),
    ("ret",       "ret",  0xD65F0000),
    ("svc_imm16", "svc",  0xD4000001),
    ("mov_reg",   "mov",  0x2A0003E0),   # orr Rd, xzr, Rm (lsl #0)
    ("movz",      "movz", 0x52800000),
    ("movn",      "movn", 0x12800000),
    ("movk",      "movk", 0x72800000),
    ("add_imm",   "add",  0x11000000),
    ("sub_imm",   "sub",  0x51000000),
    ("adds_imm",  "adds", 0x31000000),   # rd=xzr -> cmn
    ("subs_imm",  "subs", 0x71000000),   # rd=xzr -> cmp
    ("add_reg",   "add",  0x0B000000),
    ("sub_reg",   "sub",  0x4B000000),
    ("orr_reg",   "orr",  0x2A000000),
    ("and_reg",   "and",  0x0A000000),
    ("eor_reg",   "eor",  0x4A000000),
    ("ldr_uoff",  "ldr",  0x39400000),   # size field via "opc"
    ("str_uoff",  "str",  0x39000000),
    ("b_rel",     "b",    0x14000000),
    ("bl_rel",    "bl",   0x94000000),
    ("bcond_rel", "b",    0x54000000),   # rendered b.<cond>
    ("cbz_rel",   "cbz",  0x34000000),
    ("cbnz_rel",  "cbnz", 0x35000000),
)
FORMS: Dict[str, Tuple[str, int]] = {r[0]: r[1:] for r in INSN}

# Insn datum: (form, *operands).  Branch operand: ("p", label|int) — int
# is the byte offset target - branch_addr.  Shift operand for shifted-
# register forms: ("shift", "lsl"|"lsr"|"asr", imm6); omitted = lsl #0.
Insn = Tuple


# ======================================================================
# ENCODING TEMPLATES (aarch64 row data)
#
# ENCS[form] = ordered alternatives; the first whose PREDS all hold is
# emitted as the word32-fold of its FIELDS ops.  Field ops carry operand
# roles as in x86-64: rd/rn/rm/rt<i> name ops[i] by use, imm/rel/hw/sh
# take width/lsb/scale from the row.  The isw/isx alternatives prove
# width selection is row data, not core branching.
# ======================================================================

_MOVW = (("bits",), ("sf", 0), ("hw", 2), ("imm", 16, 5, 1), ("rd", 0))
_MOVW_ALTS = (
    ((("isw", 0), ("hwle16", 2)), _MOVW),      # w regs: lsl <= 16 only
    ((("isx", 0),),                 _MOVW),
)

_ADDI = (("bits",), ("sf", 0), ("sh", 3), ("imm", 12, 10, 2),
         ("rn", 1), ("rd", 0))
_ADDI_ALTS = (
    ((("sh01", 3), ("fits", 12, 2)), _ADDI),
)

_SHREG = (("bits",), ("sf", 0), ("shk", 3), ("rm", 2), ("sh6", 3),
          ("rn", 1), ("rd", 0))
_SHREG_ALTS = (
    ((("isw", 0), ("sh6le31", 3)), _SHREG),    # w regs: imm6 <= 31
    ((("isx", 0),),                  _SHREG),
)

_LDST = (
    ((("isx", 0),), (("bits",), ("opc", 3, 30, 2), ("imm", 12, 10, 2, 8),
                    ("rn", 1), ("rt", 0))),
    ((("isw", 0),), (("bits",), ("opc", 2, 30, 2), ("imm", 12, 10, 2, 4),
                    ("rn", 1), ("rt", 0))),
)

_CBZ = (("bits",), ("sf", 0), ("rel", 1, 19, 5), ("rt", 0))

ENCS: Dict[str, Tuple] = {
    "nop":       (((), (("bits",),)),),
    "ret":       (((), (("bits",), ("rn", 0, "x30"))),),
    "svc_imm16": (((("fits", 16, 0),), (("bits",), ("imm", 16, 5, 0))),),
    "mov_reg":   (((), (("bits",), ("sf", 0), ("rm", 1), ("rd", 0))),),
    "movz":      _MOVW_ALTS,
    "movn":      _MOVW_ALTS,
    "movk":      _MOVW_ALTS,
    "add_imm":   _ADDI_ALTS,
    "sub_imm":   _ADDI_ALTS,
    "adds_imm":  _ADDI_ALTS,
    "subs_imm":  _ADDI_ALTS,
    "add_reg":   _SHREG_ALTS,
    "sub_reg":   _SHREG_ALTS,
    "orr_reg":   _SHREG_ALTS,
    "and_reg":   _SHREG_ALTS,
    "eor_reg":   _SHREG_ALTS,
    "ldr_uoff":  _LDST,
    "str_uoff":  _LDST,
    "b_rel":     (((("sfits", 26, 0),), (("bits",), ("rel", 0, 26, 0))),),
    "bl_rel":    (((("sfits", 26, 0),), (("bits",), ("rel", 0, 26, 0))),),
    "bcond_rel": (((("sfits", 19, 1),),
                   (("bits",), ("rel", 1, 19, 5), ("cond", 0))),),
    "cbz_rel":   (((("sfits", 19, 1),), _CBZ),),
    "cbnz_rel":  (((("sfits", 19, 1),), _CBZ),),
}


# ======================================================================
# FIELD + PREDICATE VOCABULARY (aarch64) — the named ops ENCS references.
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


def _f_bits(ctx: _Ctx) -> Tuple[int, int, int]:
    """Row constant: full-width slice; its zero bits are the field holes."""
    return ctx.base, 0, 32


def _f_opc(ctx: _Ctx, v: int, lsb: int, w: int) -> Tuple[int, int, int]:
    """Row-data opcode bits differing across a form family (e.g. the
    load/store size field — selected by the isw/isx alternatives)."""
    return v, lsb, w


def _f_sf(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    """Operand width bit: x*/sp -> 1, w* -> 0."""
    return (0 if ctx.ops[i].startswith("w") else 1), 31, 1


def _f_rd(ctx: _Ctx, i: int, default=None) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i, default)), 0, 5


def _f_rt(ctx: _Ctx, i: int, default=None) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i, default)), 0, 5


def _f_rn(ctx: _Ctx, i: int, default=None) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i, default)), 5, 5


def _f_rm(ctx: _Ctx, i: int, default=None) -> Tuple[int, int, int]:
    return _reg(_op(ctx, i, default)), 16, 5


def _f_imm(ctx: _Ctx, w: int, lsb: int, i: int, scale: int = 1,
           default: int = 0) -> Tuple[int, int, int]:
    """Unsigned immediate ops[i] (or `default` when absent) into
    bits[lsb, lsb+w); `scale` divides the operand first (scaled load/
    store offsets) and asserts divisibility."""
    v = _op(ctx, i, default)
    assert v % scale == 0, f"imm {v} not divisible by {scale}"
    v //= scale
    assert 0 <= v < (1 << w), f"imm {v} does not fit {w} bits"
    return v, lsb, w


def _f_hw(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    """movz/movn/movk shift: ops[i] in {0,16,32,48} -> hw = ops[i]/16.
    The w-reg hw<=16 restriction is a PREDS alternative, not this field."""
    s = _op(ctx, i, 0)
    assert s % 16 == 0 and 0 <= s // 16 < 4, f"bad hw shift {s}"
    return s // 16, 21, 2


def _f_cond(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    return CONDS[ctx.ops[i]], 0, 4


def _reld(ctx: _Ctx, i: int) -> int:
    """Branch operand -> byte offset target - branch_addr."""
    o = ctx.ops[i]
    assert o[0] == "p", o
    if isinstance(o[1], int):
        return o[1]
    return ctx.resolve(o[1]) if ctx.resolve else 0


def _f_rel(ctx: _Ctx, i: int, w: int, lsb: int) -> Tuple[int, int, int]:
    """PC-rel immediate: byte offset >> 2, two's complement in w bits.
    b/bl w=26 lsb=0; b.cond/cbz/cbnz w=19 lsb=5."""
    d = _reld(ctx, i)
    assert d % 4 == 0, f"rel offset {d} not 4-aligned"
    v = d >> 2
    assert -(1 << (w - 1)) <= v < (1 << (w - 1)), \
        f"rel {d} out of {w}-bit range"
    return v & ((1 << w) - 1), lsb, w


def _f_sh(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    """add/sub-imm12 shift bit: ops[i] in {0,12} -> 1 bit at lsb 22."""
    s = _op(ctx, i, 0)
    assert s in (0, 12), f"bad imm12 shift {s}"
    return s // 12, 22, 1


def _shiftop(ctx: _Ctx, i: int) -> Tuple:
    o = _op(ctx, i, ("shift", "lsl", 0))
    assert o[0] == "shift" and o[1] in SHIFTS, o
    return o


def _f_shk(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    """Shifted-register shift kind (lsl/lsr/asr) -> 2 bits at lsb 22."""
    return SHIFTS[_shiftop(ctx, i)[1]], 22, 2


def _f_sh6(ctx: _Ctx, i: int) -> Tuple[int, int, int]:
    """Shifted-register shift amount -> imm6 at lsb 10 (w-reg <=31 bound
    is a PREDS alternative)."""
    n = _shiftop(ctx, i)[2]
    assert 0 <= n < 64, f"bad shift amount {n}"
    return n, 10, 6


FIELDS: Dict[str, Callable[..., Tuple[int, int, int]]] = {
    "bits": _f_bits, "opc": _f_opc, "sf": _f_sf,
    "rd": _f_rd, "rn": _f_rn, "rm": _f_rm, "rt": _f_rt,
    "imm": _f_imm, "hw": _f_hw, "cond": _f_cond, "rel": _f_rel,
    "sh": _f_sh, "shk": _f_shk, "sh6": _f_sh6,
}


def _p_isw(ctx: _Ctx, i: int) -> bool:
    return ctx.ops[i].startswith("w")


def _p_sfits(ctx: _Ctx, w: int, i: int) -> bool:
    """Signed rel range: ops[i] is a ("p", …) operand."""
    d = _reld(ctx, i)
    v = d >> 2
    return d % 4 == 0 and -(1 << (w - 1)) <= v < (1 << (w - 1))


PREDS: Dict[str, Callable[..., bool]] = {
    "fits":    lambda ctx, w, i, scale=1:
               _op(ctx, i) % scale == 0
               and 0 <= _op(ctx, i) // scale < (1 << w),
    "sfits":   _p_sfits,                            # signed (rel fields)
    "isw":     _p_isw,                              # w-register operand
    "isx":     lambda ctx, i: not _p_isw(ctx, i),   # x/sp/xzr operand
    "sh01":    lambda ctx, i: _op(ctx, i, 0) in (0, 12),
    "hwle16":  lambda ctx, i: _op(ctx, i, 0) <= 16,
    "sh6le31": lambda ctx, i: _shiftop(ctx, i)[2] <= 31,
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
    """Mnemonic text for the oracle (one line of aarch64 asm).
    Integer rel operands render '.+d'/'.-d' — llvm-mc reports the delta
    in the fixup annotation; label operands render the label name."""
    form, ops = insn[0], insn[1:]
    m = FORMS[form][0]

    def tgt(o) -> str:
        return f".{o[1]:+d}" if isinstance(o[1], int) else o[1]

    if form == "nop":
        return "nop"
    if form == "ret":
        return f"ret {ops[0]}" if ops else "ret"
    if form == "svc_imm16":
        return f"svc #{ops[0]}"
    if form == "mov_reg":
        return f"mov {ops[0]}, {ops[1]}"
    if form in ("movz", "movn", "movk"):
        s = ops[2] if len(ops) > 2 else 0
        return f"{m} {ops[0]}, #{ops[1]}" + (f", lsl #{s}" if s else "")
    if form in ("add_imm", "sub_imm", "adds_imm", "subs_imm"):
        s = ops[3] if len(ops) > 3 else 0
        return f"{m} {ops[0]}, {ops[1]}, #{ops[2]}" \
            + (f", lsl #{s}" if s else "")
    if form in ("add_reg", "sub_reg", "orr_reg", "and_reg", "eor_reg"):
        t = f"{m} {ops[0]}, {ops[1]}, {ops[2]}"
        sh = ops[3] if len(ops) > 3 else ("shift", "lsl", 0)
        if sh[1] != "lsl" or sh[2]:
            t += f", {sh[1]} #{sh[2]}"
        return t
    if form in ("ldr_uoff", "str_uoff"):
        off = ops[2] if len(ops) > 2 else 0
        return f"{m} {ops[0]}, [{ops[1]}" + (f", #{off}" if off else "") \
            + "]"
    if form in ("b_rel", "bl_rel"):
        return f"{m} {tgt(ops[0])}"
    if form == "bcond_rel":
        return f"b.{ops[0]} {tgt(ops[1])}"
    if form in ("cbz_rel", "cbnz_rel"):
        return f"{m} {ops[0]}, {tgt(ops[1])}"
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
    local labels.  The resolver returns target - insn_addr (aarch64
    counts branch displacement from the branch's own address — x86's
    rip counts from insn end; the stride difference lives here, not in
    the field engine)."""
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
        resolver = lambda name, _a=at: (
            symbols[name] if name in symbols else local[name]) - _a
        out += encode(insn, resolve=resolver)
    return bytes(out), local


@dataclass(frozen=True)
class ISA:
    name: str            # "aarch64"
    bits: int            # 64
    insn: tuple          # INSN rows
    fields: dict         # FIELDS — per-ISA field vocabulary
    templates: dict      # ENCS — per-form encoding alternatives
    encode: Callable     # encode(insn, resolve=None) -> bytes
    assemble: Callable   # assemble(program, symbols, base=0) -> (bytes, labels)
    render: Callable     # render_mc


AARCH64 = ISA(
    name="aarch64",
    bits=64,
    insn=INSN,
    fields=FIELDS,
    templates=ENCS,
    encode=encode,
    assemble=assemble,
    render=render_mc,
)


# ======================================================================
# Oracle: llvm-mc per-row byte equality
# ======================================================================

# (form, insn[, resolve]) — resolve maps label operands to the byte
# offset the check_rows label frame places them at.
ROW_SAMPLES: List[Tuple] = [
    ("nop", ("nop",)),
    ("ret", ("ret",)),
    ("ret", ("ret", "x5")),
    ("ret", ("ret", "x0")),
    ("svc_imm16", ("svc_imm16", 0)),
    ("svc_imm16", ("svc_imm16", 0x8000)),
    ("svc_imm16", ("svc_imm16", 0xFFFF)),
    ("mov_reg", ("mov_reg", "x3", "x5")),
    ("mov_reg", ("mov_reg", "w0", "w1")),
    ("mov_reg", ("mov_reg", "x30", "x29")),
    ("movz", ("movz", "x3", 4660, 16)),
    ("movz", ("movz", "w3", 0x1234)),
    ("movz", ("movz", "x0", 0xFFFF, 48)),
    ("movz", ("movz", "w7", 0x8000, 16)),      # max lsl for w
    ("movn", ("movn", "w7", 0xABCD)),
    ("movn", ("movn", "x9", 1, 32)),
    ("movk", ("movk", "x9", 0xFFFF, 48)),
    ("movk", ("movk", "w2", 0x1234, 16)),
    ("add_imm", ("add_imm", "x0", "x1", 5)),
    ("add_imm", ("add_imm", "w2", "w3", 0)),
    ("add_imm", ("add_imm", "x0", "x1", 5, 12)),
    ("add_imm", ("add_imm", "sp", "sp", 32)),
    ("add_imm", ("add_imm", "x4", "x5", 4095)),  # imm12 max
    ("sub_imm", ("sub_imm", "sp", "sp", 16)),
    ("sub_imm", ("sub_imm", "w6", "w7", 100, 12)),
    ("adds_imm", ("adds_imm", "xzr", "x0", 5)),    # cmn x0, #5
    ("adds_imm", ("adds_imm", "x8", "x9", 0xABC, 12)),
    ("subs_imm", ("subs_imm", "wzr", "w1", 4095)),  # cmp w1, #4095
    ("subs_imm", ("subs_imm", "xzr", "sp", 64)),
    ("add_reg", ("add_reg", "x0", "x1", "x2")),
    ("add_reg", ("add_reg", "x2", "x3", "x4", ("shift", "asr", 7))),
    ("add_reg", ("add_reg", "w0", "w1", "w2", ("shift", "lsl", 31))),
    ("sub_reg", ("sub_reg", "x5", "x6", "x7", ("shift", "lsr", 33))),
    ("sub_reg", ("sub_reg", "w8", "w9", "w10")),
    ("orr_reg", ("orr_reg", "w0", "w1", "w2", ("shift", "lsr", 5))),
    ("orr_reg", ("orr_reg", "x11", "xzr", "x12")),  # orr x11, xzr, x12
    ("and_reg", ("and_reg", "x10", "x11", "x12")),
    ("eor_reg", ("eor_reg", "x13", "x14", "x15", ("shift", "lsl", 63))),
    ("eor_reg", ("eor_reg", "w13", "w14", "w15", ("shift", "asr", 1))),
    ("ldr_uoff", ("ldr_uoff", "x0", "sp", 32)),
    ("ldr_uoff", ("ldr_uoff", "w4", "x5")),
    ("ldr_uoff", ("ldr_uoff", "x9", "x10", 32760)),  # 8*4095 max
    ("str_uoff", ("str_uoff", "w2", "x3", 8)),
    ("str_uoff", ("str_uoff", "x30", "sp", 16)),
    ("str_uoff", ("str_uoff", "wzr", "x1", 16380)),  # 4*4095 max
    ("b_rel", ("b_rel", ("p", 8))),
    ("b_rel", ("b_rel", ("p", -4))),
    ("b_rel", ("b_rel", ("p", 0))),
    ("b_rel", ("b_rel", ("p", "Lfwd")), {"Lfwd": 16}),
    ("b_rel", ("b_rel", ("p", "Lback")), {"Lback": -16}),
    ("bl_rel", ("bl_rel", ("p", 16))),
    ("bl_rel", ("bl_rel", ("p", -8))),
    ("bcond_rel", ("bcond_rel", "eq", ("p", 12))),
    ("bcond_rel", ("bcond_rel", "ne", ("p", -16))),
    ("bcond_rel", ("bcond_rel", "hs", ("p", "Lc")), {"Lc": 20}),
    ("bcond_rel", ("bcond_rel", "al", ("p", 4))),
    ("cbz_rel", ("cbz_rel", "x0", ("p", -8))),
    ("cbz_rel", ("cbz_rel", "w6", ("p", 8))),
    ("cbnz_rel", ("cbnz_rel", "x30", ("p", 0))),
    ("cbnz_rel", ("cbnz_rel", "wzr", ("p", 4096))),
]

_REL_OPS = {"b_rel": 0, "bl_rel": 0, "bcond_rel": 1, "cbz_rel": 1,
            "cbnz_rel": 1}
_FIXUP_KIND = {"b_rel": "fixup_aarch64_pcrel_branch26",
               "bl_rel": "fixup_aarch64_pcrel_call26",
               "bcond_rel": "fixup_aarch64_pcrel_branch19",
               "cbz_rel": "fixup_aarch64_pcrel_branch19",
               "cbnz_rel": "fixup_aarch64_pcrel_branch19"}


def _rel_target(insn) -> Tuple:
    o = insn[1 + _REL_OPS[insn[0]]]
    return o


def _resolve_of(sample) -> Optional[Callable]:
    if len(sample) > 2:
        rmap = sample[2]
        return lambda name: rmap[name]
    return None


def check_rows() -> bool:
    """llvm-mc oracle on every ROW_SAMPLES entry.

    Pass 1 (-show-encoding): per-insn byte equality on the concrete
    bits; symbolic fixup slots are masked out, but the fixup kind must
    match the form and the reported delta must match our operand (the
    'A' positions are proven by pass 2).

    Pass 2 (-filetype=obj + objcopy .text): label/int targets resolve
    inside the object — byte equality on the whole word, i.e. the
    oracle also sees the >>2-scaled two's-complement immediate value."""
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
    print(f"{'OK' if ok else 'FAIL'} isa_aarch64 "
          f"({len(ROW_SAMPLES)} samples vs llvm-mc)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
