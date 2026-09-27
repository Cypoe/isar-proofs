"""
isa_fasmg — the x86-64 instruction layer realized as fasmg SOURCE text:
the same Program/label/i items isa_x86_64 encodes to bytes, rendered to
assembly mnemonics that a third-party assembler (fasmg, x64.inc) turns
into the same machine code.

Sibling of isa_c (C11 statements as data): a second syntactic surface
for identical instruction data.  Where isa_x86_64.assemble resolves
symbols numerically two-pass, this assemble emits symbolic references —
`("p", name)` -> `[name]`, `("l", name)` -> `near name` — and lets fasmg
do the fixups.  encode() renders one item; assemble() walks a Program
emitting `label:` lines plus indented mnemonics.

Verification is behavioral, not byte-exact: fasmg is free to pick a
different (still valid) encoding — e.g. imm8 group forms where our table
always emits imm32.  The gate is the emitted source assembling and the
resulting PE producing identical output on probes.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, List, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from isa_x86_64 import FORMS, LBL, I, Program  # noqa: E402


def _mem(m) -> str:
    """("m", base, disp) -> "[base+d]"  ("p", name) -> "[name]"."""
    if m[0] == "p":
        return f"[{m[1]}]"
    _, base, d = m
    if d == 0:
        return f"[{base}]"
    return f"[{base}+{d:#x}]" if d > 0 else f"[{base}-{-d:#x}]"


def encode(insn: Tuple, resolve=None) -> bytes:
    """Render one item (label or i-tuple) to an unindented source line."""
    if insn[0] == "label":
        return f"{insn[1]}:".encode()
    form, ops = insn[1], insn[2:]
    mnem = FORMS[form][0]

    if FORMS[form][4] == "l":                       # rel32 branch -> near lbl
        return f"{mnem} near {ops[0][1]}".encode()
    if form in ("call_mrip", "inc_mrip"):           # ("p", name) -> qword [name]
        return f"{mnem} qword {_mem(ops[0])}".encode()
    if form in ("mov_r64_rip", "lea_r64_rip"):
        return f"{mnem} {ops[0]}, qword {_mem(ops[1])}".encode()
    if form == "mov_rip_r64":
        return f"mov qword {_mem(ops[0])}, {ops[1]}".encode()
    if form == "mov_r64_imm":
        # B8+r io: keep the 64-bit immediate explicit so fasmg does not
        # shorten to a sign-extended imm32 form on small values
        return f"mov {ops[0]}, qword {ops[1] & 0xFFFFFFFFFFFFFFFF}".encode()
    if form == "mov_r32_imm32":
        return f"mov {ops[0]}, {ops[1] & 0xFFFFFFFF}".encode()
    if form == "movzx_r32_m8":
        return f"movzx {ops[0]}, byte {_mem(ops[1])}".encode()
    if form == "mov_r32_m32":
        return f"mov {ops[0]}, dword {_mem(ops[1])}".encode()
    if form == "mov_r8_m8":
        return f"mov {ops[0]}, byte {_mem(ops[1])}".encode()
    if form == "mov_m8_r8":
        return f"mov byte {_mem(ops[0])}, {ops[1]}".encode()
    if form == "mov_m8_imm8":
        return f"mov byte {_mem(ops[0])}, {ops[1]}".encode()
    if form == "mov_m64_imm32":
        return f"mov qword {_mem(ops[0])}, {ops[1]}".encode()
    if form in ("mov_r64_m64", "lea_r64_m64"):
        return f"{mnem} {ops[0]}, qword {_mem(ops[1])}".encode()
    if form == "mov_m64_r64":
        return f"mov qword {_mem(ops[0])}, {ops[1]}".encode()
    if form == "cmp_m64_imm":
        return f"cmp qword {_mem(ops[0])}, {ops[1]}".encode()
    if len(ops) == 0:
        return mnem.encode()
    if len(ops) == 1:
        return f"{mnem} {ops[0]}".encode()
    return f"{mnem} {ops[0]}, {ops[1]}".encode()


def assemble(program: Program, symbols: Dict[str, int],
             base: int = 0) -> Tuple[bytes, Dict[str, int]]:
    """Program -> (fasmg source text, label->ordinal table).

    `symbols`/`base` are accepted for the shared ISA contract and unused:
    resolution is symbolic — fasmg fixes up [name] and `near name`.  The
    returned label table maps each label to its item ordinal (nominal —
    byte offsets belong to fasmg's pass, not ours)."""
    lines: List[str] = []
    labels: Dict[str, int] = {}
    for i, item in enumerate(program):
        if item[0] == "label":
            if item[1] in labels:
                raise ValueError(f"duplicate label {item[1]!r}")
            labels[item[1]] = i
            lines.append(encode(item).decode())
        else:
            lines.append("    " + encode(item).decode())
    return ("\n".join(lines) + "\n").encode(), labels


@dataclass(frozen=True)
class ISA:
    name: str            # "x86_64.fasmg"
    bits: int
    insn: tuple
    fields: dict
    templates: dict
    encode: Callable     # encode(insn, resolve=None) -> bytes
    assemble: Callable   # assemble(program, symbols, base=0) -> (bytes, labels)
    render: Callable     # same as encode, str form


FASMG_X86_64 = ISA(
    name="x86_64.fasmg",
    bits=64,
    insn=(),
    fields={},
    templates={},
    encode=encode,
    assemble=assemble,
    render=lambda insn, resolve=None: encode(insn, resolve).decode(),
)


def main() -> int:
    """Smoke: render the win64 kernel Program to fasmg source."""
    import routines_x86_64_win64 as rts

    import seed
    R = seed.Realization()
    prog = rts.program(R)
    src, labels = assemble(prog, {}, 0)
    ok = all(isinstance(v, int) for v in labels.values())
    print(f"{'OK' if ok else 'FAIL'} isa_fasmg: "
          f"{len(src)}B source, {len(labels)} labels")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
