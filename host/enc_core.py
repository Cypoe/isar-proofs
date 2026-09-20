"""
enc_core — the ISA-generic encoding engine, extracted from isa_x86_64.

interpret() is the single ordered-alternatives loop shared by every ISA
table: named predicates select the first matching alternative, named
field ops produce the parts, and the caller injects the combiner.  The
combiner is the whole field model:

  x86-64   fields emit byte chunks          -> b"".join
  aarch64  fields emit (value, lsb, width)  -> word32

The core knows field/predicate NAMES only — no instruction, no ISA.
That two ISAs with different field models consume the same loop is the
G10 claim "core knows no ISA" made executable.
"""
from __future__ import annotations

import struct


def interpret(fields, preds, alts, ctx, combine):
    """First alternative whose named predicates all hold -> combine() of
    its named field ops.  No mnemonic, form, or operand-shape branching."""
    for conds, tmpl in alts:
        if all(preds[c[0]](ctx, *c[1:]) for c in conds):
            return combine([fields[f[0]](ctx, *f[1:]) for f in tmpl])
    raise ValueError(f"uncovered insn operands: {ctx.ops!r}")


def word32(parts) -> bytes:
    """Fixed-width combiner (aarch64): each part is a (value, lsb, width)
    bit-slice; slices OR-fold into one 32-bit little-endian word.

    Two assertions turn table bugs into exceptions rather than wrong
    bytes: every slice must fit its width, and no two contributions may
    set the same bit.  A row constant ("bits") is a full-width slice
    whose zero bits are the holes the variable fields occupy — so the
    overlap check is on set bits, which is exactly the disjoint-OR
    invariant of a fixed-width encoding.
    """
    word = 0
    for v, lsb, w in parts:
        assert 0 < w <= 32 and 0 <= lsb and lsb + w <= 32, (v, lsb, w)
        assert 0 <= v < (1 << w), (v, lsb, w)
        assert (v << lsb) & word == 0, (v, lsb, w, hex(word))
        word |= v << lsb
    return struct.pack("<I", word)
