#!/usr/bin/env python3
"""koru.encoding — the tagged-tree codec table for the K grammar.

Mirrors `src/ISAR/FlowView.lean` (`encVal`/`encExpr`/`encArmNode`/
`encArm`/`encHead`/`encFlow`/`encCallable`/`encProg`) as declared
data — the tag assignment is the wire format, and the wire format
is a table, not an algorithm.

Tree shape (identical to FlowView): tags are right-leaning
`I`-spines `tn n`; lists are `K`-headed cons cells over an `S` nil;
a datum is `app (tn tag) (encList kids)`.  Tag/cons disjointness is
structural.  `none`/`some` are ordinary tags 23/24.

The codec itself (encode/decode + round-trip) is proved in Lean;
this module does not re-implement it — the table exists for hosts
that construct or inspect encoded trees by tag.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402


# --- datum tags: node tag kids --------------------------------------

TAG = {
    # KVal
    "val.int": 1, "val.float": 2, "val.bool": 3, "val.str": 4,
    "val.arr": 5, "val.cell": 6, "val.field": 7,
    # KExpr
    "expr.lit": 8, "expr.var": 9, "expr.bin": 10, "expr.un": 11,
    "expr.cond": 12, "expr.field": 13, "expr.index": 14,
    "expr.builtin": 15,
    # KArmNode
    "node.terminal": 16, "node.jump": 17, "node.invoke": 18,
    "node.produce": 19, "node.retCtor": 20,
    # pairs / arm / option / flow / head / callable / prog
    "pair.namedExpr": 21, "arm": 22,
    "opt.none": 23, "opt.some": 24,
    "flow": 25, "head": 26,
    "callable.bare": 27, "callable.thunk": 28, "callable.subflow": 29,
    "prog": 30, "pair.namedCallable": 31,
}

# --- operator tags ----------------------------------------------------

BINOP = {
    "add": 0, "sub": 1, "mul": 2, "div": 3, "mod": 4,
    "eq": 5, "ne": 6, "lt": 7, "le": 8, "gt": 9, "ge": 10,
    "and": 11, "or": 12, "concat": 13,
}

UNOP = {"neg": 0, "not": 1}

# --- the builtin table (name → arity shape; semantics is Lean-side) ---

BUILTINS = {
    "as": (2, "skip first arg — type name is not evaluated"),
    "intCast": (1, "int identity"),
    "truncate": (1, "int identity"),
    "divTrunc": (2, "Int, trunc toward zero; b=0 refuses"),
    "rem": (2, "Int, ktmod; b=0 refuses"),
    "mod": (2, "Int, kfmod floor; b=0 refuses"),
}


def encode(prog) -> object:
    """`KProg → TTerm`.  Refused on the Python side: the encoder is
    the proved Lean artefact (`encProg`); this host does not get a
    second, unproved codec."""
    raise NotRealized(
        "koru encoding: the codec is proved in ISAR.FlowView "
        "(encProg/decProg); no Python re-implementation — use the "
        "tag table to inspect, not to re-encode")


def decode(tree) -> object:
    """`TTerm → Option KProg`.  Same refusal as `encode`."""
    raise NotRealized(
        "koru encoding: the decoder is proved in ISAR.FlowView "
        "(decProg, refusal-as-value); no Python re-implementation")
