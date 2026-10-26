#!/usr/bin/env python3
"""koru.grammar — the admissibility layer, declared.

`wfProg` lives in `src/ISAR/KoruDialect.lean`: a decidable check of
the static half of the walker's walls.  This module declares WHICH
walls the grammar layer owns — as a refusal catalogue — and refuses
to check Python-side objects until the AST leg exists (there is no
`.k` surface yet to produce `KProg` values host-side).
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402


# The static walls, mirroring wfProg/wfFlow/wfArms in
# ISAR.KoruDialect — the grammar layer refuses a program that hits
# any row, before evaluation ever runs.
WALLS = (
    ("entry",        "p.entry resolves in p.graph"),
    ("head",         "every flow head name resolves in graph"),
    ("invoke",       "every .invoke target resolves in graph"),
    ("jump",         "every .jump label equals its enclosing "
                     "flow's preLabel (nested-label wall, static)"),
)

# The dynamic walls the grammar does NOT own — these stay in runK
# and are refusals at evaluation, not admissibility.  Declared so
# the boundary is data, not folklore.
DYNAMIC = (
    "unasserted thunk leaf (oracle miss)",
    "unhandled branch (dispatchTag no-match)",
    "catchall/unnamed arm in bare dispatch",
    "void result + arms",
    "binding arm on payload-less result",
    "guard errors or non-bool",
    "type error in expr eval",
    "fuel exhausted",
)


def wf_prog(prog) -> bool:
    """Refused: there is no Python-side KProg to check — the AST
    layer is unrealized (see `syntax`).  The grammar's contract is
    `WALLS` above; the checker itself is `wfProg` in
    ISAR.KoruDialect."""
    raise NotRealized(
        "koru grammar: no host-side KProg exists in this mirror "
        "(.k sources lower to claims in host2/src/korufe.c, not to "
        "Python objects); the decidable check is wfProg in "
        "ISAR.KoruDialect")
