#!/usr/bin/env python3
"""koru.syntax — the `.k` surface layer.

The surface parses `.k` text into `KProg`.  No *host-side* parser
exists — the realized surface leg is `host2/src/korufe.c` (C99,
declared subset: `.k` → `program.ast.json` → `[flow-eval]` claim);
the Lean layer says the same honestly (`koruSurface.parse =
fun _ => none` — koru dialect is declared there, the frontend is a
bootstrap-leg realization).  This leg exists so the refusal is
*named*, not absent.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402


def parse(text: str):
    """`.k` source → `KProg`.  Refuses: no host-side parser."""
    raise NotRealized(
        "koru syntax: no parser in this mirror — the realized .k "
        "surface leg is host2/src/korufe.c (C99, declared subset); "
        "koruSurface.parse = fun _ => none in ISAR.KoruDialect")
