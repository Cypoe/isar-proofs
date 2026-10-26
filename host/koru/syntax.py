#!/usr/bin/env python3
"""koru.syntax — the `.k` surface layer (declared-not-realized).

The surface parses `.k` text into `KProg`.  No parser exists; the
Lean layer says the same thing honestly (`koruSurface.parse =
fun _ => none`).  This leg exists so the refusal is *named*, not
absent.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402


def parse(text: str):
    """`.k` source → `KProg`.  Refuses: no surface implementation."""
    raise NotRealized(
        "koru syntax: the .k surface is declared-not-realized; "
        "koruSurface.parse = fun _ => none in ISAR.KoruDialect")
