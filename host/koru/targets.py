#!/usr/bin/env python3
"""koru.targets — registered emission backends, declared data.

A backend is a `KProg → Option<spelling>` row.  `c99` is the first
registered target — the bootstrap leg — and emits nothing until
the emission row lands.  Unregistered targets refuse by name;
registered-but-unrealized targets refuse naming the backend.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402


# Registered backend rows — the registry is data; adding a row is
# declaring intent + its refusal path, per the toolchain contract.
BACKENDS = {
    "c99": {
        "spelling": "C99 source text",
        "role": "bootstrap backend — the two-pass chain's first leg",
        "status": "declared",
    },
}


def emit(target: str, prog) -> str:
    """`KProg → Option<target spelling>`.  Both refusal shapes:
    unknown target names the axis; known-but-unrealized names the
    backend row."""
    row = BACKENDS.get(target)
    if row is None:
        raise NotRealized(
            f"koru emission: no backend registered for target "
            f"{target!r} (registered: {sorted(BACKENDS)})")
    raise NotRealized(
        f"koru emission: backend {target!r} is declared-not-realized "
        f"({row['role']}); koruC99.emit = fun _ => none in "
        f"ISAR.KoruDialect")
