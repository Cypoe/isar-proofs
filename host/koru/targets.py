#!/usr/bin/env python3
"""koru.targets — registered emission backends, declared data.

A backend is a `KProg → Option<spelling>` row.  `c99` is the first
registered target — the bootstrap leg — realized in the Lean
dialect for a declared subset (`emitC99`, witnessed fixpoint
`koru_emit_fixpoint`).  The host mirror refuses to reimplement it:
witnesses stay independent, semantics lives in `src/ISAR/`.
Unregistered targets refuse by name.
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
        "spelling": "C99 source text (CompCert-accepted subset)",
        "role": "bootstrap backend — the two-pass chain's first leg",
        "status": "realized (subset) in ISAR.KoruDialect.emitC99",
    },
}


def emit(target: str, prog) -> str:
    """`KProg → Option<target spelling>`.  Unknown target names the
    axis; a registered backend refuses here because the realized
    emitter is the Lean dialect's — the host mirror holds no KProg
    objects and duplicates no evaluator (independent witnesses)."""
    row = BACKENDS.get(target)
    if row is None:
        raise NotRealized(
            f"koru emission: no backend registered for target "
            f"{target!r} (registered: {sorted(BACKENDS)})")
    raise NotRealized(
        f"koru emission: backend {target!r} is realized in "
        f"ISAR.KoruDialect.emitC99 (declared subset; fixpoint "
        f"witnessed by ISAR.KoruEmit.koru_emit_fixpoint) — host "
        f"mirror refuses to reimplement it")
