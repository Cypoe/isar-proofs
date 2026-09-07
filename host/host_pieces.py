"""
Phase 3: Host pieces catalog — parametric runnable fragments.

Phase 3 ships Graph reduce only. Later CoGen may emit loaders
(CPU / SIMD / GPU) into this catalog; dialects never own hardware.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T  # noqa: E402
from graph_runtime import Graph  # noqa: E402


@dataclass(frozen=True)
class HostPiece:
    """A runnable fragment available on this host."""

    name: str
    kind: str  # "graph" now; later "simd" | "gpu" | …
    reduce: Callable[[T, int], Tuple[T, int, int]]
    # Returns (nf, steps_or_rounds, alloc_or_nodes)


def _graph_reduce(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    g = Graph()
    root = g.import_tree(t)
    nf_i, steps = g.reduce(root, fuel=fuel)
    return g.export_tree(nf_i), steps, g.alloc_count()


GRAPH_PIECE = HostPiece(name="graph.lo", kind="graph", reduce=_graph_reduce)


def catalog() -> List[HostPiece]:
    """Pieces available on this host (Graph only in Phase 3)."""
    return [GRAPH_PIECE]


def by_name(name: str) -> Optional[HostPiece]:
    for p in catalog():
        if p.name == name:
            return p
    return None


def default_piece() -> HostPiece:
    return GRAPH_PIECE


def run_piece(piece: HostPiece, t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    return piece.reduce(t, fuel)


def main() -> int:
    from reduce import I, KK, app  # noqa: E402

    pieces = catalog()
    assert len(pieces) == 1 and pieces[0].kind == "graph"
    nf, steps, n = run_piece(default_piece(), app(I, KK))
    ok = str(nf) == "K"
    print(f"{'OK' if ok else 'FAIL'} host_pieces graph I K => {nf} (steps={steps} alloc={n})")
    print(f"catalog: {[p.name for p in pieces]} (later: simd/gpu loaders)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
