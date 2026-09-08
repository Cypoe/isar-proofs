"""
Phase 3–4: Host pieces catalog — parametric runnable fragments.

Graph reduce ships by default. CoGen emit registers loaders into this catalog;
dialects never own hardware.
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
    kind: str  # "graph" | "cpu" | "simd" | "gpu" | …
    reduce: Callable[[T, int], Tuple[T, int, int]]
    # Returns (nf, steps_or_rounds, alloc_or_nodes)


def _graph_reduce(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    g = Graph()
    root = g.import_tree(t)
    nf_i, steps = g.reduce(root, fuel=fuel)
    return g.export_tree(nf_i), steps, g.alloc_count()


GRAPH_PIECE = HostPiece(name="graph.lo", kind="graph", reduce=_graph_reduce)

_REGISTERED: Dict[str, HostPiece] = {}


def register_piece(piece: HostPiece) -> None:
    """CoGen emit / tests register loaders here."""
    _REGISTERED[piece.name] = piece


def clear_registered() -> None:
    _REGISTERED.clear()


def catalog() -> List[HostPiece]:
    """Base graph piece plus any CoGen-registered loaders."""
    out: Dict[str, HostPiece] = {"graph.lo": GRAPH_PIECE}
    out.update(_REGISTERED)
    return list(out.values())


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
    assert any(p.name == "graph.lo" for p in pieces)
    nf, steps, n = run_piece(default_piece(), app(I, KK))
    ok = str(nf) == "K"
    print(f"{'OK' if ok else 'FAIL'} host_pieces graph I K => {nf} (steps={steps} alloc={n})")
    print(f"catalog: {[p.name for p in pieces]} (CoGen may register more)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
