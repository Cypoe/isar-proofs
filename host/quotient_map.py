"""
Phase 3: QuotientMap — dialect obligation is encode/decode only.

OperEq / host-piece NF is observational authority. No private dialect β.
Identity when the surface is already substrate (ITerm).
Reduce goes through host_pieces (Graph now; later loaders).
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Any, Callable, Optional, Tuple, TypeVar

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T  # noqa: E402
from host_pieces import HostPiece, default_piece, run_piece  # noqa: E402

S = TypeVar("S")
O = TypeVar("O")


@dataclass(frozen=True)
class QuotientMap:
    """encode surface → substrate ITerm; decode NF → observation."""

    name: str
    encode: Callable[[Any], T]
    decode: Callable[[T], Any]

    def encode_term(self, surface: Any) -> T:
        return self.encode(surface)

    def decode_obs(self, nf: T) -> Any:
        return self.decode(nf)


def identity_map(name: str = "identity") -> QuotientMap:
    """Surface already on substrate — OperEq observes directly."""
    return QuotientMap(name=name, encode=lambda t: t, decode=lambda t: t)


def observe(
    qm: QuotientMap,
    surface: Any,
    *,
    fuel: int = 100_000,
    piece: Optional[HostPiece] = None,
) -> Tuple[Any, T, int, int]:
    """
    decode(piece.reduce(encode(surface))).
    Default piece = host catalog Graph. Returns (obs, nf_tree, steps, alloc).
    """
    term = qm.encode(surface)
    p = piece if piece is not None else default_piece()
    nf, steps, alloc = run_piece(p, term, fuel=fuel)
    return qm.decode(nf), nf, steps, alloc


def obs_eq(a: Any, b: Any) -> bool:
    """Host observational equality (string form for display trees)."""
    return str(a) == str(b)


def main() -> int:
    from reduce import I, KK, app  # noqa: E402

    qm = identity_map()
    obs, nf, steps, n = observe(qm, app(I, KK))
    ok = obs_eq(obs, KK) and obs_eq(nf, KK)
    print(f"{'OK' if ok else 'FAIL'} identity observe via host_pieces I K => {obs} "
          f"(steps={steps} alloc={n})")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
