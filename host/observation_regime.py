"""
Admissible observation regime (host mirror of ISAR.ObservationRegime).

p1 ∼_O p2  iff  ObsEq(observe(p1), observe(p2)).

Primary instance: oper_eq_regime — NF via host piece (OperEq stand-in).
Dialect QuotientMaps preserve a declared regime; they do not invent ∼.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Any, Callable, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, I, KK, app  # noqa: E402
from host_pieces import HostPiece, default_piece, run_piece  # noqa: E402


@dataclass(frozen=True)
class ObservationRegime:
    """Bundled observers on a presentation type (Lean ObservationRegime)."""

    name: str
    observe: Callable[[Any], Any]
    obs_eq: Callable[[Any, Any], bool]

    def sim(self, p1: Any, p2: Any) -> bool:
        """p1 ∼_O p2."""
        return self.obs_eq(self.observe(p1), self.observe(p2))


def _nf_observe(t: T, *, piece: Optional[HostPiece] = None, fuel: int = 100_000) -> T:
    p = piece if piece is not None else default_piece()
    nf, _, _ = run_piece(p, t, fuel=fuel)
    return nf


def oper_eq_regime(*, piece: Optional[HostPiece] = None) -> ObservationRegime:
    """
    Primary ISAR regime: observe substrate terms by NF (OperEq class stand-in).
    """
    return ObservationRegime(
        name="operEq",
        observe=lambda t: _nf_observe(t, piece=piece),
        obs_eq=lambda a, b: str(a) == str(b),
    )


def encoding_regime(
    encode: Callable[[Any], T],
    *,
    piece: Optional[HostPiece] = None,
    name: str = "encoding.operEq",
) -> ObservationRegime:
    """
    Regime on presentations: observe via NF of encode(p) under OperEq stand-in.
    """
    base = oper_eq_regime(piece=piece)
    return ObservationRegime(
        name=name,
        observe=lambda p: base.observe(encode(p)),
        obs_eq=base.obs_eq,
    )


def main() -> int:
    R = oper_eq_regime()
    t1 = app(I, KK)
    t2 = KK
    ok = R.sim(t1, t2) and not R.sim(I, KK)
    print(f"{'OK' if ok else 'FAIL'} oper_eq_regime: I K ~ K, not I ~ K")
    print(f"regime={R.name} observe(I K)={R.observe(t1)}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
