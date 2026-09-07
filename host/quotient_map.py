"""
Phase 3: QuotientMap — dialect obligation is encode/decode under a regime O.

OperEq / host-piece NF is the primary ObservationRegime. No private dialect β.
Identity when the surface is already substrate (ITerm).
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Any, Callable, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T  # noqa: E402
from host_pieces import HostPiece, default_piece, run_piece  # noqa: E402
from observation_regime import (  # noqa: E402
    ObservationRegime,
    oper_eq_regime,
    encoding_regime,
)


@dataclass(frozen=True)
class QuotientMap:
    """encode surface → substrate ITerm; decode NF → observation; preserves regime."""

    name: str
    encode: Callable[[Any], T]
    decode: Callable[[T], Any]
    regime: ObservationRegime

    def encode_term(self, surface: Any) -> T:
        return self.encode(surface)

    def decode_obs(self, nf: T) -> Any:
        return self.decode(nf)

    def preserves(self, surface: Any, *, fuel: int = 100_000,
                  piece: Optional[HostPiece] = None) -> bool:
        """decode(nf(encode(p))) agrees with decode(observe_O(p))."""
        term = self.encode(surface)
        p = piece if piece is not None else default_piece()
        nf, _, _ = run_piece(p, term, fuel=fuel)
        got = self.decode(nf)
        # Regime observe may already be an NF / Obs; decode for comparison.
        expected = self.decode(self.regime.observe(surface))
        return self.regime.obs_eq(got, expected)


def identity_map(
    name: str = "identity",
    *,
    regime: Optional[ObservationRegime] = None,
) -> QuotientMap:
    """Surface already on substrate — observe under operEqRegime by default."""
    R = regime if regime is not None else oper_eq_regime()
    return QuotientMap(name=name, encode=lambda t: t, decode=lambda t: t, regime=R)


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


def obs_eq(a: Any, b: Any, *, regime: Optional[ObservationRegime] = None) -> bool:
    """Equality of observations under a regime (default: string / OperEq stand-in)."""
    if regime is not None:
        return regime.obs_eq(a, b)
    return str(a) == str(b)


def main() -> int:
    from reduce import I, KK, app  # noqa: E402

    qm = identity_map()
    obs, nf, steps, n = observe(qm, app(I, KK))
    ok = obs_eq(obs, KK, regime=qm.regime) and qm.preserves(app(I, KK))
    print(f"{'OK' if ok else 'FAIL'} identity under operEqRegime I K => {obs} "
          f"(steps={steps} alloc={n}) preserves={qm.preserves(app(I, KK))}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
