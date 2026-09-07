"""
Phase 3: Strategy — parametric specialize/residual policy.

Mix / Futamura / identity are instances of this slot, not the ontology.
Nontrivial BTA and CoGen stay later.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Protocol

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, K, app  # noqa: E402


class Strategy(Protocol):
    name: str

    def specialize(self, t: T, static_env: Dict[int, T]) -> T:
        """Residualize t under known static bindings (var index → term)."""
        ...


@dataclass(frozen=True)
class IdentityStrategy:
    """No residual shrink — return the term unchanged."""

    name: str = "identity"

    def specialize(self, t: T, static_env: Dict[int, T]) -> T:
        return t


def _subst(t: T, static_env: Dict[int, T]) -> T:
    """Thin mix-shaped specialize: replace known vars; recurse under app."""
    if t.k == K.VAR:
        got = static_env.get(t.n)
        return got if got is not None else t
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return app(_subst(t.l, static_env), _subst(t.r, static_env))
    return t


@dataclass(frozen=True)
class MixStrategy:
    """Static_env subst only — mix-shaped stub, not 1993 BTA/cogen."""

    name: str = "mix"

    def specialize(self, t: T, static_env: Dict[int, T]) -> T:
        return _subst(t, static_env)


def strategies() -> List[Strategy]:
    return [IdentityStrategy(), MixStrategy()]


def by_name(name: str) -> Optional[Strategy]:
    for s in strategies():
        if s.name == name:
            return s
    return None


def main() -> int:
    from reduce import I, KK  # noqa: E402

    id_s = IdentityStrategy()
    mix = MixStrategy()
    v0 = T(K.VAR, n=0)
    t = app(v0, I)
    assert id_s.specialize(t, {0: KK}) == t
    got = mix.specialize(t, {0: KK})
    ok = got == app(KK, I)
    print(f"{'OK' if ok else 'FAIL'} mix specialize (v0 I)[0:=K] => {got}")
    print(f"strategies: {[s.name for s in strategies()]}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
