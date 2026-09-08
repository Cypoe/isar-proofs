"""
Mine-adopt gate: accept a candidate encode only if OperEq matches a known QuotientMap.

Else refuse — require an explicit QuotientMap (Phase 3 law). No invented encode.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Any, Callable, List, Optional, Sequence, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, I, KK, S, app  # noqa: E402
from observation_regime import oper_eq_regime  # noqa: E402
from quotient_map import QuotientMap, identity_map, observe, obs_eq  # noqa: E402
from bytecode_dialect import bytecode_map, compile_bytecode  # noqa: E402
from fasm_dialect import fasm_map, encode_fasm, GOLDENS as FASM_GOLDENS  # noqa: E402


@dataclass(frozen=True)
class AdoptResult:
    accepted: bool
    matched_map: Optional[str]
    reason: str


def known_maps() -> List[QuotientMap]:
    """Maps already authored under O — candidates may match these."""
    return [identity_map(), bytecode_map(), fasm_map()]


def default_probes() -> List[T]:
    return [I, KK, S, app(I, KK), app(app(KK, S), I)]


def try_adopt(
    candidate_encode: Callable[[Any], T],
    *,
    surfaces: Sequence[Any],
    known: Optional[Sequence[QuotientMap]] = None,
    fuel: int = 100_000,
) -> AdoptResult:
    """
    Adopt iff for every surface, NF(candidate_encode(s)) ~_O NF(known.encode(s))
    for some single known map that works for all probes.
    """
    R = oper_eq_regime()
    maps = list(known) if known is not None else known_maps()
    for qm in maps:
        all_match = True
        for s in surfaces:
            try:
                cand_term = candidate_encode(s)
            except Exception as e:  # noqa: BLE001 — gate must refuse bad encodes
                return AdoptResult(False, None, f"candidate encode failed: {e}")
            try:
                known_term = qm.encode(s)
            except Exception:
                all_match = False
                break
            # Observe both under OperEq (NF).
            if not R.sim(cand_term, known_term):
                # Also allow agreement after full observe path via known decode.
                _, nf_c, _, _ = observe(identity_map(regime=R), cand_term, fuel=fuel)
                _, nf_k, _, _ = observe(qm, s, fuel=fuel)
                if not R.sim(nf_c, nf_k):
                    all_match = False
                    break
        if all_match:
            return AdoptResult(True, qm.name, f"OperEq matches known map {qm.name}")
    return AdoptResult(
        False,
        None,
        "no known QuotientMap matches under operEqRegime; define an explicit map",
    )


def main() -> int:
    ok = True
    probes = default_probes()

    # Identity encode should adopt as identity.
    r = try_adopt(lambda t: t, surfaces=probes)
    tag = "OK" if r.accepted and r.matched_map == "identity" else "FAIL"
    print(f"{tag} adopt identity encode -> {r}")
    if not r.accepted:
        ok = False

    # Bytecode compile path: surfaces are programs; use known bytecode map probes.
    from bytecode_dialect import GOLDENS  # noqa: E402

    programs = [prog for _, prog, _ in GOLDENS]
    r2 = try_adopt(compile_bytecode, surfaces=programs, known=[bytecode_map()])
    tag2 = "OK" if r2.accepted and r2.matched_map == "bytecode" else "FAIL"
    print(f"{tag2} adopt bytecode compile -> {r2}")
    if not r2.accepted:
        ok = False

    # FASM encode should adopt as fasm (or bytecode — same OperEq; prefer known list order).
    fasm_progs = [prog for _, prog, _ in FASM_GOLDENS]
    r2b = try_adopt(encode_fasm, surfaces=fasm_progs, known=[fasm_map()])
    tag2b = "OK" if r2b.accepted and r2b.matched_map == "fasm" else "FAIL"
    print(f"{tag2b} adopt fasm encode -> {r2b}")
    if not r2b.accepted:
        ok = False

    # Spurious encode: always K — must refuse.
    def always_k(_s: Any) -> T:
        return KK

    r3 = try_adopt(always_k, surfaces=probes)
    tag3 = "OK" if not r3.accepted else "FAIL"
    print(f"{tag3} refuse always_K encode -> {r3}")
    if r3.accepted:
        ok = False

    print("mine-adopt: OperEq match or explicit QuotientMap")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
