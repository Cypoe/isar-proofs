"""
Observational suite under ObservationRegime (OperEq stand-in).

Checks QuotientMap.preserves and regime sim — not bare string ontology.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, app  # noqa: E402
from quotient_map import identity_map, observe, obs_eq  # noqa: E402
from observation_regime import oper_eq_regime  # noqa: E402
from lambda_dialect import (  # noqa: E402
    GOLDENS as LAMBDA_GOLDENS,
    lambda_turner_map,
    lambda_abstract0_map,
    encode_turner,
    encode_abstract0,
    show,
)
from bytecode_dialect import (  # noqa: E402
    GOLDENS as BYTECODE_GOLDENS,
    bytecode_map,
    show_prog,
    compile_bytecode,
)
from lambda_dialect import show as show_term  # noqa: E402
from strategy import IdentityStrategy, MixStrategy  # noqa: E402
from host_pieces import catalog  # noqa: E402


def main() -> int:
    ok = True
    R = oper_eq_regime()

    print("== operEqRegime on substrate ==")
    if not R.sim(app(I, KK), KK):
        print("FAIL I K should ~ K")
        ok = False
    else:
        print("OK I K ~_O K")

    print("\n== identity QuotientMap preserves operEqRegime ==")
    qm_id = identity_map()
    if not qm_id.preserves(app(I, KK)):
        print("FAIL identity preserves")
        ok = False
    else:
        print(f"OK identity preserves under {qm_id.regime.name}")

    print("\n== lambda Turner QuotientMap (regime + goldens) ==")
    qm_t = lambda_turner_map()
    for src, expected in LAMBDA_GOLDENS:
        obs, nf, steps, n = observe(qm_t, src)
        match = obs_eq(obs, expected, regime=qm_t.regime) and qm_t.preserves(src)
        tag = "OK" if match else "FAIL"
        print(f"{tag} {src}  => {obs}  preserves={qm_t.preserves(src)}  "
              f"(steps={steps} alloc={n}) [{qm_t.regime.name}]")
        if not match:
            print(f"  EXPECTED: {expected}")
            ok = False

    print("\n== lambda abstract0 vs Turner (encode variants under same O) ==")
    qm_a = lambda_abstract0_map()
    for src, expected in LAMBDA_GOLDENS:
        ot, _, _, _ = observe(qm_t, src)
        oa, _, _, _ = observe(qm_a, src)
        same = obs_eq(ot, oa, regime=qm_t.regime)
        tag = "OK" if same else "DIFF"
        print(f"{tag} {src}  turner={ot} abstract0={oa}")
        if same and not obs_eq(ot, expected, regime=qm_t.regime):
            print(f"  FAIL both miss gold {expected}")
            ok = False
        if not same:
            et, ea = encode_turner(src), encode_abstract0(src)
            print(f"  encode sizes turner={len(show(et))} abstract0={len(show(ea))}")

    print("\n== Bytecode QuotientMap ==")
    qm_b = bytecode_map()
    for label, prog, expected in BYTECODE_GOLDENS:
        obs_prog, nf, steps, n = observe(qm_b, prog)
        got = show_term(nf)
        match = (
            obs_eq(got, expected)
            and compile_bytecode(obs_prog) == nf
            and qm_b.preserves(prog)
        )
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  => {got}  decode={show_prog(obs_prog)}  "
              f"preserves={qm_b.preserves(prog)}  (steps={steps} alloc={n})")
        if not match:
            ok = False

    print("\n== shared SKI: bytecode vs identity under operEqRegime ==")
    for label, prog, expected in BYTECODE_GOLDENS:
        if "->" not in label and label in ("I", "K", "S"):
            continue
        obs_prog, nf_b, _, _ = observe(qm_b, prog)
        term = compile_bytecode(prog)
        _, nf_i, _, _ = observe(qm_id, term)
        match = R.sim(nf_b, nf_i) and obs_eq(show_term(nf_b), expected)
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  bytecode={show_term(nf_b)} identity={show_term(nf_i)}")
        if not match:
            ok = False

    print("\n== params (strategy + host pieces); O is primary ==")
    print(f"pieces: {[p.name for p in catalog()]}")
    print(f"strategies: {[IdentityStrategy().name, MixStrategy().name]}")
    print(f"primary regime: {R.name}")
    print("Phase 3: ObservationRegime formalizes ~_O; maps preserve it")

    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
