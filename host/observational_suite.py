"""
Observational suite: decode(nf(encode(x))) ~ expected under OperEq/Graph.

λ Turner QuotientMap, Bytecode QuotientMap, identity substrate path.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, S, app  # noqa: E402
from quotient_map import identity_map, observe, obs_eq  # noqa: E402
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

    print("== identity QuotientMap (already on substrate) ==")
    qm_id = identity_map()
    obs, nf, _, _ = observe(qm_id, app(I, KK))
    if not obs_eq(obs, KK):
        print(f"FAIL identity I K => {obs}")
        ok = False
    else:
        print("OK identity I K => K")

    print("\n== lambda Turner QuotientMap ==")
    qm_t = lambda_turner_map()
    for src, expected in LAMBDA_GOLDENS:
        obs, nf, steps, n = observe(qm_t, src)
        match = obs_eq(obs, expected)
        tag = "OK" if match else "FAIL"
        print(f"{tag} {src}  => {obs}  (steps={steps} alloc={n})")
        if not match:
            print(f"  EXPECTED: {expected}")
            ok = False

    print("\n== lambda abstract0 vs Turner (encode variants; applied NF) ==")
    qm_a = lambda_abstract0_map()
    for src, expected in LAMBDA_GOLDENS:
        ot, _, _, _ = observe(qm_t, src)
        oa, _, _, _ = observe(qm_a, src)
        same = obs_eq(ot, oa)
        tag = "OK" if same else "DIFF"
        print(f"{tag} {src}  turner={ot} abstract0={oa}")
        if same and not obs_eq(ot, expected):
            print(f"  FAIL both miss gold {expected}")
            ok = False
        # DIFF is allowed (η/C); both must still be strings
        if not same:
            et, ea = encode_turner(src), encode_abstract0(src)
            print(f"  encode sizes turner={len(show(et))} abstract0={len(show(ea))}")

    print("\n== Bytecode QuotientMap ==")
    qm_b = bytecode_map()
    for label, prog, expected in BYTECODE_GOLDENS:
        obs_prog, nf, steps, n = observe(qm_b, prog)
        got = show_term(nf)
        match = obs_eq(got, expected) and compile_bytecode(obs_prog) == nf
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  => {got}  decode={show_prog(obs_prog)}  "
              f"(steps={steps} alloc={n})")
        if not match:
            ok = False

    print("\n== shared SKI: bytecode vs identity substrate ==")
    for label, prog, expected in BYTECODE_GOLDENS:
        if "->" not in label and label in ("I", "K", "S"):
            continue
        obs_prog, nf_b, _, _ = observe(qm_b, prog)
        term = compile_bytecode(prog)
        obs_i, nf_i, _, _ = observe(qm_id, term)
        match = (
            obs_eq(show_term(nf_b), expected)
            and obs_eq(nf_b, nf_i)
            and compile_bytecode(obs_prog) == nf_b
        )
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  bytecode={show_term(nf_b)} identity={show_term(nf_i)}")
        if not match:
            ok = False

    print("\n== params present (strategy + host pieces) ==")
    print(f"pieces: {[p.name for p in catalog()]}")
    print(f"strategies: {[IdentityStrategy().name, MixStrategy().name]}")
    print("Noted later: mine-adopt iff OperEq matches known map; budgeted CoGen loaders")

    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
