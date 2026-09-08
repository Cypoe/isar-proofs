"""
FASM(g)-flavored QuotientMap — presentation over the BytecodeView SKI VM.

Same compile/decompile/OperEq classes as bytecode; distinct fasmg-ish text surface.
No private β. No external fasmg assemble/link.
"""
from __future__ import annotations

import os
import sys
from typing import List, Tuple, Union

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, S, T  # noqa: E402
from quotient_map import QuotientMap, observe, obs_eq  # noqa: E402
from lambda_dialect import show  # noqa: E402
from observation_regime import encoding_regime  # noqa: E402
from bytecode_dialect import (  # noqa: E402
    Instr,
    Prog,
    compile_bytecode,
    decompile,
    GOLDENS as BYTECODE_GOLDENS,
)


_MNEMONIC = {
    Instr.PUSH_I: "push_I",
    Instr.PUSH_K: "push_K",
    Instr.PUSH_S: "push_S",
    Instr.APP: "app",
}

_HEADER = "; isar.fasm — FASM(g)-flavored SKI (presentation only; reduce via graph)"


def show_fasm(prog: Prog) -> str:
    """Pretty-print a program as line-oriented fasmg-ish source."""
    lines = [_HEADER] + [_MNEMONIC[i] for i in prog]
    return "\n".join(lines) + "\n"


def parse_fasm(src: str) -> Prog:
    """
    Parse fasmg-ish SKI dialect: one mnemonic per line; ';' comments; blank ok.
    Also accepts a single-line space-separated form.
    """
    out: Prog = []
    for raw_line in src.splitlines():
        line = raw_line.split(";", 1)[0].strip()
        if not line:
            continue
        for tok in line.replace(",", " ").split():
            t = tok.strip().lower()
            if t in ("push_i", "i"):
                out.append(Instr.PUSH_I)
            elif t in ("push_k", "k"):
                out.append(Instr.PUSH_K)
            elif t in ("push_s", "s"):
                out.append(Instr.PUSH_S)
            elif t in ("app", "@", "call"):
                out.append(Instr.APP)
            else:
                raise ValueError(f"bad fasm mnemonic: {tok!r}")
    return out


def encode_fasm(surface: Union[Prog, T, str]) -> T:
    if isinstance(surface, T):
        return surface
    if isinstance(surface, str):
        return compile_bytecode(parse_fasm(surface))
    return compile_bytecode(list(surface))


def decode_fasm(nf: T) -> Prog:
    """Decode NF to structured program (same VM as bytecode)."""
    return decompile(nf)


def fasm_map() -> QuotientMap:
    return QuotientMap(
        name="fasm",
        encode=encode_fasm,
        decode=decode_fasm,
        regime=encoding_regime(encode_fasm, name="fasm.operEq"),
    )


# Same SKI probes as bytecode; label + Prog + expected NF display
GOLDENS: List[Tuple[str, Prog, str]] = list(BYTECODE_GOLDENS)


def main() -> int:
    ok = True
    qm = fasm_map()

    print("== fasm text roundtrip ==")
    for label, prog, _ in GOLDENS[:4]:
        text = show_fasm(prog)
        back = parse_fasm(text)
        match = back == prog
        tag = "OK" if match else "FAIL"
        print(f"{tag} parse(show) {label}")
        if not match:
            ok = False

    print("\n== fasm QuotientMap observe (Graph) ==")
    for label, prog, expected in GOLDENS:
        text = show_fasm(prog)
        obs_prog, nf, steps, n = observe(qm, text)
        got = show(nf)
        match = (
            obs_eq(got, expected)
            and compile_bytecode(obs_prog) == nf
            and qm.preserves(text)
            and qm.preserves(prog)
        )
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  obs={got}  decode={show_fasm(obs_prog).splitlines()[1:]}  "
              f"preserves={qm.preserves(text)}  (steps={steps} alloc={n})")
        if not match:
            ok = False

    print("\n== fasm ~_O bytecode on shared SKI ==")
    from bytecode_dialect import bytecode_map  # noqa: E402
    from observation_regime import oper_eq_regime  # noqa: E402

    R = oper_eq_regime()
    qm_b = bytecode_map()
    for label, prog, expected in GOLDENS:
        _, nf_f, _, _ = observe(qm, prog)
        _, nf_b, _, _ = observe(qm_b, prog)
        match = R.sim(nf_f, nf_b) and obs_eq(show(nf_f), expected)
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  fasm={show(nf_f)} bytecode={show(nf_b)}")
        if not match:
            ok = False

    print("Phase 4b: FASM QuotientMap (presentation); no external fasmg")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
