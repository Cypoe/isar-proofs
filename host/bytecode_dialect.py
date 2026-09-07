"""
BytecodeView QuotientMap — Lean BytecodeView.lean mirror.

encode: Instruction list → ITerm (compile_bytecode)
decode: ITerm → Instruction list (decompile)
Observation via Graph / OperEq spine only — no private dialect β.
"""
from __future__ import annotations

import os
import sys
from enum import Enum, auto
from typing import List, Sequence, Tuple, Union

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, S, T, K, app  # noqa: E402
from quotient_map import QuotientMap, observe, obs_eq  # noqa: E402
from lambda_dialect import show  # noqa: E402
from observation_regime import encoding_regime  # noqa: E402


class Instr(Enum):
    PUSH_I = auto()
    PUSH_K = auto()
    PUSH_S = auto()
    APP = auto()


Prog = List[Instr]


def run(prog: Sequence[Instr], stack: List[T] | None = None) -> List[T]:
    st: List[T] = list(stack) if stack is not None else []
    for inst in prog:
        if inst is Instr.PUSH_I:
            st.insert(0, I)
        elif inst is Instr.PUSH_K:
            st.insert(0, KK)
        elif inst is Instr.PUSH_S:
            st.insert(0, S)
        elif inst is Instr.APP:
            if len(st) >= 2:
                x, y = st[0], st[1]
                st = [app(y, x)] + st[2:]
            elif len(st) == 1:
                st = [I, st[0]]
            else:
                st = [I]
        else:
            raise ValueError(inst)
    return st


def compile_bytecode(p: Prog) -> T:
    st = run(p, [])
    return st[0] if st else I


def decompile(t: T) -> Prog:
    if t.k == K.NORM:
        return [Instr.PUSH_I]
    if t.k == K.KONST:
        return [Instr.PUSH_K]
    if t.k == K.S:
        return [Instr.PUSH_S]
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return decompile(t.l) + decompile(t.r) + [Instr.APP]
    # L0 agents after quote: treat as push via surface atoms when possible
    if t.k == K.COMP:
        # not in Lean SKI bytecode; residualize as opaque via S-free display
        raise ValueError(f"decompile: unexpected kind {t.k} (expand/quote first)")
    if t.k == K.DUP or t.k == K.SWAP:
        raise ValueError(f"decompile: unexpected kind {t.k}")
    if t.k == K.VAR:
        raise ValueError("decompile: open var")
    raise ValueError(f"decompile: {t}")


def show_prog(p: Prog) -> str:
    names = {
        Instr.PUSH_I: "push_I",
        Instr.PUSH_K: "push_K",
        Instr.PUSH_S: "push_S",
        Instr.APP: "app",
    }
    return "[" + ", ".join(names[i] for i in p) + "]"


def encode_bytecode(surface: Union[Prog, T, str]) -> T:
    if isinstance(surface, T):
        return surface
    if isinstance(surface, str):
        return compile_bytecode(parse_prog(surface))
    return compile_bytecode(list(surface))


def decode_bytecode(nf: T) -> Prog:
    """Decode NF section to bytecode program (Lean decode_bytecode_raw shape)."""
    return decompile(nf)


def bytecode_map() -> QuotientMap:
    return QuotientMap(
        name="bytecode",
        encode=encode_bytecode,
        decode=decode_bytecode,
        regime=encoding_regime(encode_bytecode, name="bytecode.operEq"),
    )


def obs_show(nf: T) -> str:
    """Combinator display of an NF (shared goldens / OperEq stand-in)."""
    return show(nf)


def parse_prog(s: str) -> Prog:
    """Parse space/comma-separated tokens: push_I push_K push_S app (or I K S @)."""
    raw = s.replace(",", " ").split()
    out: Prog = []
    for tok in raw:
        t = tok.strip().lower()
        if t in ("push_i", "i"):
            out.append(Instr.PUSH_I)
        elif t in ("push_k", "k"):
            out.append(Instr.PUSH_K)
        elif t in ("push_s", "s"):
            out.append(Instr.PUSH_S)
        elif t in ("app", "@"):
            out.append(Instr.APP)
        else:
            raise ValueError(f"bad instruction: {tok!r}")
    return out


# Shared applied-NF suite (overlap with λ goldens as SKI programs)
GOLDENS: List[Tuple[str, Prog, str]] = [
    ("I", [Instr.PUSH_I], "I"),
    ("K", [Instr.PUSH_K], "K"),
    ("S", [Instr.PUSH_S], "S"),
    ("I K -> K", [Instr.PUSH_I, Instr.PUSH_K, Instr.APP], "K"),
    ("K S I -> S", [Instr.PUSH_K, Instr.PUSH_S, Instr.APP, Instr.PUSH_I, Instr.APP], "S"),
    ("S K K I -> I", [
        Instr.PUSH_S, Instr.PUSH_K, Instr.APP, Instr.PUSH_K, Instr.APP, Instr.PUSH_I, Instr.APP,
    ], "I"),
]


def main() -> int:
    ok = True
    qm = bytecode_map()
    print("== bytecode QuotientMap: compile_decompile identity ==")
    for label, _, _ in GOLDENS[:3]:
        pass
    for atom, term in (("I", I), ("K", KK), ("S", S)):
        back = compile_bytecode(decompile(term))
        match = back == term
        print(f"{'OK' if match else 'FAIL'} compile o decompile {atom}")
        if not match:
            ok = False

    # app tree
    t = app(app(KK, S), I)
    back = compile_bytecode(decompile(t))
    match = back == t
    print(f"{'OK' if match else 'FAIL'} compile o decompile K S I tree")
    if not match:
        ok = False

    print("\n== observe via Graph host piece ==")
    for label, prog, expected in GOLDENS:
        obs_prog, nf, steps, n = observe(qm, prog)
        got = show(nf)
        match = obs_eq(got, expected) and compile_bytecode(obs_prog) == nf
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  obs={got}  decode={show_prog(obs_prog)}  "
              f"(steps={steps} alloc={n})")
        if not match:
            print(f"  EXPECTED: {expected}  prog={show_prog(prog)}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
