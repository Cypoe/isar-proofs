"""
Host λ dialect — Turner bracket → IStepBasis collapse → IStep reduce.

Pipeline (dialect-specific, then kernel):
  1. Turner degenerate elim (η / K-lift / B / C / S) → combinator tree
  2. IStepBasis only (dupβ, swapβ) until stuck  — dialect preprocess
  3. IStep reduce (normβ, konstβ, compβ, sβ)     — gold kernel

Lean `LambdaFragment.abstract0` is a weaker proved compiler (no η/C). It is
not this dialect; observational congruence is on applied NFs after the pipeline.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import List, Optional, Set, Tuple, Union

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, S, B, C, D, T, K, app, reduce as reduce_istep  # noqa: E402


def show(t: T) -> str:
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return f"({show(t.l)} {show(t.r)})"
    return {
        K.VAR: f"v{t.n}", K.NORM: "I", K.KONST: "K",
        K.DUP: "D", K.SWAP: "C", K.COMP: "B", K.S: "S",
    }[t.k]


# ---------------------------------------------------------------------------
# Mixed lexical IR
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class V:
    name: str


@dataclass(frozen=True)
class A:
    left: "X"
    right: "X"


@dataclass(frozen=True)
class Atom:
    t: T


X = Union[V, A, Atom]


def fv(e: X) -> Set[str]:
    if isinstance(e, V):
        return {e.name}
    if isinstance(e, A):
        return fv(e.left) | fv(e.right)
    return set()


def to_closed(e: X) -> T:
    if isinstance(e, V):
        raise ValueError(f"open term: unbound {e.name}")
    if isinstance(e, Atom):
        return e.t
    return app(to_closed(e.left), to_closed(e.right))


def abs_(x: str, b: X) -> X:
    if isinstance(b, V) and b.name == x:
        return Atom(I)
    if x not in fv(b):
        return A(Atom(KK), b)
    if isinstance(b, A):
        e1, e2 = b.left, b.right
        in1, in2 = x in fv(e1), x in fv(e2)
        if not in1 and not in2:
            return A(Atom(KK), A(e1, e2))
        if not in1 and isinstance(e2, V) and e2.name == x:
            return e1
        if not in1:
            return A(A(Atom(B), e1), abs_(x, e2))
        if not in2:
            return A(A(Atom(C), abs_(x, e1)), e2)
        return A(A(Atom(S), abs_(x, e1)), abs_(x, e2))
    return A(Atom(KK), b)


# ---------------------------------------------------------------------------
# Surface AST
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NVar:
    name: str


@dataclass(frozen=True)
class NAbs:
    param: str
    body: "NExpr"


@dataclass(frozen=True)
class NApp:
    left: "NExpr"
    right: "NExpr"


@dataclass(frozen=True)
class NComb:
    atom: T


NExpr = Union[NVar, NAbs, NApp, NComb]
_COMB = {"I": I, "K": KK, "S": S, "B": B, "C": C, "D": D}


def bracket_x(e: NExpr) -> X:
    if isinstance(e, NComb):
        return Atom(e.atom)
    if isinstance(e, NVar):
        return V(e.name)
    if isinstance(e, NApp):
        return A(bracket_x(e.left), bracket_x(e.right))
    return abs_(e.param, bracket_x(e.body))


def bracket(e: NExpr) -> T:
    return to_closed(bracket_x(e))


# ---------------------------------------------------------------------------
# Dialect preprocess: IStepBasis only (dupβ, swapβ), then gold IStep
# ---------------------------------------------------------------------------

def step_basis(t: T) -> Optional[T]:
    """One LO step of IStepBasis extras only — not I/K/B/S."""
    if t.k != K.APP:
        return None
    f, x = t.l, t.r
    assert f is not None and x is not None
    if f.k == K.APP:
        fl, fr = f.l, f.r
        assert fl is not None and fr is not None
        if fl.k == K.DUP:
            return app(app(fr, x), x)
        if fl.k == K.APP:
            fll, flr = fl.l, fl.r
            assert fll is not None and flr is not None
            if fll.k == K.SWAP:
                return app(app(flr, x), fr)
    sf = step_basis(f)
    if sf is not None:
        return app(sf, x)
    sx = step_basis(x)
    if sx is not None:
        return app(f, sx)
    return None


def reduce_basis(t: T, fuel: int = 1000) -> Tuple[T, int]:
    cur, n = t, 0
    while n < fuel:
        nxt = step_basis(cur)
        if nxt is None:
            break
        cur, n = nxt, n + 1
    return cur, n


def compile_dialect(e: NExpr, fuel: int = 1000) -> T:
    """Turner + basis collapse → tree ready for IStep."""
    raw = bracket(e)
    cleaned, _ = reduce_basis(raw, fuel=fuel)
    return cleaned


def compute(src: str, fuel: int = 1000) -> Tuple[T, T, T, int]:
    """Returns (turner_raw, after_basis, nf_istep, istep_steps)."""
    raw = bracket(parse(src))
    mid, _ = reduce_basis(raw, fuel=fuel)
    nf, steps = reduce_istep(mid, fuel=fuel)
    return raw, mid, nf, steps


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

class _Tok:
    def __init__(self, s: str):
        self.s, self.i = s, 0

    def peek(self) -> str:
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1
        return "" if self.i >= len(self.s) else self.s[self.i]

    def rest(self) -> str:
        self.peek()
        return self.s[self.i:]


def parse(s: str) -> NExpr:
    tok = _Tok(s.strip())
    expr = _parse_expr(tok)
    if tok.rest():
        raise ValueError(f"trailing input: {tok.rest()!r}")
    return expr


def _parse_expr(tok: _Tok) -> NExpr:
    return _parse_app(tok)


def _parse_app(tok: _Tok) -> NExpr:
    left = _parse_atom(tok)
    while True:
        c = tok.peek()
        if c in ("", ")") or c in ("\\", "λ"):
            break
        left = NApp(left, _parse_atom(tok))
    return left


def _parse_atom(tok: _Tok) -> NExpr:
    c = tok.peek()
    if c == "":
        raise ValueError("unexpected end of input")
    if c == "(":
        tok.i += 1
        e = _parse_expr(tok)
        if tok.peek() != ")":
            raise ValueError("expected ')'")
        tok.i += 1
        return e
    if c in ("\\", "λ"):
        tok.i += 1
        name = _parse_name(tok)
        if tok.peek() == ".":
            tok.i += 1
        elif tok.rest().startswith("->"):
            tok.i += 2
        else:
            raise ValueError("expected '.' or '->' after binder")
        return NAbs(name, _parse_expr(tok))
    name = _parse_name(tok)
    if name in _COMB:
        return NComb(_COMB[name])
    return NVar(name)


def _parse_name(tok: _Tok) -> str:
    tok.peek()
    if tok.i >= len(tok.s) or not (tok.s[tok.i].isalpha() or tok.s[tok.i] == "_"):
        raise ValueError("expected name")
    start = tok.i
    tok.i += 1
    while tok.i < len(tok.s) and (tok.s[tok.i].isalnum() or tok.s[tok.i] == "_"):
        tok.i += 1
    return tok.s[start:tok.i]


GOLDENS = [
    ("\\x. x", "I"),
    ("\\x. \\y. x", "K"),
    ("\\x. \\y. \\z. (x z) (y z)", "S"),
    ("(\\x. x) K", "K"),
    ("((\\x. \\y. x) S) I", "S"),
    ("(((\\x. \\y. \\z. (x z) (y z)) K) K) I", "I"),
    # Turner emits C; basis fires swapβ → ((I I) S); IStep → S
    ("((\\x. \\y. (y x)) S) I", "S"),
]


def main(argv: List[str]) -> int:
    if len(argv) >= 2 and argv[0] == "--term":
        raw, mid, nf, steps = compute(argv[1])
        print(f"turner:  {show(raw)}")
        print(f"basis:   {show(mid)}")
        print(f"istep:   {show(nf)}  ({steps} steps)")
        return 0
    if len(argv) >= 2 and argv[0] == "--compile":
        print(show(compile_dialect(parse(argv[1]))))
        return 0

    ok = True
    for src, expected in GOLDENS:
        raw, mid, nf, steps = compute(src)
        got = show(nf)
        tag = "OK" if got == expected else "FAIL"
        print(f"{tag} {src}  =>  {got}  ({steps} IStep)  [turner {show(raw)} | basis {show(mid)}]")
        if got != expected:
            print(f"  EXPECTED: {expected}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
