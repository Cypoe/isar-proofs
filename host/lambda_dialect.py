"""
Host λ dialect — compile into the ISAR alphabet, then reduce.

Matches Lean `ISAR.LambdaFragment` (`occurs0` / `shift_down` / `abstract0` / `compile`).
Named binders are sugar for de Bruijn. Not the Rust Turner path (η / C / W).

Authority: Lean `compile`, then host `reduce` (= Lean `IStep`).

Usage (from repo root):
  python host/lambda_dialect.py
  python host/lambda_dialect.py --term "(\\x. x) K"
  python host/lambda_dialect.py --compile "\\x. \\y. x"
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import List, Optional, Tuple, Union

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, S, B, C, D, T, K, app, reduce  # noqa: E402


# ---------------------------------------------------------------------------
# Show
# ---------------------------------------------------------------------------

def show(t: T) -> str:
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return f"({show(t.l)} {show(t.r)})"
    return {
        K.VAR: f"v{t.n}",
        K.NORM: "I",
        K.KONST: "K",
        K.DUP: "D",
        K.SWAP: "C",
        K.COMP: "B",
        K.S: "S",
    }[t.k]


# ---------------------------------------------------------------------------
# Bracket abstraction (Lean abstract0 / compile)
# ---------------------------------------------------------------------------

def occurs0(t: T) -> bool:
    if t.k == K.VAR:
        return t.n == 0
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return occurs0(t.l) or occurs0(t.r)
    return False


def shift_down(t: T) -> T:
    if t.k == K.VAR:
        return T(K.VAR, n=0 if t.n == 0 else t.n - 1)
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return app(shift_down(t.l), shift_down(t.r))
    return t


def abstract0(t: T) -> T:
    if not occurs0(t):
        return app(KK, shift_down(t))
    if t.k == K.VAR and t.n == 0:
        return I
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        f, x = t.l, t.r
        if (not occurs0(f)) and occurs0(x):
            return app(app(B, shift_down(f)), abstract0(x))
        return app(app(S, abstract0(f)), abstract0(x))
    return I


# ---------------------------------------------------------------------------
# Named surface AST
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NVar:
    name: str


@dataclass(frozen=True)
class NIdx:
    n: int


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


NExpr = Union[NVar, NIdx, NAbs, NApp, NComb]

_COMB = {"I": I, "K": KK, "S": S, "B": B, "C": C, "D": D}


def compile_named(expr: NExpr, binders: Optional[List[str]] = None) -> T:
    if binders is None:
        binders = []
    if isinstance(expr, NComb):
        return expr.atom
    if isinstance(expr, NIdx):
        return T(K.VAR, n=expr.n)
    if isinstance(expr, NVar):
        for i, name in enumerate(reversed(binders)):
            if name == expr.name:
                return T(K.VAR, n=i)
        raise ValueError(f"unbound variable: {expr.name}")
    if isinstance(expr, NAbs):
        return abstract0(compile_named(expr.body, binders + [expr.param]))
    if isinstance(expr, NApp):
        return app(compile_named(expr.left, binders), compile_named(expr.right, binders))
    raise TypeError(type(expr))


# ---------------------------------------------------------------------------
# Parser
#   \x. e | λx. e | (e e) | e e e | I K S B C D | names | #n
# ---------------------------------------------------------------------------

class _Tok:
    def __init__(self, s: str):
        self.s = s
        self.i = 0

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
        if c in ("", ")"):
            break
        if c in ("\\", "λ"):
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
        # body of abs takes the rest of the app chain (classic λ)
        return NAbs(name, _parse_expr(tok))
    if c == "#":
        tok.i += 1
        start = tok.i
        while tok.i < len(tok.s) and tok.s[tok.i].isdigit():
            tok.i += 1
        if start == tok.i:
            raise ValueError("expected digits after #")
        return NIdx(int(tok.s[start:tok.i]))
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


# ---------------------------------------------------------------------------
# Compute
# ---------------------------------------------------------------------------

def compute(src: str, fuel: int = 1000) -> Tuple[T, T, int]:
    compiled = compile_named(parse(src))
    nf, steps = reduce(compiled, fuel=fuel)
    return compiled, nf, steps


GOLDENS = [
    ("(\\x. x) K", "K"),
    ("(\\x. x) S", "S"),
    ("((\\x. \\y. x) S) I", "S"),
    ("(((\\x. \\y. \\z. (x z) (y z)) K) K) I", "I"),
    ("\\x. x", "I"),
]


def main(argv: List[str]) -> int:
    if len(argv) >= 2 and argv[0] == "--term":
        compiled, nf, steps = compute(argv[1])
        print(f"compile: {show(compiled)}")
        print(f"nf:      {show(nf)}  ({steps} steps)")
        return 0
    if len(argv) >= 2 and argv[0] == "--compile":
        print(show(compile_named(parse(argv[1]))))
        return 0

    ok = True
    for src, expected in GOLDENS:
        compiled, nf, steps = compute(src)
        got = show(nf)
        tag = "OK" if got == expected else "FAIL"
        print(f"{tag} {src}  =>  {got}  ({steps} steps)  [compiled {show(compiled)}]")
        if got != expected:
            print(f"  EXPECTED: {expected}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
