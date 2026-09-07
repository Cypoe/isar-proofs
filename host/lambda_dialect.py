"""
Host λ dialect — explicit QuotientMap onto the OperEq / Graph spine.

Encode variants (static division of the map, not two kernels):
  - Turner: degenerate elim (η / K-lift / B / C / S)
  - abstract0: Lean-shaped (I / K / S only — no η/C)

Observation: decode(Graph.reduce(encode(x))). Tree pipeline remains for --tree A/B.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import List, Optional, Set, Tuple, Union

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import I, KK, S, B, C, D, T, K, app, step as step_istep  # noqa: E402
from quotient_map import QuotientMap, observe, obs_eq  # noqa: E402
from host_pieces import default_piece, run_piece  # noqa: E402
from observation_regime import encoding_regime  # noqa: E402


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
# abstract0 — Lean LambdaFragment shape (no η / no C/B special cases)
# ---------------------------------------------------------------------------

def abs0_(x: str, b: X) -> X:
    if isinstance(b, V) and b.name == x:
        return Atom(I)
    if x not in fv(b):
        return A(Atom(KK), b)
    if isinstance(b, A):
        return A(A(Atom(S), abs0_(x, b.left)), abs0_(x, b.right))
    return A(Atom(KK), b)


def bracket_x_abstract0(e: NExpr) -> X:
    if isinstance(e, NComb):
        return Atom(e.atom)
    if isinstance(e, NVar):
        return V(e.name)
    if isinstance(e, NApp):
        return A(bracket_x_abstract0(e.left), bracket_x_abstract0(e.right))
    return abs0_(e.param, bracket_x_abstract0(e.body))


def bracket_abstract0(e: NExpr) -> T:
    return to_closed(bracket_x_abstract0(e))


def encode_turner(surface) -> T:
    if isinstance(surface, str):
        surface = parse(surface)
    return bracket(surface)


def encode_abstract0(surface) -> T:
    if isinstance(surface, str):
        surface = parse(surface)
    return bracket_abstract0(surface)


def lambda_turner_map() -> QuotientMap:
    return QuotientMap(
        name="lambda.turner",
        encode=encode_turner,
        decode=show,
        regime=encoding_regime(encode_turner, name="lambda.turner.operEq"),
    )


def lambda_abstract0_map() -> QuotientMap:
    return QuotientMap(
        name="lambda.abstract0",
        encode=encode_abstract0,
        decode=show,
        regime=encoding_regime(encode_abstract0, name="lambda.abstract0.operEq"),
    )


# ---------------------------------------------------------------------------
# Tree A/B only (--tree): IStepBasis then IStep. Not QuotientMap authority.
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


def reduce_pipeline(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    """Prefer IStepBasis, then IStep, until NF. Returns (nf, basis_steps, istep_steps)."""
    cur = t
    b_n = i_n = 0
    while b_n + i_n < fuel:
        nxt = step_basis(cur)
        if nxt is not None:
            cur = nxt
            b_n += 1
            continue
        nxt = step_istep(cur)
        if nxt is not None:
            cur = nxt
            i_n += 1
            continue
        break
    return cur, b_n, i_n


def compile_dialect(e: NExpr, fuel: int = 1000) -> T:
    """Turner + exhaust basis on the closed term (no IStep yet)."""
    raw = bracket(e)
    cleaned, _ = reduce_basis(raw, fuel=fuel)
    return cleaned


def compute(src: str, fuel: int = 100_000) -> Tuple[T, T, T, int, int]:
    """Returns (turner_raw, after_first_basis, nf, basis_steps, istep_steps)."""
    return compute_expr(parse(src), fuel=fuel)


def compute_expr(e: NExpr, fuel: int = 100_000) -> Tuple[T, T, T, int, int]:
    raw = bracket(e)
    mid, _ = reduce_basis(raw, fuel=min(fuel, 10_000))
    nf, b_n, i_n = reduce_pipeline(raw, fuel=fuel)
    return raw, mid, nf, b_n, i_n


def compute_expr_graph(e: NExpr, fuel: int = 100_000) -> Tuple[T, T, T, int, int, int]:
    """Turner encode, then Graph reduce via host piece. Returns + unique_nodes."""
    raw = bracket(e)
    mid, _ = reduce_basis(raw, fuel=min(fuel, 10_000))
    nf, steps, nodes = run_piece(default_piece(), raw, fuel=fuel)
    return raw, mid, nf, steps, 0, nodes


def compute_graph(src: str, fuel: int = 100_000) -> Tuple[T, T, T, int, int, int]:
    return compute_expr_graph(parse(src), fuel=fuel)


def observe_lambda(src: str, *, variant: str = "turner", fuel: int = 100_000):
    """QuotientMap observe (Graph). variant: turner | abstract0."""
    qm = lambda_abstract0_map() if variant == "abstract0" else lambda_turner_map()
    return observe(qm, src, fuel=fuel)


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
    ("((\\x. \\y. (y x)) S) I", "S"),
]


def main(argv: List[str]) -> int:
    use_tree = False
    variant = "turner"
    args = list(argv)
    while args and args[0] in ("--tree", "--graph", "--abstract0"):
        if args[0] == "--tree":
            use_tree = True
        elif args[0] == "--abstract0":
            variant = "abstract0"
        # --graph kept as no-op (graph is default)
        args = args[1:]

    if len(args) >= 2 and args[0] == "--term":
        if use_tree:
            raw, mid, nf, b_n, i_n = compute(args[1])
            print(f"turner:  {show(raw)}")
            print(f"basis1:  {show(mid)}")
            print(f"nf:      {show(nf)}  (basis={b_n} istep={i_n}) [tree]")
        else:
            obs, nf, steps, nodes = observe_lambda(args[1], variant=variant)
            raw = encode_abstract0(args[1]) if variant == "abstract0" else encode_turner(args[1])
            print(f"encode:  {show(raw)}  [{variant}]")
            print(f"obs:     {obs}  (steps={steps} nodes={nodes}) [graph QuotientMap]")
        return 0
    if len(args) >= 2 and args[0] == "--compile":
        enc = encode_abstract0 if variant == "abstract0" else encode_turner
        print(show(enc(parse(args[1]))))
        return 0

    ok = True
    for src, expected in GOLDENS:
        if use_tree:
            raw, mid, nf, b_n, i_n = compute(src)
            got = show(nf)
            tag = "OK" if got == expected else "FAIL"
            print(f"{tag} {src}  =>  {got}  (basis={b_n} istep={i_n}) [tree]")
            if got != expected:
                print(f"  EXPECTED: {expected}")
                ok = False
            continue

        obs, nf, steps, nodes = observe_lambda(src, variant=variant)
        got = obs if isinstance(obs, str) else show(nf)
        match = obs_eq(got, expected)
        if variant == "abstract0":
            tag = "OK" if match else "DIFF"
            print(f"{tag} {src}  =>  {got}  (steps={steps} nodes={nodes}) [abstract0]")
            if not match:
                print(f"  TURNER GOLD: {expected}  (eta/C static-division gap; not a FAIL)")
            continue
        tag = "OK" if match else "FAIL"
        print(f"{tag} {src}  =>  {got}  (steps={steps} nodes={nodes}) [graph QuotientMap]")
        if not match:
            print(f"  EXPECTED: {expected}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
