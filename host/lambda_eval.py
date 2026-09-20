"""
lambda_eval — witness 3a: weak-beta lambda evaluator on named NExpr.

lstep mirrors Lean `LambdaFragment.LStep` on the lambda fragment —
beta / appL / appR, NEVER under NAbs — and additionally fires an NComb
atom by its basis rule when saturated at head position:
  I x -> x          B f g x -> f (g x)     D f x -> f x x
  K a b -> a        S f g x -> (f x)(g x)  C f x y -> f y x
Honest scope: this is the SAME weak surface semantics the graph/tree
pieces observe (beta at surface + saturated combs) — it is not a
beta-only evaluator; the LStep mirroring applies to the lambda
fragment only.

observe() maps the residual NExpr back to a T spine: NComb/NApp pass
through, a residual NAbs is bracketed via lambda_dialect's
bracket_abstract0 — the abstract0 class (Lean `compile`'s shape), NOT
Turner — so the output T compares directly with every other cube
column.  Free `v<int>` names (the cube's hole probes) map to VAR n.

LSTEP_PIECE ("lambda.lstep", kind="lambda") adapts the HostPiece
protocol: T -> NExpr -> eval -> observe -> T; alloc is always 0.
eval_xdu() runs the xdu runtime path at lambda level: the same
to_lambda source applied to a Scott list built from literal NAbs
(nibble k = 16-ary NAbs selector, Church numeral as `\\f. \\x. f^k x`)
— the output spine is decoded by the shared term_to_nibbles
convention (C h t cells -> K tail; elements B^k I; last = rc; odd
output count overrides rc to 3).
"""
from __future__ import annotations

import os
import re
import sys
from typing import Dict, List, Optional, Set, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, K, I, KK, B, S, D, C, app  # noqa: E402
from lambda_dialect import (  # noqa: E402
    NVar, NAbs, NApp, NComb, NExpr, parse, bracket_abstract0,
)
from host_pieces import HostPiece  # noqa: E402
import xdu_dialect as xd  # noqa: E402
from lambda_bench import church, MULT, EXP, appn  # noqa: E402


# ---------------------------------------------------------------------------
# capture-avoiding substitution on named vars
# ---------------------------------------------------------------------------

def _fv(e: NExpr) -> Set[str]:
    if isinstance(e, NVar):
        return {e.name}
    if isinstance(e, NAbs):
        return _fv(e.body) - {e.param}
    if isinstance(e, NApp):
        return _fv(e.left) | _fv(e.right)
    return set()


_FRESH_N = [0]


def _fresh(avoid: Set[str]) -> str:
    while True:
        _FRESH_N[0] += 1
        name = f"_f{_FRESH_N[0]}"
        if name not in avoid:
            return name


def subst(e: NExpr, x: str, s: NExpr) -> NExpr:
    """e[x := s], capture-avoiding (freshname renaming on collision)."""
    if isinstance(e, NVar):
        return s if e.name == x else e
    if isinstance(e, NComb):
        return e
    if isinstance(e, NApp):
        return NApp(subst(e.left, x, s), subst(e.right, x, s))
    if e.param == x:
        return e
    if e.param not in _fv(s):
        return NAbs(e.param, subst(e.body, x, s))
    f = _fresh(_fv(e.body) | _fv(s) | {x, e.param})
    return NAbs(f, subst(subst(e.body, e.param, NVar(f)), x, s))


# ---------------------------------------------------------------------------
# lstep — one leftmost-outermost step
# ---------------------------------------------------------------------------

_ARITY = {K.NORM: 1, K.KONST: 2, K.DUP: 2, K.S: 3, K.COMP: 3, K.SWAP: 3}


def _comb_redex(atom: T, args: List[NExpr]) -> NExpr:
    if atom.k == K.NORM:
        return args[0]
    if atom.k == K.KONST:
        return args[0]
    if atom.k == K.DUP:
        f, x = args
        return NApp(NApp(f, x), x)
    if atom.k == K.S:
        f, g, x = args
        return NApp(NApp(f, x), NApp(g, x))
    if atom.k == K.COMP:
        f, g, x = args
        return NApp(f, NApp(g, x))
    f, x, y = args
    return NApp(NApp(f, y), x)              # SWAP: C f x y -> f y x


def _head_fire(e: NApp) -> Optional[NExpr]:
    """Spine head is a saturated NComb: fire its basis rule once
    (extra args stay applied — same single redex as appL-descent)."""
    args: List[NExpr] = []
    cur: NExpr = e
    while isinstance(cur, NApp):
        args.append(cur.right)
        cur = cur.left
    args.reverse()
    if not isinstance(cur, NComb):
        return None
    need = _ARITY.get(cur.atom.k)
    if need is None or len(args) < need:
        return None
    out = _comb_redex(cur.atom, args[:need])
    for a in args[need:]:
        out = NApp(out, a)
    return out


def lstep(e: NExpr) -> Optional[NExpr]:
    """One LO step: saturated-comb/beta at head first, then appL,
    then appR — never under NAbs (same bias as graph.lo / tree)."""
    if not isinstance(e, NApp):
        return None
    if isinstance(e.left, NAbs):
        return subst(e.left.body, e.left.param, e.right)
    fired = _head_fire(e)
    if fired is not None:
        return fired
    l = lstep(e.left)
    if l is not None:
        return NApp(l, e.right)
    r = lstep(e.right)
    if r is not None:
        return NApp(e.left, r)
    return None


def eval(e: NExpr, fuel: int = 100_000) -> Tuple[NExpr, int]:
    """Iterate lstep until NF or fuel; returns (nf, steps)."""
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100_000))
    cur, n = e, 0
    while n < fuel:
        nxt = lstep(cur)
        if nxt is None:
            break
        cur, n = nxt, n + 1
    return cur, n


# ---------------------------------------------------------------------------
# observe — residual NExpr -> T (abstract0 class for residual NAbs)
# ---------------------------------------------------------------------------

_HOLE = re.compile(r"v\d+")


def observe(e: NExpr) -> T:
    if isinstance(e, NComb):
        return e.atom
    if isinstance(e, NApp):
        return app(observe(e.left), observe(e.right))
    if isinstance(e, NAbs):
        return bracket_abstract0(e)
    if _HOLE.fullmatch(e.name):
        return T(K.VAR, n=int(e.name[1:]))
    raise ValueError(f"observe: free var {e.name!r} not a hole name")


def t_to_nexpr(t: T) -> NExpr:
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return NApp(t_to_nexpr(t.l), t_to_nexpr(t.r))
    if t.k == K.VAR:
        return NVar(f"v{t.n}")
    return NComb(t)


def _lstep_reduce(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    nf, steps = eval(t_to_nexpr(t), fuel)
    return observe(nf), steps, 0


LSTEP_PIECE = HostPiece(name="lambda.lstep", kind="lambda",
                        reduce=_lstep_reduce)


# ---------------------------------------------------------------------------
# eval_xdu — the xdu runtime path witnessed at lambda level
# ---------------------------------------------------------------------------

def _nnil() -> NExpr:
    return NAbs("n", NAbs("c", NVar("n")))              # \n. \c. n


def _ncons() -> NExpr:
    return NAbs("h", NAbs("t", NAbs("n", NAbs("c",
        NApp(NApp(NVar("c"), NVar("h")), NVar("t"))))))  # \h.\t.\n.\c. c h t


def _nnib(k: int) -> NExpr:
    e: NExpr = NVar("c%d" % k)
    for i in reversed(range(16)):
        e = NAbs("c%d" % i, e)
    return e                                            # \c0..\c15. ck


def nibbles_to_nexpr(data: bytes) -> NExpr:
    """bytes -> Scott list of NAbs nibble selectors (hi then lo)."""
    t = _nnil()
    cons = _ncons()
    for byte in reversed(data):
        t = NApp(NApp(cons, _nnib(byte & 15)), t)
        t = NApp(NApp(cons, _nnib(byte >> 4)), t)
    return t


def _spine_t(e: NExpr) -> T:
    """Output-spine fragment -> T: only NComb/NApp allowed here."""
    if isinstance(e, NComb):
        return e.atom
    if isinstance(e, NApp):
        return app(_spine_t(e.left), _spine_t(e.right))
    raise ValueError("output map: residual "
                     f"{type(e).__name__} in output spine (fuel?)")


def eval_xdu(xdu: xd.XDU, data: bytes, fuel: Optional[int] = None
             ) -> Tuple[bytes, int, int]:
    """(stdout_bytes, rc, lsteps).  The lambda-level runtime path:
    parse(to_lambda(xdu)) applied to nibbles_to_nexpr(data) and a
    Church numeral NExpr; decoded by the shared spine convention."""
    n = 2 * len(data) + 1
    if fuel is None:
        fuel = 30_000 * n + 100_000
    term = NApp(NApp(parse(xd.to_lambda(xdu)),
                     nibbles_to_nexpr(data)),
                church(n))
    nf, steps = eval(term, fuel)
    out, rc = xd.term_to_nibbles(_spine_t(nf))
    return out, rc, steps


# ---------------------------------------------------------------------------
# self-test
# ---------------------------------------------------------------------------

def main() -> int:
    from reduce import reduce as tree_reduce  # noqa: E402

    ok = True
    _I, _K, _B, _S = NComb(I), NComb(KK), NComb(B), NComb(S)
    probes: List[Tuple[str, NExpr]] = [
        ("(\\x. x) K", NApp(NAbs("x", NVar("x")), _K)),
        ("(\\x. \\y. x) S I", parse("((\\x. \\y. x) S) I")),
        ("(\\x.\\y.\\z. (x z)(y z)) K K I",
         parse("(((\\x. \\y. \\z. (x z) (y z)) K) K) I")),
        ("(\\x. \\y. y x) S I", parse("((\\x. \\y. (y x)) S) I")),
        ("MULT c3 c4 B I", appn(MULT, church(3), church(4), _B, _I)),
        ("EXP c2 c3 B I", appn(EXP, church(2), church(3), _B, _I)),
    ]
    for label, e in probes:
        got = observe(eval(e, 2_000_000)[0])
        want, _ = tree_reduce(bracket_abstract0(e), fuel=2_000_000)
        good = got == want
        ok = ok and good
        print(f"{'OK' if good else 'FAIL'} {label} => {got}  "
              f"(lsteps vs tree.reduce NF {want})")

    for name in ("echo", "hexdump"):
        xdu = xd.load(xd.probe_path(name))
        for data in (b"", b"Hi", bytes(range(8))):
            exp = xd.interpret(xdu, data)
            out, rc, steps = eval_xdu(xdu, data)
            good = (out, rc) == exp
            ok = ok and good
            print(f"{'OK' if good else 'FAIL'} xdu {name} {data!r} -> "
                  f"({out!r}, rc={rc}) {steps} lsteps  want {exp!r}")

    print(f"{'OK' if ok else 'FAIL'} lambda_eval")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
