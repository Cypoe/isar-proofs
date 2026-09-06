"""
Timed λ dialect bench — SKI / Church / factorials.

Pipeline: Turner -> prefer IStepBasis else IStep.
Lean abstract0: proved compiler that does less work on purpose (no η/C).
"""
from __future__ import annotations

import os
import sys
import time
from typing import List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from lambda_dialect import (  # noqa: E402
    NAbs, NApp, NVar, NComb, NExpr,
    compute, compute_expr, compile_dialect, parse, show, I, KK,
)

# Shared combinators as NExpr
_I = NComb(I)
_K = NComb(KK)
SUCC = parse(r"\n. \f. \x. f (n f x)")
PLUS = parse(r"\m. \n. \f. \x. m f (n f x)")
MULT = parse(r"\m. \n. \f. m (n f)")
EXP = parse(r"\m. \n. n m")  # m^n  (n applied to m)


def church(n: int) -> NExpr:
    r"""Church numeral \f. \x. f^n x."""
    body: NExpr = NVar("x")
    for _ in range(n):
        body = NApp(NVar("f"), body)
    return NAbs("f", NAbs("x", body))


def appn(*xs: NExpr) -> NExpr:
    assert xs
    t = xs[0]
    for x in xs[1:]:
        t = NApp(t, x)
    return t


def fact_product(n: int) -> NExpr:
    """Church n! as (...((1*2)*3)*...*n) via MULT — no Y."""
    acc = church(1)
    for k in range(2, n + 1):
        acc = appn(MULT, church(k), acc)
    return acc


def apply_id_k(num: NExpr) -> NExpr:
    """num I K  — Church n applied to I,K reduces to K (n times Iβ)."""
    return appn(num, _I, _K)


# ---------------------------------------------------------------------------
# Small string goldens (quick regression)
# ---------------------------------------------------------------------------

STRING_CASES: List[Tuple[str, str, Optional[str]]] = [
    ("I", r"\x. x", "I"),
    ("K", r"\x. \y. x", "K"),
    ("S", r"\x. \y. \z. (x z) (y z)", "S"),
    ("B", r"\f. \g. \x. f (g x)", "B"),
    ("C", r"\f. \x. \y. f y x", "C"),
    ("Ix", r"(\x. x) K", "K"),
    ("SKKx", r"(((\x. \y. \z. (x z) (y z)) K) K) I", "I"),
    ("flip", r"((\x. \y. (y x)) S) I", "S"),
    ("and-TT", r"((\p. \q. p q p) (\a. \b. a) (\a. \b. a)) K I", "K"),
    ("or-FT", r"((\p. \q. p p q) (\a. \b. b) (\a. \b. a)) K I", "K"),
]


def _time_expr(e: NExpr, expected: Optional[str], rounds: int, fuel: int):
    t0 = time.perf_counter()
    last = None
    for _ in range(rounds):
        last = compute_expr(e, fuel=fuel)
    ms = (time.perf_counter() - t0) * 1000.0 / rounds
    raw, mid, nf, b_n, i_n = last  # type: ignore
    got = show(nf)
    ok = True if expected is None else (got == expected)
    return ok, got, b_n, i_n, ms


def main(argv: List[str]) -> int:
    rounds = 20
    if len(argv) >= 2 and argv[0] == "--rounds":
        rounds = int(argv[1])

    import sys as _sys
    _sys.setrecursionlimit(5000)

    ok_all = True
    print(f"lambda dialect bench  (rounds={rounds})")
    print(f"{'label':<16} {'ok':<4} {'ms':>10} {'b':>5} {'i':>7}  nf")
    print("-" * 72)

    # --- string suite ---
    for label, src, exp in STRING_CASES:
        e = parse(src)
        ok, got, b_n, i_n, ms = _time_expr(e, exp, rounds, fuel=10_000)
        if not ok:
            ok_all = False
        print(f"{label:<16} {'OK' if ok else 'FAIL':<4} {ms:10.3f} {b_n:5d} {i_n:7d}  {got}")
        if not ok:
            print(f"  want={exp}  src={src}")

    # --- Church numerals: c_n I K -> K ---
    print("\n-- church n  (n I K -> K) --")
    for n in [0, 1, 2, 3, 5, 10, 20, 50, 100, 200, 500]:
        e = apply_id_k(church(n))
        # larger n: fewer rounds
        r = rounds if n <= 50 else max(1, rounds // 5)
        fuel = max(10_000, n * 4 + 100)
        ok, got, b_n, i_n, ms = _time_expr(e, "K", r, fuel=fuel)
        if not ok:
            ok_all = False
        print(f"{'c'+str(n)+'-IK':<16} {'OK' if ok else 'FAIL':<4} {ms:10.3f} {b_n:5d} {i_n:7d}  {got}")

    # --- exp: 2^n via EXP ---
    print("\n-- exp 2^n  ((EXP c2) cn) I K -> K --")
    for n in [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]:
        # 2^n
        e = apply_id_k(appn(EXP, church(2), church(n)))
        r = rounds if n <= 6 else max(1, rounds // 10)
        fuel = max(50_000, (1 << n) * 4 + 1000)
        ok, got, b_n, i_n, ms = _time_expr(e, "K", r, fuel=fuel)
        if not ok:
            ok_all = False
        print(f"{'2^'+str(n):<16} {'OK' if ok else 'FAIL':<4} {ms:10.3f} {b_n:5d} {i_n:7d}  {got}")

    # --- factorials via product tower ---
    print("\n-- fact n! via MULT tower  (fact I K -> K) --")
    for n in [1, 2, 3, 4, 5, 6, 7, 8, 9]:
        import math
        nfacts = math.factorial(n)
        e = apply_id_k(fact_product(n))
        r = 3 if n <= 6 else (1 if n <= 8 else 1)
        # MULT tower needs more than n! I-steps (observed ~5-6x at n=7)
        fuel = max(200_000, nfacts * 12 + 50_000)
        ok, got, b_n, i_n, ms = _time_expr(e, "K", r, fuel=fuel)
        if not ok:
            ok_all = False
        print(f"{'fact'+str(n)+'='+str(nfacts):<16} {'OK' if ok else 'FAIL':<4} {ms:10.3f} {b_n:5d} {i_n:7d}  {got if ok else got[:40]+'...'}")

    # --- compile size for large church ---
    print("\n-- compile church(n) only --")
    for n in [10, 50, 100, 200, 500]:
        t0 = time.perf_counter()
        out = None
        rr = 10 if n <= 100 else 3
        for _ in range(rr):
            out = compile_dialect(church(n))
        ms = (time.perf_counter() - t0) * 1000.0 / rr
        s = show(out)
        print(f"  c{n:<4}  {ms:8.3f}ms  compiled_chars={len(s)}")

    print("-" * 72)
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
