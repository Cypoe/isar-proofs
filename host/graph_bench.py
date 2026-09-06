"""
Tree vs graph bench — Church / 2^n / fact.

Proves composition-shaped sharing: same NFs, report wall ms + unique nodes
(graph) vs tree-size proxy (unfolded node count).
"""
from __future__ import annotations

import math
import os
import sys
import time
from typing import List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, K  # noqa: E402
from lambda_dialect import (  # noqa: E402
    NAbs, NApp, NVar, NComb, NExpr,
    compute_expr, compute_expr_graph, bracket, show, I, KK, parse,
)
from lambda_bench import church, appn, fact_product, apply_id_k, EXP, STRING_CASES  # noqa: E402


def tree_size(t: T) -> int:
    """Unfolded size (no sharing) — proxy for tree LO heap pressure."""
    if t.k != K.APP:
        return 1
    assert t.l is not None and t.r is not None
    return 1 + tree_size(t.l) + tree_size(t.r)


def _time_tree(e: NExpr, expected: Optional[str], rounds: int, fuel: int):
    t0 = time.perf_counter()
    last = None
    for _ in range(rounds):
        last = compute_expr(e, fuel=fuel)
    ms = (time.perf_counter() - t0) * 1000.0 / rounds
    raw, mid, nf, b_n, i_n = last  # type: ignore
    got = show(nf)
    ok = True if expected is None else (got == expected)
    return ok, got, b_n, i_n, ms, tree_size(nf), tree_size(raw)


def _time_graph(e: NExpr, expected: Optional[str], rounds: int, fuel: int):
    t0 = time.perf_counter()
    last = None
    for _ in range(rounds):
        last = compute_expr_graph(e, fuel=fuel)
    ms = (time.perf_counter() - t0) * 1000.0 / rounds
    raw, mid, nf, b_n, i_n, nodes = last  # type: ignore
    got = show(nf)
    ok = True if expected is None else (got == expected)
    return ok, got, b_n, i_n, ms, nodes, tree_size(raw)


def main(argv: List[str]) -> int:
    rounds = 5
    if len(argv) >= 2 and argv[0] == "--rounds":
        rounds = int(argv[1])

    sys.setrecursionlimit(10_000)
    ok_all = True

    print(f"tree vs graph bench  (rounds={rounds})")
    print(f"{'label':<14} {'ok':<4} {'tree_ms':>9} {'graph_ms':>9} "
          f"{'t_raw':>7} {'g_nodes':>8} {'b':>4} {'i':>6}")
    print("-" * 78)

    def row(label: str, e: NExpr, exp: Optional[str], r: int, fuel: int) -> None:
        nonlocal ok_all
        ok_t, got_t, b_t, i_t, ms_t, _, raw_sz = _time_tree(e, exp, r, fuel)
        ok_g, got_g, b_g, i_g, ms_g, nodes, _ = _time_graph(e, exp, r, fuel)
        ok = ok_t and ok_g and got_t == got_g
        if not ok:
            ok_all = False
        print(f"{label:<14} {'OK' if ok else 'FAIL':<4} {ms_t:9.3f} {ms_g:9.3f} "
              f"{raw_sz:7d} {nodes:8d} {b_g:4d} {i_g:6d}")
        if not ok:
            print(f"  tree={got_t} graph={got_g} want={exp}")

    for label, src, exp in STRING_CASES[:8]:
        row(label, parse(src), exp, rounds, 10_000)

    print("\n-- church n I K -> K --")
    for n in [0, 1, 2, 5, 10, 20, 50, 100]:
        e = apply_id_k(church(n))
        r = rounds if n <= 50 else max(1, rounds // 3)
        fuel = max(10_000, n * 4 + 100)
        row(f"c{n}-IK", e, "K", r, fuel)

    print("\n-- exp 2^n I K -> K --")
    for n in [0, 1, 2, 3, 4, 5, 6, 7, 8]:
        e = apply_id_k(appn(EXP, church(2), church(n)))
        r = rounds if n <= 5 else max(1, rounds // 5)
        fuel = max(50_000, (1 << n) * 4 + 1000)
        row(f"2^{n}", e, "K", r, fuel)

    print("\n-- fact n! via MULT tower --")
    for n in [1, 2, 3, 4, 5, 6, 7]:
        nfacts = math.factorial(n)
        e = apply_id_k(fact_product(n))
        r = 2 if n <= 5 else 1
        fuel = max(200_000, nfacts * 12 + 50_000)
        row(f"fact{n}", e, "K", r, fuel)

    print("\nDone." if ok_all else "\nFAILURES.", flush=True)
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
