"""Compare LO IStep vs cd (ParStep complete development) on Church/fact.

Dialect still does Turner + basis (C/W). Then either LO IStep or cd_loop.
"""
from __future__ import annotations

import math
import os
import sys
import time

_HOST = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HOST)

from reduce import reduce, reduce_cd  # noqa: E402
from lambda_dialect import bracket, reduce_basis, show  # noqa: E402
from lambda_bench import church, apply_id_k, fact_product, appn, EXP  # noqa: E402


def prep(e, fuel_basis=50_000):
    raw = bracket(e)
    mid, b = reduce_basis(raw, fuel=fuel_basis)
    return mid, b


def bench(label, e, fuel=5_000_000):
    mid, b = prep(e)
    t0 = time.perf_counter()
    nf_lo, steps_lo = reduce(mid, fuel=fuel)
    ms_lo = (time.perf_counter() - t0) * 1000
    t0 = time.perf_counter()
    nf_cd, rounds_cd = reduce_cd(mid, fuel=fuel)
    ms_cd = (time.perf_counter() - t0) * 1000
    same = show(nf_lo) == show(nf_cd)
    print(f"{label:<14} same={same}  nf={show(nf_lo)}")
    print(f"  LO IStep:  {ms_lo:10.2f}ms  steps={steps_lo}  (basis_pre={b})")
    print(f"  cd loop:   {ms_cd:10.2f}ms  rounds={rounds_cd}")
    if steps_lo and rounds_cd:
        print(f"  speedup:   {ms_lo/max(ms_cd,1e-9):.1f}x wall  |  {steps_lo/max(rounds_cd,1):.1f}x fewer rounds")
    return same


def main():
    sys.setrecursionlimit(20000)
    ok = True
    print("LO IStep vs cd  (after Turner+basis)\n")

    for n in [10, 50, 100, 200, 500]:
        ok &= bench(f"c{n} I K", apply_id_k(church(n)))

    print()
    for n in [4, 6, 8, 10]:
        ok &= bench(f"2^{n}", apply_id_k(appn(EXP, church(2), church(n))))

    print()
    for n in [5, 6, 7]:
        ok &= bench(f"fact{n}", apply_id_k(fact_product(n)),
                    fuel=max(2_000_000, math.factorial(n) * 20))

    return 0 if ok else 1


if __name__ == "__main__":
    sys.setrecursionlimit(5000)
    sys.exit(main())
