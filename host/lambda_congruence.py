"""Observational NF congruence for λ dialect (prefer basis, then IStep)."""
from __future__ import annotations

import os
import subprocess
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HOST)
sys.path.insert(0, _HOST)

from lambda_dialect import compute, show, compile_dialect, parse  # noqa: E402

COMPILE = [
    (r"\x. x", "I"),
    (r"\x. \y. x", "K"),
    (r"\x. \y. \z. (x z) (y z)", "S"),
    (r"\f. \g. \x. f (g x)", "B"),
    (r"\f. \x. \y. f y x", "C"),
]

APPLIED = [
    (r"(\x. x) K", "K"),
    (r"((\x. \y. x) S) I", "S"),
    (r"(((\x. \y. \z. (x z) (y z)) K) K) I", "I"),
    (r"((\x. \y. (y x)) S) I", "S"),
    (r"((\p. \q. p q p) (\a. \b. a) (\a. \b. a)) K I", "K"),
    (r"((\p. \q. p q p) (\a. \b. a) (\a. \b. b)) K I", "I"),
]


def main() -> int:
    ok = True
    for src, exp in COMPILE:
        c = show(compile_dialect(parse(src)))
        if c != exp:
            print(f"FAIL compile {src}: got {c} want {exp}")
            ok = False
        else:
            print(f"OK  compile {src} => {c}")

    for src, exp in APPLIED:
        raw, mid, nf, b_n, i_n = compute(src)
        got = show(nf)
        if got != exp:
            print(f"FAIL nf {src}: got {got} want {exp} (b={b_n} i={i_n})")
            ok = False
        else:
            print(f"OK  nf {src} => {got} (basis={b_n} istep={i_n})")

    r = subprocess.run(
        ["lake", "env", "lean", "src/ISAR/LambdaEval.lean"],
        cwd=_ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    errs = [ln for ln in (r.stdout + r.stderr).splitlines() if "error:" in ln.lower()]
    if r.returncode != 0 or errs:
        print("FAIL Lean LambdaEval.lean")
        ok = False
    else:
        print("OK  Lean LambdaEval.lean (proved abstract0; less compile work by design)")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
