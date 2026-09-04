"""λ dialect congruence: observational NFs after Turner → basis → IStep.

Lean LambdaEval (conservative abstract0) is not a peer dialect column —
it only checks that the proved weaker compiler still builds.
"""
from __future__ import annotations

import os
import subprocess
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HOST)
sys.path.insert(0, _HOST)

from lambda_dialect import compute, show, compile_dialect, parse  # noqa: E402

COMPILE = [
    ("\\x. x", "I"),
    ("\\x. \\y. x", "K"),
    ("\\x. \\y. \\z. (x z) (y z)", "S"),
]

APPLIED = [
    ("(\\x. x) K", "K"),
    ("((\\x. \\y. x) S) I", "S"),
    ("(((\\x. \\y. \\z. (x z) (y z)) K) K) I", "I"),
    ("((\\x. \\y. (y x)) S) I", "S"),
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
        raw, mid, nf, steps = compute(src)
        got = show(nf)
        if got != exp:
            print(f"FAIL nf {src}: got {got} want {exp} (turner={show(raw)} basis={show(mid)})")
            ok = False
        else:
            print(f"OK  nf {src} => {got} ({steps} IStep)")

    r = subprocess.run(
        ["lake", "env", "lean", "src/ISAR/LambdaEval.lean"],
        cwd=_ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    errs = [ln for ln in (r.stdout + r.stderr).splitlines() if "error:" in ln.lower()]
    if r.returncode != 0 or errs:
        print("FAIL Lean LambdaEval.lean (weaker proved compiler still must build)")
        for ln in errs[:8]:
            print(" ", ln)
        ok = False
    else:
        print("OK  Lean LambdaEval.lean builds (weaker abstract0; not dialect authority)")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
