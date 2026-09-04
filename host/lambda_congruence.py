"""Congruence: host λ compile+reduce vs Lean LambdaEval expectations (fixed fixtures)."""
from __future__ import annotations

import os
import subprocess
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HOST)
sys.path.insert(0, _HOST)

from lambda_dialect import compute, show, compile_named, parse  # noqa: E402


# Fixtures mirrored in src/ISAR/LambdaEval.lean
FIXTURES = [
    # (host source, expected compile show, expected nf show)
    ("\\x. x", "I", "I"),
    ("\\x. \\y. x", "((B K) I)", "((B K) I)"),
    ("(\\x. x) K", "(I K)", "K"),
    ("((\\x. \\y. x) S) I", "((((B K) I) S) I)", "S"),
    ("(((\\x. \\y. \\z. (x z) (y z)) K) K) I", None, "I"),  # compile too big; NF only
]


def main() -> int:
    ok = True
    for src, exp_c, exp_nf in FIXTURES:
        compiled, nf, steps = compute(src)
        c_s, n_s = show(compiled), show(nf)
        if exp_c is not None and c_s != exp_c:
            print(f"FAIL compile {src}: got {c_s} want {exp_c}")
            ok = False
        elif n_s != exp_nf:
            print(f"FAIL nf {src}: got {n_s} want {exp_nf} ({steps} steps)")
            ok = False
        else:
            print(f"OK  {src}  compile={c_s}  nf={n_s}  ({steps} steps)")

    # Lean #guard file must typecheck
    r = subprocess.run(
        ["lake", "env", "lean", "src/ISAR/LambdaEval.lean"],
        cwd=_ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    # filter noise; fail on "error:"
    err_lines = [ln for ln in (r.stdout + r.stderr).splitlines() if "error:" in ln.lower()]
    if r.returncode != 0 or err_lines:
        print("FAIL Lean LambdaEval.lean")
        for ln in err_lines[:10]:
            print(" ", ln)
        ok = False
    else:
        print("OK  Lean LambdaEval.lean #guard")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
