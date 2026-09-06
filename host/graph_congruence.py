"""
Congruence: graph LO / ParStep(cd) NF == tree host == Lean goldens (where available).

Usage:  python host/graph_congruence.py
"""
from __future__ import annotations

import os
import re
import subprocess
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(_HOST)
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import GOLDENS, reduce as tree_reduce, reduce_cd as tree_reduce_cd, app, I, KK, S, B, K  # noqa: E402
from graph_runtime import reduce_tree_lo, reduce_tree_cd, Graph  # noqa: E402
from lambda_dialect import compute, show, GOLDENS as LAMBDA_GOLDENS  # noqa: E402
from graph_runtime import reduce_tree_pipeline  # noqa: E402


def normalize_label(s: str) -> str:
    return re.sub(r"\s+", " ", s.replace("\u2192", "->").strip())


def run_lean() -> dict[str, str]:
    r = subprocess.run(
        ["lake", "env", "lean", "--run", "Main.lean"],
        capture_output=True, text=True, cwd=ROOT, encoding="utf-8", errors="replace",
    )
    out = r.stdout + r.stderr
    results: dict[str, str] = {}
    label = None
    for line in out.splitlines():
        m = re.match(r"^[\u2713\u2717\u2714\u2716] (.+)$", line.strip())
        if m:
            label = normalize_label(m.group(1))
            continue
        sm = re.match(r"^\s+step\? \((\d+) steps?\): (.+)$", line)
        if sm and label:
            results[label] = sm.group(2).strip()
            label = None
    return results


def main() -> int:
    ok = True
    print("== IStep goldens: tree LO vs graph LO vs graph cd ==")
    for label, term, expected in GOLDENS:
        t_nf, _ = tree_reduce(term)
        g_lo, _, n_lo = reduce_tree_lo(term)
        g_cd, _, n_cd = reduce_tree_cd(term)
        t_cd, _ = tree_reduce_cd(term)
        match = (
            t_nf == expected
            and g_lo == expected
            and g_cd == expected
            and t_cd == expected
            and str(g_lo) == str(t_nf)
        )
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  tree={t_nf} graph_lo={g_lo} graph_cd={g_cd} "
              f"(nodes lo={n_lo} cd={n_cd})")
        if not match:
            ok = False
            print(f"  EXPECTED {expected}")

    print("\n== S-beta sharing (same x id) ==")
    g = Graph()
    # S I I K → (I K)(I K); both K args share
    root = g.import_tree(app(app(app(S, I), I), KK))
    after = g.step_lo(root)
    assert after is not None
    r = g.repr(after)
    la, ra = g.repr(g.left[r]), g.repr(g.right[r])
    lx, rx = g.repr(g.right[la]), g.repr(g.right[ra])
    share_ok = lx == rx
    print(f"{'OK' if share_ok else 'FAIL'} shared arg id={lx} (alloc={g.alloc_count()})")
    if not share_ok:
        ok = False

    print("\n== shared-parent kurzen ==")
    g2 = Graph()
    redex = g2.import_tree(app(I, KK))
    p1 = g2.mk_app(g2.atom(K.NORM), redex)
    p2 = g2.mk_app(g2.atom(K.KONST), redex)
    g2.step_lo(redex)
    from reduce import KK as KKonst
    kurz_ok = (
        g2.export_tree(g2.repr(g2.right[p1])) == KKonst
        and g2.export_tree(g2.repr(g2.right[p2])) == KKonst
    )
    print(f"{'OK' if kurz_ok else 'FAIL'} both parents observe forward")
    if not kurz_ok:
        ok = False

    print("\n== lambda applied NFs: tree pipeline vs graph pipeline ==")
    for src, expected in LAMBDA_GOLDENS:
        _, _, tree_nf, _, _ = compute(src)
        # bracket raw then graph pipeline
        from lambda_dialect import bracket, parse
        raw = bracket(parse(src))
        g_nf, b_n, i_n, nodes = reduce_tree_pipeline(raw)
        match = show(tree_nf) == expected and show(g_nf) == expected
        tag = "OK" if match else "FAIL"
        print(f"{tag} {src}  tree={show(tree_nf)} graph={show(g_nf)} "
              f"(b={b_n} i={i_n} nodes={nodes})")
        if not match:
            ok = False

    print("\n== Lean vs graph LO (pass --lean) ==")
    if "--lean" not in sys.argv:
        print("SKIP (use --lean to compare Main.lean)")
        return 0 if ok else 1
    try:
        lean = run_lean()
    except FileNotFoundError:
        lean = {}
        print("SKIP lake not found")
    if lean:
        for label, term, expected in GOLDENS:
            key = normalize_label(label)
            g_lo, _, _ = reduce_tree_lo(term)
            lnf = lean.get(key)
            if lnf is None:
                print(f"SKIP  {label} (Lean label missing)")
                continue
            got = str(g_lo)
            if lnf == got or lnf.replace(" ", "") == got.replace(" ", ""):
                print(f"OK    {label}  Lean={lnf}")
            else:
                if got == str(expected):
                    print(f"OK    {label}  graph={got} Lean={lnf} (string style differ)")
                else:
                    print(f"DRIFT {label}  Lean={lnf} graph={got}")
                    ok = False

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
