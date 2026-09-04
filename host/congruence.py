"""
Congruence check: host reduce.py output == Lean isar-reduce output.

Usage:  python host/congruence.py
Requires: lake env lean --run Main.lean (golden suite mode) to be runnable.
"""
from __future__ import annotations
import subprocess, sys, re, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def normalize_label(s: str) -> str:
    """Strip unicode arrows and extra whitespace for matching."""
    return re.sub(r"\s+", " ", s.replace("\u2192", "->").strip())


def run_lean() -> dict[str, str]:
    """Run Lean golden suite, parse label -> NF mapping."""
    r = subprocess.run(
        ["lake", "env", "lean", "--run", "Main.lean"],
        capture_output=True, text=True, cwd=ROOT, encoding="utf-8", errors="replace"
    )
    out = r.stdout + r.stderr
    results = {}
    label = None
    for line in out.splitlines():
        # Match golden header lines: "V label" or "X label"
        m = re.match(r"^[\u2713\u2717\u2714\u2716] (.+)$", line.strip())
        if m:
            label = normalize_label(m.group(1))
            continue
        sm = re.match(r"^\s+step\? \((\d+) steps?\): (.+)$", line)
        if sm and label:
            results[label] = sm.group(2).strip()
            label = None
    return results


def run_host() -> dict[str, str]:
    """Run host golden suite, parse label -> NF mapping."""
    r = subprocess.run(
        [sys.executable, "host/reduce.py"],
        capture_output=True, text=True, cwd=ROOT, encoding="utf-8", errors="replace"
    )
    results = {}
    for line in r.stdout.splitlines():
        m = re.match(r"^(?:OK|FAIL) (.+?)\s+=>\s+(.+?)\s+\(\d+ steps?\)$", line.strip())
        if m:
            results[normalize_label(m.group(1))] = m.group(2).strip()
    return results


def main() -> int:
    lean = run_lean()
    host = run_host()
    if not lean:
        print("ERROR: no Lean output parsed"); return 1
    if not host:
        print("ERROR: no host output parsed"); return 1

    ok = True
    all_labels = sorted(set(lean) | set(host), key=lambda s: s.encode("ascii", "replace"))
    for label in all_labels:
        l = lean.get(label)
        h = host.get(label)
        if l is None:
            print(f"SKIP  {label}  (Lean missing)"); continue
        if h is None:
            print(f"SKIP  {label}  (host missing)"); continue
        if l == h:
            print(f"OK    {label}  NF={l}")
        else:
            print(f"DRIFT {label}  Lean={l}  host={h}")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
