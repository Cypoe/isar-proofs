"""
One-command test battery: run each host suite (and the seed gate) as a
subprocess, print one OK|FAIL line per suite, dump captured output on failure.

Usage: python battery.py [--skip-seed]   (the seed gate needs fasmg.exe)
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time

_HOST = os.path.dirname(os.path.abspath(__file__))
_SEED = os.path.join(os.path.dirname(_HOST), "seed")
_JSON_OUT = os.path.join(_SEED, "build", "battery_last.json")

HOST_SUITES = [
    "cogen.py",
    "congruence.py",
    "graph_congruence.py",
    "observational_suite.py",
    "mine_adopt.py",
    "tower.py",
    "isa_x86_64.py",
    "isa_aarch64.py",
    "routines_x86_64_win64.py",
    "routines_x86_64_win64_cd.py",
    "routines_x86_64_linux_lo.py",
    "target_pe64.py",
    "target_elf64.py",
    "toolchain.py",
    "spec_project.py",
    "spec_check.py",
    "futamura_cube.py",
    "xdu_dialect.py",
    "routines_x86_64_win64_xdu.py",
    "xdu_gate.py",
    "spec_term.py",
    "lambda_eval.py",
    "lean_eval.py",
]


def run_suite(name: str, script: str, cwd: str) -> tuple[bool, float, str]:
    t0 = time.monotonic()
    p = subprocess.run(
        [sys.executable, script],
        cwd=cwd,
        capture_output=True,
        text=True,
    )
    dt = time.monotonic() - t0
    return p.returncode == 0, dt, p.stdout + p.stderr


def main() -> int:
    skip_seed = "--skip-seed" in sys.argv[1:]
    want_json = "--json" in sys.argv[1:]
    print(f"python {sys.version.split()[0]} {sys.executable}")
    ok = True
    suites = {}
    for script in HOST_SUITES:
        name = os.path.splitext(script)[0]
        good, dt, out = run_suite(name, script, _HOST)
        print(f"{'OK' if good else 'FAIL'} {name} ({dt:.1f}s)")
        suites[name] = {"ok": good, "seconds": round(dt, 3)}
        if not good:
            ok = False
            print(out)
    if not skip_seed:
        good, dt, out = run_suite("seed", "seed.py", _SEED)
        print(f"{'OK' if good else 'FAIL'} seed ({dt:.1f}s)")
        suites["seed"] = {"ok": good, "seconds": round(dt, 3)}
        if not good:
            ok = False
            print(out)
    if want_json:
        os.makedirs(os.path.dirname(_JSON_OUT), exist_ok=True)
        with open(_JSON_OUT, "w", encoding="utf-8", newline="\n") as f:
            json.dump({"python": sys.executable, "suites": suites}, f,
                      indent=2)
        print(f"wrote {_JSON_OUT}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
