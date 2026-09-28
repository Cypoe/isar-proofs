"""
Registry-driven battery: the run list comes from host/toolchain.json —
unique obligation suites (registry order) plus selftests — never a
hand-maintained HOST_SUITES list.

Suite exit protocol: 0 pass | nonzero fail | 77 whole-suite skip (env).
A suite exiting 0 whose output has a `SKIP` line is status pass* with
the skipped legs listed.

Tiers: fast < full < env.  --tier fast runs fast items only; --tier full
runs fast+full; --tier all additionally runs env items whose `requires`
tools are resolvable.  A suite whose tools are missing is status skip
("env: missing X"); a suite above the tier filter is skip ("tier ...").

Usage: python battery.py [--tier fast|full|all] [--json] [--skip-seed]
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import time

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_REPO = os.path.dirname(_HOST)
_SEED = os.path.join(_REPO, "seed")
_JSON_OUT = os.path.join(_SEED, "build", "battery_last.json")

import toolchain  # noqa: E402

SKIP_RE = re.compile(r"^\s*SKIP\b", re.M)
TIER_LEVEL = {"fast": 0, "full": 1, "env": 2}
_LLVM_BIN = (r"C:\Program Files\clang+llvm-18.1.8-x86_64-pc-windows-msvc"
             r"\bin")
_FASMG_DEFAULT = os.path.normpath(os.path.join(
    _REPO, "..", "isa-physics", "boostrap", "fasmg", "fasmg.exe"))


def tool_present(name: str) -> bool:
    """PATH lookup plus the toolchain's own resolvable fallbacks:
    fasmg via ISAR_FASMG / repo-relative default; llvm-mc/llvm-objcopy
    via the LLVM bin dir the isa modules use."""
    if shutil.which(name):
        return True
    if name == "fasmg":
        return os.path.exists(os.environ.get("ISAR_FASMG", _FASMG_DEFAULT))
    if name in ("llvm-mc", "llvm-objcopy"):
        return os.path.exists(os.path.join(_LLVM_BIN, name + ".exe"))
    return False


def _lake_decls(decls) -> list:
    """Missing lean decls: last component must appear as a
    theorem/def/structure/lemma (optionally dotted) in src/ISAR/*.lean."""
    import glob
    src = ""
    for f in glob.glob(os.path.join(_REPO, "src", "ISAR", "*.lean")):
        src += open(f, encoding="utf-8").read()
    missing = []
    for d in decls:
        last = d.rsplit(".", 1)[-1]
        if not re.search(
                rf"\b(?:theorem|def|structure|lemma)\s+"
                rf"(?:[\w'.]+\.)*{re.escape(last)}\b", src):
            missing.append(d)
    return missing


def run_suite(name: str, cmd: list, cwd: str) -> dict:
    t0 = time.monotonic()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    dt = time.monotonic() - t0
    out = p.stdout + p.stderr
    skipped = [l.strip() for l in out.splitlines() if SKIP_RE.match(l)]
    if p.returncode == 77:
        status = "skip"
    elif p.returncode == 0:
        status = "pass*" if skipped else "pass"
    else:
        status = "fail"
    r = {"status": status, "ok": status in ("pass", "pass*"),
         "seconds": round(dt, 3), "skipped": skipped, "reason": ""}
    if status == "fail":
        r["tail"] = "\n".join(out.splitlines()[-30:])
    if status == "skip" and not skipped:
        r["reason"] = "suite exited 77"
    return r


def main() -> int:
    tier = "fast"
    for i, a in enumerate(sys.argv[1:]):
        if a == "--tier":
            tier = sys.argv[i + 2]
    want_json = "--json" in sys.argv[1:]
    skip_seed = "--skip-seed" in sys.argv[1:]
    level = TIER_LEVEL[tier]
    print(f"python {sys.version.split()[0]} {sys.executable}  tier={tier}")

    obs = toolchain.obligations()
    suites_order = []
    for o in obs:
        if o.suite not in suites_order:
            suites_order.append(o.suite)
    selftests = toolchain.selftests()

    def suite_items(suite):
        oi = [o for o in obs if o.suite == suite]
        si = [s for s in selftests if s.module == suite]
        return oi, si

    results = {}
    for suite in suites_order + [s.module for s in selftests
                                 if s.module not in suites_order]:
        if suite == "seed" and skip_seed:
            continue
        oi, si = suite_items(suite)
        reqs = sorted({r for x in list(oi) + list(si)
                       for r in x.requires})
        stier = "env" if reqs else max(
            (TIER_LEVEL[x.tier] for x in list(oi) + list(si)),
            default=0)
        stier = "env" if reqs else {0: "fast", 1: "full"}[stier]
        missing = [r for r in reqs if not tool_present(r)]
        if missing:
            results[suite] = {"status": "skip", "ok": True, "seconds": 0.0,
                              "skipped": [],
                              "reason": f"env: missing {' '.join(missing)}"}
            continue
        if TIER_LEVEL[stier] > level:  # tier-filtered out
            results[suite] = {"status": "skip", "ok": True, "seconds": 0.0,
                              "skipped": [],
                              "reason": ("tier env (needs --tier all)"
                                         if stier == "env"
                                         else f"tier {stier} "
                                         f"(needs --tier {stier}|all)")}
            continue
        args = [a for x in list(oi) + list(si) for a in x.args]
        if suite == "lake":
            r = run_suite("lake", ["lake", "build",
                                   "ISAR.ObservationRegime",
                                   "ISAR.InvariantLayer", "ISAR.Futamura"],
                          _REPO)
            if r["status"] in ("pass", "pass*"):
                miss = _lake_decls(
                    d for o in oi for d in o.lean_decls)
                if miss:
                    r["status"], r["ok"] = "fail", False
                    r["reason"] = "lean decls missing: " + ", ".join(miss)
            results[suite] = r
        elif suite == "seed":
            results[suite] = run_suite(
                "seed", [sys.executable, "seed.py"] + args, _SEED)
        else:
            results[suite] = run_suite(
                suite, [sys.executable, suite + ".py"] + args, _HOST)

    ok = True
    for o in obs:
        r = results.get(o.suite)
        if r is None:
            status, sec = "·", 0.0
        else:
            status, sec = r["status"].upper().replace("*", "*"), r["seconds"]
        if r and r["status"] == "fail":
            ok = False
        reg = o.regime or "—"
        print(f"{o.id:4s} {o.family}/{o.evidence:<10s} {reg:<18s} "
              f"{status:5s} ({sec:.1f}s)")
    for s in selftests:
        r = results.get(s.module)
        if r is None:
            continue
        if r["status"] == "fail":
            ok = False
        note = r["reason"] or "; ".join(r["skipped"])
        print(f"selftest {s.module:30s} {r['status']:5s} "
              f"({r['seconds']:.1f}s) {note}")
    npass = sum(1 for r in results.values()
                if r["status"] in ("pass", "pass*"))
    nfail = sum(1 for r in results.values() if r["status"] == "fail")
    nskip = sum(1 for r in results.values() if r["status"] == "skip")
    print(f"battery: {npass} pass, {nfail} fail, {nskip} skip "
          f"({len(results)} suites)")
    for name, r in results.items():
        if r["status"] == "fail":
            print(f"--- {name} tail ---\n{r.get('tail', '')}")
    if want_json:
        os.makedirs(os.path.dirname(_JSON_OUT), exist_ok=True)
        with open(_JSON_OUT, "w", encoding="utf-8", newline="\n") as f:
            json.dump({"python": sys.executable, "suites": {
                k: {kk: v[kk] for kk in
                    ("status", "ok", "seconds", "skipped", "reason")}
                for k, v in results.items()}}, f, indent=2)
        print(f"wrote {_JSON_OUT}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
