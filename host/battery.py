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
("env: missing X").  A suite above the tier filter is NOT-RUN: printed
as such on the console and NOT recorded in battery_last.json (`skip` is
reserved for missing tools and exit-77).

Every suite streams: stdout+stderr merged, teed line-by-line to
seed/build/battery_logs/<suite>.log (fresh each run).  If a suite is
silent for 60s a heartbeat line is printed.  An optional per-suite
`timeout_s` (registry field, positive int) kills the process tree and
records a fail.  --verbose echoes child lines prefixed `  <suite>| `.

`--only a,b,c` runs just those suites (tier filter ignored; env
`requires` still enforced) and merges their records into an existing
battery_last.json.  Every record carries `commit` (HEAD sha, `+dirty`
if host/seed has uncommitted changes) and `at` (ISO timestamp).

Usage: python battery.py [--tier fast|full|all] [--json] [--skip-seed]
                         [--verbose] [--only suite,suite,...]
"""
from __future__ import annotations

import json
import os
import queue
import re
import shutil
import subprocess
import sys
import threading
import time

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_REPO = os.path.dirname(_HOST)
_SEED = os.path.join(_REPO, "seed")
_JSON_OUT = os.path.join(_SEED, "build", "battery_last.json")
_LOG_DIR = os.path.join(_SEED, "build", "battery_logs")
_HEARTBEAT_S = 60

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
    if name.startswith("wsl:"):
        # WSL-side tool (binfmt qemu, ld, …): probe inside the distro.
        try:
            cp = subprocess.run(
                ["wsl", "-e", "sh", "-c", f"command -v {name[4:]}"],
                capture_output=True, timeout=30)
            return cp.returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            return False
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


def run_suite(name: str, cmd: list, cwd: str, verbose: bool = False,
              timeout: int = None) -> dict:
    """Stream child output (merged stderr) line-by-line into
    battery_logs/<name>.log; heartbeat every 60s of silence; kill the
    process tree on `timeout` seconds."""
    os.makedirs(_LOG_DIR, exist_ok=True)
    log_path = os.path.join(_LOG_DIR, name + ".log")
    env = dict(os.environ)
    if os.path.basename(str(cmd[0])).lower().startswith("python"):
        env["PYTHONUNBUFFERED"] = "1"
        env["PYTHONIOENCODING"] = "utf-8"
    t0 = time.monotonic()
    q = queue.Queue()
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, bufsize=1,
                         errors="replace")

    def reader():
        for line in p.stdout:
            q.put(line)
        q.put(None)

    threading.Thread(target=reader, daemon=True).start()
    lines, last_line = [], ""
    timed_out = False
    done = False
    with open(log_path, "w", encoding="utf-8", newline="\n") as log:
        while not done:
            wait = _HEARTBEAT_S
            if timeout:
                wait = min(wait, max(1.0, timeout - (time.monotonic() - t0)))
            try:
                item = q.get(timeout=wait)
            except queue.Empty:
                if timeout and time.monotonic() - t0 > timeout:
                    subprocess.run(["taskkill", "/T", "/F", "/PID",
                                    str(p.pid)], capture_output=True)
                    timed_out = True
                    break
                el = int(time.monotonic() - t0)
                print(f"  ... {name} still running ({el}s elapsed, "
                      f"last line: {last_line[-80:]!r})")
                continue
            if item is None:
                done = True
            else:
                lines.append(item)
                last_line = item.rstrip("\n")
                log.write(item)
                log.flush()
                if verbose:
                    print(f"  {name}| {item}", end="")
            if timeout and time.monotonic() - t0 > timeout:
                subprocess.run(["taskkill", "/T", "/F", "/PID",
                                str(p.pid)], capture_output=True)
                timed_out = True
                break
    p.wait()
    dt = time.monotonic() - t0
    out = "".join(lines)
    skipped = [l.strip() for l in out.splitlines() if SKIP_RE.match(l)]
    if timed_out:
        status = "fail"
    elif p.returncode == 77:
        status = "skip"
    elif p.returncode == 0:
        status = "pass*" if skipped else "pass"
    else:
        status = "fail"
    r = {"status": status, "ok": status in ("pass", "pass*"),
         "seconds": round(dt, 3), "skipped": skipped, "reason": "",
         "log": log_path}
    if timed_out:
        r["reason"] = f"timeout {timeout}s"
    if status == "fail":
        r["tail"] = "\n".join(out.splitlines()[-30:])
    if status == "skip" and not skipped:
        r["reason"] = "suite exited 77"
    return r


def main() -> int:
    sys.stdout.reconfigure(line_buffering=True, encoding="utf-8",
                           errors="replace")
    sys.stderr.reconfigure(line_buffering=True, encoding="utf-8",
                           errors="replace")
    tier = "fast"
    for i, a in enumerate(sys.argv[1:]):
        if a == "--tier":
            tier = sys.argv[i + 2]
    want_json = "--json" in sys.argv[1:]
    skip_seed = "--skip-seed" in sys.argv[1:]
    verbose = "--verbose" in sys.argv[1:]
    only = None
    for i, a in enumerate(sys.argv[1:]):
        if a == "--only":
            only = set(sys.argv[i + 2].split(","))
    level = {"fast": 0, "full": 1, "all": 2}.get(tier)
    if level is None:
        print(f"usage: --tier fast|full|all")
        return 2
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

    def _commit():
        try:
            sha = subprocess.run(
                ["git", "rev-parse", "--short", "HEAD"], cwd=_REPO,
                capture_output=True, text=True).stdout.strip()
            dirty = subprocess.run(
                ["git", "status", "--porcelain", "--", "host", "seed"],
                cwd=_REPO, capture_output=True, text=True).stdout.strip()
            return sha + ("+dirty" if dirty else "")
        except OSError:
            return "?"
    commit = _commit()

    results = {}
    not_run = {}
    for suite in suites_order + [s.module for s in selftests
                                 if s.module not in suites_order]:
        if suite == "seed" and skip_seed:
            continue
        if only is not None and suite not in only:
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
            reason = f"env: missing {' '.join(missing)}"
            results[suite] = {"status": "skip", "ok": True, "seconds": 0.0,
                              "skipped": [], "reason": reason,
                              "commit": commit,
                              "at": time.strftime("%Y-%m-%dT%H:%M:%S")}
            print(f"SKIP {suite}  {reason}")
            continue
        if only is None and TIER_LEVEL[stier] > level:  # NOT-RUN
            not_run[suite] = stier
            print(f"NOT-RUN {suite}  (tier {stier})")
            continue
        args = [a for x in list(oi) + list(si) for a in x.args]
        timeouts = [x.timeout_s for x in list(oi) + list(si)
                    if x.timeout_s]
        timeout = max(timeouts) if timeouts else None
        ids = ",".join(o.id for o in oi) or "-"
        print(f"RUN  {suite}  [{ids}]  tier={stier}")
        if suite == "lake":
            r = run_suite("lake", ["lake", "build",
                                   "ISAR.ObservationRegime",
                                   "ISAR.InvariantLayer", "ISAR.Futamura"],
                          _REPO, verbose=verbose, timeout=timeout)
            if r["status"] in ("pass", "pass*"):
                miss = _lake_decls(
                    d for o in oi for d in o.lean_decls)
                if miss:
                    r["status"], r["ok"] = "fail", False
                    r["reason"] = "lean decls missing: " + ", ".join(miss)
            results[suite] = r
        elif suite == "seed":
            results[suite] = run_suite(
                "seed", [sys.executable, "seed.py"] + args, _SEED,
                verbose=verbose, timeout=timeout)
        else:
            results[suite] = run_suite(
                suite, [sys.executable, suite + ".py"] + args, _HOST,
                verbose=verbose, timeout=timeout)
        r = results[suite]
        r["commit"] = commit
        r["at"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        note = f" log={r['log']}" if r["status"] in ("fail", "pass*") else ""
        print(f"  -> {suite} {r['status']} ({r['seconds']:.1f}s){note}")

    ok = True
    for o in obs:
        r = results.get(o.suite)
        if r is None:
            status, sec = (f"NOT-RUN (tier {not_run[o.suite]})", 0.0) \
                if o.suite in not_run else ("·", 0.0)
        else:
            status, sec = r["status"].upper(), r["seconds"]
        if r and r["status"] == "fail":
            ok = False
        reg = o.regime or "—"
        print(f"{o.id:4s} {o.family}/{o.evidence:<10s} {reg:<18s} "
              f"{status:5s} ({sec:.1f}s)")
    for s in selftests:
        r = results.get(s.module)
        if r is None:
            if s.module in not_run:
                print(f"selftest {s.module:30s} NOT-RUN (tier "
                      f"{not_run[s.module]})")
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
        doc = {"python": sys.executable, "suites": {}}
        if only is not None and os.path.exists(_JSON_OUT):
            try:
                doc = json.load(open(_JSON_OUT, encoding="utf-8"))
                doc["python"] = sys.executable
            except (OSError, ValueError):
                pass
        doc["suites"].update({
            k: {kk: v[kk] for kk in
                ("status", "ok", "seconds", "skipped", "reason",
                 "commit", "at") if kk in v}
            for k, v in results.items()})
        with open(_JSON_OUT, "w", encoding="utf-8", newline="\n") as f:
            json.dump(doc, f, indent=2)
        print(f"wrote {_JSON_OUT}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
