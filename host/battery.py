"""
Registry-driven battery: the run list comes from host/toolchain.json —
obligation run units (suite, args) in registry order plus selftests —
never a hand-maintained HOST_SUITES list.

Suite exit protocol: 0 pass | nonzero fail | 77 whole-suite skip (env).
A suite exiting 0 whose output has a `SKIP` line is status pass* with
the skipped legs listed.

Tiers: fast < full < env.  --tier fast runs fast items only; --tier full
runs fast+full; --tier all additionally runs env items whose `requires`
tools are resolvable.  A suite whose tools are missing is status skip
("env: missing X").  A suite above the tier filter is NOT-RUN: printed
as such on the console and NOT recorded in battery_last.json (`skip` is
reserved for missing tools and exit-77).

Every unit streams: stdout+stderr merged, teed line-by-line to
seed/build/battery_logs/<unit>.log (fresh each run, every line
prefixed `HH:MM:SS `).  If a unit is silent for 60s a heartbeat line
is printed.  An optional `timeout_s` (registry field, positive int)
kills the process tree and records a fail.  --verbose echoes child
lines prefixed `  <unit>| `.

Run units are (suite, args): obligations sharing one invocation share
one run; different selector args run separately (log name
suite__argslug).  Obligations with `"release": true` run only under
--release; otherwise they print NOT-RUN (release gate).

`--only a,b,c` accepts suite names AND obligation ids (tier filter
ignored; env `requires` still enforced) and merges their records into
an existing battery_last.json.  Records live in "suites" (per unit,
incl. selftests) and "obligations" (per obligation id: status,
seconds, commit, at, unit).  Every record carries `commit` (HEAD sha,
`+dirty` if host/seed has uncommitted changes) and `at` (ISO
timestamp).

Usage: python battery.py [--tier fast|full|all] [--json] [--skip-seed]
                         [--release] [--verbose] [--only name,id,...]
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
                log.write(time.strftime("%H:%M:%S ") + item)
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


def _unit_name(suite: str, args) -> str:
    """Log/record name for a run unit: plain suite name, or
    suite__argslug so selector runs don't clobber each other's logs
    (`--gate X` slugifies to just the id — spec_term__G9d)."""
    if not args:
        return suite
    slug = "_".join(a.lstrip("-") for a in args if a != "--gate")
    return suite + "__" + slug if slug else suite


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
    release = "--release" in sys.argv[1:]
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
    selftests = toolchain.selftests()

    # run units: obligations grouped by (suite, args) — identical
    # invocations share one run, different selectors run separately;
    # selftests are their own units keyed by module name.
    units = []          # {name, suite, args, obs:[Obligation], sts:[Selftest]}
    umap = {}
    release_ids = set()

    def _unit_for(suite, args):
        key = (suite, tuple(args))
        if key not in umap:
            umap[key] = {"name": _unit_name(suite, args), "suite": suite,
                         "args": tuple(args), "obs": [], "sts": [],
                         "rec": None}
            units.append(umap[key])
        return umap[key]

    ob_unit = {}        # obligation id -> unit (non-release)
    for o in obs:
        if o.release and not release:
            release_ids.add(o.id)
            continue
        ob_unit[o.id] = _unit_for(o.suite, o.args)
        ob_unit[o.id]["obs"].append(o)
    for s in selftests:
        _unit_for(s.module, s.args)["sts"].append(s)
    for u in units:
        # record key: selftest-only units keep their module name so
        # suites[module] stays back-compatible; obligation units use the
        # argslug so selector runs don't collide
        u["rec"] = (u["sts"][0].module if u["sts"] and not u["obs"]
                    else u["name"])

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

    def _selected(u):
        if only is None:
            return True
        return u["suite"] in only or any(o.id in only for o in u["obs"]) \
            or any(s.module in only for s in u["sts"]) \
            or u["name"] in only

    results = {}        # unit name -> record
    unit_of = {}        # obligation id -> unit name (ran units only)
    not_run = {}        # unit name -> tier
    for u in units:
        suite, args = u["suite"], u["args"]
        if suite == "seed" and skip_seed:
            continue
        if not _selected(u):
            continue
        oi, si = u["obs"], u["sts"]
        reqs = sorted({r for x in list(oi) + list(si)
                       for r in x.requires})
        stier = "env" if reqs else {0: "fast", 1: "full"}[max(
            (TIER_LEVEL[x.tier] for x in list(oi) + list(si)),
            default=0)]
        missing = [r for r in reqs if not tool_present(r)]
        if missing:
            reason = f"env: missing {' '.join(missing)}"
            results[u["rec"]] = {"status": "skip", "ok": True,
                                 "seconds": 0.0, "skipped": [],
                                 "reason": reason, "commit": commit,
                                 "at": time.strftime("%Y-%m-%dT%H:%M:%S")}
            for o in oi:
                unit_of[o.id] = u["rec"]
            print(f"SKIP {u['name']}  {reason}")
            continue
        if only is None and TIER_LEVEL[stier] > level:  # NOT-RUN
            not_run[u["rec"]] = stier
            print(f"NOT-RUN {u['name']}  (tier {stier})")
            continue
        timeouts = [x.timeout_s for x in list(oi) + list(si)
                    if x.timeout_s]
        timeout = max(timeouts) if timeouts else None
        ids = ",".join(o.id for o in oi) or "-"
        print(f"RUN  {u['name']}  [{ids}]  tier={stier}")
        if suite == "lake":
            r = run_suite(u["name"], ["lake", "build",
                                      "ISAR.ObservationRegime",
                                      "ISAR.InvariantLayer",
                                      "ISAR.Futamura"],
                          _REPO, verbose=verbose, timeout=timeout)
            if r["status"] in ("pass", "pass*"):
                miss = _lake_decls(
                    d for o in oi for d in o.lean_decls)
                if miss:
                    r["status"], r["ok"] = "fail", False
                    r["reason"] = "lean decls missing: " + ", ".join(miss)
            results[u["rec"]] = r
        elif suite == "seed":
            results[u["rec"]] = run_suite(
                u["name"], [sys.executable, "seed.py"] + list(args), _SEED,
                verbose=verbose, timeout=timeout)
        else:
            results[u["rec"]] = run_suite(
                u["name"], [sys.executable, suite + ".py"] + list(args),
                _HOST, verbose=verbose, timeout=timeout)
        r = results[u["rec"]]
        r["commit"] = commit
        r["at"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        for o in oi:
            unit_of[o.id] = u["rec"]
        note = f" log={r['log']}" if r["status"] in ("fail", "pass*") else ""
        print(f"  -> {u['name']} {r['status']} ({r['seconds']:.1f}s){note}")

    ok = True
    ob_records = {}
    for o in obs:
        if o.id in release_ids:
            status, sec = "NOT-RUN (release gate)", 0.0
        elif o.id in unit_of:
            r = results[unit_of[o.id]]
            status, sec = r["status"].upper(), r["seconds"]
            if r["status"] == "fail":
                ok = False
            ob_records[o.id] = {
                "status": r["status"], "seconds": r["seconds"],
                "commit": r.get("commit", commit), "at": r.get("at", ""),
                "unit": unit_of[o.id]}
        elif o.id in ob_unit and ob_unit[o.id]["rec"] in not_run:
            status, sec = (f"NOT-RUN (tier "
                           f"{not_run[ob_unit[o.id]['rec']]})", 0.0)
        else:
            status, sec = "·", 0.0
        print(f"{o.id:4s} {o.family}/{o.evidence:<10s} "
              f"{(o.regime or '—'):<18s} {status:5s} ({sec:.1f}s)")
    for s in selftests:
        u_rec = next((u["rec"] for u in units if s in u["sts"]),
                     s.module)
        r = results.get(u_rec)
        if r is None:
            if u_rec in not_run:
                print(f"selftest {s.module:30s} NOT-RUN (tier "
                      f"{not_run[u_rec]})")
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
        doc = {"python": sys.executable, "suites": {}, "obligations": {}}
        if only is not None and os.path.exists(_JSON_OUT):
            try:
                doc = json.load(open(_JSON_OUT, encoding="utf-8"))
                doc["python"] = sys.executable
                doc.setdefault("obligations", {})
            except (OSError, ValueError):
                pass
        doc["suites"].update({
            k: {kk: v[kk] for kk in
                ("status", "ok", "seconds", "skipped", "reason",
                 "commit", "at") if kk in v}
            for k, v in results.items()})
        doc["obligations"].update(ob_records)
        with open(_JSON_OUT, "w", encoding="utf-8", newline="\n") as f:
            json.dump(doc, f, indent=2)
        print(f"wrote {_JSON_OUT}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
