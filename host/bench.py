"""bench — the measurement harness (Phase 9c).

Benches are REPORTS, not obligations — `claim: none` in
toolchain.json.  This module runs the registered bench suites and
its own emit-chain measures, writes seed/build/bench_last.json, and
prints a table.  Numbers are evidence class "performance
measurement" — explicitly never equivalence claims.

Measures:

  steps_per_s   redirect kernel: steps + steps/s on a fixed stream
  mt_scale      same stream on threads={1,2,4}: wall + steps each —
                scaling is a number, parity is the MT-equiv gate's
  emit_wall_s   mini emit_frames on the emitted host (gate-19 args)
  arena         declared arena + child peak RSS for one run
  modules       every toolchain.json bench entry run as a suite —
                headline stdout captured

  python host/bench.py            # all measures
  python host/bench.py --only=mt,emit   # substring selection
  python host/bench.py --json     # write bench_last.json
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from typing import Dict

_HOST = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HOST)
for p in (_HOST, _ROOT, os.path.join(_ROOT, "seed")):
    if p not in sys.path:
        sys.path.insert(0, p)

import emit_chain as ec                                        # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import toolchain                                               # noqa: E402

_JSON_OUT = os.path.join(_ROOT, "seed", "build",
                         "bench_last.json")


def _probe_roots(n: int = 8, width: int = 512):
    """fixed stream: n roots of width-B byte lists — deterministic
    work, no cache, same shape every run.  Sized for the ~3K st/s
    redirect kernel (≈30-60s serial, a real measure not a canary)."""
    return [st.bytelist_term(
        bytes(((i * 131 + j * 17) & 0xFF) for j in range(width)))
        for i in range(n)]


def _rss_of_run(exe: str, blob: bytes) -> int:
    """peak child RSS for one subprocess run (0 if psutil misses).
    stdin is written + closed up front — polling before the child
    gets EOF deadlocks it on read."""
    import psutil
    p = subprocess.Popen([exe], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    p.stdin.write(blob)
    p.stdin.close()
    peak = 0
    try:
        proc = psutil.Process(p.pid)
        while p.poll() is None:
            try:
                peak = max(peak, proc.memory_info().rss)
            except psutil.NoSuchProcess:
                break
            time.sleep(0.05)
    except psutil.Error:
        pass
    p.stdout.read()
    p.stderr.read()
    p.wait()
    return peak


def m_steps_per_s() -> dict:
    exe = ec.ir_exe_for(seed.Realization(
        reclaim="redirect", io=("stdin", "bytes")))
    run = ec.make_bytes_runner(exe)
    t0 = time.time()
    _outs, steps, alloc = run.batch(_probe_roots())
    wall = time.time() - t0
    return {"steps": steps, "alloc": alloc,
            "wall_s": round(wall, 2),
            "steps_per_s": round(steps / max(wall, 1e-9))}


def m_mt_scale() -> dict:
    rows = []
    for t in (1, 2, 4):
        R = seed.Realization(reclaim="redirect",
                             io=("stdin", "bytes"), threads=t)
        exe = (ec.ir_exe_for(R) if t == 1 else seed._exe_for(
            R, toolchain.by_name("native.x86_64.pe.ir.mt")))
        run = ec.make_bytes_runner(exe)
        t0 = time.time()
        _outs, steps, _a = run.batch(_probe_roots())
        wall = time.time() - t0
        rows.append({"threads": t, "wall_s": round(wall, 2),
                     "steps": steps})
    base = rows[0]["wall_s"]
    for r in rows:
        r["speedup"] = round(base / max(r["wall_s"], 1e-9), 2)
    return {"rows": rows}


def m_emit_wall() -> dict:
    import target_pe64
    imps, slots = ("ExitProcess",), (("x", 8),)
    base = target_pe64.text_rva(imps, slots)
    t0 = time.time()
    img, ev = ec.emit_frames(
        seed.Realization(), imports=imps, slots=slots,
        text_base=base, prog=st.fraglist_term(st.ASM_LINK))
    return {"wall_s": round(time.time() - t0, 2),
            "image_b": len(img),
            "oracle": img == ec._mini_oracle()}


def m_arena() -> dict:
    R = seed.Realization(reclaim="redirect",
                         io=("stdin", "bytes"))
    exe = ec.ir_exe_for(R)
    blob = st.pack_ir(*_probe_roots(4, 1024))
    peak = _rss_of_run(exe, blob)
    return {"declared_arena_b": R.ir_arena_bytes,
            "persist_b": R.persist_bytes,
            "peak_rss_b": peak}


def m_modules() -> dict:
    """every registered bench module, run standalone; headline
    stdout kept (numbers stay inside the module's own print)."""
    out = {}
    for b in toolchain.benches():
        if b.module == "bench":
            continue
        path = os.path.join(_HOST, b.module + ".py")
        if not os.path.exists(path):
            out[b.name] = {"status": "missing"}
            continue
        t0 = time.time()
        p = subprocess.run([sys.executable, path],
                           capture_output=True, text=True,
                           cwd=_HOST, timeout=1800)
        tail = [ln for ln in p.stdout.splitlines() if ln.strip()]
        out[b.name] = {
            "rc": p.returncode, "wall_s": round(time.time() - t0, 1),
            "tail": tail[-4:]}
    return out


def main() -> int:
    only = {s for a in sys.argv[1:] if a.startswith("--only=")
            for s in a.split("=", 1)[1].lower().split(",")}
    want_json = "--json" in sys.argv[1:]
    measures = [("steps_per_s", m_steps_per_s),
                ("mt_scale", m_mt_scale),
                ("emit_wall_s", m_emit_wall),
                ("arena", m_arena),
                ("modules", m_modules)]
    doc: Dict[str, object] = {"python": sys.executable,
                              "measures": {}}
    for name, fn in measures:
        if only and not any(s in name.lower() for s in only):
            continue
        try:
            doc["measures"][name] = fn()
        except Exception as e:                            # noqa: BLE001
            doc["measures"][name] = {
                "error": f"{type(e).__name__}: {e}"}
        print(f"  {name:<14} "
              f"{json.dumps(doc['measures'][name])[:120]}")
    if want_json:
        os.makedirs(os.path.dirname(_JSON_OUT), exist_ok=True)
        with open(_JSON_OUT, "w", encoding="utf-8") as f:
            json.dump(doc, f, indent=2, sort_keys=True)
        print(f"wrote {_JSON_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
