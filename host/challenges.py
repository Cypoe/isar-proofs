"""challenges — the standing challenge catalog.

Phase 9c: challenges are GENERATORS, replayed; the catalog grows.
Each entry is a named reproducible case with a recorded expected
outcome — an rc, a refusal prefix, a validation failure — diffed
against the observed outcome at replay, not a boolean.

Categories (the boundary-refusal vocabulary of the gates):

  v3-*      kernel .plex depacker refusal matrix — every malformed
            input must exit rc=3 on the dialect="plex.v3" kernel
            (the gate-22 matrix, restated as named cases)
  emit-*    emit.plex forges — corrupted streams, widened caps,
            incomplete schedules, out-of-correspondence stage
            streams; every one must surface NotRealized with the
            recorded refusal prefix
  axis-*    realization-axis refusals — unsupported combinations
            must refuse naming the axis, never default
  spec-*    toolchain.json mutation cases — spec_validate must
            reject each (delegates to toolchain._negative_cases)

Replay:

  python host/challenges.py            # whole catalog
  python host/challenges.py --only=v3,emit   # substring selection
  python host/challenges.py --json     # + write challenges_last.json

Exit nonzero on any drift.  Evidence category: boundary refusal —
a challenge passes by refusing correctly, never by succeeding.
"""
from __future__ import annotations

import json
import os
import struct
import subprocess
import sys
import tempfile
from typing import Callable, Dict, List, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HOST)
for p in (_HOST, _ROOT, os.path.join(_ROOT, "seed")):
    if p not in sys.path:
        sys.path.insert(0, p)

import emit_chain as ec                                        # noqa: E402
import plex_bundle as pb                                       # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import toolchain                                               # noqa: E402

_JSON_OUT = os.path.join(_ROOT, "seed", "build",
                         "challenges_last.json")


# ---- targets ------------------------------------------------------------

def _v3_exe() -> str:
    return ec.ir_exe_for(seed.Realization(
        reclaim="redirect", io=("stdin", "bytes"),
        dialect="plex.v3"))


def _v3_probe() -> Tuple[bytes, bytes]:
    """(valid bundle, pir payload) — same shape as gate 22's probe."""
    pir = st.pack_ir(st.bytelist_term(b"ab"),
                     st.bytelist_term(b""),
                     st.bytelist_term(b"cd"))
    secs = [pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0, b"s"),
            pb.Section(pb.KIND_REALIZATION, pb.U64, 4, 0, b""),
            pb.Section(pb.KIND_BYTES, pb.U8, 1, 0, b"\xde\xad\xbe\xef"),
            pb.Section(pb.KIND_PIR, pb.U8, 1, 0, pir)]
    for s in secs:
        s.rows = s.length
    return pb.pack_bundle(secs), pir


def _rc_on(exe: str, data: bytes) -> dict:
    p = subprocess.run([exe], input=data, capture_output=True)
    return {"rc": p.returncode}


def _v3_cases() -> List[Tuple[str, bytes]]:
    """The gate-22 refusal matrix as named cases — all expect rc=3."""
    data, pir = _v3_probe()
    row = lambda i, f: 12 + i * 32 + f
    cases: List[Tuple[str, bytes]] = []
    d = bytearray(data); d[0:4] = b"NOPE"
    cases.append(("v3-bad-magic", bytes(d)))
    d = bytearray(data); d[4] = 2
    cases.append(("v3-bad-version", bytes(d)))
    d = bytearray(data); struct.pack_into("<H", d, 6, 9)
    cases.append(("v3-hsize-over", bytes(d)))
    d = bytearray(data); struct.pack_into("<H", d, 6, 8)
    cases.append(("v3-hsize-under", bytes(d)))
    cases.append(("v3-trunc-dir", data[:20]))
    d = bytearray(data); d[12] = 2
    cases.append(("v3-bad-celltype", bytes(d)))
    d = bytearray(data); d[13] = 0
    cases.append(("v3-arity-zero", bytes(d)))
    d = bytearray(data); struct.pack_into("<Q", d, row(0, 24), 7)
    cases.append(("v3-len-not-rows", bytes(d)))
    i_pir = 3
    d = bytearray(data)
    off = struct.unpack_from("<Q", d, row(i_pir, 8))[0]
    struct.pack_into("<Q", d, row(i_pir, 8), off | 1)
    cases.append(("v3-pir-off-unaligned", bytes(d)))
    d = bytearray(data); struct.pack_into("<Q", d, row(i_pir, 8), 16)
    cases.append(("v3-pir-off-under-hsize", bytes(d)))
    d = bytearray(data)
    struct.pack_into("<Q", d, row(i_pir, 16), len(pir) - 4)
    cases.append(("v3-pir-len-short", bytes(d)))
    d = bytearray(data)
    struct.pack_into("<Q", d, row(i_pir, 16), len(pir) + 100000)
    cases.append(("v3-pir-len-over-eof", bytes(d)))
    secs = [pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0, b"s"),
            pb.Section(pb.KIND_REALIZATION, pb.U64, 4, 0, b"")]
    for s in secs:
        s.rows = s.length
    cases.append(("v3-no-pir", pb.pack_bundle(secs)))
    secs.append(pb.Section(pb.KIND_PIR, pb.U8, 1, 0, pir))
    secs.append(pb.Section(pb.KIND_PIR, pb.U8, 1, 0, pir))
    for s in secs:
        s.rows = s.length
    cases.append(("v3-dup-pir", pb.pack_bundle(secs)))
    secs = [pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0, b"s"),
            pb.Section(pb.KIND_REALIZATION, pb.U64, 4, 0, b""),
            pb.Section(pb.KIND_PIR, pb.U8, 1, 0, pir + b"JUNKJUNK")]
    for s in secs:
        s.rows = s.length
    cases.append(("v3-trailing-junk", pb.pack_bundle(secs)))
    cases.append(("v3-mid-payload-cut", data[:off + 2]))
    return cases


# ---- emit-bundle forges ---------------------------------------------------

def _emit_bundle(tmpdir: str, name: str = "emit.plex") -> Tuple[str, pb.Bundle]:
    path = ec.write_emit_bundle(
        os.path.join(tmpdir, name), seed.Realization())
    return path, pb.read_bundle(open(path, "rb").read())


def _refuses(fn: Callable[[], None], prefix: str) -> dict:
    try:
        fn()
    except toolchain.NotRealized as e:
        got = str(e)
        return {"refuses": prefix,
                "prefix_ok": got.startswith(prefix)}
    return {"refuses": prefix, "prefix_ok": False}


def ch_emit_map_oor(tmpdir: str) -> dict:
    """MAP src frame out of range -> refusal at pre-validation."""
    path, b = _emit_bundle(tmpdir, "e1.plex")
    data = bytearray(open(path, "rb").read())
    msec = b.section(pb.KIND_MAP)
    struct.pack_into("<I", data, msec.offset + 12, 7)
    fpath = os.path.join(tmpdir, "emit.map.plex")
    open(fpath, "wb").write(bytes(data))
    return _refuses(lambda: ec.run_emit_bundle(fpath, timeout=3600),
                    "emit bundle:")


def ch_emit_missing_stream(tmpdir: str) -> dict:
    """dep-closure stage carries no stream -> refuses pre-exec."""
    streams = ec.emit_schedule_streams(seed.Realization())
    thin = [s for s in streams if s[0] != "emit.assemble"]
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00" * 16, None, {"dialect": "plex.emit/2"}, {},
        streams=thin))
    fpath = os.path.join(tmpdir, "emit.thin.plex")
    open(fpath, "wb").write(forged)
    return _refuses(lambda: ec.run_emit_bundle(fpath, timeout=3600),
                    "emit bundle:")


def ch_emit_alien_program(tmpdir: str) -> dict:
    """program stream from another realization -> audit refusal."""
    streams = ec.emit_schedule_streams(seed.Realization())
    alien = {n: bl for n, _r, bl, _m in
             ec.emit_schedule_streams(seed.Realization(fuse_s=True))}
    mixed = [(n, r, alien[n] if n == "emit.program" else bl, m)
             for n, r, bl, m in streams]
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00" * 16, None, {"dialect": "plex.emit/2"}, {},
        streams=mixed))
    fpath = os.path.join(tmpdir, "emit.alien.plex")
    open(fpath, "wb").write(forged)
    return _refuses(lambda: ec.run_emit_bundle(fpath, timeout=3600),
                    "emit bundle:")


def ch_emit_stream_corrupt(tmpdir: str) -> dict:
    """flipped byte inside a stream span -> digest refusal."""
    path, b = _emit_bundle(tmpdir, "e2.plex")
    data = bytearray(open(path, "rb").read())
    bsec = b.section(pb.KIND_BYTES)
    names = [s[0] for s in b.stage_rows()]
    for s_i, _dig, tok in b.query_rows():
        if names[s_i] == "emit.link":
            off, _ln = (int(x) for x in tok.split(":"))
            data[bsec.offset + off] ^= 0xFF
            break
    fpath = os.path.join(tmpdir, "emit.corrupt.plex")
    open(fpath, "wb").write(bytes(data))
    return _refuses(lambda: ec.run_emit_bundle(fpath, timeout=3600),
                    "emit bundle stream")


def ch_emit_caps_widened(tmpdir: str) -> dict:
    """a bundle may claim less than the record, never more."""
    path, b = _emit_bundle(tmpdir, "e3.plex")
    real = b.kv_rows(pb.KIND_REALIZATION)
    rn = real.get("routines")
    caps = dict(toolchain.components()["routines"][rn].data
                ).get("caps")
    widened = dict(caps["ports"], forge_extra="RW")
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00", {"ports": widened, "os": caps["os"]},
        dict(real), {}))
    fpath = os.path.join(tmpdir, "emit.wide.plex")
    open(fpath, "wb").write(forged)
    return _refuses(lambda: ec.run_emit_bundle(fpath),
                    "emit bundle caps exceed")


def ch_emit_malformed(tmpdir: str) -> dict:
    """truncated header -> BundleError surfaces as NotRealized."""
    fpath = os.path.join(tmpdir, "emit.trunc.plex")
    open(fpath, "wb").write(b"\xde\xad")
    return _refuses(lambda: ec.run_emit_bundle(fpath),
                    "emit bundle:")


def _threshold_bundle(tmpdir: str, name: str, min_par: int) -> str:
    streams = ec.emit_schedule_streams(seed.Realization())
    real = {"dialect": "plex.emit/2",
            "schedule.output": "emit.pack",
            "schedule.min_parallel_roots": str(min_par)}
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00" * 16, None, real, {}, streams=streams))
    fpath = os.path.join(tmpdir, name)
    open(fpath, "wb").write(forged)
    return fpath


def ch_emit_threshold_pool(tmpdir: str) -> dict:
    """declared threshold below the stage's roots -> pool engages."""
    fpath = _threshold_bundle(tmpdir, "emit.t2.plex", 2)
    _img, ev = ec.run_emit_bundle(fpath, timeout=3600, workers=4)
    return {"pool": "pool=True" in ev.get("emit.assemble", "")}


def ch_emit_threshold_serial(tmpdir: str) -> dict:
    """declared threshold above every stage's roots -> serial even
    under workers=4 (W(n) below the regimes bound)."""
    fpath = _threshold_bundle(tmpdir, "emit.tbig.plex", 100000)
    _img, ev = ec.run_emit_bundle(fpath, timeout=3600, workers=4)
    return {"pool": "pool=True" in ev.get("emit.assemble", "")}


# ---- axis refusals ---------------------------------------------------------

def _axis(name: str, fn: Callable[[], None], word: str) -> dict:
    try:
        fn()
    except toolchain.NotRealized as e:
        return {"refuses_with": word, "hit": word in str(e)}
    except Exception as e:                              # noqa: BLE001
        return {"refuses_with": word,
                "hit": word in str(e), "type": type(e).__name__}
    return {"refuses_with": word, "hit": False}


def ch_axis_threads_token(_t) -> dict:
    """threads>1 on the token record refuses at the driver leg."""
    import routines_x86_64_win64 as rts
    return _axis(
        "axis-threads-token",
        lambda: rts.program(seed.Realization(threads=2)),
        "threads")


def ch_axis_dialect_bogus(_t) -> dict:
    """unknown container dialect refuses naming the axis."""
    import routines_x86_64_win64 as rts
    return _axis(
        "axis-dialect-bogus",
        lambda: rts.program_ir(
            seed.Realization(dialect="plex.bogus")),
        "dialect")


def ch_axis_reclaim(_t) -> dict:
    """declared-but-unrealized reclaim refuses at persist."""
    import routines_x86_64_win64 as rts
    return _axis(
        "axis-reclaim-marksweep",
        lambda: rts.program_ir(
            seed.Realization(reclaim="mark-sweep")),
        "reclaim")


# ---- spec mutation ----------------------------------------------------------

def _spec_cases() -> List[Tuple[str, Callable[[], bool]]]:
    out = []
    for name, mut in toolchain._negative_cases():
        out.append((f"spec-{name.replace(' ', '-')}",
                    lambda m=mut: bool(toolchain.validate(m))))
    return out


# ---- catalog + runner -----------------------------------------------------

def catalog() -> List[dict]:
    """Every challenge as {name, run, expect}: run(tmpdir)->observed,
    expect = the recorded expected outcome shape."""
    entries: List[dict] = []
    for name, data in _v3_cases():
        entries.append({
            "name": name,
            "expect": {"rc": 3},
            "run": (lambda d=data: (lambda _t: _rc_on(_v3_exe(), d)))(),
        })
    entries.append({
        "name": "v3-valid-control",
        "expect": {"rc": 0},
        "run": lambda t: _rc_on(_v3_exe(), _v3_probe()[0]),
    })
    for name, fn in (
            ("emit-map-frame-oor", ch_emit_map_oor),
            ("emit-missing-stream", ch_emit_missing_stream),
            ("emit-alien-program", ch_emit_alien_program),
            ("emit-stream-corrupt", ch_emit_stream_corrupt),
            ("emit-caps-widened", ch_emit_caps_widened),
            ("emit-malformed", ch_emit_malformed),
            ("axis-threads-token", ch_axis_threads_token),
            ("axis-dialect-bogus", ch_axis_dialect_bogus),
            ("axis-reclaim-marksweep", ch_axis_reclaim)):
        entries.append({"name": name, "expect": {"refused": True},
                        "run": fn})
    entries.append({"name": "emit-threshold-pool",
                    "expect": {"pool": True},
                    "run": ch_emit_threshold_pool})
    entries.append({"name": "emit-threshold-serial",
                    "expect": {"pool": False},
                    "run": ch_emit_threshold_serial})
    for name, fn in _spec_cases():
        entries.append({
            "name": name,
            "expect": {"validate_errs": True},
            "run": (lambda f=fn: (lambda _t:
                    {"validate_errs": f()}))(),
        })
    return entries


def _match(observed: dict, expect: dict) -> bool:
    if "rc" in expect:
        return observed.get("rc") == expect["rc"]
    if "refused" in expect:
        return bool(observed.get("prefix_ok", observed.get("hit")))
    if "validate_errs" in expect:
        return bool(observed.get("validate_errs"))
    if "pool" in expect:
        return observed.get("pool") == expect["pool"]
    return observed == expect


def main() -> int:
    only = {s for a in sys.argv[1:] if a.startswith("--only=")
            for s in a.split("=", 1)[1].lower().split(",")}
    want_json = "--json" in sys.argv[1:]
    entries = catalog()
    tmpdir = tempfile.mkdtemp(prefix="challenges_")
    results: List[Dict] = []
    drift = 0
    for e in entries:
        if only and not any(s in e["name"].lower() for s in only):
            continue
        try:
            obs = e["run"](tmpdir)
            ok = _match(obs, e["expect"])
        except Exception as exc:                        # noqa: BLE001
            obs = {"error": f"{type(exc).__name__}: {exc}"}
            ok = False
        st_ = "pass" if ok else "drift"
        drift += not ok
        results.append({"name": e["name"], "status": st_,
                        "expected": e["expect"], "observed": obs})
        print(f"  {e['name']:<32} {st_}"
              + ("" if ok else f"  expected={e['expect']} "
                               f"observed={obs}"))
    ran = len(results)
    print(f"challenges: {ran - drift}/{ran} "
          f"({drift} drift)")
    if want_json:
        os.makedirs(os.path.dirname(_JSON_OUT), exist_ok=True)
        doc = {"python": sys.executable, "challenges": {
            r["name"]: {"status": r["status"],
                        "observed": r["observed"]}
            for r in results}}
        with open(_JSON_OUT, "w", encoding="utf-8") as f:
            json.dump(doc, f, indent=2, sort_keys=True)
        print(f"wrote {_JSON_OUT}")
    return 1 if drift else 0


if __name__ == "__main__":
    raise SystemExit(main())
