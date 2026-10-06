"""golden fixtures — committed reference outputs for the emit gates.

Gates compare against these snapshots, never against a live oracle:
the oracle (emit_native / seed.emit) is the REFRESH path, run only
when the record's implementation changes on purpose.  A missing
fixture is a refusal naming the missing axis — never a silent
recompute and never a skip.

    golden("image.default")            -> bytes (4608B PE image)
    golden("pexec.exe")                -> the emitted executor itself
    golden("bundle.default")           -> the emit.plex wire fixture

refresh_goldens() regenerates every file from the oracle and writes
manifest.json (sha256 + size + realization axes per fixture).  The
oracle's own refusals propagate unchanged — a record the toolchain
can't emit names its axis, the refresh is honest about which leg is
missing.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURE_DIR = os.path.join(HERE, "fixtures")
MANIFEST = os.path.join(FIXTURE_DIR, "manifest.json")

# fixture name -> committed filename (extension is meaningful:
# .bin opaque image, .plex wire bundle, .exe runnable executor)
_FILES = {
    "image.default": "image.default.bin",
    "image.fuse_s": "image.fuse_s.bin",
    "image.ir": "image.ir.bin",
    "bundle.default": "bundle.default.plex",
    "pexec.exe": "pexec.exe",
}


def golden(name: str) -> bytes:
    """The committed oracle bytes for `name`.  Absent = a refusal
    naming the missing fixture axis, not a recompute."""
    import toolchain
    p = golden_path(name)
    with open(p, "rb") as f:
        return f.read()


def golden_path(name: str) -> str:
    """Fixture path for binary executables the gate runs directly —
    same refusal contract as golden()."""
    import toolchain
    fname = _FILES.get(name)
    p = os.path.join(FIXTURE_DIR, fname) if fname else None
    if fname is None or not os.path.exists(p):
        raise toolchain.NotRealized(
            f"golden fixture {name!r} absent — the fixture axis is "
            f"missing; run fixtures.refresh_goldens() against the "
            f"oracle to snapshot it")
    return p


def _oracles():
    """fixture name -> (realization summary, producer).  Each producer
    is the oracle; its NotRealized propagates naming the axis."""
    import emit_chain as ec
    import seed

    rex = seed.Realization(dialect="plex.emit", io=("stdin", "bytes"),
                           reclaim="redirect", gc="sweep")
    r_ir = seed.Realization(reclaim="redirect", io=("stdin", "bytes"),
                            gc="sweep")
    return {
        "image.default": ("R() default record, emit_native oracle",
                          lambda: ec.emit_native()),
        "image.fuse_s": ("R(fuse_s=True), emit_native oracle",
                         lambda: ec.emit_native(
                             R=seed.Realization(fuse_s=True))),
        "image.ir": ("IR kernel record (bytes+sweep), emit_native",
                     lambda: ec.emit_native(
                         "native.x86_64.pe.ir", r_ir)),
        "bundle.default": ("emit.plex schedule fixture (default R)",
                           None),   # written by refresh (needs a path)
        "pexec.exe": ("pexec executor exe (dialect=plex.emit record), "
                      "emit_native",
                      lambda: ec.emit_native(
                          "native.x86_64.pe.ir", rex)),
    }


def refresh_goldens(tmpdir: str) -> dict:
    """Regenerate every fixture from the live oracle; write
    manifest.json.  Oracle refusals propagate — a record the
    toolchain can't emit names its missing axis."""
    import emit_chain as ec
    import seed
    os.makedirs(FIXTURE_DIR, exist_ok=True)
    man = {}
    for name, (desc, fn) in _oracles().items():
        if name == "bundle.default":
            p = os.path.join(tmpdir, "emit.plex")
            ec.write_emit_bundle(p, seed.Realization())
            data = open(p, "rb").read()
        else:
            data = fn()
        out = os.path.join(FIXTURE_DIR, _FILES[name])
        with open(out, "wb") as f:
            f.write(data)
        man[os.path.basename(out)] = {
            "desc": desc,
            "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}
    with open(MANIFEST, "w") as f:
        json.dump(man, f, indent=2, sort_keys=True)
    return man


if __name__ == "__main__":
    import tempfile
    man = refresh_goldens(tempfile.mkdtemp(prefix="fixtures_"))
    for k, v in sorted(man.items()):
        print(f"{k}: {v['bytes']}B sha256:{v['sha256'][:16]}")
