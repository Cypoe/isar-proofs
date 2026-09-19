"""
spec_check — the SWITCH_SPEC rule, statically checked.

A transform owns interpretation of its opaque surface; the core (the
seed) must not branch on catalog names.  This suite locates the
§0..§3 span of seed/seed.py (the `# §0` banner to the `# §7` banner)
and fails if any component/toolchain/piece name from toolchain.json
appears there — except `native.x86_64.pe` inside `def emit(` (the
default-toolchain selection point).
"""
from __future__ import annotations

import os
import re
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

import toolchain  # noqa: E402

SEED = os.path.join(_HOST, "..", "seed", "seed.py")
ALLOWED = {"native.x86_64.pe"}


def _span(lines) -> tuple:
    """(start, end) line indices of the §0..§3 span (inclusive)."""
    i0 = next(i for i, l in enumerate(lines)
              if l.startswith("# §0") or l.startswith("# §0 "))
    i1 = next(i for i, l in enumerate(lines) if l.startswith("# §7"))
    return i0, i1


def _emit_body(lines, i0, i1):
    """Line indices inside `def emit(`'s body within the span."""
    try:
        e = next(i for i in range(i0, i1)
                 if lines[i].startswith("def emit("))
    except StopIteration:
        return set()
    out = set()
    j = e + 1
    while j < i1 and (lines[j].startswith((" ", "\t")) or not lines[j].strip()):
        out.add(j)
        j += 1
    out.add(e)
    return out


def _names() -> list:
    s = toolchain.load()
    out = []
    for sec in ("dialects", "isas", "routines", "targets", "pieces"):
        out += list(s[sec])
    out += [t.name for t in s["toolchains"]]
    return out


def main() -> int:
    lines = open(SEED, encoding="utf-8").read().splitlines()
    i0, i1 = _span(lines)
    emit_ok = _emit_body(lines, i0, i1)
    ok = True
    checked = 0
    for name in _names():
        pat = re.compile(r"(?<![\w.])" + re.escape(name) + r"(?![\w.])")
        for i in range(i0, i1):
            if not pat.search(lines[i]):
                continue
            if name in ALLOWED and i in emit_ok:
                continue
            print(f"FAIL {name!r} in §0–§3 at {os.path.basename(SEED)}:{i + 1}: "
                  f"{lines[i].strip()[:80]}")
            ok = False
        checked += 1
    print(f"checked {checked} catalog names over §0–§3 "
          f"(lines {i0 + 1}–{i1}); allowed: {sorted(ALLOWED)} inside emit()")
    print(f"{'OK' if ok else 'FAIL'} spec_check")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
