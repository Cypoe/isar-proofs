"""
xdu_gate — G8 two-paths equivalence + G8b ISAR-free emission.

The SAME XDU declaration (programs/xdu/*.json) is realized three ways;
all must agree on the declared regime (stdout bytes + rc):

  direct   interpret(xdu, data)  — table walk over the JSON; shares no
           code with either realization path.  This is the expected value.
  native   seed.emit(R, xdu.x86_64.pe, program=xdu) -> PE exe -> run with
           stdin=data, observe (stdout, returncode).  The image contains
           no reducer: program behaviour is compiled to code.
  runtime  encode(xdu, data) -> T reduced live by graph.lo (LO steps) and
           graph.cd (complete development; rounds — reported, NEVER
           compared to steps), then term_to_nibbles(nf) decodes the
           output spine.

Corpus: empty / 1B / 7B / all-16-nibbles / all-256-byte-values /
read-granule boundary (64KiB-1, 64KiB, 64KiB+37).  The runtime path is
bounded by its Church-numeral iteration (~10^3 steps per input nibble on
graph.lo), so runtime cells cover inputs <= RT_MAX (32B) in the battery;
the granule-boundary inputs gate native==direct (and a --deep run extends
runtime coverage).  Honest claim: runtime equivalence is demonstrated on
small inputs; the native granule path is exercised at full size.

G8b ISAR-free emission, checked on every probe's assembled Program:
  * the routines module's TOP-LEVEL imports are stdlib + isa_x86_64 +
    toolchain only — no seed, reduce, graph_runtime (self-test imports
    inside main() are function-scoped and excluded);
  * the label set contains none of the runtime-path reducer's labels
    (exact names) and no label from the reducer's generated families
    (prefixes st_ en_ it_ p_ cn_ red_ mk* grow_*); the xdu routines'
    own generated labels are xst_/xarm_/xeof_/xn_*.
  A Tag byte-constant scan is deliberately NOT part of the gate: nibble
  immediates share the mov-rd,imm32 encoding, so the label+import check
  is the meaningful discriminator.

G8c geometry: rebuilds two probes with read_buf_bytes=1024 — same
observations; the assembled programs differ only in granule immediates
(mov/mov-mem imm fields whose value is a granule constant).  G4
discipline: no structural change, only strategy data.

Usage: python host/xdu_gate.py [--deep]
"""
from __future__ import annotations

import ast
import os
import subprocess
import sys
from typing import List, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_SEED = os.path.normpath(os.path.join(_HOST, "..", "seed"))
if _SEED not in sys.path:
    sys.path.insert(0, _SEED)

import isa_x86_64 as _isa                    # noqa: E402
import toolchain                             # noqa: E402
import xdu_dialect as xd                     # noqa: E402
import routines_x86_64_win64_xdu as xdu_rts  # noqa: E402
from graph_runtime import reduce_tree_lo, reduce_tree_cd  # noqa: E402
import cogen                                 # noqa: E402
import seed                                  # noqa: E402

_BUILD = os.path.join(_SEED, "build")
PROBES = ("echo", "hexdump", "drop0", "toggle")
RT_MAX = 32          # runtime-path corpus cap in bytes (see docstring)

# runtime-path reducer vocabulary (host/routines_x86_64_win64.py label set)
_FORBID_EXACT = frozenset({
    "step", "do_reduce", "red_loop", "red_done", "parse_bytes",
    "parse_done", "empty", "count_nodes", "emit_nf", "itoa", "build_ds",
    "grow_heap", "grow_fail", "mkleaf", "mkleaf_ok", "mkapp", "mkapp_ok",
    "mkstk", "mkstk_ok", "exit2", "exit3",
})
_FORBID_PREFIX = ("st_", "en_", "it_", "p_", "cn_", "red_", "mk", "grow_")


# ----------------------------------------------------------------------
# corpus
# ----------------------------------------------------------------------

def corpus() -> List[Tuple[str, bytes]]:
    g = 64 << 10
    return [
        ("empty", b""),
        ("one", b"A"),
        ("seven", b"Hello7!"),
        ("allnib", bytes(range(16))),
        ("allbytes", bytes(range(256))),
        ("granule-1", bytes((i * 7 + 3) & 0xFF for i in range(g - 1))),
        ("granule", bytes((i * 5 + 1) & 0xFF for i in range(g))),
        ("granule+37", bytes((i * 11 + 7) & 0xFF for i in range(g + 37))),
    ]


# ----------------------------------------------------------------------
# the three realizations of one XDU
# ----------------------------------------------------------------------

def _exe_path(xdu: xd.XDU, tag: str = "") -> str:
    return os.path.join(_BUILD, f"xdu_{xdu.name}{tag}.exe")


def build_native(xdu: xd.XDU, R: seed.Realization, tag: str = "") -> str:
    img = seed.emit(R, tc=toolchain.by_name("xdu.x86_64.pe"), program=xdu)
    path = _exe_path(xdu, tag)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(img)
    return path


def run_native(path: str, data: bytes) -> Tuple[bytes, int]:
    cp = subprocess.run([path], input=data, capture_output=True,
                        timeout=300)
    return cp.stdout, cp.returncode


def run_runtime(xdu: xd.XDU, data: bytes, which: str
                ) -> Tuple[Tuple[bytes, int], int]:
    """(bytes, rc), steps-or-rounds.  Fuel scales with iteration count."""
    n = 2 * len(data) + 1
    t = xd.encode(xdu, data)
    if which == "lo":
        nf, cnt, _ = reduce_tree_lo(t, 30_000 * n + 100_000)
    else:
        nf, cnt, _ = reduce_tree_cd(t, 1_000 * n + 5_000)
    return xd.term_to_nibbles(nf), cnt


# ----------------------------------------------------------------------
# G8b — ISAR-free emission
# ----------------------------------------------------------------------

def _top_imports(path: str) -> List[str]:
    tree = ast.parse(open(path, encoding="utf-8").read())
    out = []
    for node in tree.body:                    # module level only
        if isinstance(node, ast.Import):
            out += [a.name.split(".")[0] for a in node.names]
        elif isinstance(node, ast.ImportFrom):
            out.append((node.module or "").split(".")[0])
    return out


def isar_free(prog: _isa.Program) -> List[str]:
    """Problems found; empty = clean."""
    problems = []
    imp = set(_top_imports(xdu_rts.__file__))
    banned = imp & {"seed", "reduce", "graph_runtime", "lambda_dialect",
                    "host_pieces", "observation_regime", "bytecode_dialect"}
    if banned:
        problems.append(f"forbidden module imports: {sorted(banned)}")
    names = {i[1] for i in prog if i[0] == "label"}
    hit = names & _FORBID_EXACT
    if hit:
        problems.append(f"reducer labels present: {sorted(hit)}")
    pref = sorted(n for n in names if n.startswith(_FORBID_PREFIX))
    if pref:
        problems.append(f"reducer label families present: {pref}")
    return problems


# ----------------------------------------------------------------------
# G8c — geometry: same observations, diffs confined to granule immediates
# ----------------------------------------------------------------------

def _granule_only_diff(pa: _isa.Program, pb: _isa.Program,
                       ga: int, gb: int) -> List[str]:
    """Positions where the two programs' insns differ other than an imm
    operand equal to one of the two granule constants."""
    bad = []
    ia = [i for i in pa]
    ib = [i for i in pb]
    if len(ia) != len(ib):
        return [f"program length {len(ia)} != {len(ib)}"]
    for k, (a, b) in enumerate(zip(ia, ib)):
        if a == b:
            continue
        if a[0] == "label" or b[0] == "label" or a[0] != b[0] \
                or len(a) != len(b):
            bad.append(f"insn {k}: {a!r} != {b!r}")
            continue
        # same form; operands may differ only where both are the granules
        diffs = [(x, y) for x, y in zip(a[1:], b[1:]) if x != y]
        if not diffs or not all(
                {x, y} == {ga, gb} for x, y in diffs):
            bad.append(f"insn {k} {a[0]}: non-granule diff {diffs!r}")
    return bad


# ----------------------------------------------------------------------
# gate
# ----------------------------------------------------------------------

def main() -> int:
    deep = "--deep" in sys.argv[1:]
    R = seed.Realization()
    ncell = nfail = 0

    # cogen picks the native-path toolchain for a declared program
    c = cogen.MachineContext.detect()
    xdu0 = xd.load(xd.probe_path(PROBES[0]))
    plan = cogen.choose(cogen.full_catalog(), cogen.Budget.SERIAL, c,
                        path="native", program=xdu0)
    ncell += 1
    if plan.toolchain != "xdu.x86_64.pe":
        nfail += 1
        print(f"FAIL choose(path=native): toolchain={plan.toolchain!r}")
    else:
        print(f"OK choose(path=native) -> {plan.toolchain} "
              f"({plan.name})")

    for name in PROBES:
        xdu = xd.load(xd.probe_path(name))

        # ---- G8b on this probe's program ---------------------------
        prog = xdu_rts.program(xdu, R)
        syms = {f"iat_{n}": 0x2000 + i * 8
                for i, n in enumerate(xdu_rts.IMPORTS)}
        off = 0x3000
        for s, sz in xdu_rts.DATA_SLOTS:
            syms[s] = off
            off += sz
        _text, labels = _isa.assemble(prog, syms)
        probs = isar_free(prog)
        ncell += 1
        if probs:
            nfail += 1
            for p in probs:
                print(f"FAIL G8b {name}: {p}")
        else:
            print(f"OK G8b {name}: {len(labels)} labels, "
                  "no reducer vocabulary")

        # ---- G8 equivalence ----------------------------------------
        exe = build_native(xdu, R)
        for iname, data in corpus():
            expected = xd.interpret(xdu, data)
            got = run_native(exe, data)
            ncell += 1
            if got != expected:
                nfail += 1
                print(f"FAIL {name}/{iname} native: {got!r} != "
                      f"{expected!r}")
                continue
            if len(data) > RT_MAX and not deep:
                print(f"OK {name}/{iname}: direct==native "
                      f"({len(data)}B in, rc={expected[1]}; "
                      "runtime cells deferred --deep)")
                continue
            line = f"{name}/{iname}: direct==native"
            good = True
            for which in ("lo", "cd"):
                try:
                    rt, cnt = run_runtime(xdu, data, which)
                except Exception as e:
                    good = False
                    print(f"FAIL {name}/{iname} graph.{which}: {e}")
                    continue
                ncell += 1
                if rt != expected:
                    nfail += 1
                    good = False
                    print(f"FAIL {name}/{iname} graph.{which}: "
                          f"{rt!r} != {expected!r}")
                else:
                    unit = "steps" if which == "lo" else "rounds"
                    line += f"==graph.{which}({cnt} {unit})"
            if good:
                print(f"OK {line} rc={expected[1]}")

    # ---- G8c geometry -------------------------------------------------
    small = seed.Realization(read_buf_bytes=1024)
    for name in ("echo", "toggle"):
        xdu = xd.load(xd.probe_path(name))
        pa = xdu_rts.program(xdu, R)
        pb = xdu_rts.program(xdu, small)
        bad = _granule_only_diff(pa, pb, R.read_buf_bytes,
                                 small.read_buf_bytes)
        ncell += 1
        if bad:
            nfail += 1
            for b in bad[:8]:
                print(f"FAIL G8c {name}: {b}")
            continue
        exe_b = build_native(xdu, small, tag="_g1024")
        # granule crossing at the SMALL granule: 3*1024+5 bytes
        data = bytes((i * 13 + 1) & 0xFF for i in range(3 * 1024 + 5))
        exp, got = xd.interpret(xdu, data), run_native(exe_b, data)
        ncell += 1
        if got != exp:
            nfail += 1
            print(f"FAIL G8c {name}: obs {got!r} != {exp!r}")
        else:
            print(f"OK G8c {name}: granule 65536->1024, same obs, "
                  ".text diffs confined to granule immediates")

    print(f"{ncell - nfail}/{ncell} cells OK")
    print(f"{'OK' if not nfail else 'FAIL'} xdu_gate")
    return 1 if nfail else 0


if __name__ == "__main__":
    raise SystemExit(main())
