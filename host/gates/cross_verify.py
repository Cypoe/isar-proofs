"""
cross_verify — behavioral cross-verification of the two hosts.

The claim is observational equivalence of running programs, not just
bit-identical artifacts: the same stdin bytes, run under the Python
host pieces and under the clang-compiled C kernel, must produce the
same observations.

Legs:

  PE <-> C    the strongest leg — the established native host vs the
              emitted C kernel, compared byte-for-byte on stdout
              (NF tokens) AND stderr (steps=/alloc=) AND rc on every
              probe.  Same IStepBasis, same alloc accounting, same
              parse/exit semantics: any drift is a kernel bug.

  graph <-> C the independent witness — graph.lo (graph_runtime's
              LO evaluator) vs the C kernel.  graph.lo is a THIRD
              IStepBasis witness: dupβ/swapβ fire, and S is expanded
              to derived_s on import — the same rule family as the
              default build, so NF AND step counts must match it
              exactly.  On fuse_s only NF is compared (primitive sβ
              legitimately costs fewer steps — that is the point of
              the build).  Two quotient-layer normalizations apply:
              (a) graph exports via quote_surface — an intact ds
              subtree prints as `S`, kernels emit the raw tree; both
              sides are re-quoted through the same surface map
              before comparing; (b) underflow probes pad the parse
              stack without building the app node in graph's
              _parse_native_out — same NF, parse-level step drift —
              steps are compared only on non-underflowing probes.

  fuel axis   both builds with fuel=5 on a term needing more steps:
              identical rc=2, identical partial-stats line shape.

Corpus: named goldens + all depth<=2 app trees over the full
alphabet + edge cases (underflow, empty, bad byte, >granule stream).

`tree WWW` is intentionally in the corpus: W W W is a dupβ fixed
point (W f x -> f x x with f = x = W yields the same term), so BOTH
hosts diverge on it (fuel=None realizations).  Divergence is a
legitimate observation: the runs are bounded by a wall-clock guard
and compared as `TIMEOUT` observations — identical non-termination
is part of the equivalence claim.  The bound is a test harness
guard, not semantics (same discipline as run_native/run_exe).
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))
_SEED = os.path.normpath(os.path.join(_HOST, "..", "seed"))
for _p in (_HOST, _SEED):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import seed                                # noqa: E402
import toolchain                           # noqa: E402
import target_c                            # noqa: E402
import routines_c                          # noqa: E402
import tower                               # noqa: E402
from seed import Realization               # noqa: E402
from reduce import T, K, app               # noqa: E402
from host_pieces import GRAPH_PIECE, run_piece  # noqa: E402

RBUF = Realization().read_buf_bytes


def _corpus() -> List[Tuple[str, str]]:
    """(label, token-text) probes — named goldens + enumerated small
    trees + structural edge cases."""
    probes: List[Tuple[str, str]] = [
        ("empty", ""),
        ("atom I", "I"),
        ("I K -> K", "I K @"),
        ("K S I", "K S @ I @"),
        ("S K K I", "S K @ K @ I @"),
        ("dup W K I", "W K @ I @"),
        ("swap C B K I", "C B @ K @ I @"),
        ("comp B B K I", "B B @ K @ I @"),
        ("underflow @", "@"),
        ("underflow I @", "I @"),
        ("double underflow", "@ @"),
        ("separators", "I ,\tK\r\n@"),
        ("bad byte", "I \x01"),
        ("stream >granule", "I " * (RBUF + 137)),
    ]
    atoms = "IKBWC"
    for a in atoms:
        for b in atoms:
            for c in atoms:
                probes.append((
                    f"tree {a}{b}{c}",
                    f"{a} {b} @ {c} @"))
    return probes


TIMEOUT = -99        # observation sentinel: still running at guard
RUN_GUARD = 15       # s — test-run bound, >> every converging probe


def _run_pe(exe: str, inp: str) -> Tuple[bytes, bytes, int]:
    try:
        out, err, rc = seed.run_native(exe, inp, timeout=RUN_GUARD)
        return out.encode(), err.encode(), rc
    except subprocess.TimeoutExpired:
        return (b"", b"", TIMEOUT)


def _run_c(exe: str, inp: str) -> Tuple[bytes, bytes, int]:
    try:
        return target_c.run_exe(exe, inp.encode(), timeout=RUN_GUARD)
    except subprocess.TimeoutExpired:
        return (b"", b"", TIMEOUT)


GRAPH_FUEL = 100_000


def _normalize_nf(text: str) -> str:
    """Re-quote an NF token stream through the surface map: a whole
    intact derived_s subtree becomes `S` (graph's quote_surface
    convention), raw kernels decompile the tree.  Same term,
    quotient-collapsed — applied to BOTH sides before comparing."""
    return " ".join(seed.bc_decompile(seed.t_from_host(
        tower.quote_surface(seed._parse_native_out(text)))))


def _underflows(inp: str) -> bool:
    """True iff the postfix stream underflows the parse stack —
    graph's _parse_native_out then pads without the app node, so
    step counts legitimately drift (NF still comparable)."""
    d = 0
    for tok in inp.split():
        if tok == "@":
            if d < 2:
                return True
            d -= 1
        else:
            d += 1
    return False


def _graph_obs(inp: str) -> Tuple[str, int, bool]:
    """graph.lo observation: parse tokens, LO-reduce, return
    (surface-normalized NF text, steps, converged)."""
    t = seed._parse_native_out(inp)
    nf, steps, _ = run_piece(GRAPH_PIECE, t, fuel=GRAPH_FUEL)
    return _normalize_nf(" ".join(
        seed.bc_decompile(seed.t_from_host(nf)))), steps, \
        steps < GRAPH_FUEL


def main() -> int:
    ok = True
    corpus = _corpus()
    print(f"cross_verify: {len(corpus)} probes x PE<->C + graph leg")

    pe_exe = seed._exe_for(Realization())
    pe_fuse_exe = seed._exe_for(Realization(fuse_s=True))
    pe_fuel_exe = seed._exe_for(Realization(fuel=5))

    with tempfile.TemporaryDirectory() as td:
        builds: Dict[str, str] = {}
        for tag, R in (("default", Realization(abi="hosted")),
                       ("fuse_s", Realization(abi="hosted", fuse_s=True)),
                       ("fuel5", Realization(abi="hosted", fuel=5))):
            c_path = os.path.join(td, f"r_{tag}.c")
            with open(c_path, "wb") as f:
                f.write(routines_c.emit_c(R))
            builds[tag] = target_c.compile_c(
                c_path, os.path.join(td, f"r_{tag}.exe"))

        nfail = 0
        for label, inp in corpus:
            # -- leg 1: PE <-> C byte-identical (default + fuse_s)
            for build, pe_exe_b in (("default", pe_exe),
                                    ("fuse_s", pe_fuse_exe)):
                pe_t = _run_pe(pe_exe_b, inp)
                c_t = _run_c(builds[build], inp)
                if pe_t != c_t:
                    nfail += 1
                    print(f"  FAIL {build} {label}: "
                          f"PE={pe_t!r}  C={c_t!r}")
                elif pe_t[2] == TIMEOUT:
                    print(f"  note {build} {label}: both diverge "
                          f"past {RUN_GUARD}s guard — same "
                          f"observation")
            # -- leg 2: graph.lo <-> C on the converging alphabet —
            # default build: NF + steps (same IStepBasis family);
            # fuse_s: NF only (primitive sβ, fewer steps by design).
            if inp and all(ch in "IKBWC @\t\r\n" for ch in inp):
                g_nf, g_steps, g_conv = _graph_obs(inp)
                for build, cmp_steps in (
                        ("default", not _underflows(inp)),
                        ("fuse_s", False)):
                    c_out, c_err, c_rc = _run_c(builds[build], inp)
                    bad = g_conv != (c_rc != TIMEOUT)
                    if not bad and g_conv:
                        m = re.search(r"steps=(\d+)", c_err.decode())
                        c_steps = int(m.group(1)) if m else -1
                        bad = not (
                            g_nf == _normalize_nf(c_out.decode())
                            and c_rc == 0
                            and (not cmp_steps or g_steps == c_steps))
                    if bad:
                        nfail += 1
                        print(f"  FAIL graph[{build}] {label}: "
                              f"graph={g_nf!r}/{g_steps}"
                              f"(conv={g_conv})  "
                              f"C={c_out!r}/{c_err!r} rc={c_rc}")
        print(f"  {'ok' if nfail == 0 else 'FAIL'} "
              f"PE<->C byte-identity (2 builds x {len(corpus)} probes) "
              f"+ graph NF/steps on token-safe subset")

        # -- fuel axis: fuel=5 on a term needing 10 steps
        pe_t = _run_pe(pe_fuel_exe, "S K @ K @ I @")
        c_t = _run_c(builds["fuel5"], "S K @ K @ I @")
        good = pe_t == c_t and pe_t[2] == 2
        print(f"  {'ok' if good else 'FAIL'} fuel=5 SKKI: "
              f"PE={pe_t!r} C={c_t!r}")
        ok = ok and good and nfail == 0

    print(f"{'OK' if ok else 'FAIL'} cross_verify "
          f"({nfail} divergences)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
