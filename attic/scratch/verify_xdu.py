"""W3 end-to-end verification: native exes + graph.lo/cd runtime for all
four xdu probes."""
import os
import subprocess
import sys

HOST = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "host"))
SEED = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "seed"))
for p in (HOST, SEED):
    if p not in sys.path:
        sys.path.insert(0, p)

import xdu_dialect as xd
import graph_runtime as gr
import cogen
from seed import Realization, emit
import toolchain

BUILD = os.path.normpath(os.path.join(os.path.dirname(__file__), "..",
                                      "seed", "build"))
os.makedirs(BUILD, exist_ok=True)

IN16 = bytes(range(16))          # ~16-byte input
IN2 = b"Hi"

ok = True

# ---- cogen.choose native plan ------------------------------------------
ctx = cogen.MachineContext.detect()
budget = cogen.Budget.SERIAL
xdu = xd.load(xd.probe_path("echo"))
plan = cogen.choose([], budget, ctx, path="native", program=xdu)
print(f"choose native: plan={plan.name} toolchain={plan.toolchain} "
      f"note={plan.note}")
try:
    cogen.choose([], budget, ctx, path="native", program=None)
    print("FAIL choose: native without program accepted")
    ok = False
except AssertionError as e:
    print(f"OK choose refuses native w/o program: {e}")

# ---- emit + run native exes ---------------------------------------------
print("\n== native executables ==")
tc = toolchain.by_name("xdu.x86_64.pe")
for probe in ("echo", "hexdump", "drop0", "toggle"):
    xdu = xd.load(xd.probe_path(probe))
    blob = emit(Realization(), tc=tc, program=xdu)
    exe = os.path.join(BUILD, f"xdu_{probe}.exe")
    with open(exe, "wb") as f:
        f.write(blob)
    for data, tag in ((IN2, "Hi"), (IN16, "0x00..0x0f"), (b"", "empty")):
        exp = xd.interpret(xdu, data)
        r = subprocess.run([exe], input=data, capture_output=True)
        got = (r.stdout, r.returncode)
        match = got == exp
        ok = ok and match
        print(f"  {'OK' if match else 'FAIL'} {probe:8s} {tag:12s} "
              f"out={got[0]!r} rc={got[1]} (expect out={exp[0]!r} rc={exp[1]})")

# ---- graph runtime lo + cd ----------------------------------------------
print("\n== graph runtime ==")
for probe in ("echo", "hexdump", "drop0", "toggle"):
    xdu = xd.load(xd.probe_path(probe))
    exp = xd.interpret(xdu, IN2)
    t = xd.encode(xdu, IN2)
    nf_lo, steps, n_lo = gr.reduce_tree_lo(t, fuel=1_000_000)
    got_lo = xd.term_to_nibbles(nf_lo)
    nf_cd, rounds, n_cd = gr.reduce_tree_cd(t, fuel=1000)
    got_cd = xd.term_to_nibbles(nf_cd)
    m_lo = got_lo == exp
    m_cd = got_cd == exp
    ok = ok and m_lo and m_cd
    print(f"  {'OK' if m_lo else 'FAIL'} {probe:8s} lo: out={got_lo[0]!r} "
          f"rc={got_lo[1]} ({steps} steps, alloc={n_lo}) expect={exp}")
    print(f"  {'OK' if m_cd else 'FAIL'} {probe:8s} cd: out={got_cd[0]!r} "
          f"rc={got_cd[1]} ({rounds} rounds, alloc={n_cd}) expect={exp}")

print(f"\n{'OK' if ok else 'FAIL'} verify_xdu")
sys.exit(0 if ok else 1)
