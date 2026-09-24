"""Turner-vs-abstract0 cost + cd feasibility on a small spec."""
import os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
sys.path.insert(0, os.path.dirname(__file__))
from spec_proto import (json_to_term, str_term, query_src, EQSTR, church_src,
                        _appn, tsize)
from lambda_dialect import parse, bracket_abstract0, bracket
from graph_runtime import reduce_tree_lo, reduce_tree_cd

# --- turner eqStr vs abstract0 -------------------------------------------
eq_a = bracket_abstract0(parse(EQSTR))
eq_t = bracket(parse(EQSTR))
n16_a = bracket_abstract0(parse(church_src(16)))
n16_t = bracket(parse(church_src(16)))
for label, eq, nn in [("abstract0", eq_a, n16_a), ("turner", eq_t, n16_t)]:
    t = _appn(eq, str_term("name"), str_term("note"), nn)
    t0 = time.time()
    nf, steps, alloc = reduce_tree_lo(t)
    print(f"eqStr name/note {label}: {steps} steps alloc={alloc} "
          f"{time.time()-t0:.2f}s nf={nf}")

# --- cd on a 2-entry spec -------------------------------------------------
small = {"toolchains": [
    {"name": "xdu.x86_64.pe", "dialect": "xdu.json", "isa": "x86_64",
     "routines": "x86_64.win64.xdu", "target": "pe64", "path": "native",
     "note": "nibble transducer plex -> PE exe (W3)"},
    {"name": "flat", "dialect": "bytecode.postfix", "isa": "x86_64",
     "routines": "x86_64.baremetal.lo", "target": "flat",
     "path": "runtime", "note": "flat binary, no loader"},
]}
ST = json_to_term(small)
src = query_src(n_top=len(small), n_ent=7, n_arr=2,
                n_emit=16, n_beq=34, n_bt=22, n_be=10)
Q = bracket_abstract0(parse(src))
t = _appn(Q, ST, str_term("flat"))

t0 = time.time()
nf, steps, alloc = reduce_tree_lo(t)
print(f"lo 2-entry 'flat': {steps} steps alloc={alloc} "
      f"{time.time()-t0:.1f}s")

t0 = time.time()
nf_cd, rounds, alloc_cd = reduce_tree_cd(t, 200_000)
print(f"cd 2-entry 'flat': {rounds} rounds alloc={alloc_cd} "
      f"{time.time()-t0:.1f}s")
print("lo nf == cd nf:", nf == nf_cd)
