"""Minimal divergence probe: eqStr 'na' vs 'na' with bounded fuel."""
import os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
sys.path.insert(0, os.path.dirname(__file__))
from spec_proto import (json_to_term, str_term, EQSTR, church_src, _appn)
from lambda_dialect import parse, bracket_abstract0
from graph_runtime import reduce_tree_lo

eq = bracket_abstract0(parse(EQSTR))
print("eq term:", eq)
n = bracket_abstract0(parse(church_src(8)))
t = _appn(eq, str_term("na"), str_term("na"), n)

from graph_runtime import Graph
g = Graph()
root = g.import_tree(t)
cur = root
for i in range(300_000):
    nxt = g.step(cur)
    if nxt is None:
        print(f"NF after {i} steps")
        break
    cur = g.repr(nxt)
    if i in (100, 1000, 10000, 50000, 100000, 200000):
        print(f"  step {i}: alloc={g.alloc_count()}")
else:
    print(f"no NF in 300k steps; alloc={g.alloc_count()}")
print("nf:", g.export_tree(cur))
