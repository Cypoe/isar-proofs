"""Trace term size growth in the eqStr reduction to find the blowup."""
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
sys.path.insert(0, os.path.dirname(__file__))
from spec_proto import str_term, EQSTR, church_src, _appn
from lambda_dialect import parse, bracket_abstract0
from graph_runtime import Graph
from reduce import K

eq = bracket_abstract0(parse(EQSTR))
n = bracket_abstract0(parse(church_src(4)))
t = _appn(eq, str_term("na"), str_term("na"), n)

g = Graph()
cur = g.import_tree(t)
seen = set()
for i in range(400_000):
    nxt = g.step(cur)
    if nxt is None:
        print(f"NF after {i} steps")
        break
    cur = g.repr(nxt)
    if i % 2000 == 0:
        # measure exported size roughly via alloc growth
        print(f"  step {i}: alloc={g.alloc_count()} uniq={g.unique_count}")
else:
    print(f"no NF in 400k steps; alloc={g.alloc_count()}")

# print the residual term (truncated)
nf = g.export_tree(cur)
s = str(nf)
print(f"residual len={len(s)}")
print(s[:2000])
