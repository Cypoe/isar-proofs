"""Find which micro-burst allocates ~190k nodes in c2 STEP acc0."""
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
sys.path.insert(0, os.path.dirname(__file__))
from spec_proto import (EQNIB, church_src, _appn, _CONS, _NIL, _SELECTORS)
from lambda_dialect import parse, bracket_abstract0
from reduce import K, app, I, KK
from graph_runtime import Graph


def tsize(t, memo=None):
    if memo is None:
        memo = set()
    if id(t) in memo:
        return 0
    memo.add(id(t))
    if t.k == K.APP:
        return 1 + tsize(t.l, memo) + tsize(t.r, memo)
    return 1


STEP = bracket_abstract0(parse(
    "\\acc. acc (\\la. \\lb. \\o. o "
    "(la "
    "(\\k2. k2 la lb (lb K (\\h. \\t. (K I))))"
    "(\\ha. \\ta. lb "
    "(\\k2. k2 la lb (K I)) "
    "(\\hb. \\tb. " + EQNIB + " ha hb "
    "(\\k2. k2 ta tb K) (\\k2. k2 ta tb (K I)))))"
    "(\\k2. k2 la lb (K I)))"))

one = _appn(_CONS, _SELECTORS[3], _NIL)
mk = bracket_abstract0(parse("\\la. \\lb. \\o. \\k2. k2 la lb o"))
acc0 = _appn(mk, one, one, KK)

for k in (1, 2):
    cn = bracket_abstract0(parse(church_src(k)))
    t = _appn(cn, STEP, acc0)
    g = Graph()
    cur = g.import_tree(t)
    prev = g.alloc_count()
    i = 0
    bursts = []
    while i < 50_000:
        nxt = g.step(cur)
        if nxt is None:
            break
        cur = g.repr(nxt)
        i += 1
        a = g.alloc_count()
        if a - prev > 2000:
            bursts.append((i, a - prev))
        prev = a
    print(f"c{k}: NF at {i} steps, alloc={g.alloc_count()}, "
          f"bursts>2k: {bursts[:10]}")
    nf = g.export_tree(cur)
    print(f"   nf size={tsize(nf)}  nf={nf}")
