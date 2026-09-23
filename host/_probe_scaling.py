# _probe_scaling.py — isolate the memory/time growth: lo vs cd on a
# pure list-emission term (ZEROFILL n -> n cons cells, same NF shape
# as pack's image bytes).  If cd is superlinear in output size while
# lo stays ~linear, the pathology is the fixpoint-sweep engine, not
# the term.  Reports steps/rounds, allocs, wall — allocs per unit is
# the arena-growth rate.
import sys, time
sys.path.insert(0, ".")
import spec_term as st
from lambda_dialect import parse, bracket
from graph_runtime import Graph

def term(src):
    return bracket(parse(src))

def run(engine, t, fuel):
    g = Graph()
    r = g.import_tree(t)
    t0 = time.time()
    if engine == "lo":
        nf, u = g.reduce(r, fuel=fuel)
    else:
        nf, u = g.reduce_cd(r, fuel=fuel)
    dt = time.time() - t0
    n_out = len(st._decode_bytecells(g.export_tree(nf)))
    return u, g.alloc_count(), dt, n_out

for n in [64, 128, 256, 512, 1024, 2048]:
    t = term(f"({st._ZEROFILL} {st._num_src(n)})")
    s, na, dt, out = run("lo", t, 10_000_000)
    print(f"ZEROFILL {n}: lo steps={s} allocs={na} "
          f"({na//max(s,1)}/step) dt={dt:.1f}s out={out}", flush=True)

for n in [64, 128, 256, 512]:
    t = term(f"({st._ZEROFILL} {st._num_src(n)})")
    r, na2, dt2, out2 = run("cd", t, 100_000)
    print(f"ZEROFILL {n}: cd rounds={r} allocs={na2} "
          f"({na2//max(r,1)}/round) dt={dt2:.1f}s out={out2}", flush=True)

# two-stage emission: JOIN [zf n, zf n] — closer to pack's shape
for n in [64, 128, 256, 512]:
    zf = term(f"({st._ZEROFILL} {st._num_src(n)})")
    lst = st._appn(st._CONS, zf, st._appn(st._CONS, zf, st._NIL))
    t = st._appn(term(st._JOIN), lst)
    s, na, dt, out = run("lo", t, 10_000_000)
    print(f"JOIN2 {n}: lo steps={s} allocs={na} "
          f"({na//max(s,1)}/step) dt={dt:.1f}s out={out}", flush=True)
    r, na2, dt2, out2 = run("cd", t, 100_000)
    print(f"        cd rounds={r} allocs={na2} "
          f"({na2//max(r,1)}/round) dt={dt2:.1f}s out={out2}", flush=True)
