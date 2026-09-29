"""Measure per-primitive LO step costs for spec_term design."""
import os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
from reduce import T, K, I, KK, B, S, C, D, app
from lambda_dialect import parse, bracket_abstract0, bracket
from graph_runtime import reduce_tree_lo


def _appn(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t


def tsize(t, memo=None):
    if memo is None:
        memo = set()
    if id(t) in memo:
        return 0
    memo.add(id(t))
    if t.k == K.APP:
        return 1 + tsize(t.l, memo) + tsize(t.r, memo)
    return 1


def sel0(k):
    return bracket_abstract0(parse(
        "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"))


def selt(k):
    return bracket(parse(
        "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"))


s0, s5 = sel0(0), sel0(5)
t0t, t5 = selt(0), selt(5)
print("abstract0 selector size:", tsize(s0), " turner:", tsize(t0t))

# cost of one full 16-arg application of a selector
VECS = []
for i in range(16):
    v = KK
    args = [KK if j == i else app(KK, I) for j in range(16)]
    VECS.append(tuple(args))

def appN(f, args):
    return _appn(f, *args)

def eqnib(a, b):
    t = a
    for i in range(16):
        t = app(t, appN(b, VECS[i]))
    return t

for label, (a, b) in [("a0 sel0 sel0", (s0, s0)), ("a0 sel5 sel0", (s5, s0)),
                      ("tur t5 t0t", (t5, t0t))]:
    t0 = time.time()
    nf, steps, alloc = reduce_tree_lo(eqnib(a, b), 50_000_000)
    print(f"{label}: {steps} steps alloc={alloc} {time.time()-t0:.1f}s nf={nf}")

# a single 16-arg selector application
t0 = time.time()
nf, steps, alloc = reduce_tree_lo(appN(s5, VECS[3]), 10_000_000)
print(f"sel0[5] applied: {steps} steps {time.time()-t0:.1f}s nf={nf}")
t0 = time.time()
nf, steps, alloc = reduce_tree_lo(appN(t5, VECS[3]), 10_000_000)
print(f"selT[5] applied: {steps} steps {time.time()-t0:.1f}s nf={nf}")
