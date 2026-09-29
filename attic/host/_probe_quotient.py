# _probe_quotient.py — measuring the quotient the reducer already
# exploits, and where it runs out.
#
# (a) Structural quotient: _app_intern hash-consing.  Two occurrences
#     of an IDENTICAL subterm intern to one node — the work is done
#     once.  Report unique_count vs alloc_count.
# (b) Redex-order quotient: cd develops all redexes in a round in
#     parallel — the k! development orders of k independent redexes
#     collapse to one class.  Compare cd rounds on an independent-pair
#     term (permutable) vs a sequential fold (not permutable).
# (c) The boundary: sequential producer chains have no permutations —
#     the quadratic there is real dependency order, not redundancy.
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
    return u, g.alloc_count(), g.unique_count, time.time() - t0

ZF = lambda n: term(f"({st._ZEROFILL} {st._num_src(n)})")

# (a) identical subterm shared: CONS (zf n) (CONS (zf n) NIL)
#     — the SAME zf term object twice; interning should make it one
#     node, developed once.
print("== (a) structural quotient: identical subterm occurrences ==",
      flush=True)
for n in [128, 256, 512]:
    zf = ZF(n)
    t = st._appn(st._CONS, zf, st._appn(st._CONS, zf, st._NIL))
    u, na, uq, dt = run("lo", t, 10_000_000)
    print(f"CONS zf{n} zf{n}: lo steps={u} allocs={na} "
          f"unique={uq} share={uq/na:.2f} dt={dt:.1f}s", flush=True)

# (b) redex-order quotient: two INDEPENDENT computations side by
#     side — cd should develop both within the same rounds (count ~
#     max, not sum).  vs JOIN2 sequential (~13n rounds).  DIFFERENT
#     producer sizes (zf n vs zf 2n, ZEROFILL vs a different term)
#     isolate parallelism from the identical-subterm sharing of (a).
print("== (b) redex-order quotient: independent pair vs sequential ==",
      flush=True)
for n in [64, 128, 256]:
    z1, z2 = ZF(n), ZF(2 * n)
    pair_t = st._appn(st._CONS, z1, st._appn(st._CONS, z2, st._NIL))
    r, na, uq, dt = run("cd", pair_t, 100_000)
    print(f"PAIR zf{n} zf{2*n}: cd rounds={r} allocs={na} "
          f"unique={uq} dt={dt:.1f}s", flush=True)
    jt = st._appn(term(st._JOIN),
                  st._appn(st._CONS, z1, st._appn(st._CONS, z2, st._NIL)))
    r2, na2, uq2, dt2 = run("cd", jt, 100_000)
    print(f"JOIN zf{n} zf{2*n}: cd rounds={r2} allocs={na2} "
          f"unique={uq2} dt={dt2:.1f}s", flush=True)

# (b2) k independent producers: CONS a1 (CONS a2 (CONS a3 (CONS a4
#      NIL))) — k! development orders collapse if cd rounds stay flat.
print("== (b2) k=4 independent producers — the k! collapse ==",
      flush=True)
for n in [64, 128, 256]:
    lst = st._NIL
    for m in reversed([n, 2 * n, 3 * n, 4 * n]):
        lst = st._appn(st._CONS, ZF(m), lst)
    r, na, uq, dt = run("cd", lst, 100_000)
    print(f"PAIR4 zf[{n},{2*n},{3*n},{4*n}]: cd rounds={r} "
          f"allocs={na} unique={uq} dt={dt:.1f}s", flush=True)
