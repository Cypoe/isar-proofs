# _probe_cla.py — witness for the carry-lookahead twin:
# B4CLA a b must normalize to the same bytes4 NF as B4ADD a b, and both
# must equal the _b4_src literal of (a+b) mod 2^32.  Also reports the
# cd round/alloc structure — the lookahead should collapse the
# sequential carry chain into independent cones.
import random, sys, time
sys.path.insert(0, ".")
import spec_term as st
from lambda_dialect import parse, bracket
from graph_runtime import Graph

def term(src):
    return bracket(parse(src))

def nf_of(t, fuel=200_000):
    g = Graph()
    r = g.import_tree(t)
    nf, rounds = g.reduce_cd(r, fuel=fuel)
    return g.export_tree(nf), rounds, g.alloc_count()

random.seed(7)
cases = [0, 1, 255, 256, 0xFFFF, 0x10000, 0x7FFFFFFF, 0x80000000,
         0xFFFFFFFF, 0x0F0F0F0F, 0xF0F0F0F0, 0xDEADBEEF]
cases += [random.getrandbits(32) for _ in range(12)]

mismatch = 0
rows = []
for a in cases:
    for b in random.sample(cases, 3):
        want_src = st._b4_src((a + b) & 0xFFFFFFFF)
        t_rip = term(f"({st._B4ADD} {st._b4_src(a)} {st._b4_src(b)})")
        t_cla = term(f"({st._B4CLA} {st._b4_src(a)} {st._b4_src(b)})")
        t_lit = term(want_src)
        nf_rip, r_rip, al_rip = nf_of(t_rip)
        nf_cla, r_cla, al_cla = nf_of(t_cla)
        nf_lit, _, _ = nf_of(t_lit)
        ok = (nf_rip == nf_cla == nf_lit)
        if not ok:
            mismatch += 1
            print(f"MISMATCH a={a:#x} b={b:#x}: rip==lit {nf_rip == nf_lit} "
                  f"cla==lit {nf_cla == nf_lit}", flush=True)
        rows.append((r_rip, al_rip, r_cla, al_cla))

n = len(rows)
sr = sum(r[0] for r in rows) / n
sc = sum(r[2] for r in rows) / n
sa = sum(r[1] for r in rows) / n
sb = sum(r[3] for r in rows) / n
print(f"{n} pairs checked, mismatches={mismatch}", flush=True)
print(f"avg rounds: ripple={sr:.0f} cla={sc:.0f}", flush=True)
print(f"avg allocs: ripple={sa:.0f} cla={sb:.0f}", flush=True)
