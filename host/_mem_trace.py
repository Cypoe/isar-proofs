# _mem_trace.py — where does the arena memory actually go?
#
# Instruments Graph.stats + Graph.census() on the measured cases:
#   PAIR (permutable, quotiented) vs JOIN (sequential, no quotient)
#   and the linkOf stage term (real toolchain shape).
#
# For each run: alloc sites (who allocated), intern outcomes (the
# quotient leaking or holding), retention (forwarded dead vs live
# reps vs semantically reachable set), and the dict residency.
import sys, time
sys.path.insert(0, ".")
import spec_term as st
from lambda_dialect import parse, bracket
from graph_runtime import Graph

def term(src):
    return bracket(parse(src))

def run(engine, t, fuel, label):
    g = Graph()
    r = g.import_tree(t)
    t0 = time.time()
    if engine == "lo":
        nf, u = g.reduce(r, fuel=fuel)
    else:
        nf, u = g.reduce_cd(r, fuel=fuel)
    dt = time.time() - t0
    live = g.live_reachable(nf)
    c = g.census()
    print(f"== {label} [{engine}] {u} rounds/steps, {dt:.1f}s ==", flush=True)
    print(f"  nodes={c['nodes']:,}  forwarded={c['forwarded']:,}  "
          f"live_reps={c['live_reps']:,}  reachable={live:,}", flush=True)
    print(f"  retention: {c['nodes'] - live:,} retained / {live:,} live "
          f"({(c['nodes'] - live) / max(live, 1):.1f}x)", flush=True)
    print(f"  est_bytes={c['est_bytes'] / 1e6:.1f}MB "
          f"(lists={c['lists_bytes'] / 1e6:.1f} dicts={c['dicts_bytes'] / 1e6:.1f})",
          flush=True)
    for k in sorted(g.stats):
        print(f"    {k:22s} {g.stats[k]:>12,}", flush=True)
    print(f"  dicts: intern={c['app_intern']:,} step_memo={c['step_memo']:,} "
          f"cd_memo={c['cd_memo']:,} nf={c['nf']:,}", flush=True)
    print(flush=True)
    return g, nf

ZF = lambda n: term(f"({st._ZEROFILL} {st._num_src(n)})")

# --- the quotient pair at moderate scale (JOIN zf256 was 51.6M
#     allocs; 64/128 keeps this probe in minutes) ---
oracle = {}
for n in [64, 128]:
    z1, z2 = ZF(n), ZF(2 * n)
    pair_t = st._appn(st._CONS, z1, st._appn(st._CONS, z2, st._NIL))
    run("cd", pair_t, 100_000, f"PAIR zf{n} zf{2*n}")
    jt = st._appn(term(st._JOIN),
                  st._appn(st._CONS, z1, st._appn(st._CONS, z2, st._NIL)))
    g, nf = run("cd", jt, 100_000, f"JOIN zf{n} zf{2*n}")
    oracle[n] = g.export_tree(nf)

# --- compact: same terms, per-round arena rebuild.  Verify the NF is
#     byte-identical to the un-compacted run — compact must change
#     residency, not semantics. ---
def run_compact(t, fuel, label, want):
    g = Graph()
    r = g.import_tree(t)
    t0 = time.time()
    nf, u = g.reduce_cd(r, fuel=fuel, compact=True)
    dt = time.time() - t0
    out = g.export_tree(nf)
    match = "MATCH" if out == want else "MISMATCH"
    c = g.census()
    print(f"== {label} [cd+compact] {u} rounds, {dt:.1f}s {match} ==",
          flush=True)
    print(f"  nodes={c['nodes']:,}  forwarded={c['forwarded']:,}  "
          f"live_reps={c['live_reps']:,}", flush=True)
    print(f"  est_bytes={c['est_bytes'] / 1e6:.1f}MB", flush=True)
    for k in sorted(g.stats):
        print(f"    {k:22s} {g.stats[k]:>12,}", flush=True)
    print(flush=True)
    return out

for n in [64, 128]:
    z1, z2 = ZF(n), ZF(2 * n)
    jt = st._appn(term(st._JOIN),
                  st._appn(st._CONS, z1, st._appn(st._CONS, z2, st._NIL)))
    run_compact(jt, 100_000, f"JOIN zf{n} zf{2*n}", oracle[n])

# --- real toolchain stage: linkOf mini (~40k steps) ---
t = st.link_query(("ExitProcess",), (("x", 8),))
g = Graph()
r = g.import_tree(t)
t0 = time.time()
nf, steps = g.reduce(r, fuel=st.LO_FUEL)
dt = time.time() - t0
live = g.live_reachable(nf)
c = g.census()
print(f"== linkOf mini [lo] {steps} steps, {dt:.1f}s ==", flush=True)
print(f"  nodes={c['nodes']:,}  forwarded={c['forwarded']:,}  "
      f"live_reps={c['live_reps']:,}  reachable={live:,}", flush=True)
print(f"  est_bytes={c['est_bytes'] / 1e6:.1f}MB", flush=True)
for k in sorted(g.stats):
    print(f"    {k:22s} {g.stats[k]:>12,}", flush=True)
