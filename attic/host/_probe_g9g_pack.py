import sys, time
sys.path.insert(0, ".")
import spec_term as st
from graph_runtime import Graph
import routines_x86_64_win64 as r
import seed, isa_x86_64 as isa, target_pe64
from types import SimpleNamespace

prog = r.program(seed.Realization())
text, loc = isa.assemble(prog, target_pe64.symbols(r.IMPORTS,
                                                   r.DATA_SLOTS), 0x1000)
want = target_pe64.pack(text, loc, r.IMPORTS, r.DATA_SLOTS,
                        SimpleNamespace(stack_reserve=64 << 20))
print("oracle: text %dB pe %dB" % (len(text), len(want)), flush=True)
g = Graph()
q = st.pack_query(text, r.IMPORTS, r.DATA_SLOTS, 64 << 20)
r0 = g.import_tree(q)
print("nodes", st.term_nodes(q), flush=True)
t0 = time.time()
nf, s = g.reduce(r0, fuel=50_000_000)
print("steps", s, "dt", time.time() - t0, flush=True)
got = st._decode_bytecells(g.export_tree(nf))
print("MATCH" if got == want else "DIFF len %d vs %d" % (len(got),
                                                       len(want)),
      flush=True)
if got != want:
    for i, (a, b) in enumerate(zip(got, want)):
        if a != b:
            print("first diff @ %#x: %#x vs %#x" % (i, a, b), flush=True)
            break
