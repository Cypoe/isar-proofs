# _probe_g9g_e2e.py — end-to-end stage composition at term level:
#   packOf ((assembleOf ASM_LINK {} 0x1000) K) imports slots stackres
# reduces in ONE graph — pack's `text` is assemble's live output, not a
# canned literal.  Compared byte-for-byte against
# target_pe64.pack(isa.assemble(...)[0], ...).  ASM_LINK (12B text,
# fwd+bwd rel32 + labels) keeps the composed reduce tractable
# (~assemble 480k + pack ~300k lo steps).
import sys, time
sys.path.insert(0, ".")
import spec_term as st
from reduce import KK
from graph_runtime import Graph

t0 = time.time()
want_b, _want_l = st.python_assemble(st.ASM_LINK, {}, 0x1000)
want_pe = st.python_pack(want_b, ("ExitProcess",), (("x", 8),), 64 << 20)
print(f"oracle: text {len(want_b)}B {want_b.hex()} -> pe {len(want_pe)}B",
      flush=True)

asm_t = st.assemble_query(st.fraglist_term(st.ASM_LINK), {}, 0x1000)
q = st.pack_query_t(st._appn(asm_t, KK), ("ExitProcess",), (("x", 8),),
                    64 << 20)

g = Graph()
r0 = g.import_tree(q)
print("nodes", st.term_nodes(q), f"built {time.time() - t0:.0f}s",
      flush=True)
nf, s = g.reduce(r0, fuel=200_000_000)
print(f"steps {s} dt {time.time() - t0:.2f}", flush=True)
got = st._decode_bytecells(g.export_tree(nf))
print("MATCH" if got == want_pe else
      f"MISMATCH len {len(got)} vs {len(want_pe)}", flush=True)
