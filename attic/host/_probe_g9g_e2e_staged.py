# _probe_g9g_e2e_staged.py — end-to-end plumbing across the stage
# boundary: assemble reduces in g1; its byte-list NF is exported as a
# term (the .lo serialization seam — stages hand off data, not heaps)
# and re-imported into fresh g2 for pack.  Peak arena is
# max(stage arenas), not their sum — the single-arena composition
# (_probe_g9g_e2e.py) pinned both and OOM-crawled at ~85GB.
#
# Verified: decode(text_term) == isa.assemble output  AND
#           pack(image) == target_pe64.pack(asm_bytes, ...) byte-exact.
import sys, time
sys.path.insert(0, ".")
import spec_term as st
from reduce import app, KK
from graph_runtime import Graph

t0 = time.time()
want_b, want_l = st.python_assemble(st.ASM_LINK, {}, 0x1000)
want_pe = st.python_pack(want_b, ("ExitProcess",), (("x", 8),), 64 << 20)
print(f"oracle: text {len(want_b)}B {want_b.hex()} -> pe {len(want_pe)}B",
      flush=True)

# --- stage 1: assemble in arena g1 --------------------------------------
asm_t = st.assemble_query(st.fraglist_term(st.ASM_LINK), {}, 0x1000)
g1 = Graph()
r1 = g1.import_tree(asm_t)
nf1, s1 = g1.reduce(r1, fuel=200_000_000)
print(f"assemble: {s1} steps, arena {g1.alloc_count()} "
      f"({time.time() - t0:.0f}s)", flush=True)
# the pair NF exported, then (pair K) reduced at tree level -> bytes term
pair_t = g1.export_tree(nf1)
text_t = st._l0_nf(app(pair_t, KK), 500_000)
got_b = st._decode_bytecells(text_t)
print(f"text seam: {len(got_b)}B match={got_b == want_b}", flush=True)
del g1   # stage-1 arena released — the seam carried data, not heap

# --- stage 2: pack in arena g2 ------------------------------------------
g2 = Graph()
q = st.pack_query_t(text_t, ("ExitProcess",), (("x", 8),), 64 << 20)
r2 = g2.import_tree(q)
nf2, s2 = g2.reduce(r2, fuel=200_000_000)
print(f"pack: {s2} steps, arena {g2.alloc_count()} "
      f"({time.time() - t0:.0f}s)", flush=True)
got_pe = st._decode_bytecells(g2.export_tree(nf2))
print("MATCH" if got_pe == want_pe else
      f"MISMATCH len {len(got_pe)} vs {len(want_pe)}", flush=True)
