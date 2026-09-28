# _probe_emit_chain_mini.py — mini-scale smoke of the staged emit
# chain's seams: link NF -> projections -> assemble -> pack2, all
# NF-as-term handoffs, vs the python oracles.  Same scale as
# _probe_g9g_e2e_staged; the win64 run is emit_chain.main().
import sys, time
sys.path.insert(0, ".")
import spec_term as st
import emit_chain as ec
from reduce import app
import seed

IMPS, SLOTS, BASE, SR = ("ExitProcess",), (("x", 8),), 0x1000, 64 << 20

want_ib, want_db, want_syms = st.python_link(IMPS, SLOTS)
want_text, want_lm = st.python_assemble(st.ASM_LINK, want_syms, BASE)
R = seed.Realization(stack_reserve=SR)
want_pe = st.python_pack(want_text, IMPS, SLOTS, SR)

t0 = time.time()
link_nf, s1, n1 = ec._graph_run(st.link_query(IMPS, SLOTS))
print(f"link:    {s1} steps {n1} nodes ({time.time()-t0:.0f}s)",
      flush=True)
got_ib, got_db, got_syms = st.decode_link(link_nf)
print(f"  decode idata={len(got_ib)}B data={len(got_db)}B "
      f"syms={len(got_syms)} match={got_syms == want_syms}", flush=True)

sym_t = app(link_nf, ec.KI)
asm_nf, s2, n2 = ec._graph_run(
    st.assemble_query_t(st.fraglist_term(st.ASM_LINK), sym_t, BASE))
print(f"assemble:{s2} steps {n2} nodes", flush=True)
got_text, got_lm = st.decode_assemble(asm_nf)
print(f"  text {len(got_text)}B match={got_text == want_text} "
      f"localmap={got_lm == want_lm}", flush=True)

text_t = st._l0_nf(app(asm_nf, ec.KK), 500_000)
img_nf, s3, n3 = ec._graph_run(st.pack2_query_t(
    text_t, app(app(link_nf, ec.KK), ec.KK),
    app(app(link_nf, ec.KK), ec.KI), SR))
print(f"pack2:   {s3} steps {n3} nodes", flush=True)
got_pe = st._decode_bytecells(img_nf)
print("MATCH" if got_pe == want_pe else
      f"MISMATCH {len(got_pe)}B vs {len(want_pe)}B", flush=True)
