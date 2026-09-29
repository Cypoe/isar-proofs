"""G9h cd pre-check — the composed linkasm term under cd, plus linkOf cd."""
import time
import spec_term as st

def main():
    imports, slots = ("ExitProcess",), (("x", 8),)

    t0 = time.time()
    t = st.link_query(imports, slots)
    nf, rounds, _ = st.reduce_tree_cd(t, st.CD_FUEL)
    val = st.decode_link(nf)
    want = st.python_link(imports, slots)
    print(f"linkOf mini cd: {rounds} rounds ({time.time()-t0:.0f}s) -> "
          f"{'MATCH' if val == want else 'MISMATCH'}", flush=True)

    t0 = time.time()
    t2 = st.linkasm_query(st.fraglist_term(st.LINKASM_PROG), imports,
                          slots, 0x1000)
    nf2, rounds2, _ = st.reduce_tree_cd(t2, st.CD_FUEL)
    val2 = st.decode_assemble(nf2)
    want_b, want_l = st.python_assemble(st.LINKASM_PROG, want[2], 0x1000)
    print(f"linkasm mini cd: {rounds2} rounds ({time.time()-t0:.0f}s) -> "
          f"{'MATCH' if val2 == (want_b, want_l) else 'MISMATCH'}",
          flush=True)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
