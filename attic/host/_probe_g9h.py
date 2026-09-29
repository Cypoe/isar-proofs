"""G9h probe — linkOf + pack2Of + linkasm on the mini case."""
import sys, time
import spec_term as st

def main():
    imports, slots = ("ExitProcess",), (("x", 8),)

    want = st.python_link(imports, slots)
    print(f"oracle link: idata {len(want[0])}B + data {len(want[1])}B, "
          f"syms {want[2]}", flush=True)

    t0 = time.time()
    t = st.link_query(imports, slots)
    nf, steps, _ = st.reduce_tree_lo(t, st.LO_FUEL)
    val = st.decode_link(nf)
    print(f"linkOf mini: {steps} lo steps ({time.time()-t0:.0f}s) -> "
          f"{'MATCH' if val == want else 'MISMATCH'}", flush=True)
    if val != want:
        print(f"  got {val}", flush=True)
        return 1

    t0 = time.time()
    t2 = st.linkasm_query(st.fraglist_term(st.LINKASM_PROG), imports,
                          slots, 0x1000)
    nf2, steps2, _ = st.reduce_tree_lo(t2, st.LO_FUEL)
    val2 = st.decode_assemble(nf2)
    want_b, want_l = st.python_assemble(st.LINKASM_PROG, want[2], 0x1000)
    print(f"linkasm mini: {steps2} lo steps ({time.time()-t0:.0f}s) -> "
          f"{len(val2[0]) if val2 else 0}B "
          f"{'MATCH' if val2 == (want_b, want_l) else 'MISMATCH'}",
          flush=True)
    if val2 != (want_b, want_l):
        print(f"  got {val2} want {(want_b, want_l)}", flush=True)
        return 1

    t0 = time.time()
    t3 = st.pack2_query(b"\xc3", want[0], want[1], 64 << 20)
    nf3, steps3, _ = st.reduce_tree_lo(t3, st.LO_FUEL)
    pe = st._decode_bytecells(nf3)
    want_pe = st.python_pack(b"\xc3", imports, slots, 64 << 20)
    print(f"pack2Of mini: {steps3} lo steps ({time.time()-t0:.0f}s) -> "
          f"{len(pe)}B {'MATCH' if pe == want_pe else 'MISMATCH'}",
          flush=True)
    return 0 if pe == want_pe else 1


if __name__ == "__main__":
    raise SystemExit(main())
