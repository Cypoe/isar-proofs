"""G9h win64 probe — linkOf at the real scale."""
import time
import spec_term as st
import routines_x86_64_win64 as rts

def main():
    imports, slots = rts.IMPORTS, rts.DATA_SLOTS
    want = st.python_link(imports, slots)
    print(f"oracle: idata {len(want[0])}B + data {len(want[1])}B, "
          f"{len(want[2])} syms", flush=True)
    t0 = time.time()
    t = st.link_query(imports, slots)
    nf, steps, _ = st.reduce_tree_lo(t, st.LO_FUEL)
    val = st.decode_link(nf)
    print(f"linkOf win64: {steps} lo steps ({time.time()-t0:.0f}s) -> "
          f"{'MATCH' if val == want else 'MISMATCH'}", flush=True)
    if val != want:
        print(f"  got {val}", flush=True)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
