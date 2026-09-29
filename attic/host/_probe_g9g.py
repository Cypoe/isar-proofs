import sys, time
sys.path.insert(0, ".")
import spec_term as st
from reduce import app, K, I, KK
from graph_runtime import Graph

def dec_b4(t):
    return int.from_bytes(st._decode_bytecells(t), "little")

def run_lo(t, fuel=50_000_000):
    g = Graph()
    r = g.import_tree(t)
    t0 = time.time()
    nf, s = g.reduce(r, fuel=fuel)
    return g.export_tree(nf), s, time.time() - t0

# --- dataOf ---------------------------------------------------------------
for name, slots in [
    ("mini", (("x", 8),)),
    ("win64", st.routines_x86_64_win64.DATA_SLOTS),
]:
    want_b, want_s = st.python_data(slots)
    nf, steps, dt = run_lo(st.data_query(slots))
    got_b, got_s = st.decode_bytesyms(nf)
    print(f"dataOf {name}: bytes {len(got_b)}B match={got_b == want_b} "
          f"syms match={got_s == want_s} [{steps} steps {dt:.0f}s]")
    if got_s != want_s:
        print("  got:", got_s, "\n  want:", want_s)

# --- idataOf --------------------------------------------------------------
for name, imps in [
    ("mini", ("ExitProcess",)),
    ("win64", st.routines_x86_64_win64.IMPORTS),
]:
    want_b, want_s = st.python_idata(imps)
    nf, steps, dt = run_lo(st.idata_query(imps))
    got_b, got_s = st.decode_bytesyms(nf)
    print(f"idataOf {name}: bytes {len(got_b)}B match={got_b == want_b} "
          f"syms match={got_s == want_s} [{steps} steps {dt:.0f}s]")
    if got_b != want_b:
        print("  got :", got_b.hex())
        print("  want:", want_b.hex())
    if got_s != want_s:
        print("  got:", got_s, "\n  want:", want_s)

# --- packOf mini ----------------------------------------------------------
text, imps, slots, res = b"\xc3", ("ExitProcess",), (("x", 8),), 64 << 20
want = st.python_pack(text, imps, slots, res)
nf, steps, dt = run_lo(st.pack_query(text, imps, slots, res))
got = st._decode_bytecells(nf)
print(f"packOf mini: {len(got)}B match={got == want} [{steps} steps {dt:.0f}s]")
if got != want:
    for i, (a, b) in enumerate(zip(got, want)):
        if a != b:
            print(f"  first diff @ {i:#x}: got {a:#x} want {b:#x}")
            print(f"  got : {got[max(0,i-8):i+8].hex()}")
            print(f"  want: {want[max(0,i-8):i+8].hex()}")
            break
    print("  len", len(got), "vs", len(want))
