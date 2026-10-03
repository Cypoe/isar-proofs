"""nanopass gates — arena-boundary machinery: bounded batches,
pin splices, blob stores, staged link, ir egress, decode evidence."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

import emit_chain as ec                                        # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
from graph_runtime import reduce_tree_lo                       # noqa: E402
from np_common import _fixed_of                                # noqa: E402


def gate_batch_bounded() -> bool:
    """_batch_bounded halves on kernel OOM (rc=4) and preserves
    query order; a persistent rc=4 on a single root and any other
    rc propagate without splitting.  The pass-2 resolver terms are
    what actually OOM — measured 32 roots OK / 64 OOM, 2026-10."""
    def oom_above(n):
        def b(qs):
            if len(qs) > n:
                raise RuntimeError(
                    "exe bytes batch failed rc=4 stderr=b''")
            return (list(qs), 0, 0)
        return b
    got = ec._batch_bounded(oom_above(8), list(range(100)))
    if got != list(range(100)):
        return False
    try:                                # single root that OOMs
        ec._batch_bounded(oom_above(0), ["x"])
        return False
    except RuntimeError as e:
        if "rc=4" not in str(e):
            return False
    try:                                # non-OOM failure: no split
        def bad_rc(qs):
            raise RuntimeError("exe bytes batch failed rc=3")
        ec._batch_bounded(bad_rc, list(range(100)))
        return False
    except RuntimeError as e:
        return "rc=3" in str(e)
    return True


def gate_pin_splice(R) -> bool:
    """pinned constants splice verbatim — the keyed Merkle root of a
    query must be identical whether the constant streams as packed
    nodes or as a stored blob (digests are position-independent)."""
    t = st.routine_of("mkapp_p")
    pins: dict = {}
    st.pin_term(t, pins)
    q = st.routine_query("mkapp_p", R)
    _b0, k0 = st.pack_ir_keyed(q)
    _b1, k1 = st.pack_ir_keyed(q, pinned=pins)
    if k0 != k1:
        return False
    # the spliced stream decodes to the same NF — run both
    nf0 = reduce_tree_lo(st.unpack_ir(_b0)[0], 200_000)[0]
    nf1 = reduce_tree_lo(st.unpack_ir(_b1)[0], 200_000)[0]
    return st.decode_frag(nf0) == st.decode_frag(nf1)


def gate_blob_store(R, tmpdir: str) -> bool:
    """named pins are content-addressed on disk: a fresh BlobStore
    reloading the blob registers a splice entry whose packed stream
    is byte-identical to the miss-path walk."""
    store1 = ec.BlobStore(os.path.join(tmpdir, "b1"))
    t = st.routine_of("st_s", _fixed_of(R), False)
    key = st.routine_pin_key("st_s", _fixed_of(R), False)
    d_miss = store1.pin_named(key, t)
    store2 = ec.BlobStore(os.path.join(tmpdir, "b1"))
    d_hit = store2.pin_named(key, t)
    if d_miss != d_hit or store2.hits != 1:
        return False
    q = st.routine_query("st_s", R, fixed=_fixed_of(R), ir_ctx=False)
    _b1, k1 = st.pack_ir_keyed(q, pinned=store1.pins)
    _b2, k2 = st.pack_ir_keyed(q, pinned=store2.pins)
    _b0, k0 = st.pack_ir_keyed(q)
    # Merkle digests are structural — identical whether the constant
    # streams as a stored blob or is re-walked.  (Byte size can grow:
    # a spliced blob can't dedup INTO the query spine — the win is
    # skipping the walk, not the wire size.)
    return k1 == k2 == k0


def gate_split_link() -> bool:
    """link_staged == decode_link(link_query) at mini scale — the
    idata/data split + seam symtab merge is the same map linkOf
    computes."""
    imps, slots = ("ExitProcess",), (("x", 8),)
    nf, _, _ = ec._graph_run(st.link_query(imps, slots))
    i0, d0, s0 = st.decode_link(nf)
    i1, d1, s1 = ec.link_staged(imps, slots, ec._graph_run)
    return i1 == i0 and d1 == d0 and s1 == s0


def gate_decode_evidence() -> bool:
    """_decode instrumentation counts the remaining Python semantic
    crossings — the manifest's evidence field; bytecells is already
    0 under the byte-egress runner (kernel decodes its own NF)."""
    base = dict(ec._DECODE_COUNT)
    ec._decode("frag", lambda x: x, "t")
    ec._decode("frag", lambda x: x, "t")
    d = ec._dec_delta(base)
    return d == {"frag": 2, "program": 0, "bytesyms": 0,
                 "bytecells": 0}


def gate_emit_ir() -> bool:
    """the kernel writes stage blobs itself: each root's reduced NF
    leaves as a [u32 len][PIR] frame — a valid packed-IR stream whose
    canonical digest equals re-packing the depacked term, and whose
    observable NF (fed back through the stdout kernel) is the same
    line the input term reduces to.  Order across roots is the input
    order; truncated/garbage streams refuse in digest_ir_blob."""
    import subprocess
    from reduce import I, KK, S, B, C, D, app
    exe_ir = ec.ir_exe_for(seed.Realization(
        reclaim="redirect", io=("stdin", "ir")))
    exe_txt = ec.ir_exe_for(seed.Realization(reclaim="redirect"))
    shared = app(S, app(KK, I))
    terms = [I, app(app(S, KK), KK), app(shared, shared),
             app(app(B, app(C, D)), app(S, I))]
    run = ec.make_blob_runner(exe_ir)
    if getattr(run, "kind", None) != "exe.ir":
        return False
    blobs, _, _ = run.batch(terms)
    if len(blobs) != len(terms):
        return False
    for b in blobs:
        # digest equivalence: kernel stream vs canonical re-pack of
        # the depacked term — same Merkle root by construction
        if st.digest_ir_blob(b) != st.pack_ir_keyed(
                st.unpack_ir(b)[0])[1]:
            return False
    # observational equivalence at kernel ground truth: each emitted
    # blob re-reduces (idempotent) to the input's own NF line
    p = subprocess.run([exe_txt], input=st.pack_ir(*terms),
                       capture_output=True, timeout=600)
    if p.returncode != 0:
        return False
    lines = [ln for ln in p.stdout.split(b"\n") if ln]
    for i, b in enumerate(blobs):
        q = subprocess.run([exe_txt], input=b, capture_output=True,
                           timeout=600)
        if [ln for ln in q.stdout.split(b"\n") if ln] != lines[i:i+1]:
            return False
    # refusal: truncated record stream and garbage headers raise,
    # never silently mint a digest
    for bad in (blobs[1][:-3], b"\x00" * 16, b""):
        try:
            st.digest_ir_blob(bad)
            return False
        except Exception:                            # noqa: BLE001
            pass
    return True


def gate_link_blob_seam() -> bool:
    """link* with ir+bytes egress: section NFs arrive as PIR blobs,
    section bytes are kernel projections (pair K), the merged symtab
    is a kernel APPEND over blob placeholders — zero decode_* at the
    seam.  Correctness is behavioral: the blob symtab must resolve
    identical to the Python dict join — rel hit, rip sym, and the
    miss path (0-end) included."""
    from reduce import KK, app
    imps, slots = ("ExitProcess",), (("x", 8),)
    store = ec.BlobStore()
    run_ir = ec.make_blob_runner(ec.ir_exe_for(seed.Realization(
        reclaim="redirect", io=("stdin", "ir"))), pinned=store.pins)
    run_bytes = ec.make_bytes_runner(ec.ir_exe_for(seed.Realization(
        reclaim="redirect", io=("stdin", "bytes"))), pinned=store.pins)
    dec0 = dict(ec._DECODE_COUNT)
    ib, db, symblob = ec.link_staged(imps, slots, ec._graph_run,
                                     store=store,
                                     run_ir=run_ir, run_bytes=run_bytes)
    if any(v for k, v in ec._dec_delta(dec0).items()):
        return False                    # the seam must not decode
    i0, d0, s0 = st.decode_link(ec._graph_run(
        st.link_query(imps, slots))[0])
    if ib != i0 or db != d0:
        return False
    # resolver probes: blob symtab vs dict symtab, byte-exact
    loc_t = st.symtab_term({})
    e4_t = st.bytelist_term((0x1000).to_bytes(4, "little"))
    sym_blob = store.blob_term(symblob)
    sym_dict = st.symtab_term(s0)
    for it in (("i", "call_rel32", ("l", "x")),
               ("i", "mov_r64_rip", "rax", ("p", "iat_ExitProcess")),
               ("i", "call_rel32", ("l", "nope"))):
        rb = st._appn(ec._resvmk(), sym_blob, loc_t, e4_t)
        rd = st._appn(ec._resvmk(), sym_dict, loc_t, e4_t)
        bb = run_bytes.batch(
            [app(st.encode_query(it, rb), KK)])[0][0]
        bd = run_bytes.batch(
            [app(st.encode_query(it, rd), KK)])[0][0]
        if bb != bd:
            return False
    return True
