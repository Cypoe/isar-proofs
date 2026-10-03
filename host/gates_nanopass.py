"""nanopass gate — Phase 1 query-engine program stage +
Phase 2 record-driven programOf.

Gates (cheap, no full emit — the byte-equality run is separate):

  1. FRAG-CONCAT: per-routine `routine_query` frags decode and
     concatenate to exactly `decode_program(program_query)` — the
     split is a pure projection of the monolithic stage.
  2. INVALIDATION: patching one routine's builder changes exactly
     its `program.<name>` checkpoint key plus the downstream
     program.items/text.bin/image.bin — all other frag keys and
     link.sections are untouched.
  3. PASS-INVARIANT: an unknown pass name refuses (ValueError), and
     a registered pass returning a non-frag shape fails decode
     rather than emitting a malformed item list.
  4. ID-CHAIN: passes=('id','id') leaves a frag unchanged — the
     chain spine itself adds no semantics.
  5. RECORD==MONOLITH: `program_query_rt(ROUTINES)` — routine names
     arriving as term data through the nibble trie — decodes to
     exactly `decode_program(program_query)`.
  6. RECORD IR+BYTES: `routine_names_ir(Rb)` under the redirect+bytes
     pin decodes to exactly `program_ir(Rb)` — the production kernel
     is stageable.
  7. TRIE-MISS: an unknown routine name in the record produces the
     malformed frag — decode refuses it.
  8. SENTINEL-LEAK: `_val_expr` refuses unmapped sentinel arithmetic
     (nb-2 style) instead of baking a literal.
  9. BOUNDED-BATCH: `_batch_bounded` halves on kernel OOM (rc=4),
     preserves query order, propagates other failures unsplit.
 10. PIN-SPLICE: a pinned routine constant splices verbatim into the
     packed query — keyed digests are position-independent, so the
     spliced stream's Merkle root equals the unpinned walk.
 11. BLOB-STORE: `pin_named` miss writes content-addressed bytes; a
     fresh store's hit produces the same full digest and a
     byte-identical splice.
 12. SPLIT-LINK: `link_staged` (idataOf + dataOf as separate queries,
     symtab merge at the seam) decodes to exactly `decode_link` of
     the monolithic `link_query` — checked at mini scale.
 13. MANIFEST-REPLAY: manifest.json names stage artifacts/runners/
     deps; `replay_emit` resolves the image by content address and
     refuses on a missing artifact.
 14. DECODE-EVIDENCE: `_decode` counters record per-emit Python
     semantic crossings; bytecells is already 0 under the bytes
     runner — frag/bytesyms/program remain until stage blobs flow
     through the ir-egress path end to end.
 15. EMIT-IR: the io=("stdin","ir") kernel emits each root's NF as a
     framed PIR blob — depackable, digest-equal to its own canonical
     re-pack (digest_ir_blob), and observationally identical when fed
     back through the stdout kernel.  Malformed blobs refuse.
 16. LINK BLOB SEAM: link_staged under ir+bytes egress produces
     section bytes via kernel projection and the merged symtab as a
     kernel APPEND over blob placeholders — zero decode_* at the
     seam, and the blob symtab resolves byte-identical to the dict
     join (hit, rip-symbol, and 0-end miss).
 17. MT EQUIV: threads in {2,4} under native.x86_64.pe.ir.mt —
     per-worker slab claims + private depack — produce byte-identical
     stdout and rc to the serial kernel across all three egress
     modes, stream counts, and empty input; steps identical except
     bytes-probe (FWD-reuse loss), alloc always differs by design.
     Refusals stay record-scoped both ways.
 18. PLEX V3 BUNDLE: _write_manifest emits image.plex beside
     manifest.json — the stage DAG as STAGES/DEPS/QUERIES row tables,
     REALIZATION/CAPS/EVIDENCE KV rows, the image as BYTES.  Round-
     trip reproduces the manifest DAG; caps ⊆ record; malformed
     headers/spans and missing required kinds refuse.

The per-routine stage is exercised byte-exact by
`emit_image(decompose_asm=True, workdir=...)` — see the
`staged==direct: True 3584B` run recorded in decision 050 and the
IR redirect+bytes emit (6656B, staged==oracle) in decision 051.
"""

import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import emit_chain as ec                                        # noqa: E402
import routines_x86_64_win64 as rts                            # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import target_pe64                                            # noqa: E402
import toolchain                                               # noqa: E402
from graph_runtime import reduce_tree_lo                       # noqa: E402


def gate_frag_concat(R) -> bool:
    mono = st.decode_program(reduce_tree_lo(st.program_query(R),
                                            500_000)[0])
    all_it = []
    for name in rts.ROUTINES:
        nf, _, _ = reduce_tree_lo(st.routine_query(name, R),
                                  500_000)
        all_it.extend(st.decode_frag(nf))
    return all_it == mono


def gate_invalidation(R) -> bool:
    tb = target_pe64.text_rva(rts.IMPORTS, rts.DATA_SLOTS)
    k1, _ = ec._ck_keys(R, rts.IMPORTS, rts.DATA_SLOTS, tb)
    orig = rts._BUILDERS["itoa"]
    try:
        # swap itoa's builder for a different function object —
        # same effect as editing its source under _src()
        rts._BUILDERS["itoa"] = rts._BUILDERS["repr"]
        k2, _ = ec._ck_keys(R, rts.IMPORTS, rts.DATA_SLOTS, tb)
    finally:
        rts._BUILDERS["itoa"] = orig
    frag_same = all(k1[f"program.{n}"] == k2[f"program.{n}"]
                    for n in rts.ROUTINES if n != "itoa")
    return (k1["program.itoa"] != k2["program.itoa"]
            and frag_same
            and k1["program.items"] != k2["program.items"]
            and k1["link.sections"] == k2["link.sections"]
            and k1["text.bin"] != k2["text.bin"]
            and k1["image.bin"] != k2["image.bin"])


def gate_pass_refusal(R) -> bool:
    try:
        st.routine_query("mkapp_p", R, passes=("bogus",))
        return False
    except ValueError:
        pass
    # a pass that returns a malformed item must hit the frag
    # invariant — "bad item tag" at decode, not a smuggled shape
    # downstream.  `bad = λf. [ ["bogus"] ]`: one item whose tag is
    # neither "label" nor "i".
    from reduce import KK, app
    bad_item = app(app(st._CONS,
                       app(app(st._CONS, st.str_term("bogus")), KK)),
                   KK)
    st._PASS_BUILDERS["bad"] = lambda: app(KK, bad_item)
    try:
        nf, _, _ = reduce_tree_lo(
            st.routine_query("mkapp_p", R, passes=("bad",)),
            200_000)
        st.decode_frag(nf)
        return False
    except ValueError as e:
        return "bad item tag" in str(e)
    finally:
        del st._PASS_BUILDERS["bad"]
        st._PASS_TERMS.pop("bad", None)


def gate_id_chain(R) -> bool:
    a = st.decode_frag(reduce_tree_lo(
        st.routine_query("mkapp_p", R), 200_000)[0])
    b = st.decode_frag(reduce_tree_lo(
        st.routine_query("mkapp_p", R, passes=("id", "id")),
        200_000)[0])
    return a == b


_PROG_AXES = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
             "node_bytes", "stack_reserve", "peephole"}


def _fixed_of(R) -> dict:
    """emit_image's generation-pin rule: every non-λ Realization
    field pins at generation time."""
    return {k: getattr(R, k) for k in vars(seed.Realization())
            if k not in _PROG_AXES}


def gate_record_eq_monolith(R) -> bool:
    """program_rt folded over the ROUTINES record decodes to exactly
    the monolithic programOf NF — the record is pure projection."""
    rt = st.decode_program(reduce_tree_lo(
        st.program_query_rt(rts.ROUTINES, R), 1_000_000)[0])
    mono = st.decode_program(reduce_tree_lo(st.program_query(R),
                                            500_000)[0])
    return rt == mono


def gate_record_ir_bytes() -> bool:
    """the production kernel staged: ROUTINES_IR_BYTES under the
    redirect+bytes pin decodes to exactly program_ir(R) — the staged
    chain can now emit the byte-egress kernel itself."""
    R = seed.Realization(reclaim="redirect", io=("stdin", "bytes"))
    items = st.decode_program(reduce_tree_lo(
        st.program_query_rt(rts.routine_names_ir(R), R,
                            fixed=_fixed_of(R)), 2_000_000)[0])
    return items == list(rts.program_ir(R))


def gate_record_refusal(R) -> bool:
    """a name the trie doesn't know must produce the malformed frag —
    decode refuses it rather than skipping a routine."""
    try:
        nf, _, _ = reduce_tree_lo(
            st.program_query_rt(("mkapp_p", "no_such_routine"), R),
            500_000)
        st.decode_program(nf)
        return False
    except ValueError as e:
        return "bad item tag" in str(e)


def gate_sentinel_leak() -> bool:
    """a builder doing Python arithmetic on a sentinel (nb-2 style)
    must refuse at _val_expr, not bake a literal."""
    try:
        st._val_expr(-0x3335)          # nb - 2 — unmapped derivation
        return False
    except ValueError as e:
        return "sentinel" in str(e)
    # derived-but-declared ones pass
    # (checked implicitly by the IR record gate)


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


def gate_manifest_replay(tmpdir: str) -> bool:
    """manifest.json names every stage's keyed artifact, its resolved
    runner, dep edges, and query blob refs; replay_emit resolves the
    image by content address alone — a missing artifact refuses
    (emit, don't replay)."""
    R = seed.Realization()
    keys = {"program.a": "h.k1", "program.b": "h.k2",
            "program.items": "h.k3", "link.sections": "h.k4",
            "text.bin": "h.k5", "image.bin": "h.k6"}
    for n, k in keys.items():
        with open(os.path.join(tmpdir, f"{n}.{k}"), "wb") as f:
            f.write(b"X")
    img = b"\x4d\x5agate"
    with open(os.path.join(tmpdir, "image.bin.h.k6"), "wb") as f:
        f.write(img)
    ec._write_manifest(tmpdir, R, "gate", ("a", "b"), keys, {},
                       {}, ec._graph_run, "pack")
    out, man = ec.replay_emit(tmpdir)
    if out != img:
        return False
    by_name = {s["name"]: s for s in man["stages"]}
    if by_name["image.bin"]["deps"] != ["text.bin", "link.sections"]:
        return False
    if by_name["program.items"]["deps"] != ["program.a", "program.b"]:
        return False
    if not by_name["image.bin"]["runner"]:
        return False
    os.remove(os.path.join(tmpdir, "text.bin.h.k5"))
    try:
        ec.replay_emit(tmpdir)
        return False
    except Exception as e:
        return "not materialized" in str(e)


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
    import struct
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
    import subprocess                                 # noqa: F401
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


def gate_plex_bundle(tmpdir: str) -> bool:
    """Phase-6 .plex v3 archive: _write_manifest emits image.plex
    beside manifest.json — directory + fixed-width row tables
    (STAGES/DEPS/QUERIES), REALIZATION + CAPS + EVIDENCE KV rows, the
    image as BYTES payload.  sections_manifest reconstructs the same
    DAG replay_emit consumes; bundle caps are checked ⊆ the routines
    record's declared caps; every malformed field refuses."""
    import plex_bundle as pb
    import toolchain
    R = seed.Realization()
    keys = {"program.a": "h.k1", "program.items": "h.k2",
            "link.sections": "h.k3", "text.bin": "h.k4",
            "image.bin": "h.k5"}
    img = b"\x4d\x5abundle"
    ec._write_manifest(tmpdir, R, "gate", ("a",), keys, {},
                       {}, ec._graph_run, "pack",
                       img=img, rt=rts.X86_64_WIN64_IR)
    path = os.path.join(tmpdir, "image.plex")
    if not os.path.exists(path):
        return False
    b = pb.read_bundle(open(path, "rb").read())
    man = pb.sections_manifest(b)
    if man["format"] != "plex.stage-manifest/1":
        return False
    by_name = {s["name"]: s for s in man["stages"]}
    if by_name["image.bin"]["deps"] != ["text.bin", "link.sections"]:
        return False
    if by_name["program.items"]["deps"] != ["program.a"]:
        return False
    if b.bytes_pool() != img:
        return False
    real = b.kv_rows(pb.KIND_REALIZATION)
    if real.get("routines") != "x86_64.win64.ir" or \
            real.get("order") != "lo":
        return False
    # caps: bundle declares the ir record's caps, verified ⊆ record
    caps = dict(toolchain.components()["routines"]
                ["x86_64.win64.ir"].data).get("caps")
    if pb.caps_dict(b.caps_rows()) != caps:
        return False
    if pb.check_bundle_caps(b, caps) != []:
        return False
    # a bundle may claim less, never more than the record
    widened = dict(caps["ports"], payload="W")
    forged = pb.pack_bundle(pb.manifest_sections(
        man, caps={"ports": widened, "os": caps["os"]}))
    if not pb.check_bundle_caps(pb.read_bundle(forged), caps):
        return False
    # refusals: bad magic, truncated dir, out-of-range span,
    # missing required section
    data = open(path, "rb").read()
    for bad in (b"NOPE" + data[4:], data[:20], data[:-2]):
        try:
            pb.read_bundle(bad)
            return False
        except pb.BundleError:
            pass
    try:
        b.require(pb.KIND_CLAIM)
        return False
    except pb.BundleError:
        pass
    return True


def gate_emit_frames() -> bool:
    """Phase-7a — the emit program as data, evaluated by the emitted
    host.  emit_frames packs the emit chain as two PIR streams:
    stream A = section bodies [link·KK·KK, link·KK·KI, asm·KK]
    (persist zone pays link once across roots), stream B = pack's
    derived chunks (ALIGN/B4ADD/U64/ZEROFILL/PADLIST numeral terms —
    the pack_staged recipe as roots).  Python constructs terms and
    splices frames; every β-reduction runs on the emitted kernel.
    The result must be byte-identical to _mini_oracle — the
    independent python_link/python_assemble/python_pack composition
    (cross-realization observation, not self-agreement).  Refusals:
    truncated stream -> rc -> NotRealized."""
    import spec_term as st
    import target_pe64
    imps, slots = ("ExitProcess",), (("x", 8),)
    base = target_pe64.text_rva(imps, slots)
    img, ev = ec.emit_frames(
        seed.Realization(), imports=imps, slots=slots,
        text_base=base, prog=st.fraglist_term(st.ASM_LINK))
    if img != ec._mini_oracle():
        return False
    for k in ("stream_a", "stream_b"):
        if "steps=" not in ev[k]:
            return False
    # refusal: a non-byte-list root on the bytes kernel exits rc=5 —
    # _run_stream must surface it as NotRealized, not an image
    try:
        ec._run_stream(ec.ir_exe_for(seed.Realization(
            reclaim="redirect", io=("stdin", "bytes"))),
            [st.church(3)])
        return False
    except toolchain.NotRealized:
        pass
    return True


def gate_mt_equiv() -> bool:
    """threads=N == N workers == serial: the MT record's workers
    depack their assigned root range into private slab claims and
    flush per-thread frames in root order — stdout/rc must be
    byte-identical to the serial kernel for every egress mode
    (text, bytes, ir), stream count, and threads in {2,4}.  Stats
    caveat (asserted for stdout/ir, not bytes): irsteps/nalloc can
    diverge honestly — private depack forfeits cross-root FWD reuse
    through shared input cells and duplicates the depack per worker.
    Refusals: program_ir refuses threads>1, program_ir_mt refuses
    threads=1 — the capability stays record-scoped."""
    import subprocess
    import toolchain
    from reduce import I, KK, S, app
    R1 = seed.Realization(reclaim="redirect")
    try:
        rts.program_ir(seed.Realization(threads=2))
        return False
    except Exception:                             # noqa: BLE001
        pass
    try:
        rts.program_ir_mt(seed.Realization(threads=1))
        return False
    except Exception:                             # noqa: BLE001
        pass
    terms = (I, app(app(S, KK), KK),
             app(app(S, app(KK, I)), app(S, app(KK, I))), I)
    blobs = [st.pack_ir(*terms),
             st.pack_ir(*terms) + st.pack_ir(app(app(S, app(S, KK)), KK)),
             b""]
    for io_out in ("stdout", "bytes", "ir"):
        Rm = seed.Realization(reclaim="redirect",
                              io=("stdin", io_out))
        if io_out == "bytes":
            blobs_m = [st.pack_ir(st.bytelist_term(b"ab"),
                                  st.bytelist_term(b"")),
                       st.pack_ir(st.bytelist_term(b"cd")) +
                       st.pack_ir(st.bytelist_term(b"e")),
                       b""]
        else:
            blobs_m = blobs
        exe_st = seed._exe_for(Rm, toolchain.by_name(
            "native.x86_64.pe.ir"))
        for blob in blobs_m:
            r0 = subprocess.run([exe_st], input=blob,
                                capture_output=True, timeout=120)
            for t in (2, 4):
                exe_mt = seed._exe_for(seed.Realization(
                    reclaim="redirect", io=("stdin", io_out),
                    threads=t), toolchain.by_name(
                    "native.x86_64.pe.ir.mt"))
                r1 = subprocess.run([exe_mt], input=blob,
                                    capture_output=True, timeout=120)
                if (r1.returncode, r1.stdout) != (r0.returncode,
                                                r0.stdout):
                    return False
                # alloc always diverges (per-worker depack); steps
                # must match except under the bytes probe, where
                # cross-root FWD reuse on shared list tails is lost
                if io_out != "bytes" and r0.returncode == 0:
                    s0 = r0.stderr.split(b"steps=")[-1].split()[0]
                    s1 = r1.stderr.split(b"steps=")[-1].split()[0]
                    if s1 != s0:
                        return False
    return True


if __name__ == "__main__":
    R = seed.Realization()
    gates = [
        ("frag-concat == monolithic", lambda: gate_frag_concat(R)),
        ("per-routine invalidation", lambda: gate_invalidation(R)),
        ("pass refusal/invariant", lambda: gate_pass_refusal(R)),
        ("id chain transparent", lambda: gate_id_chain(R)),
        ("record == monolith", lambda: gate_record_eq_monolith(R)),
        ("record IR+bytes == program_ir", gate_record_ir_bytes),
        ("record trie-miss refusal", lambda: gate_record_refusal(R)),
        ("sentinel-arithmetic refusal", gate_sentinel_leak),
        ("bounded batches halve on OOM", gate_batch_bounded),
        ("pin-splice digest equality", lambda: gate_pin_splice(R)),
        ("blob-store disk round-trip",
         lambda: gate_blob_store(R, tempfile.mkdtemp(
             prefix="nanopass_blobs_"))),
        ("split-link == linkOf", gate_split_link),
        ("manifest replay == emit", lambda: gate_manifest_replay(
            tempfile.mkdtemp(prefix="nanopass_man_"))),
        ("decode-crossing evidence", gate_decode_evidence),
        ("emit_ir blob round-trip", gate_emit_ir),
        ("link blob seam == dict join", gate_link_blob_seam),
        ("MT threads==serial observable", gate_mt_equiv),
        ("plex v3 bundle round-trip", lambda: gate_plex_bundle(
            tempfile.mkdtemp(prefix="nanopass_plex_"))),
        ("emit frames on emitted host", gate_emit_frames),
    ]
    fail = 0
    for name, g in gates:
        try:
            ok = g()
        except Exception as e:                        # noqa: BLE001
            print(f"  {name}: ERROR {e}")
            fail += 1
            continue
        print(f"  {name}: {'PASS' if ok else 'FAIL'}")
        fail += not ok
    print(f"nanopass gate: {len(gates)-fail}/{len(gates)}")
    sys.exit(1 if fail else 0)
