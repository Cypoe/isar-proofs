"""nanopass gates — kernel/container: .plex bundle format,
MT equivalence, kernel-side ingest, layer composition."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

import emit_chain as ec                                        # noqa: E402
import routines_x86_64_win64 as rts                            # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import toolchain                                               # noqa: E402


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


def gate_plex_ingest(tmpdir: str) -> bool:
    """Phase-7b — the kernel depacks .plex v3 itself.

    dialect="plex.v3" inserts plex_read after ir_entry: validate the
    12B header + every 32B directory row (type, arity, length ==
    rows*arity*type — verified by division, this ISA has no mul),
    require exactly one KIND_PIR section, skip to its span, and hand
    a bounded-EOF stream to ir_sloop (plexleft clamps every read).

    Asserts: a probe bundle produces frames byte-identical to the
    same stream on a bare "pir" kernel (ST and MT records), and the
    full refusal matrix is enforced natively at rc=3 — bad magic,
    version, misaligned/short hsize, truncated dir, bad cell type,
    arity 0, length/row-count mismatch, unaligned or sub-hsize
    offset, missing/duplicate PIR section, declared span too short
    or beyond EOF, trailing junk inside the span."""
    import subprocess
    import struct
    import plex_bundle as pb
    Rp = seed.Realization(reclaim="redirect", io=("stdin", "bytes"),
                          dialect="plex.v3")
    Rb = seed.Realization(reclaim="redirect", io=("stdin", "bytes"))
    exp, exr = ec.ir_exe_for(Rp), ec.ir_exe_for(Rb)
    pir = st.pack_ir(st.bytelist_term(b"ab"),
                     st.bytelist_term(b""),
                     st.bytelist_term(b"cd"))

    def bundle(extra_secs=(), pirsec=True, payload=pir):
        secs = [pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0, b"s"),
                pb.Section(pb.KIND_REALIZATION, pb.U64, 4, 0, b"")]
        secs += extra_secs
        if pirsec:
            secs.append(pb.Section(pb.KIND_PIR, pb.U8, 1, 0,
                                   payload))
        for s in secs:
            s.rows = s.length
        return pb.pack_bundle(secs)

    data = bundle(
        extra_secs=(pb.Section(pb.KIND_BYTES, pb.U8, 1, 0,
                               b"\xde\xad\xbe\xef"),))
    ra = subprocess.run([exp], input=data, capture_output=True)
    rb = subprocess.run([exr], input=pir, capture_output=True)
    if (ra.returncode, ra.stdout) != (rb.returncode, rb.stdout):
        return False
    # MT parity — the walk happens once on the main thread
    exmt = seed._exe_for(seed.Realization(
        reclaim="redirect", io=("stdin", "bytes"),
        dialect="plex.v3", threads=2),
        toolchain.by_name("native.x86_64.pe.ir.mt"))
    rm = subprocess.run([exmt], input=data, capture_output=True)
    if (rm.returncode, rm.stdout) != (ra.returncode, ra.stdout):
        return False
    # emit.plex carries KIND_PIR last — the deployed shape
    path = ec.write_emit_bundle(
        os.path.join(tmpdir, "emit.plex"), seed.Realization())
    b = pb.read_bundle(open(path, "rb").read())
    if b.sections[-1].kind != pb.KIND_PIR:
        return False
    pirsec = b.sections[-1]
    if pirsec.offset + pirsec.length > len(b.data):
        return False
    # ---- refusal matrix, all rc=3 ----
    row = lambda i, f: 12 + i * 32 + f          # dir row i field off
    cases = []
    d = bytearray(data); d[0:4] = b"NOPE"; cases.append(bytes(d))
    d = bytearray(data); d[4] = 2; cases.append(bytes(d))
    d = bytearray(data); struct.pack_into("<H", d, 6, 9)
    cases.append(bytes(d))
    d = bytearray(data); struct.pack_into("<H", d, 6, 8)
    cases.append(bytes(d))
    cases.append(data[:20])                       # truncated dir
    d = bytearray(data); d[12] = 2; cases.append(bytes(d))
    d = bytearray(data); d[13] = 0; cases.append(bytes(d))
    d = bytearray(data); struct.pack_into("<Q", d, row(0, 24), 7)
    cases.append(bytes(d))
    i_pir = 3                                     # PIR is row 3 in data
    d = bytearray(data)
    off = struct.unpack_from("<Q", d, row(i_pir, 8))[0]
    struct.pack_into("<Q", d, row(i_pir, 8), off | 1)
    cases.append(bytes(d))
    d = bytearray(data)
    struct.pack_into("<Q", d, row(i_pir, 8), 16)
    cases.append(bytes(d))
    d = bytearray(data)
    struct.pack_into("<Q", d, row(i_pir, 16), len(pir) - 4)
    cases.append(bytes(d))
    d = bytearray(data)
    struct.pack_into("<Q", d, row(i_pir, 16), len(pir) + 100000)
    cases.append(bytes(d))
    cases.append(bundle(pirsec=False))            # missing PIR
    dup = bundle(extra_secs=(pb.Section(
        pb.KIND_PIR, pb.U8, 1, 0, pir),))
    cases.append(dup)                             # duplicate PIR
    cases.append(bundle(payload=pir + b"JUNKJUNK"))
    cases.append(data[:off + 2])                  # mid-payload cut
    for bad in cases:
        r = subprocess.run([exp], input=bad, capture_output=True)
        if r.returncode != 3:
            return False
    return True


def gate_layer_chain() -> bool:
    """Phase-8 — kernel composition is declared data (layers.py).

    A kernel image is an ordered sequence of legs, each gated by one
    realization axis: container <- dialect, driver <- threads, egress
    <- io, basis tail <- fuse_s, persist <- reclaim.  compose() walks
    the declared legs; a value with no row refuses naming its axis.

    Asserts: composed routine lists equal the frozen pre-refactor
    tuples for every record family (ST/MT x text/bytes/ir, plex.v3,
    fuse_s); data_slots parity incl. the MT corner cases (bytes
    subset, ir-egress empty); specs/*.json conformance — every
    realized container/egress leg value has a spec, every realized
    spec's impl names exist in _BUILDERS; refusals name axis+layer.
    """
    import dataclasses
    import layers
    R0 = seed.Realization()
    RR = lambda **kw: dataclasses.replace(R0, **kw)   # noqa: E731

    EXP_ST = ("ir_entry", "ir_read", "ir_depack", "ir_reduce",
              "stats", "exits", "grow_heap_ir", "mkleaf", "mkapp",
              "mkapp_p", "repr", "step", "st_norm", "st_konst",
              "st_dup", "st_swap", "st_comp", "step_congr",
              "freduce", "count_nodes", "emit_nf", "itoa",
              "build_ds")
    EXP_MT = ("ir_entry", "ir_read", "ir_spawn", "stats", "exits",
              "mt_worker", "ir_depack", "grow_heap_ir", "mkleaf",
              "mkapp", "mkapp_p", "repr", "step", "st_norm",
              "st_konst", "st_dup", "st_swap", "st_comp",
              "step_congr", "freduce", "count_nodes", "emit_nf",
              "itoa", "build_ds")
    EXP_TOK = ("entry", "parse", "reduce", "stats", "exits",
               "grow_heap", "mkleaf", "mkapp", "mkapp_p", "mkstk",
               "repr", "step", "st_norm", "st_konst", "st_dup",
               "st_swap", "st_comp", "step_congr", "freduce",
               "count_nodes", "emit_nf", "itoa", "build_ds")
    EB = ("emit_bytes", "peval", "selidx")
    for legs, R, exp in (
        (rts._LEGS_IR, RR(), EXP_ST),
        (rts._LEGS_IR, RR(io=("stdin", "bytes")), EXP_ST + EB),
        (rts._LEGS_IR, RR(io=("stdin", "ir")), EXP_ST + ("emit_ir",)),
        (rts._LEGS_IR, RR(threads=2), EXP_MT),
        (rts._LEGS_IR, RR(threads=2, io=("stdin", "bytes")),
         EXP_MT + EB),
        (rts._LEGS_IR, RR(threads=2, io=("stdin", "ir")),
         EXP_MT + ("emit_ir",)),
        (rts._LEGS_IR, RR(dialect="plex.v3"),
         ("ir_entry", "plex_read") + EXP_ST[1:]),
        (rts._LEGS_IR, RR(dialect="plex.v3", threads=2),
         ("ir_entry", "plex_read") + EXP_MT[1:]),
        (rts._LEGS_IR, RR(dialect="plex.emit",
                          io=("stdin", "bytes")),
         ("ir_entry", "pexec") + EXP_ST[2:] + EB),
        (rts._LEGS_IR, RR(fuse_s=True),
         EXP_ST[:17] + ("st_s",) + EXP_ST[17:-1]),
        (rts._LEGS_TOKEN, R0, EXP_TOK),
        (rts._LEGS_TOKEN, RR(fuse_s=True),
         EXP_TOK[:17] + ("st_s",) + EXP_TOK[17:-1]),
    ):
        if layers.compose(R, legs) != exp:
            return False

    # slot parity — .data layout is image contract
    base = rts.DATA_SLOTS_IR
    exp = base + rts.DATA_SLOTS_PS + rts.DATA_SLOTS_PX + (
        ("slabtop", 8), ("mtslab", 8),
        ("mtctxs", 3 * rts.MT_CTX_BYTES), ("mthandles", 16)) + (
        ("eb_i", 8), ("eb_k", 8), ("eb_ki", 8), ("eb_marks", 8),
        ("eb_dec", 8))
    got = rts.data_slots_ir(RR(reclaim="redirect", dialect="plex.v3",
                               threads=2, io=("stdin", "bytes")))
    if got != exp:
        return False
    # MT + ir egress: all ei_* state is ctx fields — no .data rows
    got = rts.data_slots_ir(RR(threads=2, io=("stdin", "ir")))
    if any(n.startswith("ei_") for n, _ in got):
        return False
    if rts.data_slots_ir(RR(io=("stdin", "ir")))[-7:] != \
            rts.DATA_SLOTS_EI:
        return False

    # specs/*.json — the contract side
    specs = layers.load_specs()
    if set(s["name"] for s in specs.values()
           if s["layer"] == "container") != \
            {"pir", "plex.v3", "plex.emit"}:
        return False
    if set(s["name"] for s in specs.values()
           if s["layer"] == "egress") != {"stdout", "bytes", "ir"}:
        return False
    for s in specs.values():
        if s["status"] == "realized":
            for fam, names in s["impl"].items():
                if fam.startswith("x86_64.win64") and not all(
                        n in rts._BUILDERS for n in names):
                    return False
    # every realized dialect axis value has a leg row + a spec
    if layers.leg_values(rts._LEGS_IR, "dialect") != \
            {"pir", "plex.v3", "plex.emit"}:
        return False

    # refusals name axis + layer, never silently default
    for R, legs, frag in (
        (RR(dialect="bogus"), rts._LEGS_IR, "dialect"),
        (RR(dialect="plex.v3"), rts._LEGS_TOKEN, "dialect"),
        (RR(threads=2), rts._LEGS_TOKEN, "threads"),
        (RR(io=("stdin", "bytes")), rts._LEGS_TOKEN, "io"),
        (RR(io=("memory", "stdout")), rts._LEGS_IR, "io"),
        (RR(reclaim="refcount"), rts._LEGS_IR, "reclaim"),
    ):
        try:
            layers.compose(R, legs)
            return False
        except Exception as e:                      # noqa: BLE001
            if frag not in str(e):
                return False

    # plex.emit's cross-axis contract refuses in routine_names_ir
    for R in (RR(dialect="plex.emit"),
              RR(dialect="plex.emit", io=("stdin", "bytes"),
                 threads=2)):
        try:
            rts.routine_names_ir(R)
            return False
        except Exception as e:                      # noqa: BLE001
            if "plex.emit" not in str(e):
                return False

    # the emitted programs still build through the composed lists
    return len(rts.program(R0)) > 0 \
        and len(rts.program_ir(R0)) > 0 \
        and len(rts.program_ir_mt(RR(threads=2))) > 0
