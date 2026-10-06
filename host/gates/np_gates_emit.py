"""nanopass gates — emit chain: manifest replay, staged frames,
self-hosting fixpoint, serialized emit.plex DAG."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

import emit_chain as ec                                        # noqa: E402
import fixtures                                                # noqa: E402
import routines_x86_64_win64 as rts                            # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import toolchain                                               # noqa: E402


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


def gate_selfhost_fixpoint(tmpdir: str) -> bool:
    """Phase-7 — the self-hosting fixpoint on the emitted host.

    emit_frames(staged=True) drives the WHOLE emit as packed-IR
    stream roots on emitted kernels: program frag queries (term
    egress) -> link blob seam (ir egress, symtab never decoded) ->
    per-item encodeOf roots (bytes egress) -> pack chunk roots.
    Python does term construction, loc bookkeeping, and the byte
    splice only.

    fixpoint: emit_frames on the ir-bytes record must reproduce the
    on-disk kernel byte-identically (H1 == H0; sha bacc6505…).
    behavioral: H1 must evaluate a probe stream identically to H0 —
    frames AND the rc=5 refusal on a non-byte-list root.
    pickup: a changed Realization (stack_reserve) must produce a
    DIFFERENT image that still equals seed.emit's oracle for the
    changed R and still works as a kernel — the change is picked
    up, not served stale.

    Evidence category: construction-seam byte comparison (fixpoint,
    oracle) + cross-realization observation (probe parity)."""
    import subprocess
    # .lo record — the staged schedule against the committed golden
    # image (workers=4 exercises the strided chunk pool — scheduling
    # only, the mt-equiv gate is the parity witness)
    img_lo, ev_lo = ec.emit_frames(seed.Realization(), staged=True,
                                   workers=4)
    if img_lo != fixtures.golden("image.default"):
        return False
    # fixpoint — the bytes kernel reproduces its own image
    Rb = seed.Realization(reclaim="redirect", io=("stdin", "bytes"))
    exe0 = ec.ir_exe_for(Rb)
    h0 = open(exe0, "rb").read()
    img, ev = ec.emit_frames(Rb, rt=rts.X86_64_WIN64_IR,
                             staged=True, timeout=3600, workers=4)
    if img != h0:
        return False
    # behavioral — H1 works as a kernel, identical frames + refusal
    h1 = os.path.join(tmpdir, "H1.exe")
    open(h1, "wb").write(img)
    K = lambda n: ec.bracket(ec.parse(getattr(st, n)))
    b4 = lambda v: st.bytelist_term(v.to_bytes(4, "little"))
    roots = [st._appn(K("_U64"), b4(7)),
             st._appn(K("_ZEROFILL"), st.church(5)),
             st.church(3)]
    data = st.pack_ir(*roots)
    outs = []
    for exe in (exe0, h1):
        p = subprocess.run([exe], input=data, capture_output=True)
        if p.returncode != 5:
            return False
        outs.append(p.stdout)
    if outs[0] != outs[1]:
        return False
    # pickup — changed Realization -> different valid kernel
    import dataclasses
    Rb2 = dataclasses.replace(Rb, stack_reserve=32 << 20)
    img2, _ev2 = ec.emit_frames(Rb2, rt=rts.X86_64_WIN64_IR,
                                staged=True, timeout=3600, workers=4)
    if img2 == h0:
        return False
    if img2 != seed.emit(
            Rb2, tc=toolchain.by_name("native.x86_64.pe.ir")):
        return False
    h1p = os.path.join(tmpdir, "H1p.exe")
    open(h1p, "wb").write(img2)
    p = subprocess.run([h1p], input=data, capture_output=True)
    return p.returncode == 5 and p.stdout == outs[0]


def gate_pexec_schedule(tmpdir: str) -> bool:
    """Phase-8c — the schedule executor IS the kernel
    (dialect='plex.emit').

    pexec consumes the emit.plex bundle in-process: v3 directory
    validation, output-stage dep closure off DEPS, declared-order
    depack + freduce of each stage's BYTES-pool span (emit.term
    rides KIND_PIR), per-stage frame store, MAP-declared positional
    splices, one [u32 len][bytes] egress frame.  No Python between
    the archive and the image — spawn + file write only.

    Golden-fixture discipline: comparison is against the committed
    snapshot (fixtures.golden), never a live oracle — host emit
    machinery is the refresh path only.  A freshly emitted executor
    must still equal the committed pexec.exe (emit-pipeline drift
    check).  Refusals — a truncated bundle, a MAP src_frame out of
    range, and a stage stream span that fails the PIR length
    relation all exit rc=3."""
    import struct
    import subprocess
    import plex_bundle as pb
    # emit-side drift: the current source must still emit the
    # committed executor byte-identically
    Rex = seed.Realization(dialect="plex.emit", io=("stdin", "bytes"),
                           reclaim="redirect", gc="sweep")
    exe = ec.ir_exe_for(Rex)
    if open(exe, "rb").read() != fixtures.golden("pexec.exe"):
        return False
    # host-independent execution: committed executor + committed
    # bundle -> committed image; nothing emitted at gate time
    data = fixtures.golden("bundle.default")
    p = subprocess.run([exe], input=data, capture_output=True,
                       timeout=3600)
    if p.returncode != 0 or len(p.stdout) < 4:
        return False
    n = struct.unpack_from("<I", p.stdout, 0)[0]
    if n != len(p.stdout) - 4:
        return False
    if p.stdout[4:] != fixtures.golden("image.default"):
        return False
    # refusal: truncated archive
    if subprocess.run([exe], input=data[:len(data) // 2],
                      capture_output=True).returncode != 3:
        return False
    # refusal: MAP row src_frame out of range
    b = pb.read_bundle(data)
    msec = b.section(pb.KIND_MAP)
    bad = bytearray(data)
    struct.pack_into("<I", bad, msec.offset + 12, 7)
    if subprocess.run([exe], input=bytes(bad),
                      capture_output=True).returncode != 3:
        return False
    # refusal: a stage stream that fails the PIR span relation —
    # bump n_nodes inside emit.link's stream header in the pool
    bsec = b.section(pb.KIND_BYTES)
    names = [s[0] for s in b.stage_rows()]
    li = names.index("emit.link")
    for s_i, _dig, tok in b.query_rows():
        if s_i == li:
            off, _ln = (int(x) for x in tok.split(":"))
            bad = bytearray(data)
            nn_addr = bsec.offset + off + 8   # PIR hdr: n_nodes
            nn = struct.unpack_from("<I", bad, nn_addr)[0]
            struct.pack_into("<I", bad, nn_addr, nn + 1)
            if subprocess.run([exe], input=bytes(bad),
                              capture_output=True).returncode != 3:
                return False
            break
    else:
        return False
    return True


def gate_host_independence(tmpdir: str) -> bool:
    """Phase-8d — the host-independence checklist.  The emitted
    artifacts carry the schedule without host emit machinery in the
    execution path; the phi2/rel.rs status table is the task list —
    closed rows are verified here, open rows must stay NAMED (a
    missing refusal or a silently-changed corpus is failure, not
    progress).

    verified:
      executor   the committed pexec.exe + committed
                 bundle.default.plex -> golden image.default, with a
                 steps= observation — running-program evidence, not
                 byte comparison only
      gc axis    'gc' registered on the toolchain; sweep realized on
                 the win64 IR kernel (native cogen's realization)
      digests    streams.digest=sha256 declared inside the bundle's
                 own REALIZATION rows (decision 064 as data)
    named open:
      gc off-win64      the C emitter refuses gc!=none BY NAME —
                        the collector is win64-realized only
      corpus batch      primitives are a deliberate decision —
                        corpus rel count pinned at 30; adding
                        byte-add must update this gate
      program equiv     observational equivalence of generated
                        programs beyond image+step parity — the
                        cross_verify harness is the declared witness
    """
    import subprocess
    import plex_bundle as pb
    # --- realized: schedule execution needs zero host emission ----
    exe = fixtures.golden_path("pexec.exe")
    data = fixtures.golden("bundle.default")
    p = subprocess.run([exe], input=data, capture_output=True,
                       timeout=3600)
    if p.returncode != 0:
        return False
    if p.stdout[4:] != fixtures.golden("image.default"):
        return False
    if b"steps=" not in p.stderr:
        return False
    # --- the gc'd realization is on the toolchain contract --------
    ax = toolchain.strategy_axes().get("gc")
    if not ax or ax.get("sweep") != "realized":
        return False
    import routines_c
    try:
        routines_c.program(seed.Realization(gc="sweep"))
        return False
    except toolchain.NotRealized as e:
        if "gc" not in str(e):
            return False
    # --- the digest decision rides inside the bundle --------------
    real = pb.read_bundle(data).kv_rows(pb.KIND_REALIZATION)
    if real.get("streams.digest") != "sha256":
        return False
    # --- open items stay named ------------------------------------
    # corpus batch primitives: adding byte-add changes the corpus —
    # pinned rel count forces that change through this gate
    import dialect
    cor = os.path.join(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), "corpus", "stdlib.phi")
    if len(dialect.PROJECTIONS["phi.rel"](cor)["rels"]) != 30:
        return False
    # program equivalence: the running-programs harness is declared —
    # PE<->C host parity exists; systematic equivalence of emitted
    # artifact chains is the named open item
    if not os.path.exists(os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "cross_verify.py")):
        return False
    return True


def gate_emit_bundle(tmpdir: str) -> bool:
    """Phase-7 — emit.plex as the executable emit archive.

    write_emit_bundle serializes the schedule: the canonical
    monolithic emit.term PIR payload plus the stage-level streams
    (program frags, link byte projections, merged symtab) as
    digest-referenced spans in the BYTES pool, with STAGES rows,
    DEPS edges, REALIZATION layout fields, and record caps.

    run_emit_bundle must reconstruct the image byte-identically
    to emit_native, driving every reduction off the bundle's own
    streams — dep-order execution plus MAP-declared concat.  Refusals:
    a corrupted stream payload (digest mismatch) and a bundle
    whose caps exceed the routines record."""
    import plex_bundle as pb
    path = ec.write_emit_bundle(
        os.path.join(tmpdir, "emit.plex"), seed.Realization())
    b = pb.read_bundle(open(path, "rb").read())
    names = [s[0] for s in b.stage_rows()]
    if names != ["emit.term", "emit.program", "emit.link",
                 "emit.symtab", "emit.assemble", "emit.pack"]:
        return False
    edges = {(names[a], names[c]) for a, c in b.dep_edges()}
    if not {("emit.assemble", "emit.program"),
            ("emit.assemble", "emit.link"),
            ("emit.assemble", "emit.symtab"),
            ("emit.pack", "emit.link"),
            ("emit.pack", "emit.assemble")} <= edges:
        return False
    real = b.kv_rows(pb.KIND_REALIZATION)
    if real.get("dialect") != "plex.emit/2":
        return False
    streams = ec.emit_bundle_streams(b)
    if set(streams) != {"emit.term", "emit.program", "emit.link",
                        "emit.symtab", "emit.assemble", "emit.pack"}:
        return False
    img, ev = ec.run_emit_bundle(path, timeout=3600)
    if img != fixtures.golden("image.default"):
        return False
    # corruption: flip a byte inside a stream span -> digest refuse
    data = bytearray(open(path, "rb").read())
    bsec = b.section(pb.KIND_BYTES)
    for s_i, _dig, tok in b.query_rows():
        if names[s_i] == "emit.link":
            off, ln = (int(x) for x in tok.split(":"))
            data[bsec.offset + off] ^= 0xFF
            bad = os.path.join(tmpdir, "emit.bad.plex")
            open(bad, "wb").write(bytes(data))
            try:
                ec.run_emit_bundle(bad)
                return False
            except toolchain.NotRealized:
                break
    else:
        return False
    # widened caps: a bundle may claim less, never more
    rn = real.get("routines")
    caps = dict(toolchain.components()["routines"][rn].data
                ).get("caps")
    widened = dict(caps["ports"], forge_extra="RW")
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00", {"ports": widened, "os": caps["os"]},
        dict(real), {}))
    fpath = os.path.join(tmpdir, "emit.wide.plex")
    open(fpath, "wb").write(forged)
    try:
        ec.run_emit_bundle(fpath)
        return False
    except toolchain.NotRealized:
        pass
    return True


def gate_emit_schedule(tmpdir: str) -> bool:
    """Phase-8b — the staged DAG is fully serialized.

    emit.plex carries every stage's stream: emit.assemble is one
    `encodeOf` root per prep position (frames concat to .text —
    resv/loc/end4 baked seed-side from the Python oracles), and
    emit.pack is _pack_recipe serialized (literals as passthrough
    queries, computed fields as roots, MAP rows declaring the
    section interleave).  run_emit_bundle is a pure executor:
    dep closure -> topo order -> declared runner -> MAP-guided
    concat; slice_ir bounds each exe call's arena (halve on rc=4).

    Asserts: all six stage rows are pir-stream; the MAP section
    declares pack's three splices; replay byte-identical to
    emit_native; refusals — MAP src frame out of range, a
    dep-closure stage carrying no stream, and program/assemble
    streams out of correspondence (the audit)."""
    import struct
    import plex_bundle as pb
    path = ec.write_emit_bundle(
        os.path.join(tmpdir, "emit.plex"), seed.Realization())
    b = pb.read_bundle(open(path, "rb").read())
    if any(s[1] != "pir-stream" for s in b.stage_rows()):
        return False
    names = [s[0] for s in b.stage_rows()]
    sidx = {n: i for i, n in enumerate(names)}
    if b.map_rows() != [(sidx["emit.pack"], 47, sidx["emit.link"], 0),
                        (sidx["emit.pack"], 48, sidx["emit.link"], 1),
                        (sidx["emit.pack"], 49, sidx["emit.assemble"],
                         pb.MAP_ALL)]:
        return False
    if b.kv_rows(pb.KIND_REALIZATION).get("schedule.output") \
            != "emit.pack":
        return False
    img, _ev = ec.run_emit_bundle(path, timeout=3600)
    if img != fixtures.golden("image.default"):
        return False
    # forge 1 — MAP src frame out of range -> refusal at assembly
    data = bytearray(open(path, "rb").read())
    msec = b.section(pb.KIND_MAP)
    struct.pack_into("<I", data, msec.offset + 12, 7)  # row0 frame
    fpath = os.path.join(tmpdir, "emit.map.plex")
    open(fpath, "wb").write(bytes(data))
    try:
        ec.run_emit_bundle(fpath, timeout=3600)
        return False
    except toolchain.NotRealized:
        pass
    streams = ec.emit_schedule_streams(seed.Realization())
    # forge 2 — a dep-closure stage carries no stream -> refusal
    thin = [s for s in streams if s[0] != "emit.assemble"]
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00" * 16, None, {"dialect": "plex.emit/2"}, {},
        streams=thin))
    fpath = os.path.join(tmpdir, "emit.thin.plex")
    open(fpath, "wb").write(forged)
    try:
        ec.run_emit_bundle(fpath, timeout=3600)
        return False
    except toolchain.NotRealized:
        pass
    # forge 3 — program stream from another realization: decoded
    # items no longer enumerate the baked roots -> audit refusal
    alien = {n: bl for n, _r, bl, _m in
             ec.emit_schedule_streams(seed.Realization(fuse_s=True))}
    mixed = [(n, r, alien[n] if n == "emit.program" else bl, m)
             for n, r, bl, m in streams]
    forged = pb.pack_bundle(ec.emit_sections(
        b"\x00" * 16, None, {"dialect": "plex.emit/2"}, {},
        streams=mixed))
    fpath = os.path.join(tmpdir, "emit.alien.plex")
    open(fpath, "wb").write(forged)
    try:
        ec.run_emit_bundle(fpath, timeout=3600)
        return False
    except toolchain.NotRealized:
        pass
    return True
