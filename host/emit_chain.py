"""
emit_chain — the seed emits its own host.

The full emit chain — resolve -> program -> link -> assemble -> pack —
runs as staged basis-term reductions (the G9a..G9h stage functions).
Each stage's NF serializes across the boundary as a TERM — either an
exported graph tree, or the surface token stream itself
(bc_decompile / _parse_native_out — the same wire the exes speak).
That is the staged model _probe_g9g_e2e_staged established: stages
hand off DATA, not heaps; single-arena composition is retention-bound
(>50GB measured, the 027/028 pathology).

Python is plumbing only:

- toolchain.resolve stays a catalog lookup — declaration, not
  computation (the records ARE the data the spec declares).
- every stage's computation is a real reduction on a host piece:
  graph.lo for the in-process runner, or a real emitted exe via
  make_exe_runner — the host computing its own emission stages.
- stage seams carry exported terms:  programOf's NF IS the
  frag-list shape assembleOf consumes;  linkOf's NF `L` projects
  `L (K I)` -> merged symtab, `L K K`/`L K (K I)` -> idata/datab;
  assembleOf's NF projects `nf K` -> .text bytes.
- the final NF decodes to the image bytes.

Gate:  emit_image(R) == seed.emit(R)  byte-for-byte — the emitted
host image produced by reduction, identical to the record-driven
emit.

Measured limits (2026-09-26 box, 128GB):

- mini scale (ASM_LINK + 1 import/slot): all four witnesses byte-exact.
- win64 scale on graph.lo: stage arenas exceed RAM in assemble/pack
  (single-stage peak >85GB — killed before OOM).
- win64 scale on reducer_default.exe: lean arena (~24B/node) but the
  naive tree reducer re-reduces every shared redex — programOf alone
  exceeded a 60min cap (DAG sharing is what keeps graph cheap;
  the exe pays every occurrence).  A `reclaim`/sharing realization
  is the known next lever, not a correctness gap.

Usage: python host/emit_chain.py [--on-exe]
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import time
from typing import Callable, Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
_SEED = os.path.normpath(os.path.join(_HOST, "..", "seed"))
for _p in (_HOST, _SEED):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from reduce import T, I, KK, app                 # noqa: E402
from graph_runtime import Graph                  # noqa: E402
from lambda_dialect import parse, bracket        # noqa: E402
import seed                                      # noqa: E402
import spec_term as st                           # noqa: E402
import routines_x86_64_win64 as rts              # noqa: E402
import target_pe64                               # noqa: E402
import toolchain                                 # noqa: E402

KI = app(KK, I)                                  # \a.\b.b — snd selector


def _nf_to_text(nf: T) -> str:
    """NF term -> surface token stream (the wire the exes speak —
    the same rep a serialized stage boundary carries)."""
    return seed.bc_decompile(seed.t_from_host(nf))


def _nf_from_text(text: str) -> T:
    """token stream -> host T — the inverse of _nf_to_text."""
    return seed._parse_native_out(text)


def _graph_run(t: T, fuel: int = st.LO_FUEL,
               compact_every: int = 200_000) -> Tuple[T, int, int]:
    """One stage in a fresh graph arena -> (exported NF term, steps,
    arena nodes).  Fresh arena per stage IS the staged model; the
    between-step compact pass keeps the live-set bounded inside a
    stage (retention is residue, not load — decisions 028/030)."""
    g = Graph()
    nf_i, steps = g.reduce(g.import_tree(t), fuel=fuel,
                           compact_every=compact_every)
    return g.export_tree(nf_i), steps, g.alloc_count()


def _graph_cd_run(t: T, rounds: int = st.CD_FUEL
                  ) -> Tuple[T, int, int]:
    """One stage via complete development + per-round compaction.

    cd develops independent cones in parallel — the pad/join chunks in
    pack2Of are disjoint, so a round does what LO takes thousands of
    steps to sequence, and compact reclaims every round.  Measured:
    pack-mini 18,354 rounds / ~157MB peak where lo needed ~14GB.
    Returns (NF, rounds, nodes) — rounds are NOT lo steps (divergent
    step-size is expected; the NF is the observable)."""
    g = Graph()
    nf_i, n = g.reduce_cd(g.import_tree(t), fuel=rounds,
                          compact=True)
    return g.export_tree(nf_i), n, g.alloc_count()


def make_exe_runner(exe: str, timeout: int = 3600
                    ) -> Callable[[T], Tuple[T, int, int]]:
    """The host runs the stage itself: decompile the query term to
    surface tokens -> exe stdin -> parse the NF back to a term.
    Same term, a real emitted host computing the emission."""
    def run(t: T) -> Tuple[T, int, int]:
        text = seed.bc_decompile(seed.t_from_host(t))
        cp = subprocess.run([exe], input=text.encode(),
                            capture_output=True, timeout=timeout)
        m = re.search(rb"steps=(\d+)", cp.stderr)
        if cp.returncode != 0:
            raise RuntimeError(
                f"exe stage failed rc={cp.returncode} "
                f"stderr={cp.stderr!r} "
                f"(2=fuel exhausted — never a silent success)")
        nf = seed._parse_native_out(cp.stdout.decode())
        return nf, int(m.group(1)) if m else -1, -1
    return run


_AUDIT = os.environ.get("ISAR_AUDIT", "") not in ("", "0")


def _audit(msg: str) -> None:
    """Chain-level counters, on demand — ISAR_AUDIT=1 prints one line
    per IR batch: pack/wire/exe split, cache hits, steps.  Off by
    default; the counters exist so no ad-hoc probe is needed."""
    if _AUDIT:
        print(f"[audit] {msg}", file=sys.stderr, flush=True)


def make_ir_runner(exe: str, timeout: int = 3600,
                   workers: int = 1,
                   cache_dir: Optional[str] = None,
                   fuse_s: bool = False
                   ) -> Callable[[T], Tuple[T, int, int]]:
    """Packed-IR exe runner (ADR-005): the exe seam carries the term
    graph itself.  One `pack_ir_keyed` walk produces the canonical
    multi-root blob AND per-root Merkle digests; misses are repacked
    into per-chunk multi-root blobs (cross-query sharing dedups within
    each worker's stream).

    workers > 1 splits the miss list into strided chunks across N
    exes — the stream as a work pool (the shape a CUDA grid inherits
    later; per-worker step counts merge, root order and NFs are
    preserved).  cache_dir is a content-addressed NF store keyed by
    the Merkle digest; cached values are the NF's stdout token line."""
    import concurrent.futures

    if cache_dir is not None:
        os.makedirs(cache_dir, exist_ok=True)

    def _one_batch(blob: bytes, expect: int
                   ) -> Tuple[List[str], int, float, Dict[str, int]]:
        t0 = time.time()
        cp = subprocess.run([exe], input=blob,
                            capture_output=True, timeout=timeout)
        wall = time.time() - t0
        m = re.search(rb"steps=(\d+)", cp.stderr)
        if cp.returncode != 0:
            raise RuntimeError(
                f"exe ir batch failed rc={cp.returncode} "
                f"stderr={cp.stderr!r} "
                f"(2=fuel exhausted — never a silent success)")
        lines = cp.stdout.decode().splitlines()
        if len(lines) != expect:
            raise RuntimeError(
                f"ir batch: {len(lines)} NF lines for "
                f"{expect} streams stderr={cp.stderr!r}")
        rules: Dict[str, int] = {}
        mr = re.search(rb"rules=([^\n]+)", cp.stderr)
        if mr:  # audit-built kernel: per-rule histogram
            for kv in mr.group(1).decode().split(","):
                k, _, v = kv.partition(":")
                rules[k] = int(v)
        return lines, int(m.group(1)) if m else -1, wall, rules

    def batch(qs: List[T]) -> Tuple[List[T], int, int]:
        if not qs:
            return [], 0, -1
        t_all = time.time()
        lines: List[Optional[str]] = [None] * len(qs)
        keys: Optional[List[str]] = None
        miss_at: List[int] = []
        pack_s = 0.0
        hits = 0
        if cache_dir is not None:
            # one keyed walk: Merkle digest per root = content key
            t0 = time.time()
            _, keys = st.pack_ir_keyed(*qs)
            pack_s += time.time() - t0
            for i, k in enumerate(keys):
                try:
                    with open(os.path.join(cache_dir, k)) as f:
                        lines[i] = f.read()
                    hits += 1
                except OSError:
                    miss_at.append(i)
        else:
            miss_at = list(range(len(qs)))
        steps = 0
        exe_s = 0.0
        pool_wall = 0.0
        wire = 0
        rules: Dict[str, int] = {}
        if miss_at:
            # strided chunks — consecutive queries tend to cost alike,
            # so round-robin spreads heavy roots across workers
            n = min(max(1, workers), len(miss_at))
            chunks_idx = [miss_at[j::n] for j in range(n)]
            t0 = time.time()
            blobs = [st.pack_ir(*[qs[i] for i in c])
                     for c in chunks_idx]
            pack_s += time.time() - t0
            wire = sum(len(b) for b in blobs)
            t0 = time.time()
            if n <= 1:
                outs = [_one_batch(blobs[0], len(chunks_idx[0]))]
            else:
                with concurrent.futures.ThreadPoolExecutor(n) as pool:
                    outs = list(pool.map(
                        _one_batch, blobs,
                        [len(c) for c in chunks_idx]))
            pool_wall = time.time() - t0
            for c, (ls, s, w, rr) in zip(chunks_idx, outs):
                exe_s += w
                if s > 0:
                    steps += s
                for k, v in rr.items():
                    rules[k] = rules.get(k, 0) + v
                for i, ln in zip(c, ls):
                    lines[i] = ln
                    if keys is not None:
                        with open(os.path.join(cache_dir, keys[i]),
                                  "w") as f:
                            f.write(ln)
        rule_str = (" rules=" + ",".join(
            f"{k}:{rules[k]}" for k in
            ("I", "K", "W", "C", "B", "S", "L", "R") if rules.get(k))
                   ) if rules else ""
        _audit(
            f"ir.batch roots={len(qs)} hits={hits} "
            f"misses={len(miss_at)} "
            f"workers={min(max(1, workers), max(1, len(miss_at)))} "
            f"pack_s={pack_s:.2f} wire={wire / 1e6:.2f}MB "
            f"exe_s={exe_s:.2f} pool_wall_s={pool_wall:.2f} "
            f"steps={steps} wall_s={time.time() - t_all:.2f}{rule_str}")
        outs = [seed._parse_native_out(ln) for ln in lines]
        if fuse_s:
            # fuse_s NFs keep primitive-S leaves; lower to the
            # default-basis view so downstream decoders see the same
            # term shape either kernel emits (quotient map on the seam)
            outs = [st.lower_s_view(nf) for nf in outs]
        return outs, steps, -1

    def run(t: T) -> Tuple[T, int, int]:
        nfs, s, n = batch([t])
        return nfs[0], s, n
    run.batch = batch
    return run


def ir_exe_for(R: seed.Realization) -> str:
    """The emitted packed-IR kernel for realization R (cached per
    process by seed._exe_for)."""
    return seed._exe_for(R, toolchain.by_name("native.x86_64.pe.ir"))


def reduce_batch_native(terms: List[T], R: Optional[seed.Realization] = None,
                        workers: Optional[int] = None,
                        cache_dir: Optional[str] = None
                        ) -> Tuple[List[T], int]:
    """seed.reduce_native vectorized over the packed-IR seam: one keyed
    pack -> Merkle cache + pool of emitted exes -> NF lines -> surface
    view.  Same NF contract as _reduce_via (quote_surface applied; the
    fuse_s runner lowers primitive-S NFs first), but the marshal is the
    batch stream — Python stays out of the evaluation loop."""
    import tower
    R = R or seed.DEFAULT
    workers = workers if workers is not None else (os.cpu_count() or 4)
    if cache_dir is None:
        tag = "fuse_s" if R.fuse_s else "default"
        cache_dir = os.path.join(_HOST, "emit_work", "nf_cache", tag)
    run = make_ir_runner(ir_exe_for(R), workers=workers,
                         cache_dir=cache_dir, fuse_s=R.fuse_s)
    nfs, steps, _ = run.batch(list(terms))
    return [tower.quote_surface(nf) for nf in nfs], steps


def emit_image(R: seed.Realization,
               imports=rts.IMPORTS, slots=rts.DATA_SLOTS,
               text_base: int = target_pe64.TEXT_RVA,
               run: Callable[[T], Tuple[T, int, int]] = _graph_run,
               stage_runs: Optional[dict] = None,
               decompose_asm: bool = False,
               decompose_pack: bool = False,
               workdir: Optional[str] = None,
               verbose: bool = True) -> Tuple[bytes, List[tuple]]:
    """Emit the host image for R via the staged term chain.

    `stage_runs` maps a stage name to a different runner — the hosts
    have complementary cost profiles:  folds over the whole program
    (program/link) suit graph.lo's sharing, the per-insn encodes suit
    the emitted exes (small independent terms, ~0.3-1s each), and
    pack's growing live set needs graph compaction.  The reduction is
    the same on either host — the choice is an observation regime.

    Returns (image_bytes, stage_report) where stage_report lists
    (stage, steps, arena_nodes) per reduction.
    """
    report: List[tuple] = []
    runs = stage_runs or {}

    def _stage(name, q):
        t0 = time.time()
        nf, s, n = runs.get(name, run)(q)
        report.append((name, s, n))
        if verbose:
            print(f"    {name}: {s} steps / {n} nodes "
                  f"({time.time()-t0:.0f}s)", flush=True)
        return nf

    # stages 1/2 are lazy — a resumed run whose seams are already
    # checkpointed never re-reduces programOf/linkOf.
    _nfs: dict = {}

    def _prog_nf() -> T:
        if "program" not in _nfs:
            _nfs["program"] = _stage("program", st.program_query(R))
        return _nfs["program"]

    def _link_nf() -> T:
        if "link" not in _nfs:
            _nfs["link"] = _stage("link", st.link_query(imports, slots))
        return _nfs["link"]

    # stage 3 — .text bytes + localmap.  `decompose_asm` runs
    # assemble_staged (per-insn encodeOf terms at the data seam) when
    # the monolithic assembleOf reduction is arena-bound; the term is
    # the same quotient map, the fold bookkeeping is boundary glue.
    # `workdir` checkpoints decoded artifacts (items/sections/text)
    # so a dead stage retries without recomputing its ancestors —
    # the data seam is literally persisted.
    def _ck(name: str, produce, save, load):
        p = os.path.join(workdir, name) if workdir else None
        if p and os.path.exists(p):
            if verbose:
                print(f"    [ckpt] {name}", flush=True)
            return load(p)
        v = produce()
        if p:
            save(p, v)
        return v

    if decompose_asm:
        import pickle

        def _dump(p, v):
            with open(p, "wb") as f:
                pickle.dump(v, f)

        def _load(p):
            with open(p, "rb") as f:
                return pickle.load(f)

        t0 = time.time()
        items = _ck("program.items",
                    lambda: st.decode_program(_prog_nf()),
                    _dump, _load)
        ib, db, syms = _ck("link.sections",
                           lambda: st.decode_link(_link_nf()),
                           _dump, _load)
        text, _loc = _ck("text.bin", lambda: assemble_staged(
            items, syms, text_base, runs.get("assemble*", run),
            verbose=verbose), _dump, _load)
        report.append(("assemble*", -1, -1))
        if verbose:
            print(f"    assemble*: decomposed {len(items)} items "
                  f"({time.time()-t0:.0f}s)", flush=True)
        text_t = st.bytelist_term(text)
        idata_t, datab_t = st.bytelist_term(ib), st.bytelist_term(db)
        if decompose_pack:
            t0 = time.time()
            img = _ck("image.bin",
                      lambda: pack_staged(
                          text, ib, db, R.stack_reserve,
                          runs.get("pack*", run), verbose=verbose),
                      lambda p, v: open(p, "wb").write(v),
                      lambda p: open(p, "rb").read())
            report.append(("pack*", -1, -1))
            if verbose:
                print(f"    pack*: decomposed {len(img)}B "
                      f"({time.time()-t0:.0f}s)", flush=True)
            return img, report
    else:
        link_nf = _link_nf()
        asm_nf = _stage("assemble",
                        st.assemble_query_t(_prog_nf(),
                                            app(link_nf, KI),
                                            text_base))
        text_t = st._l0_nf(app(asm_nf, KK), 500_000)
        idata_t = app(app(link_nf, KK), KK)
        datab_t = app(app(link_nf, KK), KI)

    # stage 4 — pack2Of text idata datab stackres: the image
    img_nf = _stage("pack", st.pack2_query_t(
        text_t, idata_t, datab_t, R.stack_reserve))

    img = st._decode_bytecells(img_nf)
    if workdir:
        with open(os.path.join(workdir, "image.bin"), "wb") as f:
            f.write(img)
    return img, report


_RESVMK: Optional[T] = None


def _resvmk() -> T:
    """`λsym λloc λe4 λnm` — assembleOf's per-site resolver closure as
    data: sym is the merged link symtab, loc the boundary-accumulated
    label map, e4 the insn's end address (bytes4).  Mirrors `resv` in
    st._assemble_src: symbols shadow locals, a resolver miss yields
    0-end."""
    global _RESVMK
    if _RESVMK is None:
        src = ("(\\sym. \\loc. \\e4. \\nm. (" + st._ALOOK + " sym nm) (("
               + st._ALOOK + " loc nm) (" + st._B4SUB + " "
               + st._b4_src(0) + " e4) (\\lv. " + st._B4SUB
               + " lv e4)) (\\sv. " + st._B4SUB + " sv e4))")
        _RESVMK = bracket(parse(src))
    return _RESVMK


def _is_rel_item(it) -> bool:
    """item has a resolver-sensitive operand — ("l",name) rel32 or
    ("p",name) rip-symbol — so its pass-2 bytes depend on resv."""
    return any(isinstance(o, tuple) and o[0] in ("l", "p")
               for o in it[2:])


def assemble_staged(items: List[tuple], syms: dict, base: int,
                    run: Callable[[T], Tuple[T, int, int]],
                    verbose: bool = False) -> Tuple[bytes, dict]:
    """assembleOf decomposed at insn granularity — the boundary seam
    drops below the stage function.

    assembleOf = pass1 fold + pass2 fold over the item list.  Here
    every instruction's encoding is still a real `encodeOf` term
    reduction (identical quotient map per insn, memoized since equal
    items reduce to equal NFs by confluence), while the two passes'
    bookkeeping — position accumulation, the local label map, the
    end4 arithmetic — runs as data-level ops on the serialized seam,
    exactly the glue the stage boundaries already perform.

    Cost profile vs monolithic assembleOf: ~N independent small
    reductions instead of one giant spine.  Each gets a fresh arena,
    so the win64 kernel (~484 insns, ~323 unique encodes) is minutes
    instead of an unbounded single-arena retention blowup.  This is
    also the shape parallel/CUDA evaluation takes — independent
    redexes, independent contexts.

    Returns (text_bytes, local_map) matching isa.assemble / assembleOf.
    """
    sym_t = st.symtab_term(syms)
    loc: dict = {}
    prep: List[tuple] = []          # (item, off, len, zero_bytes)
    t0 = time.time()
    n_red = 0
    batch = getattr(run, "batch", None)
    # pass 1 — ZRESV encodes (resv never consulted: rel fields emit
    # four zero cells — byte COUNT is correct) give per-insn lengths;
    # labels record base+pos exactly as assembleOf's label_case.
    # With a packed-IR runner the uniques go out as ONE batch stream —
    # the multi-root header is the work unit (fork-pool / CUDA shape).
    uniq: dict = {}
    for it in items:
        if it[0] != "label" and it not in uniq:
            uniq[it] = None
    uq = list(uniq)
    if batch is not None:
        nfs, _, _ = batch([st.encode_query(it) for it in uq])
        for it, nf in zip(uq, nfs):
            uniq[it] = st.decode_encode(nf)
        n_red += len(uq)
        if verbose:
            print(f"      pass1: {n_red} encodes (1 batch) "
                  f"({time.time()-t0:.0f}s)", flush=True)
    else:
        for it in uq:
            uniq[it] = st.decode_encode(run(st.encode_query(it))[0])
            n_red += 1
            if verbose and n_red % 50 == 0:
                print(f"      pass1: {n_red} encodes "
                      f"({time.time()-t0:.0f}s)", flush=True)
    pos = 0
    for it in items:
        if it[0] == "label":
            loc[it[1]] = base + pos
            continue
        b = uniq[it]
        prep.append((it, pos, len(b), b))
        pos += len(b)
    # pass 2 — rel-sensitive items re-encode with the real resolver
    # (same term as assembleOf's insn_emit calls); all others reuse
    # the pass-1 bytes — their resv is never applied.
    loc_t = st.symtab_term(loc)
    rel = [(i, it) for i, (it, off, ln, b0) in enumerate(prep)
           if _is_rel_item(it)]
    rel_bytes: List[bytes] = []
    if rel:
        if batch is not None:
            nfs, _, _ = batch([
                st.encode_query(it, st._appn(
                    _resvmk(), sym_t, loc_t,
                    st.bytelist_term(
                        (base + prep[i][1] + prep[i][2]).to_bytes(
                            4, "little"))))
                for i, it in rel])
            rel_bytes = [st.decode_encode(nf) for nf in nfs]
            n_red += len(rel)
            if verbose:
                print(f"      pass2: {n_red} encodes (1 batch) "
                      f"({time.time()-t0:.0f}s)", flush=True)
        else:
            for i, it in rel:
                e4 = st.bytelist_term(
                    (base + prep[i][1] + prep[i][2]).to_bytes(
                        4, "little"))
                resv_t = st._appn(_resvmk(), sym_t, loc_t, e4)
                rel_bytes.append(
                    st.decode_encode(
                        run(st.encode_query(it, resv_t))[0]))
                n_red += 1
                if verbose and n_red % 50 == 0:
                    print(f"      pass2: {n_red} encodes "
                          f"({time.time()-t0:.0f}s)", flush=True)
    out = bytearray()
    for i, (it, off, ln, b0) in enumerate(prep):
        out += b0
    for (i, _it), b in zip(rel, rel_bytes):
        # splice pass-2 bytes back over the pass-1 placeholder positions
        off_i = prep[i][1]
        out[off_i:off_i + prep[i][2]] = b
    return bytes(out), loc


def pack_staged(text: bytes, idata: bytes, datab: bytes,
                stackres: int,
                run: Callable[[T], Tuple[T, int, int]],
                verbose: bool = False) -> bytes:
    """pack2Of decomposed at chunk granularity — mirrors _pack_body's
    chunk list exactly.  Every derived chunk (bytes4 size fields, the
    u64 stack-reserve, zerofills, padlists) is a small `run`-ed term
    reduction over the same vocabulary constants; the byte join is
    the seam (identical to what pack2Of's JOIN computes — the oracle
    gate `python_pack` verifies byte-exact)."""
    import struct
    _c: dict = {}

    def K_(name: str):
        if name not in _c:
            _c[name] = bracket(parse(getattr(st, name)))
        return _c[name]

    def b4(v: int) -> T:
        return st.bytelist_term(v.to_bytes(4, "little"))

    def r1(q: T) -> T:
        return run(q)[0]

    def dec(t: T) -> bytes:
        return st._decode_bytecells(t)

    # the lets — ALIGN/B4ADD/U64/PADLIST/ZEROFILL as standalone
    # reductions over bytes4/Church numerals (tiny terms; section
    # contents never enter).  lt/li/ld are NOT re-folded through
    # LENB4: at the chunk seam the sections are serialized bytes and
    # their length is boundary metadata — the same discipline as
    # assemble_staged's pos/loc bookkeeping.  (LENB4-as-term measured
    # OOM-class: ~16GB LO live set / 72GB naive-exe arena on the
    # 2696-cell win64 text — a sequential fold has no cones to
    # develop and nothing to share.)
    lt = r1(b4(len(text)))
    li = r1(b4(len(idata)))
    ld = r1(b4(len(datab)))
    traw = r1(st._appn(K_("_ALIGN512"), lt))
    iraw = r1(st._appn(K_("_ALIGN512"), li))
    draw = r1(st._appn(K_("_ALIGN512"), ld))
    iptr = r1(st._appn(K_("_B4ADD"), b4(0x200), traw))
    dptr = r1(st._appn(K_("_B4ADD"), iptr, iraw))
    iddr = r1(st._appn(K_("_B4ADD"), iraw, draw))
    img = r1(st._appn(K_("_ALIGN4096"),
                      st._appn(K_("_B4ADD"), b4(0x3000), ld)))
    u64 = r1(st._appn(K_("_U64"), b4(stackres)))

    def zf(n: int) -> bytes:
        return dec(r1(st._appn(K_("_ZEROFILL"), st.church(n))))

    def pad(len4: T) -> bytes:
        return dec(r1(st._appn(K_("_PADLIST"), len4)))

    sizes = {"lt": lt, "li": li, "ld": ld, "traw": traw,
             "iraw": iraw, "draw": draw, "iptr": iptr,
             "dptr": dptr, "iddr": iddr, "img": img}
    sects = {"text": text, "idata": idata, "datab": datab}
    z12 = zf(12)
    chunks = [
        b"MZ", zf(58), struct.pack("<I", 0x40), b"PE\x00\x00",
        struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0, 0x22),
        struct.pack("<HBB", 0x20B, 0, 0),
        dec(traw), dec(iddr), struct.pack("<I", 0),
        struct.pack("<I", 0x1000), struct.pack("<I", 0x1000),
        struct.pack("<Q", 0x140000000),
        struct.pack("<II", 0x1000, 0x200),
        struct.pack("<HHHHHH", 6, 0, 0, 0, 6, 0),
        struct.pack("<I", 0), dec(img),
        struct.pack("<II", 0x200, 0),
        struct.pack("<HH", 3, 0x8100),
        dec(u64),
        struct.pack("<QQQ", 0x1000, 0x100000, 0x1000),
        struct.pack("<II", 0, 16), struct.pack("<II", 0, 0),
        struct.pack("<I", 0x2000), dec(li),
        zf(14 * 8),
        b".text\x00\x00\x00", dec(lt),
        struct.pack("<I", 0x1000), dec(traw),
        struct.pack("<I", 0x200), z12,
        struct.pack("<I", 0x60000020),
        b".idata\x00\x00", dec(li),
        struct.pack("<I", 0x2000), dec(iraw), dec(iptr), z12,
        struct.pack("<I", 0x40000040),
        b".data\x00\x00\x00", dec(ld),
        struct.pack("<I", 0x3000), dec(draw), dec(dptr), z12,
        struct.pack("<I", 0xC0000040),
        zf(0x200 - 448),
        text, pad(lt), idata, pad(li), datab, pad(ld),
    ]
    return b"".join(chunks)


def emit_native(name: str = "native.x86_64.pe",
                R: Optional[seed.Realization] = None) -> bytes:
    """The record-driven emit — the oracle this file gates against."""
    return seed.emit(R if R is not None else seed.Realization(),
                     tc=toolchain.by_name(name))


def emit_mini_image(run: Callable[[T], Tuple[T, int, int]],
                    stage_runs: Optional[dict] = None,
                    decompose_asm: bool = False,
                    decompose_pack: bool = False
                    ) -> Tuple[bytes, List[tuple]]:
    """The staged chain at mini scale (ASM_LINK frag list + one
    import/slot) — small enough for the native/C exes to compute:
    the emitted host itself reducing the emit stages.  Whole-stage
    terms on the naive exe re-reduce shared redexes without bound
    (assemble/pack measured >20M steps); for exe legs `decompose_asm`
    and per-stage runners keep every reduction inside a small term."""
    imps, slots, base, sr = ("ExitProcess",), (("x", 8),), 0x1000, \
        64 << 20
    runs = stage_runs or {}
    report: List[tuple] = []
    link_nf, s, n = runs.get("link", run)(st.link_query(imps, slots))
    report.append(("link", s, n))
    sym_t = app(link_nf, KI)
    if decompose_asm:
        items = [it for fr in st.ASM_LINK for it in fr]
        syms = st.decode_symbols(st._l0_nf(sym_t, 500_000))
        text, _loc = assemble_staged(items, syms, base,
                                     runs.get("assemble*", run))
        report.append(("assemble*", -1, -1))
        text_t = st.bytelist_term(text)
    else:
        asm_nf, s, n = runs.get("assemble", run)(st.assemble_query_t(
            st.fraglist_term(st.ASM_LINK), sym_t, base))
        report.append(("assemble", s, n))
        text_t = st._l0_nf(app(asm_nf, KK), 500_000)
    if decompose_pack:
        tb = text if decompose_asm else st._decode_bytecells(text_t)
        ib, db, _s2 = st.decode_link(link_nf)
        img = pack_staged(tb, ib, db, sr, runs.get("pack*", run))
        report.append(("pack*", -1, -1))
        return img, report
    img_nf, s, n = runs.get("pack", run)(st.pack2_query_t(
        text_t, app(app(link_nf, KK), KK),
        app(app(link_nf, KK), KI), sr))
    report.append(("pack", s, n))
    return st._decode_bytecells(img_nf), report


def _mini_oracle() -> bytes:
    _ib, _db, syms = st.python_link(("ExitProcess",), (("x", 8),))
    _text, _lm = st.python_assemble(st.ASM_LINK, syms, 0x1000)
    return st.python_pack(_text, ("ExitProcess",), (("x", 8),),
                          64 << 20)


def main() -> int:
    ok = True

    # mini chain on graph.lo — the fast regression leg (decomposed:
    # the same stage seams the win64 legs exercise)
    t0 = time.time()
    want_mini = _mini_oracle()
    got, report = emit_mini_image(_graph_run, decompose_asm=True,
                                  decompose_pack=True)
    good = got == want_mini
    ok = ok and good
    print(f"{'OK ' if good else 'FAIL'} mini on graph.lo: "
          f"{len(got)}B == {len(want_mini)}B ({time.time()-t0:.0f}s) "
          + "  ".join(f"{n}:{s}st" for n, s, _ in report), flush=True)

    if "--on-exe" in sys.argv[1:]:
        exes = {"pe": seed._exe_for(seed.Realization())}
        try:
            import routines_c
            exes["c"] = routines_c._exe_for(
                seed.Realization(abi="hosted"))
        except Exception as e:                       # noqa: BLE001
            print(f"  (c kernel skipped: {e})")
        for tag, exe in exes.items():
            t0 = time.time()
            # fueled exe: a runaway stage term bounds to fuel steps
            # (rc=2 + partial stats) instead of an unbounded arena —
            # the 100GB lesson from unconstrained probes.
            runner = make_exe_runner(
                seed._exe_for(seed.Realization(fuel=2_000_000))
                if tag == "pe" else exe)
            got, report = emit_mini_image(
                _graph_run, decompose_asm=True, decompose_pack=True,
                stage_runs={"link": runner, "assemble*": runner})
            good = got == want_mini
            ok = ok and good
            stages = "  ".join(f"{n}:{s}st" for n, s, _ in report)
            print(f"{'OK ' if good else 'FAIL'} on-exe[{tag}] mini: "
                  f"{len(got)}B == {len(want_mini)}B "
                  f"({time.time()-t0:.0f}s)  {stages}", flush=True)

    if "--win64" in sys.argv[1:]:
        # pack's live set is image-construction-sized on LO (the JOIN
        # spine holds all section intermediates); decomposed chunks are
        # small enough for the default LO runner.  cd+compact is the
        # monolithic alternative ("pack": _graph_cd_run).
        for tag, R in (("default", seed.Realization()),
                       ("fuse_s", seed.Realization(fuse_s=True))):
            # per-realization stage runners — a fuse_s leg must run on
            # the fuse_s kernel (derived-S view differs), not just when
            # checkpoints happen to be cold
            sr = {}
            if "--insns-on-exe" in sys.argv[1:]:
                # the emitted host computes the per-insn encodes of its
                # own image — self-hosting through the stage seam, not
                # just around it.  --ir: the seam carries packed IR
                # batches (ADR-005) instead of per-encode token marshal.
                if "--ir" in sys.argv[1:]:
                    ir_runner = make_ir_runner(
                        seed._exe_for(
                            seed.Realization(fuel=2_000_000,
                                             fuse_s=R.fuse_s,
                                             audit=_AUDIT),
                            tc=toolchain.by_name(
                                "native.x86_64.pe.ir")),
                        workers=os.cpu_count() or 4,
                        # NF cache is keyed by term content but the VALUE
                        # is realization-dependent (fuse_s reduces tag-3
                        # primitively) — namespace per realization or
                        # cross-leg hits serve the wrong NF
                        cache_dir=os.path.join(_HOST, "emit_work",
                                               "nf_cache", tag),
                        fuse_s=R.fuse_s)
                    sr["assemble*"] = ir_runner
                    sr["pack*"] = ir_runner
                else:
                    sr["assemble*"] = make_exe_runner(
                        seed._exe_for(seed.Realization(
                            fuel=2_000_000, fuse_s=R.fuse_s)))
            t0 = time.time()
            want = emit_native("native.x86_64.pe", R)
            wd = os.path.join(_HOST, "emit_work", tag)
            os.makedirs(wd, exist_ok=True)
            got, report = emit_image(R, decompose_asm=True,
                                     decompose_pack=True,
                                     stage_runs=sr, workdir=wd)
            good = got == want
            ok = ok and good
            stages = "  ".join(f"{n}:{s}st/{a}n" for n, s, a in report)
            print(f"{'OK ' if good else 'FAIL'} emit_chain {tag}: "
                  f"{len(got)}B == {len(want)}B  "
                  f"({time.time()-t0:.0f}s)  {stages}", flush=True)
            if not good:
                k = next((i for i, (a, b) in enumerate(zip(got, want))
                          if a != b), min(len(got), len(want)))
                print(f"  first diff at {k}: "
                      f"{got[k:k+8].hex()} vs {want[k:k+8].hex()}")

    print(f"{'OK' if ok else 'FAIL'} emit_chain "
          f"(seed emits its own host)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
