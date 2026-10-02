"""
emit_chain — the seed emits its own host.

The full emit chain — resolve -> program -> link -> assemble -> pack —
runs as staged basis-term reductions (the G9a..G9h stage functions).
Each stage's NF serializes across the boundary as a TERM — either an
exported graph tree, or the surface token stream itself
(bc_decompile / _parse_native_out — the same wire the exes speak).
That is the staged model attic/host/_probe_g9g_e2e_staged established: stages
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

Usage: python host/emit_chain.py [--on-exe] [--win64] [--cold]
"""
from __future__ import annotations

import hashlib
import inspect
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from typing import Callable, Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
_SEED = os.path.normpath(os.path.join(_HOST, "..", "seed"))
for _p in (_HOST, _SEED):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from reduce import T, I, KK, B, C, D, app        # noqa: E402
from graph_runtime import Graph, fmt_dur         # noqa: E402
from lambda_dialect import parse, bracket        # noqa: E402
import seed                                      # noqa: E402
import spec_term as st                           # noqa: E402
import routines_x86_64_win64 as rts              # noqa: E402
import target_pe64                               # noqa: E402
import toolchain                                 # noqa: E402

KI = app(KK, I)                                  # \a.\b.b — snd selector


def _nf_to_text(nf: T) -> str:
    """NF term -> surface token stream (the wire the exes speak —
    space-separated postfix, the same rep a serialized stage
    boundary carries and _parse_native_out reads back)."""
    return " ".join(seed.bc_decompile(seed.t_from_host(nf)))


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


def make_graph_runner(fuel: int = st.LO_FUEL,
                      compact_every: int = 200_000,
                      cache_dir: Optional[str] = None
                      ) -> Callable[[T], Tuple[T, int, int]]:
    """graph.lo stage runner in the same (T)->(T, steps, nodes) seam
    shape as the exe pools — the pinned host for deep sequential
    folds (the exes' immutable-cell rebuild model OOMs on them;
    measured: 735K-step peephole term needs >2.8G cells).

    cache_dir content-addresses stage NFs by the query term's
    packed-IR Merkle digest — the same digest the exe seam uses, so
    an NF derived once (by ANY host writing this format) is served
    to every later run: the serialized stage boundary as a store."""
    if cache_dir is not None:
        os.makedirs(cache_dir, exist_ok=True)

    def run(t: T) -> Tuple[T, int, int]:
        p = None
        if cache_dir is not None:
            p = os.path.join(cache_dir,
                             st.pack_ir_keyed(t)[1][0] + ".nf")
            try:
                with open(p) as f:
                    return _nf_from_text(f.read()), -1, -1
            except OSError:
                pass
        nf, s, n = _graph_run(t, fuel=fuel,
                              compact_every=compact_every)
        if p is not None:
            with open(p, "w") as f:
                f.write(_nf_to_text(nf))
        return nf, s, n

    def batch(qs: List[T]) -> Tuple[List[T], int, int]:
        """Sequential batch — same queries, same cache keys; the
        batch seam is transport, not scheduling (this runner has no
        parallel streams to fill)."""
        nfs, tot = [], 0
        for q in qs:
            nf, s, _ = run(q)
            nfs.append(nf)
            tot += s
        return nfs, tot, -1
    run.batch = batch
    return run


_PEEP_ITEM_RUN = None


def _peephole_item_runner():
    """The per-item exe runner for the decomposed peephole stage —
    each `step acc it` call is a small bounded term that fits the
    emitted kernel's arena (the monolithic fold OOMs it).  Lazily
    built: the leg emits the exe on first use."""
    global _PEEP_ITEM_RUN
    if _PEEP_ITEM_RUN is None:
        _PEEP_ITEM_RUN = make_ir_runner(
            seed._exe_for(
                seed.Realization(fuel=8_000_000, audit=_AUDIT,
                                 # chase-heavy single items legitimately
                                 # reach ~3G cells under reclaim=none
                                 # (commit-ahead: untouched pages free);
                                 # per-root DECOMMIT reset keeps the
                                 # batch footprint at the worst root
                                 ir_arena_bytes=8 << 30),
                tc=toolchain.by_name("native.x86_64.pe.ir")),
            workers=4,
            cache_dir=os.path.join(_HOST, "emit_work", "nf_cache",
                                   "peepitem"))
    return _PEEP_ITEM_RUN


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
            f"pack={fmt_dur(pack_s)} wire={wire / 1e6:.2f}MB "
            f"exe={fmt_dur(exe_s)} pool_wall={fmt_dur(pool_wall)} "
            f"steps={steps} wall={fmt_dur(time.time() - t_all)}{rule_str}")
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


def _bytes_frames(buf: bytes, expect: int) -> List[bytes]:
    """[u32le len][bytes]* — the byte-egress frame wire: one frame per
    root, in root order, across however many streams the batch packed.
    Newlines/NULs are payload, not structure (that is the point)."""
    out: List[bytes] = []
    off = 0
    while off < len(buf):
        if off + 4 > len(buf):
            raise RuntimeError(
                f"bytes frame: truncated u32 len at {off}/{len(buf)}")
        n = int.from_bytes(buf[off:off + 4], "little")
        off += 4
        if off + n > len(buf):
            raise RuntimeError(
                f"bytes frame: {n}B payload at {off} overruns "
                f"{len(buf)}B of stdout")
        out.append(buf[off:off + n])
        off += n
    if len(out) != expect:
        raise RuntimeError(
            f"bytes batch: {len(out)} frames for {expect} roots")
    return out


def make_bytes_runner(exe: str, timeout: int = 3600,
                      workers: int = 1,
                      cache_dir: Optional[str] = None
                      ) -> Callable[[T], Tuple[bytes, int, int]]:
    """Packed-IR runner over the byte-egress kernel (Realization
    io=("stdin","bytes")): the exe decodes each root's byte-list NF
    itself — Python never rebuilds the byte-list term.  Wire out is one
    [u32le len][bytes] frame per root, order preserved; stderr keeps
    `steps=`/`alloc=` for the query reductions plus `dec=` for the
    kernel's own decode probes.

    run(q) -> (bytes, steps, alloc); .batch(qs) -> ([bytes], steps,
    alloc); .is_bytes marks the runner so byte-producing seams pick the
    raw-bytes path.  cache_dir is a content-addressed payload store —
    values are raw bytes, never share a dir with the NF cache."""
    import concurrent.futures

    if cache_dir is not None:
        os.makedirs(cache_dir, exist_ok=True)
    stats = {"dec": 0}

    def _one(blob: bytes, expect: int) -> Tuple[List[bytes], int, int]:
        cp = subprocess.run([exe], input=blob,
                            capture_output=True, timeout=timeout)
        m = re.search(rb"steps=(\d+) alloc=(\d+)", cp.stderr)
        md = re.search(rb" dec=(\d+)", cp.stderr)
        if cp.returncode != 0:
            raise RuntimeError(
                f"exe bytes batch failed rc={cp.returncode} "
                f"stderr={cp.stderr!r} "
                f"(2=fuel exhausted, 3=bad IR, 5=not a byte-list NF "
                f"— never a silent success)")
        if md:
            stats["dec"] += int(md.group(1))
        frames = _bytes_frames(cp.stdout, expect)
        return (frames, int(m.group(1)) if m else -1,
                int(m.group(2)) if m else -1)

    def batch(qs: List[T]) -> Tuple[List[bytes], int, int]:
        if not qs:
            return [], 0, -1
        outs: List[Optional[bytes]] = [None] * len(qs)
        keys: Optional[List[str]] = None
        miss_at = list(range(len(qs)))
        if cache_dir is not None:
            _, keys = st.pack_ir_keyed(*qs)
            miss_at = []
            for i, k in enumerate(keys):
                try:
                    with open(os.path.join(cache_dir, k), "rb") as f:
                        outs[i] = f.read()
                except OSError:
                    miss_at.append(i)
        steps = alloc = 0
        if miss_at:
            n = min(max(1, workers), len(miss_at))
            chunks = [miss_at[j::n] for j in range(n)]
            blobs = [st.pack_ir(*[qs[i] for i in c]) for c in chunks]
            if n <= 1:
                res = [_one(blobs[0], len(chunks[0]))]
            else:
                with concurrent.futures.ThreadPoolExecutor(n) as pool:
                    res = list(pool.map(
                        _one, blobs, [len(c) for c in chunks]))
            for c, (fs, s, a) in zip(chunks, res):
                if s > 0:
                    steps += s
                if a > 0:
                    alloc += a
                for i, b in zip(c, fs):
                    outs[i] = b
                    if keys is not None:
                        with open(os.path.join(cache_dir, keys[i]),
                                  "wb") as f:
                            f.write(b)
        _audit(f"bytes.batch roots={len(qs)} "
               f"misses={len(miss_at)} steps={steps} dec={stats['dec']}")
        return outs, steps, alloc

    def run(t: T) -> Tuple[bytes, int, int]:
        outs, s, a = batch([t])
        return outs[0], s, a
    run.batch = batch
    run.is_bytes = True                    # byte-producing seams see this
    run.stats = stats                      # cumulative decode-probe steps
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


def _stage_key(*parts) -> str:
    """Content key for a checkpointed stage: sha256 over the parts'
    bytes (str -> utf-8, bytes as-is), 16 hex chars — short enough for
    filenames, collision-proof for a handful of stages per workdir."""
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else str(p).encode("utf-8"))
        h.update(b"\x00")
    return h.hexdigest()[:16]


def _src(fn) -> str:
    """sha256 of a stage function's source — decoder/fold code edits
    invalidate its checkpoints, unrelated edits don't."""
    return hashlib.sha256(inspect.getsource(fn).encode("utf-8")).hexdigest()


def _ck_label(R: seed.Realization, host_name: str) -> str:
    """Readable key prefix: host triplet + the strategy knobs that
    change artifacts — `x86_64.pe.peephole.<hash>` beats an opaque
    buildstamp; the content hash stays the uniqueness, the label is
    the provenance."""
    flags: List[str] = []
    if getattr(R, "fuse_s", False):
        flags.append("fuse_s")
    if getattr(R, "peephole", False):
        flags.append("peephole")
    if R.order != "lo":
        flags.append(str(R.order))
    if getattr(R, "io", ("stdin", "stdout")) != ("stdin", "stdout"):
        flags.append("io_" + "-".join(R.io))
    if getattr(R, "reclaim", "none") not in (None, "none"):
        flags.append(str(R.reclaim))
    if R.fuel is not None:
        flags.append("fuel%d" % R.fuel)
    base = (host_name or "host").replace("native.", "").replace(".", "-")
    return base + "." + (".".join(flags) if flags else "plain")


def _ck_keys(R: seed.Realization, imports, slots,
             text_base: int, host_name: str = "") -> Dict[str, str]:
    """Content keys for the four checkpointed artifacts, keyed on the
    stage INPUTS (the packed-IR digest of each stage's root term, the
    realization knobs that change it, and the producing code's source)
    — a stale file can't survive an input or code change.  Keys carry
    a readable <triplet>.<strategy>. prefix so `ls emit_work` says who
    built what; the 16-hex suffix is still the content proof."""
    pre = _ck_label(R, host_name)
    prog_q = st.program_query(R)
    if getattr(R, "peephole", False):
        # the program.items checkpoint holds the OPTIMIZED items for a
        # peephole realization — key on the stage's real input term or
        # an unpeepholed run's file would be served
        prog_q = st.peephole_query(prog_q)
    prog = _stage_key(pre, st.pack_ir_keyed(prog_q)[1][0],
                      "fuse_s=%d" % R.fuse_s, _src(st.decode_program))
    link = _stage_key(pre,
                      st.pack_ir_keyed(st.link_query(imports, slots))[1][0],
                      _src(st.decode_link))
    text = _stage_key(prog, link, "base=%d" % text_base,
                      _src(assemble_staged))
    image = _stage_key(text, link, "stackres=%d" % R.stack_reserve,
                       _src(pack_staged))
    return {"program.items": f"{pre}.{prog}",
            "link.sections": f"{pre}.{link}",
            "text.bin": f"{pre}.{text}", "image.bin": f"{pre}.{image}"}


def emit_image(R: seed.Realization,
               imports=rts.IMPORTS, slots=rts.DATA_SLOTS,
               text_base: Optional[int] = None,
               run: Callable[[T], Tuple[T, int, int]] = _graph_run,
               stage_runs: Optional[dict] = None,
               bytes_run: Optional[Callable] = None,
               term_run: Optional[Callable] = None,
               decompose_asm: bool = False,
               decompose_pack: bool = False,
               workdir: Optional[str] = None,
               label: str = "",
               verbose: bool = True) -> Tuple[bytes, List[tuple]]:
    """Emit the host image for R via the staged term chain.

    `stage_runs` maps a stage name to a different runner — the hosts
    have complementary cost profiles:  folds over the whole program
    (program/link) suit graph.lo's sharing, the per-insn encodes suit
    the emitted exes (small independent terms, ~0.3-1s each), and
    pack's growing live set needs graph compaction.  The reduction is
    the same on either host — the choice is an observation regime.

    `bytes_run` is a make_bytes_runner egress pool: byte-producing
    seams (assemble* encodes, pack* chunks, the monolithic pack root)
    default to it — the kernel decodes the byte-list NF natively and
    the seam carries raw bytes, no Python _decode_bytecells.  Explicit
    stage_runs entries still win per stage.

    `term_run` is a make_ir_runner for term-NF stages whose egress is
    cheap relative to compute — measured 2026-10: `link` runs 3x
    faster on the redirect kernel (108.9s vs 326s graph.lo, small
    query + 436K-step fold), while `program` is pack-bound (its query
    embeds the ~12M-node generated constant; pack_ir dominates at
    ~392s vs 62.9s) and stays on `run` until packed stage blobs are
    persisted.

    Returns (image_bytes, stage_report) where stage_report lists
    (stage, steps, arena_nodes) per reduction.
    """
    report: List[tuple] = []
    # programOf is generated at sentinel defaults — only fs/fuel/
    # rbb/cb/nb flow in as parameters (stack_reserve enters at pack,
    # peephole is its own stage).  Any other R field left non-default
    # would be silently dropped; refuse rather than emit the wrong
    # kernel — silent realization downgrade is exactly what the staged
    # chain exists to prevent.
    _d = seed.Realization()
    _param = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
              "node_bytes", "stack_reserve", "peephole"}
    _bad = {k: getattr(R, k) for k in vars(_d)
            if k not in _param and getattr(R, k) != getattr(_d, k)}
    if _bad:
        raise toolchain.NotRealized(
            f"emit_image: programOf realizes only fs/fuel/rbb/cb/nb/"
            f"stack_reserve/peephole; non-default {sorted(_bad)} needs "
            f"an extended programOf or a different routines record")
    if text_base is None:
        # .text is emitted last in the image — its RVA is a function of
        # the (already fixed) idata/data layout, not a constant.
        text_base = target_pe64.text_rva(imports, slots)
    runs = dict(stage_runs or {})
    if bytes_run is not None:
        runs.setdefault("assemble*", bytes_run)
        runs.setdefault("pack*", bytes_run)
        runs.setdefault("pack", bytes_run)
    if term_run is not None:
        runs.setdefault("link", term_run)

    def _stage(name, q):
        t0 = time.time()
        nf, s, n = runs.get(name, run)(q)
        report.append((name, s, n))
        if verbose:
            print(f"    {name}: {s} steps / {n} nodes "
                  f"({fmt_dur(time.time()-t0)})", flush=True)
        return nf

    # stages 1/2 are lazy — a resumed run whose seams are already
    # checkpointed never re-reduces programOf/linkOf.
    _nfs: dict = {}

    def _prog_nf() -> T:
        if "program" not in _nfs:
            _nfs["program"] = _stage("program", st.program_query(R))
            if getattr(R, "peephole", False):
                # G9i: peepholeOf staged as SEAM-DECOMPOSED per-item
                # reductions — decompose_asm's contract (same term,
                # fold bookkeeping at the boundary).  Each `step`/
                # `latstep` call is a small bounded term that fits
                # the emitted kernel's arena; the monolithic fold
                # OOM'd every native host at ~3.9K cells/step and
                # cd replays the sequential scan chains at a worse
                # constant — measured, not theorized.
                runs.setdefault("peephole", lambda p: (
                    lambda r: (r[0], r[2], r[1]))(
                        st.peephole_fixpoint_seamed(
                            p, runs.get("peephole_item")
                            or _peephole_item_runner())))
                _nfs["program"] = _stage("peephole", _nfs["program"])
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
    ckpt = [0, 0]  # [hits, misses] — report provenance appended below

    def _ck(name: str, key: str, produce, save, load):
        p = os.path.join(workdir, f"{name}.{key}") if workdir else None
        if p and os.path.exists(p):
            ckpt[0] += 1
            if verbose:
                print(f"    [ckpt hit] {name} {key}", flush=True)
            return load(p)
        if p:
            ckpt[1] += 1
            if verbose:
                print(f"    [ckpt miss] {name} {key}", flush=True)
        v = produce()
        if p:
            save(p, v)
            # provenance sidecar — the content key says WHAT it is,
            # the meta says who/when (the hash alone is opaque)
            try:
                with open(p + ".meta", "w") as mf:
                    json.dump({
                        "artifact": name, "key": key,
                        "created_utc": time.strftime(
                            "%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                        "realization": repr(R),
                    }, mf)
            except OSError:
                pass
        return v

    if decompose_asm:
        import pickle

        def _dump(p, v):
            with open(p, "wb") as f:
                pickle.dump(v, f)

        def _load(p):
            with open(p, "rb") as f:
                return pickle.load(f)

        keys = _ck_keys(R, imports, slots, text_base,
                        host_name=label) if workdir else {}

        t0 = time.time()
        items = _ck("program.items", keys.get("program.items", ""),
                    lambda: st.decode_program(_prog_nf()),
                    _dump, _load)
        ib, db, syms = _ck("link.sections", keys.get("link.sections", ""),
                           lambda: st.decode_link(_link_nf()),
                           _dump, _load)
        text, _loc = _ck("text.bin", keys.get("text.bin", ""),
                         lambda: assemble_staged(
            items, syms, text_base, runs.get("assemble*", run),
            verbose=verbose), _dump, _load)
        report.append(("assemble*", -1, -1))
        if verbose:
            print(f"    assemble*: decomposed {len(items)} items "
                  f"({fmt_dur(time.time()-t0)})", flush=True)
        text_t = st.bytelist_term(text)
        idata_t, datab_t = st.bytelist_term(ib), st.bytelist_term(db)
        if decompose_pack:
            t0 = time.time()
            img = _ck("image.bin", keys.get("image.bin", ""),
                      lambda: pack_staged(
                          text, ib, db, R.stack_reserve,
                          runs.get("pack*", run), verbose=verbose),
                      lambda p, v: open(p, "wb").write(v),
                      lambda p: open(p, "rb").read())
            report.append(("pack*", -1, -1))
            if verbose:
                print(f"    pack*: decomposed {len(img)}B "
                      f"({fmt_dur(time.time()-t0)})", flush=True)
            report.append(("ckpt", ckpt[0], ckpt[1]))
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

    # stage 4 — pack2Of text idata datab stackres: the image.  A bytes
    # runner decodes the byte-list NF in the kernel — the stage result
    # IS the image; term mode decodes the NF as before.
    img_out = _stage("pack", st.pack2_query_t(
        text_t, idata_t, datab_t, R.stack_reserve))

    img = img_out if isinstance(img_out, bytes) \
        else st._decode_bytecells(img_out)
    if workdir:
        with open(os.path.join(workdir, "image.bin"), "wb") as f:
            f.write(img)
    report.append(("ckpt", ckpt[0], ckpt[1]))
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
    bytes_mode = getattr(run, "is_bytes", False)

    def _enc_q(it, resv=None):
        q = st.encode_query(it, resv)
        # bytes egress: decode_encode's `nf KK` projection moves INSIDE
        # the query so the root NF itself is the byte list — the kernel
        # decodes it natively, no Python _l0_nf/_decode_bytecells
        return app(q, KK) if bytes_mode else q

    def _enc_b(x):
        return x if bytes_mode else st.decode_encode(x)
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
        nfs, _, _ = batch([_enc_q(it) for it in uq])
        for it, nf in zip(uq, nfs):
            uniq[it] = _enc_b(nf)
        n_red += len(uq)
        if verbose:
            print(f"      pass1: {n_red} encodes (1 batch) "
                  f"({fmt_dur(time.time()-t0)})", flush=True)
    else:
        for it in uq:
            uniq[it] = _enc_b(run(_enc_q(it))[0])
            n_red += 1
            if verbose and n_red % 50 == 0:
                print(f"      pass1: {n_red} encodes "
                      f"({fmt_dur(time.time()-t0)})", flush=True)
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
                _enc_q(it, st._appn(
                    _resvmk(), sym_t, loc_t,
                    st.bytelist_term(
                        (base + prep[i][1] + prep[i][2]).to_bytes(
                            4, "little"))))
                for i, it in rel])
            rel_bytes = [_enc_b(nf) for nf in nfs]
            n_red += len(rel)
            if verbose:
                print(f"      pass2: {n_red} encodes (1 batch) "
                      f"({fmt_dur(time.time()-t0)})", flush=True)
        else:
            for i, it in rel:
                e4 = st.bytelist_term(
                    (base + prep[i][1] + prep[i][2]).to_bytes(
                        4, "little"))
                resv_t = st._appn(_resvmk(), sym_t, loc_t, e4)
                rel_bytes.append(
                    _enc_b(run(_enc_q(it, resv_t))[0]))
                n_red += 1
                if verbose and n_red % 50 == 0:
                    print(f"      pass2: {n_red} encodes "
                          f"({fmt_dur(time.time()-t0)})", flush=True)
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

    # bytes-mode runner (io=("stdin","bytes")): r1's results are raw
    # bytes already — dec is identity; a value that re-enters a query
    # as a term (bytes4 intermediates feeding ALIGN512/B4ADD/PADLIST)
    # re-wraps via bytelist_term — construction, not NF decode.
    if getattr(run, "is_bytes", False):
        def r1(q: T):
            return run(q)[0]

        def dec(b) -> bytes:
            return b

        def tm(b) -> T:
            return st.bytelist_term(b)
    else:
        def r1(q: T) -> T:
            return run(q)[0]

        def dec(t: T) -> bytes:
            return st._decode_bytecells(t)

        def tm(t: T) -> T:
            return t

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
    traw = r1(st._appn(K_("_ALIGN512"), tm(lt)))
    iraw = r1(st._appn(K_("_ALIGN512"), tm(li)))
    draw = r1(st._appn(K_("_ALIGN512"), tm(ld)))
    # section VAs — .idata fixed at 0x1000, .data and .text computed
    # (pack2Of's drva/trva lets); .text LAST keeps code size unbounded.
    drva = r1(st._appn(K_("_ALIGN4096"),
                       st._appn(K_("_B4ADD"), b4(0x1000), tm(li))))
    trva = r1(st._appn(K_("_ALIGN4096"),
                       st._appn(K_("_B4ADD"), tm(drva), tm(ld))))
    dptr = r1(st._appn(K_("_B4ADD"), b4(0x200), tm(iraw)))
    tptr = r1(st._appn(K_("_B4ADD"), tm(dptr), tm(draw)))
    iddr = r1(st._appn(K_("_B4ADD"), tm(iraw), tm(draw)))
    img = r1(st._appn(K_("_ALIGN4096"),
                      st._appn(K_("_B4ADD"), tm(trva), tm(lt))))
    u64 = r1(st._appn(K_("_U64"), b4(stackres)))

    def zf(n: int) -> bytes:
        return dec(r1(st._appn(K_("_ZEROFILL"), st.church(n))))

    def pad(len4: T) -> bytes:
        return dec(r1(st._appn(K_("_PADLIST"), len4)))

    sizes = {"lt": lt, "li": li, "ld": ld, "traw": traw,
             "iraw": iraw, "draw": draw, "drva": drva, "trva": trva,
             "dptr": dptr, "tptr": tptr, "iddr": iddr, "img": img}
    sects = {"text": text, "idata": idata, "datab": datab}
    z12 = zf(12)
    chunks = [
        b"MZ", zf(58), struct.pack("<I", 0x40), b"PE\x00\x00",
        struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0, 0x22),
        struct.pack("<HBB", 0x20B, 0, 0),
        dec(traw), dec(iddr), struct.pack("<I", 0),
        dec(trva), dec(trva),
        struct.pack("<Q", 0x140000000),
        struct.pack("<II", 0x1000, 0x200),
        struct.pack("<HHHHHH", 6, 0, 0, 0, 6, 0),
        struct.pack("<I", 0), dec(img),
        struct.pack("<II", 0x200, 0),
        struct.pack("<HH", 3, 0x8100),
        dec(u64),
        struct.pack("<QQQ", 0x1000, 0x100000, 0x1000),
        struct.pack("<II", 0, 16), struct.pack("<II", 0, 0),
        struct.pack("<I", 0x1000), dec(li),
        zf(14 * 8),
        b".idata\x00\x00", dec(li),
        struct.pack("<I", 0x1000), dec(iraw),
        struct.pack("<I", 0x200), z12,
        struct.pack("<I", 0x40000040),
        b".data\x00\x00\x00", dec(ld),
        dec(drva), dec(draw), dec(dptr), z12,
        struct.pack("<I", 0xC0000040),
        b".text\x00\x00\x00", dec(lt),
        dec(trva), dec(traw), dec(tptr), z12,
        struct.pack("<I", 0x60000020),
        zf(0x200 - 448),
        idata, pad(tm(li)), datab, pad(tm(ld)), text, pad(tm(lt)),
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
    imps, slots, base, sr = ("ExitProcess",), (("x", 8),), \
        target_pe64.text_rva(("ExitProcess",), (("x", 8),)), 64 << 20
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
    img_out, s, n = runs.get("pack", run)(st.pack2_query_t(
        text_t, app(app(link_nf, KK), KK),
        app(app(link_nf, KK), KI), sr))
    report.append(("pack", s, n))
    return (img_out if isinstance(img_out, bytes)
            else st._decode_bytecells(img_out)), report


def _mini_oracle() -> bytes:
    _ib, _db, syms = st.python_link(("ExitProcess",), (("x", 8),))
    _text, _lm = st.python_assemble(
        st.ASM_LINK, syms,
        target_pe64.text_rva(("ExitProcess",), (("x", 8),)))
    return st.python_pack(_text, ("ExitProcess",), (("x", 8),),
                          64 << 20)


def _nf_cons(h: T, t: T) -> T:
    """`_CONS h t` spelled as its fixed kernel NF —
    K (D ((B (C (D ((B (C I)) (K h)))) (K t)))) — the exact spine
    _cell_parts dereferences (verified: structural path returns
    (h, t)).  S-free, so it is the kernel-space NF directly."""
    return app(KK, app(D, app(app(B, app(C, app(D, app(
        app(B, app(C, I)), app(KK, h))))), app(KK, t))))


def _g16_egress() -> bool:
    """G16 — native byte egress: the io=("stdin","bytes") IR kernel
    decodes each root's byte-list NF itself and frames raw bytes
    ([u32le len][bytes] per root, root order kept) — Python never
    rebuilds the byte-list term.

    Corpus: kernel-space NF roots (cons spines built directly — the
    naive kernel's own reduction of a >512B bytelist term exceeds the
    2GB arena before egress even runs, so big payloads arrive as NF
    roots, which is exactly the egress contract) plus small QUERY
    roots the exe reduces first.  Expected = graph.lo NF ->
    _decode_bytecells; cross-checked against the term-mode kernel's NF
    lines byte-for-byte.  Negative legs: non-byte-list NF -> exit5,
    truncated PIR -> exit3, fuel -> exit2."""
    ok = True
    exe_t = ir_exe_for(seed.Realization())
    exe_b = ir_exe_for(seed.Realization(io=("stdin", "bytes")))

    # kernel-space byte-cell NFs: the term-mode kernel itself produces
    # them — depack expands S into the ds tree, so the emitted NF is
    # the shape emit_bytes sees (no S leaves anywhere)
    cp = subprocess.run(
        [exe_t],
        input=st.pack_ir(*[st.byte_term(v) for v in range(256)]),
        capture_output=True, timeout=600)
    if cp.returncode != 0:
        print(f"FAIL egress setup: byte-cell batch "
              f"rc={cp.returncode} {cp.stderr[:200]!r}", flush=True)
        return False
    byte_nf = [seed._parse_native_out(ln)
               for ln in cp.stdout.decode().splitlines()]

    def nf_list(bs):
        t = KK
        for b in reversed(bs):
            t = _nf_cons(byte_nf[b], t)
        return t

    corpus = [
        b"", b"\x00", b"\xff", bytes(range(256)),
        bytes(((i * 31) ^ (i >> 3)) & 0xFF for i in range(1024)),
        bytes(((i * 131) ^ (i >> 5)) & 0xFF for i in range(4096)),
    ]
    roots = [nf_list(bs) for bs in corpus]
    # query roots: the exe reduces then decodes (a small bytelist and
    # real encodeOf projections — the assemble* seam shape)
    qroots = [st.bytelist_term(b"\x01\x02\x03"),
              st.bytelist_term(bytes(range(32))),
              app(st.encode_query(("i", "ret")), KK),
              app(st.encode_query(
                  ("i", "mov_m8_r8", ("m", "rsi", 0), "al")), KK)]
    all_roots = roots + qroots

    t0 = time.time()
    wants = [st._decode_bytecells(_graph_run(q)[0]) for q in all_roots]
    good = wants[:len(corpus)] == corpus
    print(f"{'OK ' if good else 'FAIL'} egress nf corpus sanity: "
          f"graph decode == payloads", flush=True)
    ok = ok and good

    blob = st.pack_ir(*all_roots)
    brun = make_bytes_runner(exe_b)
    got, steps, alloc = brun.batch(all_roots)
    good = list(got) == wants
    ok = ok and good
    print(f"{'OK ' if good else 'FAIL'} egress corpus: "
          f"{len(all_roots)} roots, {sum(len(b) for b in got)}B, "
          f"steps={steps} alloc={alloc} dec={brun.stats['dec']} "
          f"(graph {fmt_dur(time.time()-t0)})", flush=True)

    # term-mode kernel on the same blob: NF lines decoded by Python
    # must equal the framed bytes — the two egress modes agree
    cp = subprocess.run([exe_t], input=blob, capture_output=True,
                        timeout=600)
    want_t = [st._decode_bytecells(seed._parse_native_out(ln))
              for ln in cp.stdout.decode().splitlines()]
    good = cp.returncode == 0 and want_t == list(got)
    ok = ok and good
    print(f"{'OK ' if good else 'FAIL'} egress vs term-mode: "
          f"byte-identical across {len(all_roots)} roots", flush=True)

    def _rc(exe, data):
        return subprocess.run([exe], input=data,
                              capture_output=True, timeout=600)

    # non-byte-list NF (bare I) -> exit5; the runner must refuse too
    bad = _rc(exe_b, st.pack_ir(I))
    good = bad.returncode == 5
    try:
        brun(I)
        good = False
    except RuntimeError:
        pass
    ok = ok and good
    print(f"{'OK ' if good else 'FAIL'} egress not-a-list: "
          f"rc={bad.returncode} (want 5), runner raised",
          flush=True)

    # truncated packed-IR stream -> exit3
    bad = _rc(exe_b, blob[:-3])
    good = bad.returncode == 3
    ok = ok and good
    print(f"{'OK ' if good else 'FAIL'} egress truncated PIR: "
          f"rc={bad.returncode} (want 3)", flush=True)

    # fuel=0 kernel: any reducing root hits the per-root cap -> exit2
    exe_f = ir_exe_for(seed.Realization(io=("stdin", "bytes"), fuel=0))
    bad = _rc(exe_f, st.pack_ir(app(I, I)))
    good = bad.returncode == 2
    ok = ok and good
    print(f"{'OK ' if good else 'FAIL'} egress fuel cap: "
          f"rc={bad.returncode} (want 2)", flush=True)
    return ok


def main() -> int:
    if "--help" in sys.argv[1:]:
        print("usage: emit_chain.py [--on-exe] [--win64] "
              "[--insns-on-exe] [--ir] [--cold] [--egress]")
        return 0
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
          f"{len(got)}B == {len(want_mini)}B ({fmt_dur(time.time()-t0)}) "
          + "  ".join(f"{n}:{s}st" for n, s, _ in report), flush=True)

    if "--on-exe" in sys.argv[1:]:
        exes = {"pe": seed._exe_for(seed.Realization())}
        try:
            import routines_c
            exes["c"] = routines_c._exe_for(
                seed.Realization(abi="hosted"))
        except Exception as e:                       # noqa: BLE001
            print(f"SKIP c-kernel ({e})")
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
                  f"({fmt_dur(time.time()-t0)})  {stages}", flush=True)

    # keyed-checkpoint refusal: the same R twice must give identical
    # keys, a different R must give a different PROG key, and a file
    # planted under another realization's key must NOT be found.
    with tempfile.TemporaryDirectory() as wd:
        ka = _ck_keys(seed.Realization(), rts.IMPORTS, rts.DATA_SLOTS,
                      target_pe64.text_rva(rts.IMPORTS, rts.DATA_SLOTS))
        kb = _ck_keys(seed.Realization(fuel=7), rts.IMPORTS,
                      rts.DATA_SLOTS,
                      target_pe64.text_rva(rts.IMPORTS, rts.DATA_SLOTS))
        same = ka == _ck_keys(
            seed.Realization(), rts.IMPORTS, rts.DATA_SLOTS,
            target_pe64.text_rva(rts.IMPORTS, rts.DATA_SLOTS))
        with open(os.path.join(wd, f"text.bin.{ka['text.bin']}"),
                  "wb") as f:
            f.write(b"stale")
        stale_hit = os.path.exists(
            os.path.join(wd, f"text.bin.{kb['text.bin']}"))
        good = (ka["program.items"] != kb["program.items"]
                and same and not stale_hit)
        ok = ok and good
        print("ok keyed ckpt refuses stale" if good
              else "FAIL keyed ckpt accepted stale", flush=True)

    if "--win64" in sys.argv[1:]:
        # pack's live set is image-construction-sized on LO (the JOIN
        # spine holds all section intermediates); decomposed chunks are
        # small enough for the default LO runner.  cd+compact is the
        # monolithic alternative ("pack": _graph_cd_run).
        legs = [("default", seed.Realization()),
                ("fuse_s", seed.Realization(fuse_s=True))]
        if "--peephole" in sys.argv[1:]:
            # G9i/G10 leg: staged peepholeOf vs the seed route's
            # opt_peephole — the images must be byte-equal.
            legs.append(("peephole",
                         seed.Realization(peephole=True)))
        for tag, R in legs:
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
                    # --cold bypasses the NF cache too: the release gate
                    # re-derives every reduction, not just the files
                    _nf_tmp = (tempfile.TemporaryDirectory()
                               if "--cold" in sys.argv[1:] else None)
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
                        cache_dir=(_nf_tmp.name if _nf_tmp
                                   else os.path.join(_HOST, "emit_work",
                                                     "nf_cache", tag)),
                        fuse_s=R.fuse_s)
                    # byte-producing seams ride the egress kernel
                    # (io=("stdin","bytes")): the emitted exe decodes
                    # each byte-list NF itself and the wire carries
                    # [u32le len][bytes] frames — no Python rebuild.
                    bytes_runner = make_bytes_runner(
                        seed._exe_for(
                            seed.Realization(fuel=2_000_000,
                                             fuse_s=R.fuse_s,
                                             audit=_AUDIT,
                                             io=("stdin", "bytes")),
                            tc=toolchain.by_name(
                                "native.x86_64.pe.ir")),
                        workers=os.cpu_count() or 4,
                        cache_dir=(None if _nf_tmp
                                   else os.path.join(
                                       _HOST, "emit_work",
                                       "bytes_cache", tag)))
                    sr["assemble*"] = bytes_runner
                    sr["pack*"] = bytes_runner
                    if "--ir-redir" in sys.argv[1:]:
                        # W3: reclaim="redirect" kernel — consume-on-
                        # collapse + persist zone.  program/link ride
                        # the native exe: the shared-input-redex class
                        # that kept them on graph.lo collapses once.
                        # NFs are byte-identical to naive (84506 steps
                        # on `program`, = graph.lo), ~5x slower per
                        # step than graph.lo — memory is bounded
                        # instead of >48GB.
                        red_runner = make_ir_runner(
                            seed._exe_for(
                                seed.Realization(fuel=2_000_000,
                                                 fuse_s=R.fuse_s,
                                                 reclaim="redirect",
                                                 audit=_AUDIT),
                                tc=toolchain.by_name(
                                    "native.x86_64.pe.ir")),
                            workers=os.cpu_count() or 4,
                            cache_dir=(None if _nf_tmp
                                       else os.path.join(
                                           _HOST, "emit_work",
                                           "nf_cache", tag + "red")),
                            fuse_s=R.fuse_s)
                        sr["program"] = red_runner
                        sr["link"] = red_runner
                        # the peephole item runner stays on the naive
                        # exe even under --ir-redir: per-item calls
                        # are small bounded terms (the deep-fold OOM
                        # profile doesn't apply) — redirect's ~250
                        # steps/s is pure cost there.
                    # else program/link stay on graph.lo: on the naive
                    # exe they blow a 48GB arena — reclaim="none"
                    # retains every redex forever; --ir-redir is the
                    # consume-on-collapse leg.
                else:
                    sr["assemble*"] = make_exe_runner(
                        seed._exe_for(seed.Realization(
                            fuel=2_000_000, fuse_s=R.fuse_s)))
            t0 = time.time()
            want = emit_native("native.x86_64.pe", R)
            if "--cold" in sys.argv[1:]:
                # release gate: every staged stage re-derived — a fresh
                # workdir means zero checkpoint reuse by construction
                _tmp = tempfile.TemporaryDirectory()
                wd = _tmp.name
            else:
                _tmp = None
                wd = os.path.join(_HOST, "emit_work", tag)
                os.makedirs(wd, exist_ok=True)
            got, report = emit_image(R, decompose_asm=True,
                                     decompose_pack=True,
                                     stage_runs=sr, workdir=wd,
                                     label="native.x86_64.pe")
            del _tmp
            good = got == want
            ok = ok and good
            stages = "  ".join(f"{n}:{s}st/{a}n" for n, s, a in report
                               if n != "ckpt")
            ck = next((r for r in report if r[0] == "ckpt"),
                      ("ckpt", 0, 0))
            print(f"{'OK ' if good else 'FAIL'} emit_chain {tag}: "
                  f"{len(got)}B == {len(want)}B  "
                  f"({fmt_dur(time.time()-t0)})  {stages}  "
                  f"ckpt hits={ck[1]}/{ck[1] + ck[2]}", flush=True)
            if not good:
                k = next((i for i, (a, b) in enumerate(zip(got, want))
                          if a != b), min(len(got), len(want)))
                print(f"  first diff at {k}: "
                      f"{got[k:k+8].hex()} vs {want[k:k+8].hex()}")

    if "--egress" in sys.argv[1:]:
        ok = _g16_egress() and ok

    print(f"{'OK' if ok else 'FAIL'} emit_chain "
          f"(seed emits its own host)")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
