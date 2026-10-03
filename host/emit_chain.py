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
import struct
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
    _graph_run.calls += 1          # unified-runtime gate counts these
    g = Graph()
    nf_i, steps = g.reduce(g.import_tree(t), fuel=fuel,
                           compact_every=compact_every)
    return g.export_tree(nf_i), steps, g.alloc_count()


_graph_run.calls = 0
_graph_run.kind = "graph.lo"       # manifest runner label (oracle)


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
                   fuse_s: bool = False,
                   pinned: Optional[Dict[int, tuple]] = None
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
            _, keys = st.pack_ir_keyed(*qs, pinned=pinned)
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
            blobs = [st.pack_ir(*[qs[i] for i in c],
                                pinned=pinned)
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
    run.kind = "exe.term"          # manifest runner label
    run.exe = exe
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
                      cache_dir: Optional[str] = None,
                      pinned: Optional[Dict[int, tuple]] = None
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
            _, keys = st.pack_ir_keyed(*qs, pinned=pinned)
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
            blobs = [st.pack_ir(*[qs[i] for i in c],
                                pinned=pinned) for c in chunks]
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
    run.kind = "exe.bytes"                 # manifest runner label
    run.exe = exe
    return run


def make_blob_runner(exe: str, timeout: int = 3600,
                     workers: int = 1,
                     pinned: Optional[Dict[int, tuple]] = None
                     ) -> Callable[[T], Tuple[bytes, int, int]]:
    """Packed-IR runner over the IR-egress kernel (Realization
    io=("stdin","ir")): each root's reduced NF leaves the kernel as
    its own PIR blob — the stage's output IS the next stage's input,
    no term rebuild in between.  Wire out is one
    [u32le len][PIR blob] frame per root, order preserved.

    run(q) -> (blob, steps, alloc) where blob is a single-root PIR
    stream; .batch(qs) -> ([blob], steps, alloc).  .blobs marks the
    runner so stage seams ingest frames as content-addressed IR
    artifacts (digest_ir_blob keys them) instead of decoding terms.
    Frames are validated structurally — malformed blobs raise."""
    import concurrent.futures
    stats = {"dec": 0}

    def _one(blob: bytes, expect: int) -> Tuple[List[bytes], int, int]:
        cp = subprocess.run([exe], input=blob,
                            capture_output=True, timeout=timeout)
        m = re.search(rb"steps=(\d+) alloc=(\d+)", cp.stderr)
        if cp.returncode != 0:
            raise RuntimeError(
                f"exe ir batch failed rc={cp.returncode} "
                f"stderr={cp.stderr!r} "
                f"(2=fuel, 3=bad IR, 4=alloc — never a silent success)")
        frames = _bytes_frames(cp.stdout, expect)
        for f in frames:
            st.digest_ir_blob(f)          # header/root/forward-ref check
        return (frames, int(m.group(1)) if m else -1,
                int(m.group(2)) if m else -1)

    def batch(qs: List[T]) -> Tuple[List[bytes], int, int]:
        if not qs:
            return [], 0, -1
        n = min(max(1, workers), len(qs))
        chunks = [list(range(j, len(qs), n)) for j in range(n)]
        blobs = [st.pack_ir(*[qs[i] for i in c],
                            pinned=pinned) for c in chunks]
        if n <= 1:
            res = [_one(blobs[0], len(chunks[0]))]
        else:
            with concurrent.futures.ThreadPoolExecutor(n) as pool:
                res = list(pool.map(
                    _one, blobs, [len(c) for c in chunks]))
        outs: List[Optional[bytes]] = [None] * len(qs)
        steps = alloc = 0
        for c, (fs, s, a) in zip(chunks, res):
            if s > 0:
                steps += s
            if a > 0:
                alloc += a
            for i, b in zip(c, fs):
                outs[i] = b
        return [b for b in outs if b is not None], steps, alloc

    def run(t: T) -> Tuple[bytes, int, int]:
        outs, s, a = batch([t])
        return outs[0], s, a
    run.batch = batch
    run.blobs = True                     # stage seams ingest PIR frames
    run.stats = stats
    run.kind = "exe.ir"                  # manifest runner label
    run.exe = exe
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


# Phase-4b evidence: decode_* calls on the emit path.  Each entry is
# a Python semantic crossing the plan wants gone — the manifest
# records per-emit counts so the remaining seams are auditable data,
# and gates can refuse regressions (bytecells is already zero under
# the byte-egress runner; frag/bytesyms/program wait on emit_ir —
# the kernel-side packed egress routine).
_DECODE_COUNT: Dict[str, int] = {"frag": 0, "program": 0,
                                 "bytesyms": 0, "bytecells": 0}


def _decode(kind: str, fn, *a):
    _DECODE_COUNT[kind] += 1
    return fn(*a)


def _dec_delta(dec0: dict) -> dict:
    return {k: _DECODE_COUNT[k] - dec0.get(k, 0)
            for k in _DECODE_COUNT}


def _blob_tok(key: str) -> str:
    """Blob filename token for a pin key — the manifest references
    blobs by this so the directory listing IS the dep store."""
    return "b" + hashlib.sha256(key.encode()).hexdigest()[:24]


class BlobStore:
    """Content-addressed packed-IR constants — workdir/blobs/<tok>.ir.

    `pin_named(key, t)`: the key names the INPUTS that generated t
    (builder source + pinned axes — see st.routine_pin_key /
    st.const_pin_key).  A hit loads the stored node stream and
    registers id(t) for splice-packing — the pack walk that produced
    the blob is never repeated.  A miss packs once and writes the
    blob + a .meta sidecar (root digest, key) for the next process.

    Trust regime: the same content-keyed trust the _ck artifacts
    already use — a stale blob can only exist under a rotated key
    (regeneration with unchanged inputs is deterministic), and even
    a corrupt blob can't smuggle: emitted digests derive from the
    actual blob content, so downstream checkpoint keys describe
    exactly what was reduced.

    `pin(t)` is the ephemeral form — same registration, no disk;
    for constants only reused inside one emit (symtab terms and
    friends are deliberately NOT pinned: they recur across multi-
    root streams where pack-time dedup is the better sharing).

    The blob format is exactly the packed-IR file a kernel depacks —
    blobs/ is a query-fragment store readable by anything that
    speaks IR (the .plex v3 BYTES payload later).
    """

    def __init__(self, dir: Optional[str] = None):
        self.dir = dir
        self.pins: Dict[int, tuple] = {}
        self.hits = 0
        self.misses = 0
        if dir:
            os.makedirs(dir, exist_ok=True)

    def pin_named(self, key: str, t: T) -> str:
        tok = _blob_tok(key)
        path = os.path.join(self.dir, tok + ".ir") if self.dir \
            else None
        if path and os.path.exists(path):
            with open(path + ".meta") as f:
                meta = json.load(f)
            with open(path, "rb") as f:
                blob, nn, root = st.unpack_ir_pin(f.read())
            self.pins[id(t)] = (blob, nn, root,
                                bytes.fromhex(meta["digest"]), t)
            self.hits += 1
            return meta["digest"][:32]
        blob, root, rd = st.pin_term(t, self.pins)
        if path:
            with open(path, "wb") as f:
                f.write(struct.pack("<IIII", st.IR_MAGIC,
                                    st.IR_VERSION,
                                    len(blob) // 9, 1))
                f.write(struct.pack("<I", root))
                f.write(blob)
            with open(path + ".meta", "w") as f:
                json.dump({"digest": rd.hex(), "key": key,
                           "created_utc": time.strftime(
                               "%Y-%m-%dT%H:%M:%SZ", time.gmtime())},
                          f)
        self.misses += 1
        return rd.hex()[:32]

    def pin(self, t: T) -> str:
        """Ephemeral pin — register for splice, no disk."""
        _b, _r, rd = st.pin_term(t, self.pins)
        return rd.hex()[:32]

    def blob_term(self, data: bytes) -> T:
        """A stored/kernel-emitted single-root PIR blob as a query
        argument: returns a placeholder T whose pin entry carries the
        blob's node bytes + canonical root digest — pack splices it,
        no term is ever built.  The placeholder is a VAR leaf on
        purpose: an unpinned pack would encode a var record that the
        depacker maps to a hole — loud failure, not silent splice.
        Multi-root frames are per-root blobs already (emit_ir frames
        nr=1 each), so the single-root pin shape holds."""
        ph = st.T(st.K.VAR, n=0)
        self.pins[id(ph)] = st.blob_pin_entry(data, ph)
        return ph

    def digest_of(self, key: str, build) -> str:
        """Root digest of a lazily-built term, content-addressed by
        `key`.  Disk hit: reads the .meta sidecar only — no term is
        built, no walk is paid (the key must cover everything that
        determines the term: builder source, axes, pass material).
        Miss: builds via thunk, pins, stores, returns the digest."""
        tok = _blob_tok(key)
        mp = os.path.join(self.dir, tok + ".ir.meta") if self.dir \
            else None
        if mp and os.path.exists(mp):
            with open(mp) as f:
                self.hits += 1
                return json.load(f)["digest"][:32]
        self.misses += 1
        return self.pin_named(key, build())


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


def _pass_src(passes) -> str:
    """Key material for a per-routine pass chain — the pass names plus
    the generating source of any term built from code, so editing the
    pass invalidates the fragments that ran it."""
    parts = list(passes)
    if "peephole" in passes:
        parts.append(st._peephole_pass_src())
    return "|".join(parts)


def _ck_keys(R: seed.Realization, imports, slots,
             text_base: int, host_name: str = "",
             routines=None, passes=(), fixed=None,
             ir_ctx: bool = False,
             pinned: Optional[Dict[int, tuple]] = None,
             store=None) -> Dict[str, str]:
    """Content keys for the checkpointed artifacts, keyed on the stage
    INPUTS (the packed-IR digest of each stage's root term, the
    realization knobs that change it, and the producing code's source)
    — a stale file can't survive an input or code change.  Keys carry
    a readable <triplet>.<strategy>. prefix so `ls emit_work` says who
    built what; the 16-hex suffix is still the content proof.

    Per-routine `program.<name>` keys are the query-engine
    invalidation unit: editing one builder changes one digest, so one
    fragment re-reduces while the rest hit.  `program.items` keys on
    the joined routine keys (plus the whole-program peephole marker
    when set — that pass runs on the frag-list, after the per-frag
    stage, so it doesn't disturb the per-frag keys)."""
    routines = rts.ROUTINES if routines is None else routines
    pre = _ck_label(R, host_name)
    psrc = _pass_src(passes)
    keys: Dict[str, str] = {}
    qdigs: Dict[str, str] = {}      # stage -> query digest|blob tok
    rkeys = []
    for name in routines:
        # the query's root digest IS the content key — via the blob
        # store a warm emit reads it from the .meta sidecar and never
        # rebuilds the term.  (Ambient-state drift a builder could
        # commit unseen by source hash is the residual risk — the
        # trade is recorded in decision 052.)
        qkey = "|".join((
            "q.program." + name, pre,
            st.routine_pin_key(name, fixed, ir_ctx),
            _src(st.routine_query),
            "fuse_s=%d" % R.fuse_s, psrc,
            _src(rts._BUILDERS[name])))
        if store is not None:
            rdig = store.digest_of(
                qkey, lambda name=name: st.routine_query(
                    name, R, passes, fixed=fixed, ir_ctx=ir_ctx))
        else:
            rdig = st.pack_ir_keyed(
                st.routine_query(name, R, passes, fixed=fixed,
                                 ir_ctx=ir_ctx), pinned=pinned)[1][0]
        rk = _stage_key(pre, rdig,
                        _src(rts._BUILDERS[name]), psrc,
                        _src(st.decode_frag))
        keys[f"program.{name}"] = f"{pre}.{rk}"
        qdigs[f"program.{name}"] = rdig + "|" + _blob_tok(qkey)
        rkeys.append(rk)
    prog = _stage_key(pre, *rkeys,
                      "peephole=%d" % getattr(R, "peephole", False),
                      _src(st.decode_program))
    if store is not None:
        # the digest cache key covers the section-constant source,
        # the query constructor, and the arg VALUES (imports/slots/
        # drva) — a generator edit or a different symtab rotates it.
        ik = "|".join(("q.idata", pre, _src(st.idata_query),
                       repr(list(imports)),
                       st.const_pin_key(
                           "idata.%d" % len(imports),
                           st.idata_src(len(imports)))))
        dk = "|".join(("q.data", pre, _src(st.data_query),
                       repr(list(slots)),
                       repr(target_pe64.data_rva(imports)),
                       st.const_pin_key(
                           "data.%d" % len(slots),
                           st.data_src(len(slots)))))
        idig = store.digest_of(ik, lambda: st.idata_query(imports))
        ddig = store.digest_of(
            dk, lambda: st.data_query(
                slots, target_pe64.data_rva(imports)))
        ldig = idig + "|" + ddig
        qdigs["link.sections"] = (
            idig + "|" + _blob_tok(ik) + ";" +
            ddig + "|" + _blob_tok(dk))
    else:
        ldig = "|".join(st.pack_ir_keyed(
            st.idata_query(imports),
            st.data_query(slots, target_pe64.data_rva(imports)),
            pinned=pinned)[1])
    link = _stage_key(pre, ldig,
                      _src(st.decode_bytesyms),
                      _src(link_staged))
    text = _stage_key(prog, link, "base=%d" % text_base,
                      _src(assemble_staged))
    image = _stage_key(text, link, "stackres=%d" % R.stack_reserve,
                       _src(pack_staged))
    keys.update({"program.items": f"{pre}.{prog}",
                 "link.sections": f"{pre}.{link}",
                 "text.bin": f"{pre}.{text}",
                 "image.bin": f"{pre}.{image}"})
    return keys, qdigs


def _runner_label(r) -> str:
    """Manifest runner identity — 'exe.term:<exe>' / 'exe.bytes:<exe>'
    / 'graph.lo'.  The label is provenance, not a resolution handle:
    replay re-enters emit_image, which re-resolves runners."""
    if r is None:
        return "?"
    kind = getattr(r, "kind", None) or getattr(
        r, "__name__", type(r).__name__)
    exe = getattr(r, "exe", None)
    return f"{kind}:{os.path.basename(exe)}" if exe else str(kind)


# stage name -> the `runs` slot that serves it (runner resolution as
# data — the manifest records the resolved identity per stage)
_STAGE_SLOT = {"program.items": "program", "link.sections": "link",
               "text.bin": "assemble*", "image.bin": "pack*"}


def _stage_deps(name: str, keys: Dict[str, str]) -> List[str]:
    """DAG edges implicit in the key chain, made explicit."""
    if name == "program.items":
        return sorted(n for n in keys
                      if n.startswith("program.") and n != name)
    return {"text.bin": ["program.items", "link.sections"],
            "image.bin": ["text.bin", "link.sections"],
            }.get(name, [])


def _write_manifest(workdir: str, R: seed.Realization, label: str,
                    routines, keys: Dict[str, str],
                    qdigs: Dict[str, str], runs: dict, run,
                    pack_slot: str,
                    decodes: Optional[dict] = None,
                    img: Optional[bytes] = None, rt=None) -> dict:
    """Phase-4 stage DAG as data: workdir/manifest.json names every
    stage's artifact (content key), its query blob ref, its resolved
    runner, and its deps — replayable addressing, not a code path."""
    slot = dict(_STAGE_SLOT)
    slot["image.bin"] = pack_slot
    order = [f"program.{n}" for n in routines] + [
        "program.items", "link.sections", "text.bin", "image.bin"]
    stages = []
    for name in order:
        if name not in keys:
            continue
        q = qdigs.get(name)
        stages.append({
            "name": name,
            "artifact": f"{name}.{keys[name]}",
            "key": keys[name],
            "runner": _runner_label(
                runs.get(slot.get(name, "program"), run)),
            "deps": _stage_deps(name, keys),
            # "digest|blobtok" — the blob file that IS the query
            "queries": ([{"digest": d, "blob": f"blobs/{t}.ir"}
                         for d, t in (p.split("|")[:2]
                                      for p in q.split(";"))]
                        if q else []),
        })
    man = {
        "format": "plex.stage-manifest/1",
        "label": label,
        "realization": repr(R),
        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ",
                                     time.gmtime()),
        # remaining Python semantic crossings this emit — the audit
        # trail until emit_ir removes them (Phase 4c)
        "decodes": decodes,
        "stages": stages,
    }
    p = os.path.join(workdir, "manifest.json")
    with open(p, "w") as f:
        json.dump(man, f, indent=1)
    if img is not None:
        _write_bundle(workdir, man, img, R, rt)
    return man


def _write_bundle(workdir: str, man: dict, img: bytes,
                  R: seed.Realization, rt) -> str:
    """Phase-6 .plex v3 archive beside manifest.json: the stage DAG,
    query blob refs, realization fields, the routines record's caps,
    decode evidence, and the image payload — one ingestible unit."""
    import plex_bundle as pb
    rname = rt.name if rt is not None else "x86_64.win64.lo"
    comp = toolchain.components()["routines"].get(rname)
    caps = dict(comp.data).get("caps") if comp is not None else None
    real = {k: str(v) for k, v in vars(R).items()}
    real["routines"] = rname
    secs = pb.manifest_sections(man, image=img, caps=caps,
                                realization=real)
    data = pb.pack_bundle(secs)
    bundle = pb.read_bundle(data)          # writer self-check
    if caps is not None:
        errs = pb.check_bundle_caps(bundle, caps)
        if errs:
            raise toolchain.NotRealized(
                f"bundle caps exceed record {rname}: {errs[0]}")
    p = os.path.join(workdir, "image.plex")
    with open(p, "wb") as f:
        f.write(data)
    return p


# ---------------------------------------------------------------------------
# Phase 7a — the emit program as data.
#
# The whole emit is one reducible term: program_rt's record-driven fold
# feeds linkOf's projections into assembleOf and pack2Of, all as
# UNREDUCED queries.  Python's only roles here are term construction
# (data assembly) and packing (serialization) — every β-step of the
# emit runs on the consuming host.  This is the POC shape: a single
# root; the staged-DAG decomposition (stage queries as roots, DEPS
# rows as scheduling data) is the Phase-8 final shape.


def _emit_layout(R: seed.Realization, routines=None, rt=None,
                 imports=None, slots=None,
                 text_base: Optional[int] = None):
    """(routines, imports, slots, text_base, fixed) — the emit's
    layout resolution, shared by the term composition (_emit_queries)
    and the staged schedule (emit_frames staged=True): rt.names_for
    picks the R-specialized routine set, rt.data_slots sizes .data
    per realization, `fixed` carries the non-program axes into the
    program queries."""
    if rt is not None:
        if R.order not in rt.orders:
            raise toolchain.NotRealized(
                f"emit: order={R.order!r} not in {rt.orders}")
        if R.io not in rt.ios:
            raise toolchain.NotRealized(
                f"emit: io={R.io!r} not realized by {rt.name}")
        if routines is None:
            nf = getattr(rt, "names_for", None)
            routines = nf(R) if nf else rt.routines
        if imports is None:
            imports = rt.imports
        if slots is None:
            slots = rt.data_slots(R) if callable(rt.data_slots) \
                else rt.data_slots
    imports = rts.IMPORTS if imports is None else imports
    slots = rts.DATA_SLOTS if slots is None else slots
    routines = rts.ROUTINES if routines is None else routines
    if text_base is None:
        text_base = target_pe64.text_rva(imports, slots)
    _d = seed.Realization()
    _prog_axes = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
                  "node_bytes", "stack_reserve", "peephole", "dialect"}
    fixed = {k: getattr(R, k) for k in vars(_d) if k not in _prog_axes}
    return routines, imports, slots, text_base, fixed


def _emit_queries(R: seed.Realization,
                  routines=None,
                  passes: Tuple[str, ...] = (),
                  rt=None,
                  imports=None,
                  slots=None,
                  text_base: Optional[int] = None,
                  prog: Optional[T] = None
                  ) -> Tuple[T, T]:
    """(link_query, assemble_query) for the emit — the shared
    composition used by emit_term (monolithic, the semantic form)
    and emit_frames (scheduled roots, the executable form)."""
    if getattr(R, "peephole", False):
        raise toolchain.NotRealized(
            "emit_term: peephole's fixpoint is a seamed per-item "
            "runner loop — it has no single-term form")
    routines, imports, slots, text_base, fixed = _emit_layout(
        R, routines, rt, imports, slots, text_base)
    link_q = st.link_query(imports, slots)
    prog_q = prog if prog is not None else st.program_query_rt(
        routines, R, passes, fixed=fixed)
    asm_q = st.assemble_query_t(prog_q, app(link_q, KI), text_base)
    return link_q, asm_q


def emit_term(R: seed.Realization,
              routines=None,
              passes: Tuple[str, ...] = (),
              rt=None,
              imports=None,
              slots=None,
              text_base: Optional[int] = None,
              prog: Optional[T] = None) -> T:
    """`pack2Of (assembleOf program (linkOf .. (K I))) ..` — the full
    emit chain as one term, zero Python reduction inside: the
    emit program's SEMANTIC form.  Executable form is emit_frames —
    pack2's concat-spine live set is the documented wall (>4min even
    at 280B of sections; the chunked decompose exists for it), so the
    single root is the equality oracle, not the schedule."""
    link_q, asm_q = _emit_queries(R, routines, passes, rt, imports,
                                  slots, text_base, prog)
    return st.pack2_query_t(app(asm_q, KK),
                            app(app(link_q, KK), KK),
                            app(app(link_q, KK), KI),
                            R.stack_reserve)


def _parse_frames(buf: bytes) -> List[bytes]:
    """`[u32le len][payload]` frames -> payload list (root order)."""
    out, pos = [], 0
    while pos + 4 <= len(buf):
        ln = struct.unpack_from("<I", buf, pos)[0]
        if pos + 4 + ln > len(buf):
            raise toolchain.NotRealized(
                f"frame stream truncated: need {ln} at {pos}")
        out.append(buf[pos + 4:pos + 4 + ln])
        pos += 4 + ln
    if pos != len(buf):
        raise toolchain.NotRealized(
            f"frame stream: {len(buf) - pos} trailing bytes")
    return out


def _run_stream(exe: str, roots: List[T],
                pinned: Optional[dict] = None,
                timeout: int = 600) -> Tuple[List[bytes], str]:
    """Pack roots as one PIR stream -> run the kernel -> egress
    frames.  Returns (frames, stderr) — rc != 0 refuses."""
    data = st.pack_ir(*roots, pinned=pinned)
    p = subprocess.run([exe], input=data, capture_output=True,
                       timeout=timeout)
    if p.returncode != 0:
        raise toolchain.NotRealized(
            f"emit stream refused: rc={p.returncode} "
            f"{p.stderr[:160]!r}")
    return _parse_frames(p.stdout), p.stderr.decode("utf-8",
                                                    "replace")


def emit_frames(R: seed.Realization,
                routines=None,
                passes: Tuple[str, ...] = (),
                rt=None,
                imports=None,
                slots=None,
                text_base: Optional[int] = None,
                prog: Optional[T] = None,
                exe: Optional[str] = None,
                pinned: Optional[dict] = None,
                timeout: int = 600,
                staged: bool = False,
                store=None) -> Tuple[bytes, dict]:
    """The emit program EXECUTED on the emitted host: packed streams
    of bounded roots, kernel does every β-reduction, Python
    constructs terms and splices bytes.

    Unstaged (mini scale): stream A = section bodies —
    [link·KK·KK, link·KK·KI, asm·KK]; the persist zone pays link
    once across roots (measured: 548K steps / 1.9s for mini
    link+asm in one stream).  At real scale the monolithic asm root
    is OOM-class (measured rc=4 at 48GB arena — bump-allocation has
    no intra-root GC), so `staged=True` decomposes the same stages:

    - program: per-routine frag queries -> items (term-construction
      enumeration; `prog=` fraglists enumerate seed-side);
    - link: link_staged blob seam — section bytes via bytes roots,
      the merged symtab a PIR blob, never decoded Python-side;
    - assemble: assemble_staged — per-item encodeOf roots as batched
      streams (the documented arena-boundary decomposition);
    - pack: stream B — the pack_staged recipe's derived chunks as
      roots (ALIGN512/B4ADD/U64/ZEROFILL/PADLIST numerals).

    Python's residue: enumeration/bookkeeping/splice — boundary
    metadata + moving the file.  Returns (image_bytes, evidence) —
    evidence carries per-stream stderr stats and the decode-crossing
    counts for the gate's provenance trail."""
    if exe is None:
        exe = ir_exe_for(seed.Realization(
            reclaim="redirect", io=("stdin", "bytes")))
    routines, imports, slots, text_base, fixed = _emit_layout(
        R, routines, rt, imports, slots, text_base)
    ev: dict = {}
    if staged:
        if store is None:
            store = BlobStore()
        brun = make_bytes_runner(exe, workers=1,
                                 pinned=pinned or store.pins)
        # program stage — items as boundary enumeration.  `prog`
        # fraglists enumerate seed-side; otherwise per-routine frag
        # queries reduce on a term-egress kernel and decode at the
        # boundary (the decode crossing, counted in evidence).
        if prog is not None:
            items = [it for fr in st.ASM_LINK for it in fr]
            ev["program"] = "fraglist"
        else:
            _ir_ctx = any(n.startswith("ir_") for n in routines)
            trun = make_ir_runner(
                ir_exe_for(seed.Realization(reclaim="redirect")),
                workers=1, pinned=store.pins)
            for name in routines:
                store.pin_named(
                    st.routine_pin_key(name, fixed, _ir_ctx),
                    st.routine_of(name, fixed, _ir_ctx))
            nfs, s_p, _ = trun.batch(
                [st.routine_query(n, R, passes, fixed=fixed,
                                  ir_ctx=_ir_ctx)
                 for n in routines])
            items = []
            for nf in nfs:
                items.extend(st.decode_frag(nf))
                _DECODE_COUNT["frag"] += 1
            ev["program"] = f"frags={len(nfs)} steps={s_p}"
        # link stage — blob seam: kernel projections for the byte
        # sections, kernel APPEND for the merged symtab (PIR blob).
        blob_run = make_blob_runner(
            ir_exe_for(seed.Realization(
                reclaim="redirect", io=("stdin", "ir"))),
            workers=1, pinned=store.pins)
        ib, db, syms = link_staged(
            imports, slots, None, store=store,
            run_ir=blob_run, run_bytes=brun)
        ev["link"] = f"ib={len(ib)} db={len(db)} symblob={len(syms)}"
        # assemble stage — per-item encodeOf roots, batched streams.
        tb, _loc = assemble_staged(items, syms, text_base, brun,
                                   store=store)
        ev["assemble"] = (f"items={len(items)} text={len(tb)}B "
                          f"loc={len(_loc)}")
    else:
        link_q, asm_q = _emit_queries(R, routines, passes, rt,
                                      imports, slots, text_base,
                                      prog)
        roots_a = [app(app(link_q, KK), KK),
                   app(app(link_q, KK), KI),
                   app(asm_q, KK)]
        fa, ev_a = _run_stream(exe, roots_a, pinned, timeout)
        ib, db, tb = fa
        ev["stream_a"] = ev_a

    def K_(name: str):
        return bracket(parse(getattr(st, name)))

    def b4(v: int) -> T:
        return st.bytelist_term(v.to_bytes(4, "little"))

    lt, li, ld = b4(len(tb)), b4(len(ib)), b4(len(db))
    traw = st._appn(K_("_ALIGN512"), lt)
    iraw = st._appn(K_("_ALIGN512"), li)
    draw = st._appn(K_("_ALIGN512"), ld)
    drva = st._appn(K_("_ALIGN4096"),
                    st._appn(K_("_B4ADD"), b4(0x1000), li))
    trva = st._appn(K_("_ALIGN4096"),
                    st._appn(K_("_B4ADD"), drva, ld))
    dptr = st._appn(K_("_B4ADD"), b4(0x200), iraw)
    tptr = st._appn(K_("_B4ADD"), dptr, draw)
    iddr = st._appn(K_("_B4ADD"), iraw, draw)
    img = st._appn(K_("_ALIGN4096"),
                   st._appn(K_("_B4ADD"), trva, lt))
    u64 = st._appn(K_("_U64"), b4(R.stack_reserve))
    roots_b = [traw, iraw, draw, drva, trva, dptr, tptr, iddr,
               img, u64,
               st._appn(K_("_ZEROFILL"), st.church(12)),
               st._appn(K_("_ZEROFILL"), st.church(58)),
               st._appn(K_("_ZEROFILL"), st.church(14 * 8)),
               st._appn(K_("_ZEROFILL"), st.church(0x200 - 448)),
               st._appn(K_("_PADLIST"), li),
               st._appn(K_("_PADLIST"), ld),
               st._appn(K_("_PADLIST"), lt)]
    fb, ev_b = _run_stream(exe, roots_b, pinned or (
        store.pins if store is not None else None), timeout)
    ev["stream_b"] = ev_b
    (v_traw, v_iraw, v_draw, v_drva, v_trva, v_dptr, v_tptr,
     v_iddr, v_img, v_u64, z12, z58, z112, zfh,
     padi, padd, padt) = fb
    chunks = [
        b"MZ", z58, struct.pack("<I", 0x40), b"PE\x00\x00",
        struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0, 0x22),
        struct.pack("<HBB", 0x20B, 0, 0),
        v_traw, v_iddr, struct.pack("<I", 0),
        v_trva, v_trva,
        struct.pack("<Q", 0x140000000),
        struct.pack("<II", 0x1000, 0x200),
        struct.pack("<HHHHHH", 6, 0, 0, 0, 6, 0),
        struct.pack("<I", 0), v_img,
        struct.pack("<II", 0x200, 0),
        struct.pack("<HH", 3, 0x8100),
        v_u64,
        struct.pack("<QQQ", 0x1000, 0x100000, 0x1000),
        struct.pack("<II", 0, 16), struct.pack("<II", 0, 0),
        struct.pack("<I", 0x1000), len(ib).to_bytes(4, "little"),
        z112,
        b".idata\x00\x00", len(ib).to_bytes(4, "little"),
        struct.pack("<I", 0x1000), v_iraw,
        struct.pack("<I", 0x200), z12,
        struct.pack("<I", 0x40000040),
        b".data\x00\x00\x00", len(db).to_bytes(4, "little"),
        v_drva, v_draw, v_dptr, z12,
        struct.pack("<I", 0xC0000040),
        b".text\x00\x00\x00", len(tb).to_bytes(4, "little"),
        v_trva, v_traw, v_tptr, z12,
        struct.pack("<I", 0x60000020),
        zfh,
        ib, padi, db, padd, tb, padt,
    ]
    return b"".join(chunks), ev


def _schedule_items(rt, R, routines, passes) -> list:
    """the program stage's item list as seed-side schedule data —
    mirrors routine_expr's emission exactly: raw per-builder items
    (no _mt_xform — the term carries pre-xform frags), the fs
    conditional that st_s/build_ds encode in-term applied as a
    skip, then the pass chain per frag.  Every pass must have a
    Python mirror (_PASS_PY): `peephole` mirrors the SINGLE
    PEEPHOLE_PASS application the term chain performs per
    occurrence — the fixpoint lives elsewhere
    (peephole_fixpoint); a pass with no mirror refuses rather than
    silently emitting un-passed items."""
    import opt_peephole
    _PASS_PY = {
        "id": lambda prog: list(prog),
        "peephole": lambda prog: opt_peephole._pass_once(
            list(prog), "x86_64")[0],
    }
    _FS_NEED = {"st_s": True, "build_ds": False}
    mod = getattr(rt, "module", None) or rt
    builders = getattr(mod, "_BUILDERS", None)
    if builders is None:
        if passes:
            raise toolchain.NotRealized(
                "emit schedule: per-frag passes need "
                "routines-module _BUILDERS")
        return list(mod.program(R))
    ctx = mod._ctx()
    ctx["ir"] = any(n.startswith("ir_") for n in routines)
    ctx["irnext"] = "ir_spawn" if R.threads > 1 else "ir_depack"
    items = []
    for name in routines:
        need = _FS_NEED.get(name)
        if need is not None and bool(need) != bool(R.fuse_s):
            continue                       # emits fs ? frag : NIL
        frag = list(builders[name](R, ctx))
        for p in passes:
            apply = _PASS_PY.get(p)
            if apply is None:
                raise toolchain.NotRealized(
                    f"emit schedule: pass {p!r} has no seed mirror")
            frag = apply(frag)
        items += frag
    return items


def _assemble_stream(items, syms, base: int,
                     pinned: Optional[dict] = None
                     ) -> Tuple[bytes, int]:
    """emit.assemble's stream: one `encodeOf item resv` per prep
    position, in order — the frames concat to .text directly, no
    substitution bookkeeping.  rel-sensitive items carry their
    resv-closed query (symtab/loc/end4 as seed-side schedule data:
    loc accumulates positions predicted by the Python encode
    oracle — the same lengths encodeOf's frames prove).  Returns
    (stream, text_len)."""
    import isa_x86_64 as isa
    sym_t = st.symtab_term(syms)
    loc: dict = {}
    prep: List[tuple] = []
    pos = 0
    for it in items:
        if it[0] == "label":
            loc[it[1]] = base + pos
            continue
        n = len(isa.encode(tuple(it[1:])))
        prep.append((it, pos, n))
        pos += n
    loc_t = st.symtab_term(loc)
    roots = []
    for it, off, ln in prep:
        if _is_rel_item(it):
            e4 = st.bytelist_term(
                (base + off + ln).to_bytes(4, "little"))
            resv = st._appn(_resvmk(), sym_t, loc_t, e4)
            q = st.encode_query(it, resv)
        else:
            q = st.encode_query(it)
        roots.append(app(q, KK))
    return st.pack_ir(*roots, pinned=pinned), pos


def _pack_stream(text_len: int, idata_len: int, datab_len: int,
                 stackres: int,
                 pinned: Optional[dict] = None
                 ) -> Tuple[bytes, List[Tuple[int, str, int]]]:
    """emit.pack's stream: _pack_recipe serialized — lit/root
    elements become stream queries in splice order (literals ride
    as already-NF bytelist terms: format constants are data, not
    computed answers); stage elements become MAP rows.  Returns
    (stream, [(at_stream_idx, src_stage, src_frame)])."""
    import plex_bundle as pb
    roots: List[T] = []
    mmap: List[Tuple[int, str, int]] = []
    for e in _pack_recipe(text_len, idata_len, datab_len, stackres):
        if e[0] == "stage":
            mmap.append((len(roots), e[1], e[2]))
        elif e[0] == "lit":
            roots.append(st.bytelist_term(e[1]))
        else:
            roots.append(e[1])
    return st.pack_ir(*roots, pinned=pinned), mmap


def emit_schedule_streams(R: seed.Realization,
                          routines=None,
                          passes: Tuple[str, ...] = (),
                          rt=None, imports=None, slots=None,
                          text_base: Optional[int] = None,
                          pinned: Optional[dict] = None
                          ) -> List[Tuple[str, str, bytes, tuple]]:
    """The staged schedule's streams — every stage's executable
    form as (name, runner, PIR-stream, map_rows), the complete
    serialized DAG beside pack_emit_program's canonical monolith:

    - `emit.program`: per-routine frag queries (term-egress);
    - `emit.link`: `[idata·KK, datab·KK]` byte projections;
    - `emit.symtab`: `[APPEND (idata·KI) (datab·KI)]` merged
      symtab, ir-egress (provenance + the blob-seam audit);
    - `emit.assemble`: per-prep-position `encodeOf` roots —
      frames concat to .text (the loc/resv schedule authored
      seed-side from the Python oracles);
    - `emit.pack`: the chunk recipe — literals as passthrough
      queries, computed fields as numeral roots, and MAP rows
      declaring where emit.link/emit.assemble frames interleave.

    The canonical `emit.term` rides separately as the bundle's
    primary PIR payload.  With all six stages serialized the
    schedule is fully data: replay is dep-order execution plus
    MAP-declared concat — Python's residue is spawn, concat,
    compare."""
    routines, imports, slots, text_base, fixed = _emit_layout(
        R, routines, rt, imports, slots, text_base)
    rt_eff = rt if rt is not None else rts
    _ir_ctx = any(n.startswith("ir_") for n in routines)
    drva = target_pe64.data_rva(imports)
    iq, dq = st.idata_query(imports), st.data_query(slots, drva)
    items = _schedule_items(rt_eff, R, routines, passes)
    ib, db, syms = st.python_link(imports, slots)
    asm_stream, text_len = _assemble_stream(items, syms, text_base,
                                            pinned)
    pack_stream, pack_map = _pack_stream(
        text_len, len(ib), len(db), R.stack_reserve, pinned)
    return [
        ("emit.program", "exe.term",
         st.pack_ir(*[st.routine_query(
                      n, R, passes, fixed=fixed, ir_ctx=_ir_ctx)
                     for n in routines], pinned=pinned), ()),
        ("emit.link", "exe.bytes",
         st.pack_ir(app(iq, KK), app(dq, KK), pinned=pinned), ()),
        ("emit.symtab", "exe.ir",
         st.pack_ir(st._appn(st.append_term(),
                             app(iq, st._KI), app(dq, st._KI)),
                    pinned=pinned), ()),
        ("emit.assemble", "exe.bytes", asm_stream, ()),
        ("emit.pack", "exe.bytes", pack_stream, tuple(pack_map)),
    ]


def _pin_emit_consts(store: "BlobStore", R, routines, fixed) -> None:
    """Register the emit term's generated constants so pack splices
    stored blobs instead of re-walking (program_rt's routine trie is
    the ~12M-node constant; pack_ir on it dominates at ~400s cold).
    A fresh store still walks each once — pinning only reorders."""
    h = st._fix_key(fixed)
    ir_ctx = any(n.startswith("ir_") for n in routines)
    store.pin_named(
        f"emit.program_rt.{h}.{int(ir_ctx)}",
        st.program_rt(fixed, ir_ctx))
    store.pin_named(
        st.const_pin_key("assemble", st._pin_src(st._g("_ASSEMBLE"))),
        st._g("_ASSEMBLE"))


def pack_emit_program(R: seed.Realization,
                      routines=None,
                      passes: Tuple[str, ...] = (),
                      rt=None,
                      imports=None,
                      slots=None,
                      text_base: Optional[int] = None,
                      store: Optional["BlobStore"] = None
                      ) -> Tuple[bytes, str]:
    """emit_term -> (PIR stream, root Merkle digest).  `store` (a
    BlobStore, optionally disk-backed via workdir) splices the
    generated constants; the stream is complete either way."""
    t = emit_term(R, routines, passes, rt, imports, slots, text_base)
    if store is not None:
        _d = seed.Realization()
        _prog_axes = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
                      "node_bytes", "stack_reserve", "peephole", "dialect"}
        fixed = {k: getattr(R, k)
                 for k in vars(_d) if k not in _prog_axes}
        rn = routines if routines is not None else (
            (rt.names_for(R) if getattr(rt, "names_for", None)
             else rt.routines) if rt is not None else rts.ROUTINES)
        _pin_emit_consts(store, R, rn, fixed)
        store.pin_named(st.const_pin_key(
            "link.%d.%d" % (len(imports if imports is not None
                            else rts.IMPORTS),
                            len(slots if slots is not None
                                else rts.DATA_SLOTS)),
            st.link_src(len(imports if imports is not None
                            else rts.IMPORTS),
                        len(slots if slots is not None
                            else rts.DATA_SLOTS))),
            st.link_term(len(imports if imports is not None
                             else rts.IMPORTS),
                         len(slots if slots is not None
                             else rts.DATA_SLOTS)))
        store.pin_named(st.const_pin_key("pack2", st.pack2_src()),
                        st.pack2_term())
        data, keys = st.pack_ir_keyed(t, pinned=store.pins)
        return data, keys[0]
    data, keys = st.pack_ir_keyed(t)
    return data, keys[0]


def emit_sections(pir: bytes, caps: Optional[dict],
                  realization: dict, evidence: dict,
                  streams: Optional[List[Tuple[str, str, bytes,
                                               tuple]]] = None
                  ) -> list:
    """v3 sections for an emit program bundle — not a stage manifest:
    STRINGS + REALIZATION + CAPS + EVIDENCE + the PIR stream as BYTES.
    `realization` should carry `dialect=plex.emit/1` and `routines`.

    `streams` (emit_schedule_streams' output) upgrades the archive to
    `plex.emit/2`: STAGES rows for all six stages, DEPS edges, MAP
    rows declaring emit.pack's output assembly, and QUERIES rows
    whose blob token is `off:len` into the BYTES pool — each stream
    aligned at 8 inside the pool, `emit.term` first.  Every stage
    carries its executable stream: replay is dep-order execution
    plus MAP-declared concat, never stage resolution."""
    import plex_bundle as pb
    pool = pb._Pool()
    secs = [pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0, b"")]

    def _u64rows(rows):
        return b"".join(struct.pack(f"<{len(r)}Q", *r) for r in rows)

    stage_rows = []
    dep_pairs = []
    query_rows = []
    map_rows = []
    blob_pool = bytearray()
    if streams:
        stages = [("emit.term", "pir-stream", "exe.bytes"),
                  ("emit.program", "pir-stream", "exe.term"),
                  ("emit.link", "pir-stream", "exe.bytes"),
                  ("emit.symtab", "pir-stream", "exe.ir"),
                  ("emit.assemble", "pir-stream", "exe.bytes"),
                  ("emit.pack", "pir-stream", "exe.bytes")]
        s_of = {s[0]: i for i, s in enumerate(stages)}
        deps = {"emit.assemble": ("emit.program", "emit.link",
                                  "emit.symtab"),
                "emit.pack": ("emit.link", "emit.assemble")}
        for i, (name, artifact, runner) in enumerate(stages):
            stage_rows.append(tuple(
                v for f in (name, artifact, runner)
                for v in pool.ref(f)))
            for d in deps.get(name, ()):
                dep_pairs.append((i, s_of[d]))
        do, dl = pool.ref(hashlib.sha256(pir).hexdigest())
        bo, bl = pool.ref(f"0:{len(pir)}")
        query_rows.append((s_of["emit.term"], do, dl, bo, bl))
        for name, runner, blob, mmap in streams:
            dig = hashlib.sha256(blob).hexdigest()
            do, dl = pool.ref(dig)
            bo, bl = pool.ref(f"{len(blob_pool)}:{len(blob)}")
            query_rows.append((s_of[name], do, dl, bo, bl))
            blob_pool += blob
            blob_pool += b"\x00" * (-len(blob_pool) % 8)
            for at, src, sf in mmap:
                map_rows.append((s_of[name], at, s_of[src], sf))
        if stage_rows:
            secs.append(pb.Section(pb.KIND_STAGES, pb.U64, 6,
                                   len(stage_rows),
                                   _u64rows(stage_rows)))
        if dep_pairs:
            secs.append(pb.Section(pb.KIND_DEPS, pb.U32, 2,
                                   len(dep_pairs),
                                   b"".join(struct.pack("<II", *p)
                                            for p in dep_pairs)))
        if map_rows:
            secs.append(pb.Section(pb.KIND_MAP, pb.U32, 4,
                                   len(map_rows),
                                   b"".join(struct.pack("<IIII", *r)
                                            for r in map_rows)))
        secs.append(pb.Section(pb.KIND_QUERIES, pb.U64, 5,
                               len(query_rows),
                               _u64rows(query_rows)))
    rrows = [pool.ref(str(k)) + pool.ref(str(v))
             for k, v in sorted(realization.items())]
    secs.append(pb.Section(pb.KIND_REALIZATION, pb.U64, 4,
                           len(rrows), _u64rows(rrows)))
    if caps:
        crows = []
        for p, m in sorted(caps.get("ports", {}).items()):
            crows.append((pb.CAP_PORT,) + pool.ref(str(p))
                         + pool.ref(str(m)))
        for b, pl in sorted(caps.get("os", {}).items()):
            crows.append((pb.CAP_OS,) + pool.ref(str(b))
                         + pool.ref(",".join(str(p) for p in pl)))
        secs.append(pb.Section(pb.KIND_CAPS, pb.U64, 5,
                               len(crows), _u64rows(crows)))
    erows = [pool.ref(str(k)) + pool.ref(str(v))
             for k, v in sorted(evidence.items())]
    secs.append(pb.Section(pb.KIND_EVIDENCE, pb.U64, 4,
                           len(erows), _u64rows(erows)))
    if blob_pool:
        secs.append(pb.Section(pb.KIND_BYTES, pb.U8, 1, 0,
                               bytes(blob_pool)))
        secs[-1].rows = secs[-1].length
    # the canonical emit term is its own section kind — the
    # kernel-side ingest contract (dialect="plex.v3"): exactly
    # one KIND_PIR span = the packed-IR program stream
    secs.append(pb.Section(pb.KIND_PIR, pb.U8, 1, 0, pir))
    secs[-1].rows = secs[-1].length
    secs[0] = pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0,
                         bytes(pool.buf))
    secs[0].rows = secs[0].length
    return secs


def write_emit_bundle(path: str, R: seed.Realization,
                      routines=None,
                      passes: Tuple[str, ...] = (),
                      rt=None,
                      imports=None,
                      slots=None,
                      text_base: Optional[int] = None,
                      workdir: Optional[str] = None,
                      schedule: bool = True) -> str:
    """emit_term -> emit.plex: the emit program + its caps/realization
    contract as one ingestible archive.  Returns the path.

    `schedule` (default) upgrades the archive to `plex.emit/2`:
    emit_schedule_streams' stage-level PIR streams ride in the
    BYTES pool beside the canonical emit term, with STAGES/DEPS/
    QUERIES rows making the DAG skeleton data — a consumer reads
    `emit.program`/`emit.link` streams and drives the staged
    schedule; the monolithic `emit.term` stays the semantic
    oracle."""
    import plex_bundle as pb
    store = BlobStore(os.path.join(workdir, "blobs")) if workdir \
        else None
    pir, rdig = pack_emit_program(R, routines, passes, rt, imports,
                                  slots, text_base, store=store)
    real = {k: str(v) for k, v in vars(R).items()}
    real["routines"] = rt.name if rt is not None else "x86_64.win64.lo"
    real["dialect"] = "plex.emit/2" if schedule else "plex.emit/1"
    if schedule:
        _rn, _im, _sl, _tb, _fx = _emit_layout(
            R, routines, rt, imports, slots, text_base)
        real["imports"] = ",".join(str(n) for n in _im)
        real["slots"] = ",".join(f"{n}:{s}" for n, s in _sl)
        real["text_base"] = hex(_tb)
        real["routines_list"] = ",".join(_rn)
        real["schedule.output"] = "emit.pack"
    comp = toolchain.components()["routines"].get(real["routines"])
    caps = dict(comp.data).get("caps") if comp is not None else None
    streams = emit_schedule_streams(
        R, routines, passes, rt, imports, slots, text_base,
        pinned=store.pins if store is not None else None) \
        if schedule else None
    ev = {"format": "plex.emit/2" if schedule else "plex.emit/1",
          "emit_root_digest": rdig,
          "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ",
                                       time.gmtime())}
    data = pb.pack_bundle(emit_sections(pir, caps, real, ev,
                                        streams=streams))
    bundle = pb.read_bundle(data)
    if caps is not None:
        errs = pb.check_bundle_caps(bundle, caps)
        if errs:
            raise toolchain.NotRealized(
                f"emit bundle caps exceed record "
                f"{real['routines']}: {errs[0]}")
    os.makedirs(os.path.dirname(os.path.abspath(path))
                or ".", exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)
    return path


def emit_bundle_streams(bundle) -> Dict[str, bytes]:
    """emit.plex (plex.emit/2) -> {stage_name: PIR stream}: the
    QUERIES rows' `off:len` blob tokens sliced out of their pool —
    `emit.term` spans the KIND_PIR section (the canonical payload),
    every other stream spans the BYTES pool.  Digests verified — a
    malformed span or digest mismatch refuses."""
    import plex_bundle as pb
    pool = bundle.bytes_pool()
    psec = bundle.section(pb.KIND_PIR)
    ppool = psec.payload(bundle.data) if psec is not None else b""
    stages = bundle.stage_rows()
    out = {}
    for sidx, dig, tok in bundle.query_rows():
        name = stages[sidx][0]
        src = ppool if name == "emit.term" else pool
        off_s, len_s = tok.split(":")
        off, ln = int(off_s), int(len_s)
        if off < 0 or ln < 0 or off + ln > len(src):
            raise toolchain.NotRealized(
                f"emit bundle stream {name!r}: span "
                f"{off}:{ln} outside pool {len(src)}")
        blob = src[off:off + ln]
        if hashlib.sha256(blob).hexdigest() != dig:
            raise toolchain.NotRealized(
                f"emit bundle stream {name!r}: digest "
                f"mismatch — content missing or corrupted")
        out[name] = blob
    return out


def run_emit_bundle(path, R: Optional[seed.Realization] = None,
                    exe: Optional[str] = None,
                    timeout: int = 3600) -> Tuple[bytes, dict]:
    """emit.plex -> PE image: EXECUTE the serialized schedule —
    every stage's stream rides the archive; replay is dep-order
    execution plus MAP-declared output assembly, never stage
    resolution.

    Contract: `dialect=plex.emit/2`, stream digests verified
    (emit_bundle_streams), caps ⊆ the routines record.  The dep
    closure of `schedule.output` topologically orders the stages;
    each stage runs on its declared runner; a stage in the closure
    with no stream is a refusal (the bundle is incomplete, not
    underresolved).  Output assembly walks a stage's MAP rows —
    before consuming its own stream frame `at`, splice src's
    frame(s).  Audit: the decoded program items must enumerate
    exactly the baked encode roots — a bundle whose assemble
    stream no longer corresponds to its declared program is a
    refusal, not a different image.

    Python's residue: subprocess per runner, frame concat, write
    the file.  Returns (image_bytes, evidence)."""
    import plex_bundle as pb
    data = open(path, "rb").read() if isinstance(path, str) \
        else path
    try:
        b = pb.read_bundle(data)
    except pb.BundleError as e:
        raise toolchain.NotRealized(f"emit bundle: {e}")
    real = b.kv_rows(pb.KIND_REALIZATION)
    if real.get("dialect") != "plex.emit/2":
        raise toolchain.NotRealized(
            f"emit bundle dialect {real.get('dialect')!r} — "
            f"need plex.emit/2 (schedule streams)")
    rn = real.get("routines", "")
    comp = toolchain.components().get("routines", {}).get(rn) \
        if rn else None
    declared = dict(comp.data).get("caps") if comp is not None \
        else None
    if declared is not None:
        errs = pb.check_bundle_caps(b, declared)
        if errs:
            raise toolchain.NotRealized(
                f"emit bundle caps exceed record {rn}: {errs[0]}")
    try:
        streams = emit_bundle_streams(b)
    except pb.BundleError as e:
        raise toolchain.NotRealized(f"emit bundle: {e}")
    ev: dict = {}
    if exe is None:
        exe = ir_exe_for(seed.Realization(
            reclaim="redirect", io=("stdin", "bytes")))

    def _run_pir(x, blob, mode):
        p = subprocess.run([x], input=blob, capture_output=True,
                           timeout=timeout)
        if p.returncode != 0:
            raise toolchain.NotRealized(
                f"emit bundle stage refused: rc={p.returncode} "
                f"{p.stderr[:160]!r}")
        if mode == "term":
            return p.stdout, p.stderr
        # bytes + ir egress share the [u32le len][payload] framing;
        # ir frames are validated as PIR blobs (the blob seam keeps
        # them opaque — never decoded Python-side)
        frames = _parse_frames(p.stdout)
        if mode == "ir":
            for f in frames:
                st.digest_ir_blob(f)
        return frames, p.stderr

    def _run_stage(x, blob, mode):
        """one stage stream -> its output, arena-bounded: the bump
        arena accumulates across a stream's roots (the same wall
        _batch_bounded halves on), so execution slices the root
        table and halves the span on rc=4 — executor scheduling,
        not schedule resolution; root order and content are
        unchanged (slice_ir preserves digests)."""
        try:
            nr = st.ir_roots(blob)
        except ValueError:
            raise toolchain.NotRealized(
                "emit bundle: stream is not a packed-IR stream")
        span = nr
        while True:
            try:
                if span >= nr:
                    return _run_pir(x, blob, mode)
                outs = []
                err = b""
                for i in range(0, nr, span):
                    out, err = _run_pir(
                        x, st.slice_ir(blob, i, min(span, nr - i)),
                        mode)
                    outs.append(out)
                if mode == "term":
                    return b"".join(outs), err
                return [f for o in outs for f in o], err
            except toolchain.NotRealized as e:
                if "rc=4" not in str(e) or span == 1:
                    raise
                span = max(1, span // 2)

    try:
        stages = b.stage_rows()
        deps = b.dep_edges()
        maps = b.map_rows()
    except pb.BundleError as e:
        raise toolchain.NotRealized(f"emit bundle: {e}")
    s_of = {n: i for i, (n, _a, _r) in enumerate(stages)}
    out_name = real.get("schedule.output", "emit.pack")
    if out_name not in s_of:
        raise toolchain.NotRealized(
            f"emit bundle: output stage {out_name!r} "
            f"not in STAGES")
    # dep closure of the output stage, topo-ordered (deps first —
    # a cycle is a malformed schedule, not a scheduling problem)
    need: set = set()
    stack = [s_of[out_name]]
    while stack:
        i = stack.pop()
        if i in need:
            continue
        need.add(i)
        stack += [d for a, d in deps if a == i]
    order, done = [], set()
    while len(order) < len(need):
        progressed = False
        for i in sorted(need):
            if i in done:
                continue
            if all(d in done for a, d in deps if a == i):
                order.append(i)
                done.add(i)
                progressed = True
        if not progressed:
            raise toolchain.NotRealized(
                "emit bundle: DEPS cycle — no topological order")
    # structural completeness — every closure stage carries its
    # stream and every MAP row stays inside declared bounds; these
    # are bundle-shape properties, checked before any execution
    for i in need:
        if stages[i][0] not in streams:
            raise toolchain.NotRealized(
                f"emit bundle: stage {stages[i][0]!r} in the dep "
                f"closure of {out_name!r} carries no stream — "
                f"incomplete schedule, not resolvable")
    for si, at, src, _sf in maps:
        if si >= len(stages) or src >= len(stages):
            raise toolchain.NotRealized(
                "emit bundle: MAP row outside STAGES")
        src_name = stages[src][0]
        if si in need and src_name not in {stages[i][0]
                                          for i in need}:
            raise toolchain.NotRealized(
                f"emit bundle: MAP src {src_name!r} is not a dep "
                f"of {stages[si][0]!r}")
        bl = streams.get(stages[si][0])
        if bl is not None:
            try:
                nr = st.ir_roots(bl)
            except ValueError:
                raise toolchain.NotRealized(
                    f"emit bundle: stage {stages[si][0]!r} stream "
                    f"is not a packed-IR stream")
            if at > nr:
                raise toolchain.NotRealized(
                    f"emit bundle: MAP row at={at} exceeds "
                    f"{stages[si][0]} roots {nr}")
    exes = {"exe.term": (ir_exe_for(seed.Realization(
                            reclaim="redirect")), "term"),
            "exe.bytes": (exe, "bytes"),
            "exe.ir": (ir_exe_for(seed.Realization(
                        reclaim="redirect", io=("stdin", "ir"))),
                       "ir")}
    frames: Dict[str, list] = {}
    progs: Dict[str, bytes] = {}
    for i in order:
        name, _art, runner = stages[i]
        blob = streams[name]
        xm = exes.get(runner)
        if xm is None:
            raise toolchain.NotRealized(
                f"emit bundle: stage {name!r} runner "
                f"{runner!r} not realized")
        out, err = _run_stage(xm[0], blob, xm[1])
        if xm[1] == "term":
            progs[name] = out
        else:
            frames[name] = out
        ev[name] = (f"roots={len(out) if isinstance(out, list) else '?'} "
                    f"err={len(err)}B")
    # audit — the program stage's decoded items must enumerate
    # exactly the assemble stream's baked roots (a bundle whose
    # streams no longer correspond is corrupt, not alternate)
    items = []
    ptxt = progs.get("emit.program")
    if ptxt is not None:
        for line in ptxt.decode("utf-8", "replace").splitlines():
            if line.strip():
                items.extend(st.decode_frag(_nf_from_text(line)))
                _DECODE_COUNT["frag"] += 1
    asm = frames.get("emit.assemble")
    if ptxt is not None and asm is not None:
        n_prep = sum(1 for it in items if it[0] != "label")
        if n_prep != len(asm):
            raise toolchain.NotRealized(
                f"emit bundle: program items {n_prep} != assemble "
                f"roots {len(asm)} — streams out of correspondence")
        ev["program"] = f"items={len(items)}"
    # MAP-declared output assembly
    def _output(name: str) -> bytes:
        fr = frames.get(name)
        if fr is None:
            raise toolchain.NotRealized(
                f"emit bundle: stage {name!r} has no frames to "
                f"assemble")
        rows = sorted((r for r in maps if r[0] == s_of[name]),
                      key=lambda r: r[1])
        parts, cur = [], 0
        for _s, at, src, sf in rows:
            if at > len(fr):
                raise toolchain.NotRealized(
                    f"emit bundle: MAP row at={at} exceeds "
                    f"{name} frames {len(fr)}")
            parts.extend(fr[cur:at])
            cur = at
            src_name = stages[src][0] if src < len(stages) else "?"
            srcf = frames.get(src_name)
            if srcf is None:
                raise toolchain.NotRealized(
                    f"emit bundle: MAP src {src_name!r} has no "
                    f"frames")
            if sf == pb.MAP_ALL:
                parts.extend(srcf)
            elif sf < len(srcf):
                parts.append(srcf[sf])
            else:
                raise toolchain.NotRealized(
                    f"emit bundle: MAP src frame {sf} exceeds "
                    f"{src_name} frames {len(srcf)}")
        parts.extend(fr[cur:])
        return b"".join(parts)

    img = _output(out_name)
    return img, ev


def replay_emit(workdir: str) -> Tuple[bytes, dict]:
    """Resolve the recorded stage DAG — pure artifact addressing:
    every stage must already be materialized under its content key;
    a missing artifact is a refusal, not a recompute (recompute =
    emit_image, replay = the bundle-loader contract in miniature)."""
    with open(os.path.join(workdir, "manifest.json")) as f:
        man = json.load(f)
    stages = {s["name"]: s for s in man["stages"]}
    for s in man["stages"]:
        for d in s.get("deps", []):
            if d not in stages:
                raise toolchain.NotRealized(
                    f"manifest: stage {s['name']} dep {d} "
                    f"is not a stage")
        if not os.path.exists(os.path.join(workdir, s["artifact"])):
            raise toolchain.NotRealized(
                f"manifest replay: {s['name']} artifact "
                f"{s['artifact']} not materialized — emit, "
                f"don't replay")
    img_stage = stages.get("image.bin")
    if img_stage is None:
        raise toolchain.NotRealized(
            "manifest: no image.bin stage — not an image manifest")
    with open(os.path.join(workdir, img_stage["artifact"]),
              "rb") as f:
        return f.read(), man


def emit_image(R: seed.Realization,
               imports=None, slots=None,
               text_base: Optional[int] = None,
               run: Callable[[T], Tuple[T, int, int]] = _graph_run,
               stage_runs: Optional[dict] = None,
               bytes_run: Optional[Callable] = None,
               term_run: Optional[Callable] = None,
               blob_run: Optional[Callable] = None,
               routines=None,
               passes: Tuple[str, ...] = (),
               rt=None,
               decompose_asm: bool = False,
               decompose_pack: Optional[bool] = None,
               workdir: Optional[str] = None,
               label: str = "",
               exe_default: bool = False,
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
    persisted.  With the blob store populated (decompose + workdir)
    the pack cost splices away — program on the exe is the default
    there.

    `exe_default` — unified-runtime mode: byte seams default to the
    emitted redirect+bytes kernel (`ir_exe_for`), term-NF seams to
    the packed-IR kernel; `run=` remains the oracle path.  Opt-in
    this phase — flipping the default waits on Phase 4's manifest
    runner resolution.  Under exe_default, `decompose_pack=None`
    resolves True — the chunked pack* seam is the exe-shaped pack;
    the monolithic pack2 query on a single kernel process crawls
    (concat-heavy live set, measured >4min vs 4.7s chunked).

    Returns (image_bytes, stage_report) where stage_report lists
    (stage, steps, arena_nodes) per reduction.
    """
    report: List[tuple] = []
    dec0 = dict(_DECODE_COUNT)   # per-emit decode evidence baseline
    if decompose_pack is None:
        # exe_default means all stages exe-shaped — pack* chunked is
        # the designed byte-seam path; monolithic pack2 crawls on a
        # single kernel process.
        decompose_pack = bool(exe_default)
    # programOf is generated at sentinel defaults — only fs/fuel/
    # rbb/cb/nb flow in as parameters (stack_reserve enters at pack,
    # peephole is its own stage).  Any other R field left non-default
    # would be silently dropped; refuse rather than emit the wrong
    # kernel — silent realization downgrade is exactly what the staged
    # chain exists to prevent.
    _d = seed.Realization()
    # λ-bound program params: fs/fuel/rbb/cb/nb flow into the routine
    # spine; stack_reserve enters at pack, peephole is its own stage.
    # Everything else is a GENERATION axis — pinned into the routine
    # terms via `fixed` so builder-level branches on reclaim/io/payload
    # emit the declared variant instead of silently defaulting.
    _prog_axes = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
                  "node_bytes", "stack_reserve", "peephole", "dialect"}
    fixed = {k: getattr(R, k) for k in vars(_d) if k not in _prog_axes}
    if rt is not None:
        if R.order not in rt.orders:
            raise toolchain.NotRealized(
                f"emit_image: order={R.order!r} not in {rt.orders}")
        if R.io not in rt.ios:
            raise toolchain.NotRealized(
                f"emit_image: io={R.io!r} not realized by {rt.name}")
        if routines is None:
            nf = getattr(rt, "names_for", None)
            routines = nf(R) if nf else rt.routines
        if imports is None:
            imports = rt.imports
        if slots is None:
            slots = rt.data_slots(R) if callable(rt.data_slots) \
                else rt.data_slots
    imports = rts.IMPORTS if imports is None else imports
    slots = rts.DATA_SLOTS if slots is None else slots
    if routines is None and rt is None:
        # the default record's own honesty checks — an io mode or
        # order the .lo record doesn't realize must be refused, not
        # baked into routines that can't express it
        if R.io != ("stdin", "stdout"):
            raise toolchain.NotRealized(
                f"emit_image: io={R.io!r} needs a routines record "
                f"that declares it (ROUTINES has no egress block)")
        if R.order != "lo":
            raise toolchain.NotRealized(
                f"emit_image: order={R.order!r} not realized")
    if (routines is not None and tuple(routines) != tuple(rts.ROUTINES)) \
            or rt is not None:
        # a non-baked routine selection is itself a request for the
        # record-driven staged path
        decompose_asm = True
    if passes and not decompose_asm:
        raise toolchain.NotRealized(
            "emit_image: `passes` are per-routine stage parameters — "
            "the monolithic assemble path has no chain entry point; "
            "set decompose_asm=True")
    if text_base is None:
        # .text is emitted last in the image — its RVA is a function of
        # the (already fixed) idata/data layout, not a constant.
        text_base = target_pe64.text_rva(imports, slots)
    store = BlobStore(os.path.join(workdir, "blobs")) if workdir \
        else BlobStore()
    runs = dict(stage_runs or {})
    if exe_default:
        # unified runtime: the emitted kernels ARE the runners —
        # byte seams on the byte-egress exe, term-NF seams on the
        # packed-IR exe, both splice-aware via the blob store.
        if bytes_run is None:
            bytes_run = make_bytes_runner(
                ir_exe_for(seed.Realization(
                    reclaim="redirect", io=("stdin", "bytes"))),
                workers=os.cpu_count() or 4, pinned=store.pins,
                cache_dir=(os.path.join(workdir, "nf_bytes")
                           if workdir else None))
        if term_run is None:
            term_run = make_ir_runner(
                ir_exe_for(seed.Realization(reclaim="redirect")),
                # 4 exe processes stride a miss batch — each reserves
                # the full ir_arena (2GB) so this stays bounded.
                workers=4,
                pinned=store.pins,
                cache_dir=(os.path.join(workdir, "nf_terms")
                           if workdir else None))
        if blob_run is None:
            # IR-egress kernel: stage NFs leave as PIR blobs the next
            # stage splices — the no-decode seam.
            blob_run = make_blob_runner(
                ir_exe_for(seed.Realization(
                    reclaim="redirect", io=("stdin", "ir"))),
                workers=4, pinned=store.pins)
    if bytes_run is not None:
        runs.setdefault("assemble*", bytes_run)
        runs.setdefault("pack*", bytes_run)
        runs.setdefault("pack", bytes_run)
    if term_run is not None:
        runs.setdefault("link", term_run)
        runs.setdefault("program", term_run)

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
            store.pin_named(st.program_pin_key(), st.PROGRAM_OF)
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
            store.pin_named(
                st.const_pin_key(
                    "link.%d.%d" % (len(imports), len(slots)),
                    st.link_src(len(imports), len(slots))),
                st.link_term(len(imports), len(slots)))
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
            os.makedirs(workdir, exist_ok=True)
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

        routines = rts.ROUTINES if routines is None else routines
        # _emit's record-context rule: IR-layout node code iff any
        # routine name is ir_* — same derivation the Python path uses
        _ir_ctx = any(n.startswith("ir_") for n in routines)
        # packed stage constants as content-addressed blobs: the
        # per-routine constants and the link section builders are
        # Pins are a pure splice overlay — registered lazily inside the
        # miss paths, so a fully-checkpointed warm emit never builds a
        # constant it won't pack (the pack2 bracket alone is ~22s).
        keys, qdigs = _ck_keys(R, imports, slots, text_base,
                               host_name=label, routines=routines,
                               passes=passes, fixed=fixed,
                               ir_ctx=_ir_ctx,
                               pinned=store.pins,
                               store=store) if workdir else ({}, {})

        prog_run = runs.get("program", run)

        def _frag_query(name: str) -> T:
            return st.routine_query(name, R, passes, fixed=fixed,
                                    ir_ctx=_ir_ctx)

        def _frag_items(name: str) -> list:
            """one routine query -> decoded frag items."""
            store.pin_named(st.routine_pin_key(name, fixed, _ir_ctx),
                            st.routine_of(name, fixed, _ir_ctx))
            nf, s, n = prog_run(_frag_query(name))
            report.append((f"program.{name}", s, n))
            if verbose:
                print(f"      program.{name}: {s} steps / {n} nodes",
                      flush=True)
            return _decode("frag", st.decode_frag, nf)

        def _prog_items() -> list:
            if getattr(R, "peephole", False):
                # the whole-program pass needs the frag-LIST NF —
                # cons the per-routine frag NFs back into
                # programOf's shape and run the seamed fixpoint.
                # Per-frag ckpts hold the PRE-pass items (the pass's
                # real input), so they stay valid under either
                # peephole setting.
                fragl: T = KK
                for name in reversed(routines):
                    t0r = time.time()
                    nf, s, n = prog_run(_frag_query(name))
                    report.append((f"program.{name}", s, n))
                    if verbose:
                        print(f"      program.{name}: {s} steps / "
                              f"{n} nodes ({fmt_dur(time.time()-t0r)})",
                              flush=True)
                    fragl = app(app(st._CONS, nf), fragl)
                prog_nf, npass, met = st.peephole_fixpoint_seamed(
                    fragl, runs.get("peephole_item")
                    or _peephole_item_runner())
                report.append(("peephole", met, npass))
                if verbose:
                    print(f"    peephole: {npass} passes", flush=True)
                return _decode("program", st.decode_program, prog_nf)
            out: List[tuple] = []
            names = list(routines)
            # batch the cache-miss fragments — the runner's pool
            # strides them across exes; hits never reach the reducer.
            bfn = getattr(prog_run, "batch", None)
            batched: Dict[str, list] = {}
            if bfn is not None:
                miss = [n for n in names if not (
                    workdir and os.path.exists(os.path.join(
                        workdir, "program.%s.%s"
                        % (n, keys.get("program." + n, "")))))]
                if miss:
                    for _n in miss:
                        store.pin_named(
                            st.routine_pin_key(_n, fixed, _ir_ctx),
                            st.routine_of(_n, fixed, _ir_ctx))
                    t0b = time.time()
                    nfs, s_b, _nb = bfn([_frag_query(n)
                                         for n in miss])
                    report.append(("program.batch", s_b, -1))
                    if verbose:
                        print(f"      program.batch: {len(miss)} "
                              f"frags, {s_b} steps "
                              f"({fmt_dur(time.time()-t0b)})",
                              flush=True)
                    for n, nf in zip(miss, nfs):
                        batched[n] = _decode("frag", st.decode_frag, nf)

            def _produce(name: str) -> list:
                if name in batched:
                    return batched[name]
                return _frag_items(name)

            for name in names:
                out.extend(_ck(f"program.{name}",
                               keys.get(f"program.{name}", ""),
                               lambda name=name: _produce(name),
                               _dump, _load))
            return out

        t0 = time.time()
        items = _ck("program.items", keys.get("program.items", ""),
                    _prog_items, _dump, _load)
        ib, db, syms = _ck("link.sections",
                           keys.get("link.sections", ""),
                           lambda: link_staged(
                               imports, slots, runs.get("link", run),
                               store=store, verbose=verbose,
                               run_ir=blob_run, run_bytes=bytes_run),
                           _dump, _load)
        text, _loc = _ck("text.bin", keys.get("text.bin", ""),
                         lambda: assemble_staged(
            items, syms, text_base, runs.get("assemble*", run),
            store=store, verbose=verbose), _dump, _load)
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
            if workdir:
                _write_manifest(workdir, R, label, routines, keys,
                                qdigs, runs, run, "pack*",
                                decodes=_dec_delta(dec0),
                                img=img, rt=rt)
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
    store.pin_named(st.const_pin_key("pack2", st.pack2_src()),
                    st.pack2_term())
    img_out = _stage("pack", st.pack2_query_t(
        text_t, idata_t, datab_t, R.stack_reserve))

    img = img_out if isinstance(img_out, bytes) \
        else _decode("bytecells", st._decode_bytecells, img_out)
    if workdir:
        with open(os.path.join(workdir, "image.bin"), "wb") as f:
            f.write(img)
        if decompose_asm:
            # keep the content-keyed name the manifest addresses —
            # the monolithic pack didn't go through _ck for image
            kimg = keys.get("image.bin")
            if kimg:
                with open(os.path.join(
                        workdir, "image.bin." + kimg), "wb") as f:
                    f.write(img)
            _write_manifest(workdir, R, label, routines, keys,
                            qdigs, runs, run, "pack",
                            decodes=_dec_delta(dec0),
                            img=img, rt=rt)
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


def _batch_bounded(batch, qs):
    """Batch in arena-bounded chunks.  A whole-list batch can exceed
    the kernel arena (pass-2 queries each re-carry the sym_t/loc_t
    resolver terms) even though every encode alone is small.  Halve
    on OOM until chunks fit; non-OOM failures and single-root
    failures propagate unchanged.  Pure scheduling — every query is
    independent and chunk order is preserved."""
    try:
        nfs, _, _ = batch(qs)
    except RuntimeError as e:
        if "rc=4" not in str(e) or len(qs) == 1:
            raise
        mid = len(qs) // 2
        return _batch_bounded(batch, qs[:mid]) \
            + _batch_bounded(batch, qs[mid:])
    return nfs


def link_staged(imports, slots,
                run: Callable[[T], Tuple[T, int, int]],
                store=None, verbose: bool = False,
                run_ir=None, run_bytes=None):
    """linkOf split at the section builders — the nanopass seam drops
    below linkOf itself: `idataOf IMPORTS` and `dataOf drva SLOTS`
    run as separate term reductions; drva = align(0x1000 + |idata|)
    is computed at the boundary (the same arithmetic
    target_pe64.data_rva performs — boundary glue, identical map);
    the symtab merge is the seam's dict-join, mirroring linkOf's
    `APPEND iat_syms data_syms` (data last — dict.update order).

    Both queries are program-independent — they only need imports/
    slots — so this leg can overlap the program stage entirely, and
    each query is small enough for the emitted kernels (the
    monolithic linkOf fold was the last graph.lo-sized term).
    Returns (idata, datab, syms) matching decode_link."""
    t0 = time.time()
    # drva depends on |idata| only — computable at the seam via the
    # oracle builder, so both queries ship in ONE batch stream.
    drva = target_pe64.data_rva(imports)
    if store is not None:
        store.pin_named(
            st.const_pin_key("idata.%d" % len(imports),
                             st.idata_src(len(imports))),
            st.idata_term(len(imports)))
        store.pin_named(
            st.const_pin_key("data.%d" % len(slots),
                             st.data_src(len(slots))),
            st.data_term(len(slots)))
    if (run_ir is not None and run_bytes is not None
            and store is not None
            and getattr(run_ir, "batch", None) is not None
            and getattr(run_bytes, "batch", None) is not None):
        # blob seam — zero decode_*: section NFs arrive as PIR blobs;
        # the byte sections are KERNEL projections (pair K -> byte
        # list -> byte-egress frames), and the merged symtab is a
        # kernel APPEND over blob args — a PIR blob that downstream
        # pass-2 queries splice via blob_term.  Python carries bytes
        # and blob refs only.
        sec, _, _ = run_ir.batch([st.idata_query(imports),
                                 st.data_query(slots, drva)])
        ph_i = store.blob_term(sec[0])
        ph_d = store.blob_term(sec[1])
        sects, _, _ = run_bytes.batch([app(ph_i, st.KK),
                                       app(ph_d, st.KK)])
        sm, _, _ = run_ir.batch([st._appn(st.append_term(),
                                        app(ph_i, st._KI),
                                        app(ph_d, st._KI))])
        if verbose:
            print(f"      link*: blob seam — idata+data frames, "
                  f"symtab {len(sm[0])}B PIR ({fmt_dur(time.time()-t0)})",
                  flush=True)
        # (idata_bytes, datab_bytes, symtab_blob) — the blob bytes are
        # what the checkpoint stores; assemble re-registers via
        # blob_term so the identity is content, not object.
        return sects[0], sects[1], sm[0]
    bfn = getattr(run, "batch", None)
    if bfn is not None:
        nfs, _, _ = bfn([st.idata_query(imports),
                         st.data_query(slots, drva)])
        idata, iat_syms = _decode("bytesyms", st.decode_bytesyms,
                                  nfs[0])
        datab, data_syms = _decode("bytesyms", st.decode_bytesyms,
                                   nfs[1])
    else:
        idata, iat_syms = _decode(
            "bytesyms", st.decode_bytesyms,
            run(st.idata_query(imports))[0])
        datab, data_syms = _decode(
            "bytesyms", st.decode_bytesyms,
            run(st.data_query(slots, drva))[0])
    syms = dict(iat_syms)
    syms.update(data_syms)
    if verbose:
        print(f"      link*: idata {len(idata)}B + data {len(datab)}B, "
              f"{len(syms)} syms ({fmt_dur(time.time()-t0)})", flush=True)
    return idata, datab, syms


def assemble_staged(items: List[tuple], syms: dict, base: int,
                    run: Callable[[T], Tuple[T, int, int]],
                    store=None,
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
    if isinstance(syms, (bytes, bytearray)):
        # blob seam: the merged symtab arrives as a kernel-emitted PIR
        # blob — registered as a placeholder, spliced into every
        # pass-2 query, never decoded Python-side.
        if store is None:
            raise toolchain.NotRealized(
                "symtab as packed-IR blob needs a BlobStore to splice")
        sym_t = store.blob_term(bytes(syms))
    else:
        sym_t = st.symtab_term(syms)
        if store is not None:
            # every pass-2 query re-carries sym_t/loc_t (plus the resv
            # closure) — pin once, every pack splices instead of
            # walking.
            store.pin_named(
                st.const_pin_key(
                    "symtab.%d" % len(syms), repr(sorted(syms.items()))),
                sym_t)
    if store is not None:
        store.pin(_resvmk())
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
        enc1 = _batch_bounded(batch, [_enc_q(it) for it in uq])
        for it, nf in zip(uq, enc1):
            uniq[it] = _enc_b(nf)
        n_red += len(uq)
        if verbose:
            print(f"      pass1: {n_red} encodes (bounded batches) "
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
    if store is not None:
        # loc is rebuilt per emit (positions), so this is an ephemeral
        # pin — same effect, no disk entry that could alias a
        # different layout
        store.pin(loc_t)
    rel = [(i, it) for i, (it, off, ln, b0) in enumerate(prep)
           if _is_rel_item(it)]
    rel_bytes: List[bytes] = []
    if rel:
        if batch is not None:
            qs2 = [_enc_q(it, st._appn(
                       _resvmk(), sym_t, loc_t,
                       st.bytelist_term(
                           (base + prep[i][1] + prep[i][2]).to_bytes(
                               4, "little"))))
                   for i, it in rel]
            rel_bytes = [_enc_b(nf)
                         for nf in _batch_bounded(batch, qs2)]
            n_red += len(rel)
            if verbose:
                print(f"      pass2: {n_red} encodes (bounded batches) "
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


_PACK_T: Dict[str, T] = {}


def _pack_term(name: str) -> T:
    """bracket(parse(st._NAME)) memoized — the pack recipe's
    vocabulary constants (ALIGN512/B4ADD/ZEROFILL/PADLIST/U64)."""
    t = _PACK_T.get(name)
    if t is None:
        t = _PACK_T[name] = bracket(parse(getattr(st, name)))
    return t


def _pack_recipe(text_len: int, idata_len: int, datab_len: int,
                 stackres: int) -> List[Tuple]:
    """pack2Of's chunk list as element data, in splice order:

      ("lit", bytes)   — format constants the stage emits verbatim
      ("root", T)      — a term whose NF is the chunk's bytes
      ("stage", name, frame) — a prior stage's frame(s); frame
                         0xFFFFFFFF splices all its frames in order

    The two realizations read it identically: the emit.plex bake
    serializes lit/root elements as stream queries and stage
    elements as MAP rows; pack_staged evaluates roots on a runner
    and inserts literals/section bytes directly.  Section sizes are
    int arguments (boundary metadata — the same discipline as
    assemble's pos bookkeeping; LENB4-as-term measured OOM-class),
    and the numeral args stay unreduced inside each query —
    confluence makes embedding the numeral identical to embedding
    its value."""
    def b4(v: int) -> T:
        return st.bytelist_term(v.to_bytes(4, "little"))

    lt, li, ld = b4(text_len), b4(idata_len), b4(datab_len)
    traw = st._appn(_pack_term("_ALIGN512"), lt)
    iraw = st._appn(_pack_term("_ALIGN512"), li)
    draw = st._appn(_pack_term("_ALIGN512"), ld)
    # section VAs — .idata fixed at 0x1000, .data and .text computed
    # (pack2Of's drva/trva lets); .text LAST keeps code size unbounded.
    drva = st._appn(_pack_term("_ALIGN4096"),
                    st._appn(_pack_term("_B4ADD"), b4(0x1000), li))
    trva = st._appn(_pack_term("_ALIGN4096"),
                    st._appn(_pack_term("_B4ADD"), drva, ld))
    dptr = st._appn(_pack_term("_B4ADD"), b4(0x200), iraw)
    tptr = st._appn(_pack_term("_B4ADD"), dptr, draw)
    iddr = st._appn(_pack_term("_B4ADD"), iraw, draw)
    img = st._appn(_pack_term("_ALIGN4096"),
                   st._appn(_pack_term("_B4ADD"), trva, lt))
    u64 = st._appn(_pack_term("_U64"), b4(stackres))

    def zf(n: int) -> T:
        return st._appn(_pack_term("_ZEROFILL"), st.church(n))

    def pad(len4: T) -> T:
        return st._appn(_pack_term("_PADLIST"), len4)

    z12 = zf(12)
    L = lambda b: ("lit", b)
    R_ = lambda t: ("root", t)
    ALL = 0xFFFFFFFF
    return [
        L(b"MZ"), R_(zf(58)), L(struct.pack("<I", 0x40)),
        L(b"PE\x00\x00"),
        L(struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0, 0x22)),
        L(struct.pack("<HBB", 0x20B, 0, 0)),
        R_(traw), R_(iddr), L(struct.pack("<I", 0)),
        R_(trva), R_(trva),
        L(struct.pack("<Q", 0x140000000)),
        L(struct.pack("<II", 0x1000, 0x200)),
        L(struct.pack("<HHHHHH", 6, 0, 0, 0, 6, 0)),
        L(struct.pack("<I", 0)), R_(img),
        L(struct.pack("<II", 0x200, 0)),
        L(struct.pack("<HH", 3, 0x8100)),
        R_(u64),
        L(struct.pack("<QQQ", 0x1000, 0x100000, 0x1000)),
        L(struct.pack("<II", 0, 16)), L(struct.pack("<II", 0, 0)),
        L(struct.pack("<I", 0x1000)), R_(li),
        R_(zf(14 * 8)),
        L(b".idata\x00\x00"), R_(li),
        L(struct.pack("<I", 0x1000)), R_(iraw),
        L(struct.pack("<I", 0x200)), R_(z12),
        L(struct.pack("<I", 0x40000040)),
        L(b".data\x00\x00\x00"), R_(ld),
        R_(drva), R_(draw), R_(dptr), R_(z12),
        L(struct.pack("<I", 0xC0000040)),
        L(b".text\x00\x00\x00"), R_(lt),
        R_(trva), R_(traw), R_(tptr), R_(z12),
        L(struct.pack("<I", 0x60000020)),
        R_(zf(0x200 - 448)),
        ("stage", "emit.link", 0), R_(pad(li)),
        ("stage", "emit.link", 1), R_(pad(ld)),
        ("stage", "emit.assemble", ALL), R_(pad(lt)),
    ]


def pack_staged(text: bytes, idata: bytes, datab: bytes,
                stackres: int,
                run: Callable[[T], Tuple[T, int, int]],
                verbose: bool = False) -> bytes:
    """pack2Of decomposed at chunk granularity — evaluates
    _pack_recipe: root elements are small `run`-ed term reductions
    over the vocabulary constants; lit elements are emitted
    verbatim; stage elements insert the linked/assembled sections.
    The byte join is the seam (identical to what pack2Of's JOIN
    computes — the oracle gate `python_pack` verifies byte-exact)."""
    import plex_bundle as pb
    sects = {("emit.link", 0): idata, ("emit.link", 1): datab,
             ("emit.assemble", pb.MAP_ALL): text}
    bytes_mode = getattr(run, "is_bytes", False)
    chunks = []
    for e in _pack_recipe(len(text), len(idata), len(datab),
                          stackres):
        if e[0] == "lit":
            chunks.append(e[1])
        elif e[0] == "stage":
            chunks.append(sects[(e[1], e[2])])
        else:
            nf = run(e[1])[0]
            chunks.append(nf if bytes_mode
                          else st._decode_bytecells(nf))
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
        ka = _ck_keys(seed.Realization(), rts.IMPORTS,
                      rts.DATA_SLOTS,
                      target_pe64.text_rva(rts.IMPORTS,
                                           rts.DATA_SLOTS))[0]
        kb = _ck_keys(seed.Realization(fuel=7), rts.IMPORTS,
                      rts.DATA_SLOTS,
                      target_pe64.text_rva(rts.IMPORTS,
                                           rts.DATA_SLOTS))[0]
        same = ka == _ck_keys(
            seed.Realization(), rts.IMPORTS, rts.DATA_SLOTS,
            target_pe64.text_rva(rts.IMPORTS, rts.DATA_SLOTS))[0]
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
