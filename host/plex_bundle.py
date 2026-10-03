"""plex_bundle — .plex v3 archive (ADR-0006): directory + fixed-width
row tables + COO relations.  Python writer/reader; the layout is chosen
so a native depacker needs only index arithmetic — no varints, no
pointers inside rows, every string/blob an (off,len) ref into a pool
section.

Wire layout (little-endian):

    offset  size  field
    0       4     magic 'PLEX'
    4       1     version = 3
    5       1     flags (0)
    6       2     header_size (u16) — offset of section area =
                  align8(12 + 32*n_sections)
    8       4     n_sections (u32)
    12      n*32  directory entries
    ..      pad   to 8
    hsize   ..    sections, each offset 8B-aligned

Directory entry (32B):

    +0   u8   type      cell width: 1=u8, 4=u32, 8=u64
    +1   u8   arity     cells per row
    +2   u16  kind      role (below)
    +4   u32  reserved  0
    +8   u64  offset    absolute, 8B-aligned
    +16  u64  length    payload bytes
    +24  u64  rows      row count

Invariant: length == rows * arity * type_width.  Pool sections
(STRINGS/BYTES) are (u8, arity 1) so rows == length.

Section kinds (the contract role table):

    1 STRINGS      UTF-8 pool; row refs are (off,len) into it
    2 STAGES       u64 arity 6: (name, artifact, runner) string refs —
                   the manifest's stage DAG nodes
    3 DEPS         u32 arity 2: (stage_idx, dep_stage_idx) — COO edges
    4 QUERIES      u64 arity 5: stage_idx + (digest, blob) string refs
    5 CAPS         u64 arity 5: tag(0=port,1=os binding) + key ref +
                   val ref (mode / comma ports / "" = intrinsic)
    6 REALIZATION  u64 arity 4: (key, val) string refs — R fields +
                   routines-record name
    7 CLAIM        u64 arity 6: (statement, checker, boundary) refs —
                   W |-_{L,B} C(A); emitted only with evidence
    8 EVIDENCE     u64 arity 4: (key, val) string refs — decode
                   counters, format label, oracle digests
    9 BYTES        payload pool (image.bin, stage blobs)

Refusals (BundleError): bad magic/version, truncated header or
directory, unknown cell type, zero arity, length != rows*arity*type,
unaligned or out-of-range section span, missing required section kind,
string ref out of the pool.  No silent defaults — a malformed bundle
is a loud failure, not a partial read.
"""
from __future__ import annotations

import struct
from typing import Dict, Iterable, List, Optional, Tuple

MAGIC = b"PLEX"
VERSION = 3
_HEADER = 12           # magic + ver + flags + hsize + n_sections
_DIR_ENT = 32
_ALIGN = 8

# cell widths
U8, U32, U64 = 1, 4, 8
_WIDTHS = {U8, U32, U64}

# section kinds — the contract role table
KIND_STRINGS = 1
KIND_STAGES = 2
KIND_DEPS = 3
KIND_QUERIES = 4
KIND_CAPS = 5
KIND_REALIZATION = 6
KIND_CLAIM = 7
KIND_EVIDENCE = 8
KIND_BYTES = 9

_KIND_NAMES = {v: k for k, v in {
    "STRINGS": KIND_STRINGS, "STAGES": KIND_STAGES, "DEPS": KIND_DEPS,
    "QUERIES": KIND_QUERIES, "CAPS": KIND_CAPS,
    "REALIZATION": KIND_REALIZATION, "CLAIM": KIND_CLAIM,
    "EVIDENCE": KIND_EVIDENCE, "BYTES": KIND_BYTES}.items()}

CAP_PORT = 0
CAP_OS = 1


class BundleError(ValueError):
    """Malformed or unclaimed bundle content — a refusal, never a
    partial read."""


class Section:
    """One directory entry: kind/geometry + payload span."""
    __slots__ = ("kind", "type", "arity", "offset", "length", "rows",
                 "_payload")

    def __init__(self, kind: int, type: int, arity: int,
                 rows: int, payload: bytes = b""):
        self.kind, self.type, self.arity = kind, type, arity
        self.offset, self.rows = 0, rows
        if payload and type == U8 and arity == 1:
            self.length = len(payload)
            self.rows = rows or len(payload)
        else:
            self.length = rows * arity * type
        self._payload = payload

    def payload(self, data: bytes) -> bytes:
        return data[self.offset:self.offset + self.length]


def _pad8(n: int) -> int:
    return (-n) % _ALIGN


def pack_bundle(sections: Iterable[Section]) -> bytes:
    """Serialize directory + aligned section payloads."""
    secs = list(sections)
    hsize = _HEADER + _DIR_ENT * len(secs)
    hsize += _pad8(hsize)
    out = bytearray()
    out += struct.pack("<4sBBHI", MAGIC, VERSION, 0, hsize, len(secs))
    dir_pos = len(out)
    out += b"\x00" * (hsize - dir_pos)
    pos = hsize
    body = bytearray()
    for s in secs:
        if s.type not in _WIDTHS:
            raise BundleError(f"section kind {s.kind}: bad cell "
                              f"width {s.type}")
        if s.arity < 1:
            raise BundleError(f"section kind {s.kind}: arity 0")
        if s.length != s.rows * s.arity * s.type:
            raise BundleError(
                f"section kind {s.kind}: length {s.length} != "
                f"rows*arity*type {s.rows * s.arity * s.type}")
        payload = s._payload
        if len(payload) != s.length:
            payload = payload.ljust(s.length, b"\x00")[:s.length]
        s.offset = pos
        struct.pack_into("<BBHIQQQ", out, dir_pos, s.type, s.arity,
                         s.kind, 0, s.offset, s.length, s.rows)
        dir_pos += _DIR_ENT
        body += payload
        pad = _pad8(len(payload))
        body += b"\x00" * pad
        pos += s.length + pad
    return bytes(out + body)


class Bundle:
    """Parsed v3 archive — directory view + decoded row helpers."""
    __slots__ = ("data", "flags", "sections")

    def __init__(self, data: bytes, flags: int,
                 sections: List[Section]):
        self.data, self.flags, self.sections = data, flags, sections

    def section(self, kind: int) -> Optional[Section]:
        for s in self.sections:
            if s.kind == kind:
                return s
        return None

    def require(self, kind: int) -> Section:
        s = self.section(kind)
        if s is None:
            raise BundleError(
                f"bundle: required section {_KIND_NAMES.get(kind, kind)} "
                f"({kind}) is missing")
        return s

    def _rows(self, kind: int, arity: int, fmt: str
              ) -> List[Tuple[int, ...]]:
        s = self.require(kind)
        if s.arity != arity:
            raise BundleError(
                f"bundle: {_KIND_NAMES[kind]} arity {s.arity} != "
                f"{arity}")
        cell = struct.calcsize(fmt)
        if s.type != cell:
            raise BundleError(
                f"bundle: {_KIND_NAMES[kind]} cell width {s.type} != "
                f"{cell}")
        row_fmt = f"<{arity}{fmt[1:]}"
        p = s.payload(self.data)
        return [struct.unpack_from(row_fmt, p, i * cell * arity)
                for i in range(s.rows)]

    # -- typed views -------------------------------------------------
    def strings(self) -> bytes:
        return self.require(KIND_STRINGS).payload(self.data)

    def _sref(self, pool: bytes, off: int, ln: int) -> str:
        if off + ln > len(pool):
            raise BundleError(
                f"bundle: string ref ({off},{ln}) outside "
                f"pool {len(pool)}")
        return pool[off:off + ln].decode("utf-8")

    def stage_rows(self) -> List[Tuple[str, str, str]]:
        pool = self.strings()
        return [tuple(self._sref(pool, r[i], r[i + 1])
                      for i in (0, 2, 4))
                for r in self._rows(KIND_STAGES, 6, "<Q")]

    def dep_edges(self) -> List[Tuple[int, int]]:
        s = self.section(KIND_DEPS)
        if s is None:
            return []
        return [(r[0], r[1]) for r in self._rows(KIND_DEPS, 2, "<I")]

    def query_rows(self) -> List[Tuple[int, str, str]]:
        s = self.section(KIND_QUERIES)
        if s is None:
            return []
        pool = self.strings()
        return [(r[0], self._sref(pool, r[1], r[2]),
                 self._sref(pool, r[3], r[4]))
                for r in self._rows(KIND_QUERIES, 5, "<Q")]

    def caps_rows(self) -> List[Tuple[int, str, str]]:
        s = self.section(KIND_CAPS)
        if s is None:
            return []
        pool = self.strings()
        return [(r[0], self._sref(pool, r[1], r[2]),
                 self._sref(pool, r[3], r[4]))
                for r in self._rows(KIND_CAPS, 5, "<Q")]

    def kv_rows(self, kind: int) -> Dict[str, str]:
        s = self.section(kind)
        if s is None:
            return {}
        if kind not in (KIND_REALIZATION, KIND_EVIDENCE):
            raise BundleError(f"bundle: kind {kind} is not a KV table")
        pool = self.strings()
        return {self._sref(pool, r[0], r[1]): self._sref(pool, r[2], r[3])
                for r in self._rows(kind, 4, "<Q")}

    def bytes_pool(self) -> bytes:
        s = self.section(KIND_BYTES)
        return s.payload(self.data) if s is not None else b""


def read_bundle(data: bytes) -> Bundle:
    """Parse + validate a v3 archive.  Raises BundleError on any
    malformed field — no partial reads."""
    if len(data) < _HEADER:
        raise BundleError("bundle: truncated header")
    magic, ver, flags, hsize, nsec = struct.unpack_from(
        "<4sBBHI", data, 0)
    if magic != MAGIC:
        raise BundleError(f"bundle: bad magic {magic!r}")
    if ver != VERSION:
        raise BundleError(f"bundle: version {ver} != {VERSION}")
    dir_end = _HEADER + _DIR_ENT * nsec
    if hsize < dir_end or hsize % _ALIGN:
        raise BundleError(
            f"bundle: header_size {hsize} covers {nsec} entries")
    if len(data) < dir_end:
        raise BundleError("bundle: truncated directory")
    sections = []
    for i in range(nsec):
        t, ar, kind, _res, off, ln, rows = struct.unpack_from(
            "<BBHIQQQ", data, _HEADER + i * _DIR_ENT)
        if t not in _WIDTHS:
            raise BundleError(f"bundle: section {i} bad type {t}")
        if ar < 1:
            raise BundleError(f"bundle: section {i} arity 0")
        if ln != rows * ar * t:
            raise BundleError(
                f"bundle: section {i} length {ln} != "
                f"rows*arity*type {rows * ar * t}")
        if off < hsize or off % _ALIGN or off + ln > len(data):
            raise BundleError(
                f"bundle: section {i} span ({off:#x}+{ln:#x}) "
                f"outside archive {len(data):#x}")
        s = Section(kind, t, ar, rows)
        s.offset, s.length = off, ln
        sections.append(s)
    return Bundle(data, flags, sections)


# -------------------------------------------------------------------
# manifest <-> sections: the emit chain's stage DAG as row tables


class _Pool:
    def __init__(self):
        self.buf = bytearray()
        self.refs: Dict[str, Tuple[int, int]] = {}

    def ref(self, s: str) -> Tuple[int, int]:
        r = self.refs.get(s)
        if r is None:
            b = s.encode("utf-8")
            r = (len(self.buf), len(b))
            self.buf += b
            self.refs[s] = r
        return r


def manifest_sections(man: dict, image: Optional[bytes] = None,
                      caps: Optional[dict] = None,
                      realization: Optional[dict] = None
                      ) -> List[Section]:
    """Encode a plex.stage-manifest/1 dict as v3 sections: STAGES rows
    (name, artifact, runner), DEPS COO edges, QUERIES blob refs,
    EVIDENCE KV (format/label/created/decodes), REALIZATION KV, CAPS
    rows, and the image as BYTES payload."""
    pool = _Pool()
    stages = man.get("stages", [])
    sidx = {s["name"]: i for i, s in enumerate(stages)}

    stage_rows = []
    dep_pairs: List[Tuple[int, int]] = []
    query_rows = []
    for i, s in enumerate(stages):
        for f in ("name", "artifact", "runner"):
            if f not in s:
                raise BundleError(f"manifest stage {i}: missing {f!r}")
        for d in s.get("deps", []):
            if d not in sidx:
                raise BundleError(
                    f"manifest stage {s['name']}: dep {d} not a stage")
            dep_pairs.append((i, sidx[d]))
        for q in s.get("queries", []):
            do, dl = pool.ref(str(q.get("digest", "")))
            bo, bl = pool.ref(str(q.get("blob", "")))
            query_rows.append((i, do, dl, bo, bl))
        stage_rows.append(tuple(v for f in ("name", "artifact",
                                            "runner")
                                for v in pool.ref(str(s[f]))))

    ev: Dict[str, str] = {"format": str(man.get("format", "")),
                          "label": str(man.get("label", "")),
                          "created_utc": str(man.get("created_utc", ""))}
    for k, v in (man.get("decodes") or {}).items():
        ev[f"decodes.{k}"] = str(v)
    ev_rows = [pool.ref(k) + pool.ref(val) for k, val in
               sorted(ev.items())]

    secs = [Section(KIND_STRINGS, U8, 1, 0, bytes(pool.buf))]
    secs[0].rows = secs[0].length

    def _u64rows(rows: List[Tuple[int, ...]]) -> bytes:
        return b"".join(struct.pack(f"<{len(r)}Q", *r) for r in rows)

    secs.append(Section(KIND_STAGES, U64, 6, len(stage_rows),
                        _u64rows(stage_rows)))
    if dep_pairs:
        secs.append(Section(KIND_DEPS, U32, 2, len(dep_pairs),
                            b"".join(struct.pack("<II", *p)
                                     for p in dep_pairs)))
    if query_rows:
        secs.append(Section(KIND_QUERIES, U64, 5, len(query_rows),
                            _u64rows(query_rows)))
    if realization:
        rrows = [pool.ref(str(k)) + pool.ref(str(v))
                 for k, v in sorted(realization.items())]
        secs.append(Section(KIND_REALIZATION, U64, 4, len(rrows),
                            _u64rows(rrows)))
    if caps:
        crows = []
        for p, m in sorted(caps.get("ports", {}).items()):
            ko, kl = pool.ref(str(p))
            vo, vl = pool.ref(str(m))
            crows.append((CAP_PORT, ko, kl, vo, vl))
        for b, pl in sorted(caps.get("os", {}).items()):
            ko, kl = pool.ref(str(b))
            vo, vl = pool.ref(",".join(str(p) for p in pl))
            crows.append((CAP_OS, ko, kl, vo, vl))
        secs.append(Section(KIND_CAPS, U64, 5, len(crows),
                            _u64rows(crows)))
    secs.append(Section(KIND_EVIDENCE, U64, 4, len(ev_rows),
                        _u64rows(ev_rows)))
    if image is not None:
        secs.append(Section(KIND_BYTES, U8, 1, 0, image))
        secs[-1].rows = secs[-1].length
    # the string pool grew while building later sections — rebuild it
    secs[0] = Section(KIND_STRINGS, U8, 1, 0, bytes(pool.buf))
    secs[0].rows = secs[0].length
    return secs


def sections_manifest(bundle: Bundle) -> dict:
    """Reconstruct the plex.stage-manifest/1 dict from a bundle —
    the replay path consumes the same shape it consumed from
    manifest.json."""
    stages = [{"name": n, "artifact": a, "runner": r}
              for n, a, r in bundle.stage_rows()]
    for s in stages:
        s["deps"] = []
        s["queries"] = []
    for i, j in bundle.dep_edges():
        if i >= len(stages) or j >= len(stages):
            raise BundleError(f"bundle: dep edge ({i},{j}) outside "
                              f"{len(stages)} stages")
        stages[i]["deps"].append(stages[j]["name"])
    for i, dig, blob in bundle.query_rows():
        if i >= len(stages):
            raise BundleError(f"bundle: query stage {i} outside "
                              f"{len(stages)} stages")
        stages[i]["queries"].append({"digest": dig, "blob": blob})
    ev = bundle.kv_rows(KIND_EVIDENCE)
    dec = {k[len("decodes."):]: int(v) for k, v in ev.items()
           if k.startswith("decodes.")}
    man = {"format": ev.get("format", ""),
           "label": ev.get("label", ""),
           "created_utc": ev.get("created_utc", ""),
           "decodes": dec or None,
           "stages": stages}
    return man


def caps_dict(rows: List[Tuple[int, str, str]]) -> dict:
    """CAPS rows -> the {ports, os} declaration shape."""
    ports, osb = {}, {}
    for tag, k, v in rows:
        if tag == CAP_PORT:
            ports[k] = v
        elif tag == CAP_OS:
            osb[k] = [p for p in v.split(",") if p]
        else:
            raise BundleError(f"bundle: caps row tag {tag}")
    return {"ports": ports, "os": osb}


def check_bundle_caps(bundle: Bundle, declared: dict) -> List[str]:
    """bundle caps ⊆ the routines record's declared caps — the
    archive may claim less than the host record, never more; an
    undeclared binding or widened port mode is a refusal."""
    errs = []
    have = caps_dict(bundle.caps_rows())
    for b, plist in have["os"].items():
        if b not in declared.get("os", {}):
            errs.append(f"bundle: binding {b!r} not in record caps")
        elif set(plist) - set(declared["os"][b]):
            errs.append(f"bundle: binding {b!r} ports {plist} widen "
                        f"record {declared['os'][b]}")
    for p, m in have["ports"].items():
        if p not in declared.get("ports", {}):
            errs.append(f"bundle: port {p!r} not in record caps")
        elif m != declared["ports"][p]:
            errs.append(f"bundle: port {p!r} mode {m!r} != record "
                        f"{declared['ports'][p]!r}")
    return errs
