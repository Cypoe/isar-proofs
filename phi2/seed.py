"""seed.py - the sole Python substrate of phi2.

Everything above this file is data: .plex bundles carrying terms,
rel-graphs, kernel matrices, quotient maps.  seed.py holds only what
cannot yet be data:

    .plex v3 codec      read/write the canonical bundle (index
                        arithmetic only - no varints, no pointers)
    kernel decode       KERNEL section -> the four ISAR matrices;
                        slice signatures derived, not hardcoded
    the stepper         the 8 declared ops {ATOM PAIR FRESH UNIFY
                        MATCH APPLY CHOICE RUN} executed over terms -
                        union-find subst, lazy goal streams, clause
                        extensions, fuel as the termination invariant
    ports               file/stdout/stdin - the machine-context seam

The Lean vocabulary is the contract: this file is `eval`'s stage-0
realization.  specialize/realize/cogen live in the corpus as .plex
programs; when eval.plex can run them the stepper here shrinks to
the codec + kernel decode alone.

Term encoding (wire + runtime, one form):
    ("atom", bits, payload:int)   T[n] nibble atom; (0,0) is NIL
    ("pair", a, b)                adjacency
    ("var", id:int|str)           logic var (int = fresh, str = pat-scope)
    ("sym", name)                 'name literal - rel names as values
    ("reldef", name)              env_lookup result
    ("goalterm", name, [args])    a call as data - RUN/CHOICE dispatch
    ("atom_lazy", *fields)        atom_dyn deferred under subst
    ("pat", name) ("bodycall", name)   def.pat / def.body projections
"""
from __future__ import annotations

import itertools
import json
import os
import struct
import sys
from typing import Dict, Iterator, List, Optional, Tuple

# ---------------------------------------------------------------------------
# .plex v3 codec - directory + fixed-width rows (re-derived, no host import)
# ---------------------------------------------------------------------------

MAGIC = b"PLEX"
VERSION = 3
_HEADER = 12
_DIR = 32
_ALIGN = 8
U8, U32, U64 = 1, 4, 8
_WIDTHS = {U8, U32, U64}

KIND_STRINGS = 1
KIND_REALIZATION = 6
KIND_BYTES = 9
KIND_KERNEL = 12          # u8 x 16 x 4: the four 4x4 kernel matrices
KIND_OPS = 13             # u8 x 1: the declared op slice ordering

_KIND_NAMES = {1: "STRINGS", 6: "REALIZATION", 9: "BYTES",
               12: "KERNEL", 13: "OPS"}


class BundleError(ValueError):
    """Malformed bundle - a refusal, never a partial read."""


class Section:
    __slots__ = ("kind", "type", "arity", "offset", "length", "rows",
                 "_payload")

    def __init__(self, kind, type, arity, rows, payload=b""):
        self.kind, self.type, self.arity = kind, type, arity
        self.offset, self.rows = 0, rows
        if payload and type == U8 and arity == 1:
            self.length = len(payload)
            self.rows = rows or len(payload)
        else:
            self.length = rows * arity * type
        self._payload = payload

    def payload(self, data):
        return data[self.offset:self.offset + self.length]


def _pad8(n):
    return (-n) % _ALIGN


def pack_bundle(sections):
    secs = list(sections)
    hsize = _HEADER + _DIR * len(secs)
    hsize += _pad8(hsize)
    out = bytearray()
    out += struct.pack("<4sBBHI", MAGIC, VERSION, 0, hsize, len(secs))
    dpos = len(out)
    out += b"\x00" * (hsize - dpos)
    pos, body = hsize, bytearray()
    for s in secs:
        if s.type not in _WIDTHS:
            raise BundleError(f"section kind {s.kind}: bad width "
                              f"{s.type}")
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
        struct.pack_into("<BBHIQQQ", out, dpos, s.type, s.arity,
                         s.kind, 0, s.offset, s.length, s.rows)
        dpos += _DIR
        body += payload + b"\x00" * _pad8(len(payload))
        pos += s.length + _pad8(len(payload))
    return bytes(out + body)


class Bundle:
    __slots__ = ("data", "flags", "sections")

    def __init__(self, data, flags, sections):
        self.data, self.flags, self.sections = data, flags, sections

    def section(self, kind):
        for s in self.sections:
            if s.kind == kind:
                return s
        return None

    def require(self, kind):
        s = self.section(kind)
        if s is None:
            raise BundleError(
                f"bundle: required section "
                f"{_KIND_NAMES.get(kind, kind)} ({kind}) missing")
        return s

    def _rows(self, kind, arity, fmt):
        s = self.require(kind)
        if s.arity != arity:
            raise BundleError(
                f"bundle: {_KIND_NAMES[kind]} arity {s.arity} != "
                f"{arity}")
        cell = struct.calcsize(fmt)
        if s.type != cell:
            raise BundleError(
                f"bundle: {_KIND_NAMES[kind]} cell width {s.type} "
                f"!= {cell}")
        row_fmt = f"<{arity}{fmt[1:]}"
        p = s.payload(self.data)
        return [struct.unpack_from(row_fmt, p, i * cell * arity)
                for i in range(s.rows)]

    def strings(self):
        return self.require(KIND_STRINGS).payload(self.data)

    def _sref(self, pool, off, ln):
        if off + ln > len(pool):
            raise BundleError(
                f"bundle: string ref ({off},{ln}) outside "
                f"pool {len(pool)}")
        return pool[off:off + ln].decode("utf-8")

    def kv_rows(self, kind):
        s = self.section(kind)
        if s is None:
            return {}
        if kind != KIND_REALIZATION:
            raise BundleError(f"bundle: kind {kind} is not a KV table")
        pool = self.strings()
        return {self._sref(pool, r[0], r[1]):
                self._sref(pool, r[2], r[3])
                for r in self._rows(kind, 4, "<Q")}

    def bytes_pool(self):
        s = self.section(KIND_BYTES)
        return s.payload(self.data) if s is not None else b""


def read_bundle(data):
    if len(data) < _HEADER:
        raise BundleError("bundle: truncated header")
    magic, ver, flags, hsize, nsec = struct.unpack_from(
        "<4sBBHI", data, 0)
    if magic != MAGIC:
        raise BundleError(f"bundle: bad magic {magic!r}")
    if ver != VERSION:
        raise BundleError(f"bundle: version {ver} != {VERSION}")
    dir_end = _HEADER + _DIR * nsec
    if hsize < dir_end or hsize % _ALIGN:
        raise BundleError(
            f"bundle: header_size {hsize} covers {nsec} entries")
    if len(data) < dir_end:
        raise BundleError("bundle: truncated directory")
    sections = []
    for i in range(nsec):
        t, ar, kind, _r, off, ln, rows = struct.unpack_from(
            "<BBHIQQQ", data, _HEADER + i * _DIR)
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


class _Pool:
    def __init__(self):
        self.buf = bytearray()
        self.refs: Dict[str, Tuple[int, int]] = {}

    def ref(self, s):
        r = self.refs.get(s)
        if r is None:
            b = s.encode("utf-8")
            r = (len(self.buf), len(b))
            self.buf += b
            self.refs[s] = r
        return r


def kv_section(realization: dict, pool: _Pool) -> Section:
    rrows = [pool.ref(str(k)) + pool.ref(str(v))
             for k, v in sorted(realization.items())]
    return Section(KIND_REALIZATION, U64, 4, len(rrows),
                   b"".join(struct.pack(f"<{len(r)}Q", *r)
                            for r in rrows))


def graph_bundle(graph: dict) -> bytes:
    """phi.rel/1 rel-graph -> .plex (STRINGS + REALIZATION + BYTES).
    Same section shape the donor phi_rel.graph_bundle writes - the
    corpus bundles are readable by both machines."""
    if graph.get("format") != "phi.rel/1":
        raise BundleError(
            f"rel-graph format {graph.get('format')!r} - need "
            f"phi.rel/1")
    pool = _Pool()
    secs = [Section(KIND_STRINGS, U8, 1, 0, b"")]
    secs.append(kv_section(
        {"dialect": "phi.rel/1",
         "rels": str(len(graph.get("rels", [])))}, pool))
    blob = json.dumps(graph, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")
    secs.append(Section(KIND_BYTES, U8, 1, 0, blob))
    secs[-1].rows = secs[-1].length
    secs[0] = Section(KIND_STRINGS, U8, 1, 0, bytes(pool.buf))
    secs[0].rows = secs[0].length
    return pack_bundle(secs)


def read_graph_bundle(data: bytes) -> dict:
    b = read_bundle(data)
    real = b.kv_rows(KIND_REALIZATION)
    if real.get("dialect") != "phi.rel/1":
        raise BundleError(
            f"rel bundle dialect {real.get('dialect')!r} - need "
            f"phi.rel/1")
    blob = b.bytes_pool()
    if not blob:
        raise BundleError("rel bundle: no rel-graph blob")
    return json.loads(blob)


# ---------------------------------------------------------------------------
# kernel - the 64-byte head: four 4x4 matrices, ops as declared slices
# ---------------------------------------------------------------------------

# Lean ISARMatrices.lean version 1 (isar_categorical_proof lineage -
# plex/core's set; v2 differs only in R, conjugate via gauge P and
# derivable, so v1 is the stored form).
_KERNEL_V1 = (
    (1, 0, 0, 0,  0, 0, 0, 0,  0, 0, 1, 0,  0, 0, 0, 0),   # I
    (1, 0, 0, 0,  0, 0, 0, 0,  0, 1, 0, 0,  0, 0, 1, 0),   # R
    (0, 0, 0, 0,  1, 0, 0, 0,  0, 1, 0, 0,  0, 0, 0, 0),   # A
    (1, 1, 0, 0,  0, 1, 0, 0,  0, 0, 1, 0,  0, 0, 0, 1),   # S
)
_KERNEL_NAMES = ("I", "R", "A", "S")

# The declared op slice ordering - nibble tags are indices into this
# table, never hardcoded constants (patent phi-boot-self K table).
OPS = ("ATOM", "PAIR", "FRESH", "UNIFY",
       "MATCH", "APPLY", "CHOICE", "RUN")
OP = {n: i for i, n in enumerate(OPS)}


def kernel_bundle() -> bytes:
    """kernel.plex - KERNEL cells (u8, +1 bias for the {-1,0,1}
    alphabet) + OPS ordering + REALIZATION declaring the set."""
    pool = _Pool()
    secs = [Section(KIND_STRINGS, U8, 1, 0, b"")]
    cells = bytes(v + 1 for m in _KERNEL_V1 for v in m)
    secs.append(Section(KIND_KERNEL, U8, 16, 4, cells))
    secs.append(Section(KIND_OPS, U8, 1, 0,
                        bytes(range(len(OPS)))))
    secs[-1].rows = 8
    secs[-1].length = 8
    secs.append(kv_section({
        "dialect": "phi.kernel/1",
        "set": "isar.v1",
        "matrices": ",".join(_KERNEL_NAMES),
        "bias": "1",
        "ops": ",".join(OPS)}, pool))
    secs[0] = Section(KIND_STRINGS, U8, 1, 0, bytes(pool.buf))
    secs[0].rows = secs[0].length
    return pack_bundle(secs)


def _matmul(A, B):
    return tuple(
        sum(A[r * 4 + k] * B[k * 4 + c] for k in range(4))
        for r in range(4) for c in range(4))


def sig_diag(m):
    return sum(1 << i for i in range(4) if m[i * 4 + i] != 0) & 7


def sig_row(m, row):
    return sum(1 << i for i in range(4) if m[row * 4 + i] != 0) & 7


def read_kernel(data: bytes) -> dict:
    """kernel.plex -> {matrices, ops} - slices decoded and checked
    against the declared ordering; a forged kernel field is a
    refusal, not a silent default."""
    b = read_bundle(data)
    real = b.kv_rows(KIND_REALIZATION)
    if real.get("dialect") != "phi.kernel/1":
        raise BundleError(
            f"kernel bundle dialect {real.get('dialect')!r}")
    bias = int(real.get("bias", "1"))
    s = b.require(KIND_KERNEL)
    if s.arity != 16 or s.rows != 4:
        raise BundleError(
            f"kernel: KERNEL section must be 4 rows x 16 cells, "
            f"got {s.rows}x{s.arity}")
    p = s.payload(b.data)
    mats = {name: tuple(v - bias for v in
                      p[i * 16:(i + 1) * 16])
            for i, name in enumerate(_KERNEL_NAMES)}
    decl = real.get("ops", "")
    ops = tuple(decl.split(",")) if decl else ()
    if ops != OPS:
        raise BundleError(
            f"kernel: ops ordering {decl!r} != the declared "
            f"8-slice table")
    # slice signatures: the standing derivation check - the
    # ontological value-tags come out of the matrices, not a table.
    i, a, s_ = mats["I"], mats["A"], mats["S"]
    assert sig_diag(a) == 0, "TAG_INT slice drifted"
    assert sig_diag(i) == 5, "TAG_SYM slice drifted"
    assert sig_row(s_, 0) == 3, "TAG_DAT slice drifted"
    # the rewrite operator K = I*R*A*S is nilpotent (Lean: rfl)
    k = _matmul(mats["I"], _matmul(
        mats["R"], _matmul(mats["A"], mats["S"])))
    assert _matmul(k, k) == (0,) * 16, "K^2 != 0 - kernel drifted"
    return {"matrices": mats, "ops": ops}


# ---------------------------------------------------------------------------
# terms + subst + unify - the stepper's value model
# ---------------------------------------------------------------------------

# terms live in an interned flat arena: every node is an int id.
# Structural equality is id equality (hash-consing), groundness is
# a construction-time bit, memo keys are tuples of ints — the same
# discipline as graph_runtime's interned dag heap, ported to the
# relational stepper.  Sharing instead of copies is what makes the
# corpus eval cheap enough to interpret itself (the L2 wall on the
# naive tuple stepper was retention, not search).

_ND: List[tuple] = []        # node payload by id
_IN: Dict[tuple, int] = {}   # structural key -> id
_GR: List[bool] = []         # ground bit: no 'v'/'lz' reachable


def _nd(*key) -> int:
    i = _IN.get(key)
    if i is None:
        i = len(_ND)
        _IN[key] = i
        _ND.append(key)
        _GR.append(_gnd(key))
    return i


def _gnd(k) -> bool:
    t = k[0]
    if t == "p":
        return _GR[k[1]] and _GR[k[2]]
    if t == "gt":
        return all(_GR[a] for a in k[2])
    if t == "d":
        return _GR[k[1]]
    return t not in ("v", "lz")


def t_atom(bits: int, v: int) -> int:
    return _nd("a", bits, v)


def t_pair(a, b) -> int:
    return _nd("p", intern_term(a), intern_term(b))


def t_var(i) -> int:
    return _nd("v", i)


def t_sym(name: str) -> int:
    return _nd("s", name)


def t_lazy(es) -> int:
    return _nd("lz", *es)


def t_const(c: int) -> int:
    return _nd("c", c)


def t_delta(v: int, d: int) -> int:
    return _nd("d", intern_term(v), d)


def t_reldef(name: str) -> int:
    return _nd("rd", name)


def t_pat(name: str) -> int:
    return _nd("pat", name)


def t_bodycall(name: str) -> int:
    return _nd("bc", name)


def t_goalterm(name: str, args) -> int:
    return _nd("gt", name,
               tuple(intern_term(a) for a in args))


NIL = t_atom(0, 0)
_fresh_i = itertools.count(1)


def fresh() -> int:
    return t_var(next(_fresh_i))


def _reset_fresh() -> None:
    global _fresh_i
    _fresh_i = itertools.count(1)
    _FIELDS.clear()


_FIELDS: Dict[object, Tuple[int, str]] = {}


def intern_term(t) -> int:
    """tuple-form term (external boundary) -> arena id."""
    if isinstance(t, int):
        return t
    if isinstance(t, tuple):
        tag = t[0]
        if tag == "pair":
            return t_pair(intern_term(t[1]), intern_term(t[2]))
        if tag == "atom":
            return t_atom(t[1], t[2])
        if tag == "sym":
            return t_sym(t[1])
        if tag == "var":
            return t_var(t[1])
        if tag == "atom_lazy":
            return t_lazy(tuple(
                t_const(e[1]) if e[0] == "const"
                else t_delta(intern_term(e[1]), e[2])
                for e in t[1:]))
        if tag == "reldef":
            return t_reldef(t[1])
        if tag == "pat":
            return t_pat(t[1])
        if tag == "bodycall":
            return t_bodycall(t[1])
        if tag == "goalterm":
            return t_goalterm(t[1],
                              [intern_term(a) for a in t[2]])
    raise EvalError(f"seed: uninternable term {t!r}")


def thaw(t: int) -> tuple:
    """arena id -> tuple-form term (boundary reads only)."""
    k = _ND[t]
    tag = k[0]
    if tag == "p":
        return ("pair", thaw(k[1]), thaw(k[2]))
    if tag == "a":
        return ("atom", k[1], k[2])
    if tag == "s":
        return ("sym", k[1])
    if tag == "v":
        return ("var", k[1])
    if tag == "lz":
        return ("atom_lazy",) + tuple(
            ("const", _ND[e][1]) if _ND[e][0] == "c"
            else ("delta", thaw(_ND[e][1]), _ND[e][2])
            for e in k[1:])
    if tag == "rd":
        return ("reldef", k[1])
    if tag == "pat":
        return ("pat", k[1])
    if tag == "bc":
        return ("bodycall", k[1])
    if tag == "gt":
        return ("goalterm", k[1], [thaw(a) for a in k[2]])
    return k


def term_str(t: int) -> str:
    k = _ND[t]
    if k[0] == "a":
        return f"ATOM({k[1]},{k[2]})" if k[1] else "[]"
    if k[0] == "p":
        items, cur = [], t
        while _ND[cur][0] == "p":
            items.append(term_str(_ND[cur][1]))
            cur = _ND[cur][2]
        if cur == NIL:
            return "[" + ", ".join(items) + "]"
        return f"({term_str(k[1])} · {term_str(k[2])})"
    if k[0] == "v":
        return f"?{k[1]}"
    if k[0] == "s":
        return f"'{k[1]}"
    if k[0] == "rd":
        return f"<reldef {k[1]}>"
    if k[0] == "gt":
        return f"<goal {k[1]}/>"
    if k[0] == "pat":
        return f"<pat {k[1]}>"
    if k[0] == "bc":
        return f"<body {k[1]}>"
    return repr(k)


Subst = Dict[object, tuple]


def walk(t: int, s: Subst) -> int:
    while True:
        k = _ND[t]
        if k[0] != "v" or k[1] not in s:
            break
        t = s[k[1]]
    k = _ND[t]
    if k[0] == "v" and k[1] in _FIELDS:
        root, fld = _FIELDS[k[1]]
        rv = _force(walk(root, s), s)
        if _ND[rv][0] == "rd":
            return t_pat(_ND[rv][1]) if fld == "pat" else \
                t_bodycall(_ND[rv][1])
    return t


def unify(u: int, v: int, s: Subst) -> Optional[Subst]:
    u, v = _force(walk(u, s), s), _force(walk(v, s), s)
    if u == v:
        return s
    ku, kv = _ND[u], _ND[v]
    if ku[0] == "v":
        return {**s, ku[1]: v}
    if kv[0] == "v":
        return {**s, kv[1]: u}
    if ku[0] == "p" and kv[0] == "p":
        s2 = unify(ku[1], kv[1], s)
        return unify(ku[2], kv[2], s2) if s2 is not None else None
    return None


def reify(t: int, s: Subst) -> int:
    t = _force(walk(t, s), s)
    if _GR[t]:
        return t          # ground terms canonicalize to themselves
    k = _ND[t]
    if k[0] == "p":
        return t_pair(reify(k[1], s), reify(k[2], s))
    return t


class EvalError(ValueError):
    """Runtime refusal: unbound names, unexecutable forms, undeclared
    recursion.  Fuel exhaustion is NOT here: it is an observable
    empty stream."""


# ---------------------------------------------------------------------------
# lift - rel-graph node -> runtime term (ren = this scope's renaming)
# ---------------------------------------------------------------------------

def lift(node, ren: Dict[str, int]) -> int:
    if node is None:
        return NIL
    if "var" in node:
        n = node["var"]
        if n not in ren:
            ren[n] = fresh()
            if "." in n:
                root = lift({"var": n.split(".", 1)[0]}, ren)
                _FIELDS[_ND[ren[n]][1]] = (root,
                                           n.split(".", 1)[1])
        return ren[n]
    if "wild" in node:
        return fresh()
    if "atom" in node:
        return t_atom(node["atom"][0], node["atom"][1])
    if "atom_dyn" in node:
        be, pe = node["atom_dyn"]
        bits = _aval(be, ren)
        pay = _aval(pe, ren)
        if bits is not None and pay is not None:
            return t_atom(bits, pay)
        return t_lazy((_lazy_e(be, ren), _lazy_e(pe, ren)))
    if "pair" in node:
        return t_pair(lift(node["pair"][0], ren),
                      lift(node["pair"][1], ren))
    if "typed" in node:
        return lift(node["typed"][0], ren)
    if "type" in node:
        return fresh()
    if "var_lit" in node:
        return intern_term(node["var_lit"])
    if "sym" in node:
        return t_sym(node["sym"])
    if "call_term" in node:
        name, args = node["call_term"]
        return t_goalterm(name, [lift(a, ren) for a in args])
    if "__term" in node:
        return intern_term(node["__term"])
    raise EvalError(f"seed: unliftable term node {node!r}")


def _aval(e: dict, ren) -> Optional[int]:
    if "const" in e:
        return e["const"]
    name, d = e["var_delta"]
    v = ren.get(name)
    if v is not None and _ND[v][0] == "a":
        return _ND[v][2] + d
    return None


def _lazy_e(e: dict, ren):
    if "const" in e:
        return t_const(e["const"])
    name, d = e["var_delta"]
    if name not in ren:
        ren[name] = fresh()
    return t_delta(ren[name], d)


def _force(t: int, s: Subst) -> int:
    if _ND[t][0] != "lz":
        return t
    out = []
    for e in _ND[t][1:]:
        ek = _ND[e]
        if ek[0] == "c":
            out.append(ek[1])
            continue
        v = _force(walk(ek[1], s), s)
        if _ND[v][0] != "a":
            return t
        out.append(_ND[v][2] + ek[2])
    return t_atom(out[0], out[1])


# ---------------------------------------------------------------------------
# goals - lazy subst streams, clause extensions, the RUN quotient
# ---------------------------------------------------------------------------

def _conj(gs: List[dict], env, s: Subst, fuel, ren,
          tout) -> Iterator[Subst]:
    if not gs:
        yield s
        return
    for s1 in _one(gs[0], env, s, fuel, ren, tout):
        yield from _conj(gs[1:], env, s1, fuel, ren, tout)


def _interleave(a: Iterator, b: Iterator) -> Iterator:
    ita, itb = iter(a), iter(b)
    try:
        while True:
            yield next(ita)
            ita, itb = itb, ita
    except StopIteration:
        yield from itb


def _one(g: dict, env, s: Subst, fuel, ren, tout) -> Iterator[Subst]:
    fuel[0] -= 1
    if fuel[0] < 0:
        return
    if "unify" in g:
        s2 = unify(lift(g["unify"][0], ren),
                   lift(g["unify"][1], ren), s)
        if s2 is not None:
            yield s2
        return
    if "cmp" in g:
        op, na, nb = g["cmp"]
        a = _force(walk(lift(na, ren), s), s)
        b = _force(walk(lift(nb, ren), s), s)
        va = _ND[a][2] if _ND[a][0] == "a" else None
        vb = _ND[b][2] if _ND[b][0] == "a" else None
        if va is None or vb is None:
            raise EvalError(
                f"cmp {op}: operands must be ground atoms "
                f"(got {term_str(a)} {op} {term_str(b)})")
        ok = {"<": va < vb, ">": va > vb, "<=": va <= vb,
              ">=": va >= vb, "!=": va != vb}[op]
        if ok:
            yield s
        return
    if "emit" in g:
        if tout is None:
            raise EvalError(
                "emit (! t): no relation output in scope - "
                "emit is the clause's extension, it needs a call")
        s2 = unify(lift(g["emit"], ren), tout, s)
        if s2 is not None:
            yield s2
        return
    if "call" in g:
        c = g["call"]
        yield from _rel_call(c["rel"], c["args"], c["out"],
                             env, s, fuel, ren)
        return
    if "run" in g:
        yield from _run_goal(g["run"], env, s, fuel, ren)
        return
    if "choice" in g:
        c = g["choice"]
        outs = lift(c["out"], ren) if c["out"] is not None else None
        ga = _branch(c["a"], env, outs, s, fuel, ren)
        gb = _branch(c["b"], env, outs, s, fuel, ren)
        yield from _interleave(ga, gb)
        return
    if "fresh" in g:
        ren2 = dict(ren)
        for n in g["fresh"]["vars"]:
            ren2[n] = fresh()
        yield from _conj(g["fresh"]["goals"], env, s, fuel,
                         ren2, tout)
        return
    if "builtin" in g:
        yield from _builtin(g["builtin"], env, s, fuel, ren)
        return
    raise EvalError(f"seed: goal {g!r} not executable")


def _goal_parts(gnode, env, s, ren):
    if isinstance(gnode, dict) and "call_term" in gnode:
        name, args = gnode["call_term"]
        return name, args
    gt = _force(walk(lift(gnode, ren), s), s)
    if _ND[gt][0] == "gt":
        return _ND[gt][1], [{"__term": a} for a in _ND[gt][2]]
    raise EvalError(
        f"goal must be a call_term or goalterm, got "
        f"{term_str(gt)}")


def _branch(node, env, out_t, s, fuel, ren) -> Iterator[Subst]:
    name, args = _goal_parts(node, env, s, ren)
    ov = fresh()
    for sx in _rel_call(name, args, {"var_lit": ov},
                        env, s, fuel, ren):
        if out_t is None:
            yield sx
        else:
            s2 = unify(out_t, ov, sx)
            if s2 is not None:
                yield s2


def _run_goal(r: dict, env, s: Subst, fuel, ren) -> Iterator[Subst]:
    gnode = r["goal"]
    n = walk(lift(r["n"], ren), s)
    nlim = _ND[n][2] if _ND[n][0] == "a" else 0
    name, args = _goal_parts(gnode, env, s, ren)
    ov = fresh()
    results = []
    for sx in _rel_call(name, args, {"var_lit": ov},
                        env, s, fuel, ren):
        results.append(reify(ov, sx))
        if nlim and len(results) >= nlim:
            break
    lst = NIL
    for x in reversed(results):
        lst = t_pair(x, lst)
    s2 = unify(lift(r["out"], ren), lst, s)
    if s2 is not None:
        yield s2


# ---------------------------------------------------------------------------
# MATCH/APPLY - the meta-level: patterns as data, defs as data
# ---------------------------------------------------------------------------

def _pat_lift(node):
    if "var" in node:
        return t_var(node["var"])
    if "wild" in node:
        return fresh()
    if "atom" in node:
        return t_atom(node["atom"][0], node["atom"][1])
    if "atom_dyn" in node:
        be, pe = node["atom_dyn"]
        out = []
        for e in (be, pe):
            if "const" in e:
                out.append(t_const(e["const"]))
            else:
                name, d = e["var_delta"]
                out.append(t_delta(t_var(name), d))
        return t_lazy(tuple(out))
    if "pair" in node:
        return t_pair(_pat_lift(node["pair"][0]),
                      _pat_lift(node["pair"][1]))
    if "typed" in node:
        return _pat_lift(node["typed"][0])
    if "type" in node:
        return fresh()
    if "sym" in node:
        return t_sym(node["sym"])
    raise EvalError(f"seed: unliftable pattern node {node!r}")


def _tvars(t: int) -> Iterator[int]:
    """var node ids (named/pat-level vars only) in a term."""
    k = _ND[t]
    if k[0] == "v" and isinstance(k[1], str):
        yield t
    elif k[0] == "p":
        yield from _tvars(k[1])
        yield from _tvars(k[2])
    elif k[0] == "lz":
        for e in k[1:]:
            if _ND[e][0] == "d":
                yield from _tvars(_ND[e][1])


def _rtuple(terms: list):
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = t_pair(t, out)
    return out


def _decode_binds(lst: int, s: Subst) -> Dict[object, int]:
    out: Dict[object, int] = {}
    cur = _force(lst, s)
    while _ND[cur][0] == "p":
        ent = _ND[cur][1]
        ek = _ND[ent]
        if ek[0] == "p" and _ND[ek[1]][0] == "v":
            out[_ND[ek[1]][1]] = _force(walk(ek[2], s), s)
        cur = _force(walk(_ND[cur][2], s), s)
    return out


def _instantiate(node, binds: Dict[object, int]) -> int:
    if "var" in node:
        return binds.get(node["var"], t_var(node["var"]))
    if "wild" in node:
        return fresh()
    if "atom" in node:
        return t_atom(node["atom"][0], node["atom"][1])
    if "atom_dyn" in node:
        be, pe = node["atom_dyn"]
        out = []
        ok = True
        for e in (be, pe):
            if "const" in e:
                out.append(e["const"])
                continue
            name, d = e["var_delta"]
            v = binds.get(name)
            if v is not None and _ND[v][0] == "a":
                out.append(_ND[v][2] + d)
            else:
                ok = False
        if ok:
            return t_atom(out[0], out[1])
        return t_lazy(tuple(
            t_const(e["const"]) if "const" in e else
            t_delta(binds.get(e["var_delta"][0],
                              t_var(e["var_delta"][0])),
                    e["var_delta"][1])
            for e in (be, pe)))
    if "pair" in node:
        return t_pair(_instantiate(node["pair"][0], binds),
                      _instantiate(node["pair"][1], binds))
    if "typed" in node:
        return _instantiate(node["typed"][0], binds)
    if "type" in node:
        return fresh()
    if "sym" in node:
        return t_sym(node["sym"])
    raise EvalError(f"seed: uninstantiable node {node!r}")


def _builtin(b: dict, env, s: Subst, fuel, ren) -> Iterator[Subst]:
    name, args, out = b["name"], b["args"], b["out"]
    if name == "FRESH":
        if out is None:
            yield s
        else:
            s2 = unify(lift(out, ren), fresh(), s)
            if s2 is not None:
                yield s2
        return
    if name == "MATCH":
        if len(args) != 2:
            raise EvalError("MATCH(pat, term) = subst expected")
        pat = _force(walk(lift(args[0], ren), s), s)
        argterm = lift(args[1], ren)
        if _ND[pat][0] == "pat":
            rname = _ND[pat][1]
            rel = env["rels"].get(rname)
            if rel is None:
                raise EvalError(f"MATCH: unbound rel {rname!r}")
            ins = [_pat_lift(n) for n in rel["in"]]
            shadow = {_ND[v][1] for n in ins for v in _tvars(n)}
            s_sh = {k: v for k, v in s.items() if k not in shadow}
            target = ins[0] if len(ins) == 1 else _rtuple(ins)
            s2 = unify(target, argterm, s_sh)
        else:
            s2 = unify(pat, argterm, s)
        if s2 is None:
            return
        if out is None:
            yield s2
            return
        binds = NIL
        for k, v in sorted(s2.items(), key=lambda kv: str(kv[0])):
            binds = t_pair(t_pair(t_var(k), reify(v, s2)), binds)
        s3 = unify(lift(out, ren), binds, s2)
        if s3 is not None:
            yield s3
        return
    if name == "APPLY":
        t = _force(walk(lift(args[-1], ren), s), s)
        if _ND[t][0] == "bc":
            rel = env["rels"].get(_ND[t][1])
            if rel is None:
                raise EvalError(f"APPLY: unbound rel {_ND[t][1]!r}")
            binds = _decode_binds(
                _force(walk(lift(args[0], ren), s), s), s)
            argnodes = [{"__term": _instantiate(n, binds)}
                        for n in rel["in"]]
            ov = fresh()
            for sx in _rel_call(_ND[t][1], argnodes,
                                {"var_lit": ov},
                                env, s, fuel, ren):
                if out is None:
                    yield sx
                else:
                    s2 = unify(lift(out, ren), ov, sx)
                    if s2 is not None:
                        yield s2
            return
        if out is None:
            yield s
        else:
            s2 = unify(lift(out, ren), reify(t, s), s)
            if s2 is not None:
                yield s2
        return
    if name == "env_lookup":
        nm = walk(lift(args[0], ren), s)
        if _ND[nm][0] != "s":
            raise EvalError(
                f"env_lookup: rel name must be a symbol, got "
                f"{term_str(nm)}")
        if _ND[nm][1] not in env["rels"]:
            raise EvalError(
                f"env_lookup: unbound rel {_ND[nm][1]!r}")
        s2 = unify(lift(out, ren), t_reldef(_ND[nm][1]), s) \
            if out is not None else s
        if s2 is not None:
            yield s2
        return
    if name == "call":
        if not args:
            raise EvalError("call<f, args..> = out")
        f = walk(lift(args[0], ren), s)
        if _ND[f][0] != "rd":
            raise EvalError(
                f"call: first arg must reify to a reldef, got "
                f"{term_str(f)}")
        yield from _rel_call(_ND[f][1], args[1:], out, env, s,
                             fuel, ren)
        return
    raise EvalError(f"seed: builtin {name!r} not realized")


# ---------------------------------------------------------------------------
# rel calls - clauses are extensions (disj over them); fresh renaming
# per instantiation.  Shape contract: declared lowering forms only.
# ---------------------------------------------------------------------------

def _callers(rel: dict) -> set:
    out = set()

    def scan(gs):
        for g in gs:
            if "call" in g:
                out.add(g["call"]["rel"])
            if "call_term" in g:
                out.add(g["call_term"][0])
            if "fresh" in g:
                scan(g["fresh"]["goals"])
            if "run" in g and "call_term" in g["run"]["goal"]:
                out.add(g["run"]["goal"]["call_term"][0])
    for cl in rel["clauses"] or []:
        scan(cl["goals"])
        if cl["guard"]:
            scan(cl["guard"])
    return out


def _cyclic(rels: Dict[str, dict]) -> set:
    edges = {n: _callers(r) & set(rels) for n, r in rels.items()}
    reach = {n: set(es) for n, es in edges.items()}
    changed = True
    while changed:
        changed = False
        for n, rs in reach.items():
            new = set(rs)
            for r in rs:
                new |= reach.get(r, set())
            if new != rs:
                reach[n] = new
                changed = True
    return {n for n, rs in reach.items() if n in rs}


LOWERINGS = {
    "self": "depth-fueled recursive unfold",
    "pairwise": "unfold - split scheduling declared-not-wired",
}


def _rel_call(name: str, args: List[dict], out_node,
              env, s: Subst, fuel, caller_ren) -> Iterator[Subst]:
    rel = env["rels"].get(name)
    if rel is None:
        raise EvalError(f"seed: unbound rel {name!r}")
    if "cyc" not in env:
        env["cyc"] = _cyclic(env["rels"])
    if name in env["cyc"]:
        shape = rel.get("shape")
        if shape is None:
            raise EvalError(
                f"seed: recursive rel {name!r} declares no "
                f"shape - admissible construction refuses")
        if shape not in LOWERINGS:
            raise EvalError(
                f"seed: rel {name!r} declares shape {shape!r} - "
                f"lowering not realized")
    if len(args) != len(rel["in"]):
        raise EvalError(
            f"seed: {name} arity {len(rel['in'])} != call args "
            f"{len(args)}")
    targs = [lift(a, caller_ren) for a in args]
    tout = lift(out_node, caller_ren) if out_node is not None \
        else None
    # --- tabling: a ground call's out-stream is a pure function of
    #     its args (the rel semantics is context-free).  Streams
    #     memoize as they complete; a suspended producer RESUMES for
    #     the next caller — the same sharing discipline as graph.cd's
    #     sealed memo, in the relational substrate.  Keys are
    #     interned arg ids: hash-consed, gc-stable, O(1) compares,
    #     and ground args resolve in O(1) via the arena ground bit.
    #     Tabled only when out is an unbound var slot (replay
    #     unifies it per caller). ---
    key = None
    if tout is not None:
        wo = walk(tout, s)
        if _ND[wo][0] == "v":
            key = _tab_key(name, targs, s)
    if key is not None:
        ent = env["tab"].get(key)
        if ent is not None and not ent[2]:
            vals, it, _, ptout = ent
            fuel[0] -= 1
            for v in vals:
                s2 = unify(tout, v, s)
                if s2 is not None:
                    yield s2
            if it is not None:
                env["tab"][key] = (vals, it, True, ptout)
                for s1 in it:
                    v = reify(ptout, s1)  # producer's own out —
                                        # caller's tout unbound in s1
                    if _GR[v]:
                        vals.append(v)
                        s2 = unify(tout, v, s)
                        if s2 is not None:
                            yield s2
                    else:
                        env["tab"].pop(key, None)
                if key in env["tab"]:
                    env["tab"][key] = (vals, None, False, ptout)
            return
        if ent is not None:
            key = None    # active producer — same-goal recursion
                          # bypasses the table (diverges as before)
    gen = _rel_body(rel, targs, tout, env, s, fuel)
    if key is None:
        yield from gen
        return
    vals: list = []
    it = iter(gen)
    env["tab"][key] = (vals, it, True, tout)
    for s1 in it:
        v = reify(tout, s1)
        if _GR[v]:
            vals.append(v)
        else:
            env["tab"].pop(key, None)   # existential out —
                                        # never cache
        yield s1
    if key in env["tab"]:
        env["tab"][key] = (vals, None, False, tout)


def _rel_body(rel: dict, targs, tout, env, s: Subst,
              fuel) -> Iterator[Subst]:
    clauses = rel["clauses"] if rel["clauses"] is not None \
        else [None]
    for cl in clauses:
        ren: Dict[str, tuple] = {}
        s0 = s
        ok = True
        for ta, pat in zip(targs, rel["in"]):
            s0 = unify(ta, lift(pat, ren), s0)
            if s0 is None:
                ok = False
                break
        if not ok:
            continue
        if tout is not None and rel["out"]:
            s0 = unify(tout, lift(rel["out"][0], ren), s0)
            if s0 is None:
                continue
        if cl is None:
            yield s0
            continue
        if cl["fresh"]:
            for n in cl["fresh"]:
                ren[n] = fresh()
        yield from _conj((cl["guard"] or []) + cl["goals"],
                         env, s0, fuel, ren, tout)


def _tab_key(name: str, targs, s):
    """Ground-arg call -> memo key of interned ids.  reify walks
    substs but interned nodes canonicalize: equal structures share
    one id, ground terms resolve in O(1) via _GR.  None when any
    arg is open."""
    ks = []
    for ta in targs:
        v = reify(ta, s)
        if not _GR[v]:
            return None
        ks.append(v)
    return (name, *ks)


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def _env(graph: dict) -> dict:
    return {"rels": {r["name"]: r for r in graph["rels"]},
            "tab": {}}


def merge_graphs(graphs: List[dict]) -> dict:
    """std/*.plex files are one library - rels merge by name; a
    collision is a refusal, never a silent override."""
    rels: Dict[str, dict] = {}
    for g in graphs:
        for r in g.get("rels", []):
            if r["name"] in rels:
                raise EvalError(
                    f"merge: rel {r['name']!r} defined twice across "
                    f"the corpus")
            rels[r["name"]] = r
    return {"format": "phi.rel/1", "rels": list(rels.values())}


def lit(t) -> dict:
    return {"var_lit": t}


def run(graph: dict, rel: str, args: List[dict], out: dict,
        n: int = 1, fuel: int = 100_000) -> List[Subst]:
    env = _env(graph)
    fuel_cell = [fuel]
    ren: Dict[str, tuple] = {}
    sols = []
    for s in _rel_call(rel, args, out, env, {}, fuel_cell, ren):
        sols.append(s)
        if n and len(sols) >= n:
            break
    return sols


def run_value(graph: dict, rel: str, args: List[tuple],
              n: int = 1, fuel: int = 100_000) -> List[tuple]:
    env = _env(graph)
    fuel_cell = [fuel]
    ren: Dict[str, tuple] = {}
    ov = fresh()
    sols = []
    for s in _rel_call(rel, [lit(a) for a in args],
                       lit(ov), env, {}, fuel_cell, ren):
        sols.append(reify(ov, s))
        if n and len(sols) >= n:
            break
    return sols


def run_solutions(graph: dict, rel: str, arg_terms: List[tuple],
                  out_term, n: int = 0,
                  fuel: int = 100_000) -> List[Subst]:
    env = _env(graph)
    fuel_cell = [fuel]
    ren: Dict[str, tuple] = {}
    sols = []
    for s in _rel_call(rel, [lit(a) for a in arg_terms],
                       lit(out_term), env, {}, fuel_cell, ren):
        sols.append(s)
        if n and len(sols) >= n:
            break
    return sols


# ---------------------------------------------------------------------------
# corpus load + CLI
# ---------------------------------------------------------------------------

def load_graph(path: str) -> dict:
    data = open(path, "rb").read()
    return read_graph_bundle(data)


def load_corpus(paths: List[str]) -> dict:
    return merge_graphs([load_graph(p) for p in paths])


# ---------------------------------------------------------------------------
# enc'er — surface rel-graph (dict form) -> enc'd env term.
# Any corpus program becomes data in the corpus eval's own domain:
# the self-description + Futamura-1 substrate.  Unsupported goal
# forms refuse by name — the enc domain's boundary is explicit.
# ---------------------------------------------------------------------------

def _e(tag, *xs):
    """'tag(a, b, ...) — right-nested tagged enc node."""
    o = xs[-1] if xs else NIL
    for x in reversed(xs[:-1]):
        o = t_pair(x, o)
    return t_pair(t_sym(tag), o)


def _esym(x):
    return t_pair(t_sym("sym"), t_sym(x))


def enc_term(t: dict, wc: list):
    """dict-form surface term -> enc'd term.  wc threads a
    wildcard counter so each `_` gets a distinct 'nvar name."""
    if "wild" in t:
        wc[0] += 1
        return _e("nvar", t_sym(f"_w{wc[0]}"))
    if "var" in t:
        if t["var"] == "_":
            wc[0] += 1
            return _e("nvar", t_sym(f"_w{wc[0]}"))
        return _e("nvar", t_sym(t["var"]))
    if "sym" in t:
        return _esym(t["sym"])
    if "atom" in t:
        return _e("atom", t_atom(8, t["atom"][0]),
                  t_atom(8, t["atom"][1]))
    if "atom_dyn" in t:
        be, ve = t["atom_dyn"]
        if be.get("const") != 8:
            raise EvalError("enc: non-T[8] atom_dyn — 'adyn axis")
        if "const" in ve:
            return _e("atom", t_atom(8, 8), t_atom(8, ve["const"]))
        name, d = ve["var_delta"]
        return _e("adyn", _e("nvar", t_sym(name)),
                  _e("atom", t_atom(8, 8), t_atom(8, d)))
    if "pair" in t:
        return _e("pair", enc_term(t["pair"][0], wc),
                  enc_term(t["pair"][1], wc))
    if "typed" in t:
        return enc_term(t["typed"][0], wc)     # sig types drop
    if "type" in t or "const" in t or "var_delta" in t:
        raise EvalError(f"enc: stray term form {t!r}")
    raise EvalError(f"enc: unsupported term {t!r}")


_CMPS = {"!=": "neq", "==": "eq", "<": "lt", ">": "gt",
         "<=": "le", ">=": "ge"}


def enc_goal(g: dict, wc: list):
    """dict-form surface goal -> enc'd goal node."""
    if "unify" in g:
        return _e("unify", enc_term(g["unify"][0], wc),
                  enc_term(g["unify"][1], wc))
    if "cmp" in g:
        op, a, b = g["cmp"]
        if op == "=":
            return _e("unify", enc_term(a, wc), enc_term(b, wc))
        if op not in _CMPS:
            raise EvalError(f"enc: cmp op {op!r} — unsupported")
        return _e("cmp", t_sym(_CMPS[op]), enc_term(a, wc),
                  enc_term(b, wc))
    if "call" in g:
        c = g["call"]
        args = NIL
        for a in reversed(c["args"]):
            args = t_pair(enc_term(a, wc), args)
        return _e("call", _esym(c["rel"]), args,
                  enc_term(c["out"], wc))
    if "run" in g:
        r = g["run"]
        wc[0] += 1
        outv = _e("nvar", t_sym(f"_ro{wc[0]}"))
        goal = r["goal"]
        if "call_term" in goal:
            args = NIL
            for a in reversed(goal["call_term"][1]):
                args = t_pair(enc_term(a, wc), args)
            inner = _e("call", _esym(goal["call_term"][0]),
                       args, outv)
        elif "call" in goal:
            inner = enc_goal(goal, wc)
        else:
            raise EvalError(f"enc: RUN goal {goal!r} — axis")
        return _e("run", inner, enc_term(r["n"], wc),
                  enc_term(r["out"], wc))
    if "fresh" in g:
        raise EvalError("enc: nested fresh — splice into clause "
                        "goals instead (axis)")
    if "builtin" in g:
        raise EvalError(
            f"enc: builtin {g['builtin']['name']!r} — axis")
    if "emit" in g or "choice" in g:
        raise EvalError("enc: emit/choice goal — axis")
    raise EvalError(f"enc: unsupported goal {g!r}")


def enc_rel(r: dict):
    """rel dict -> 'def(ins, outPat, clauses) enc'd term."""
    wc = [0]
    ins = NIL
    for p in reversed(r["in"]):
        ins = t_pair(enc_term(p, wc), ins)
    if len(r["out"]) != 1:
        raise EvalError(
            f"enc: rel {r['name']!r} multi-out sig — axis")
    out = enc_term(r["out"][0], wc)
    cls = NIL
    # sig-only rels are direct extensions — one empty-goal clause
    for c in reversed(r.get("clauses") or [{"goals": []}]):
        goals = [enc_goal(g, wc)
                 for g in c.get("guard") or []] \
              + [enc_goal(g, wc) for g in c["goals"]]
        gl = NIL
        for g in reversed(goals):
            gl = t_pair(g, gl)
        cls = t_pair(_e("clause", gl), cls)
    return _e("def", ins, out, cls)


def enc_env(graph: dict):
    """rel-graph -> enc'd env-alist term [[name|def]...]."""
    env = NIL
    for r in reversed(graph["rels"]):
        env = t_pair(t_pair(_esym(r["name"]), enc_rel(r)), env)
    return env


# ===========================================================================
# phi.rel encode - corpus rel-graph -> substrate (I/K/S) combinator terms.
#
# The encode is the declared `phi.rel` dialect map (toolchain catalog,
# decision 016): corpus rels lower to stream-functions over a 3-case
# union data rep, bracketed abstract0 (I/K/S only - D/C are syntax tags
# with no beta rule on this substrate).  The emitted kernels (graph.cd,
# reducer_cd.exe) reduce the result; congruence vs the seed stepper is
# the witness, never a second semantics claim.
#
# Data rep - a 3-ary scott union mirroring the corpus term tree:
#   mkatom b v = \ca\cs\cp. ca (p2 b v)
#   mksym  n   = \ca\cs\cp. cs n
#   mkcell a b = \ca\cs\cp. cp (p2 a b)
# case-of t = t hAtom hSym hCell.  Tagged enc nodes ('var/'atom/'call/
# ...) stay ordinary cells whose car is a sym leaf - the open-tag
# discipline: dispatch is structural, never tag-enumerated.
#
# Nats are scott (z = \z\s.z, sn n = \z\s.s n): pred and case are O(1).
# Streams and data lists share one rep: mkcell-spine ending dnil
# (mkatom(0,0) - the corpus NIL).  Machine fns:  d : T -> args... ->
# stream  with T the shared fn-tuple; mutual recursion is fuel-unrolled
# M = F^depth(BOT) - the bound is term structure, honest like stepper
# fuel; no fixpoint combinator (eager NF expands a buried self-app
# forever).
# ===========================================================================

_SD: List[tuple] = []          # ("a",l,r) | ("I",) | ("K",) | ("S",)
_SI: Dict[tuple, int] = {}


def _sd(k) -> int:
    i = _SI.get(k)
    if i is None:
        i = len(_SD)
        _SD.append(k)
        _SI[k] = i
    return i


def sapp(a: int, b: int) -> int:
    return _sd(("a", a, b))


cI = _sd(("I",))
cK = _sd(("K",))
cS = _sd(("S",))


# --- lambda mixed IR: ("v",name) ("a",f,x) ("l",p,b) ("c",id) ("p",nm) -
def lv(n): return ("v", n)
def la(f, x): return ("a", f, x)
def ll(p, b): return ("l", p, b)
def lc(i): return ("c", i)
def lp(n): return ("p", n)


def _apps(f, *xs):
    for x in xs:
        f = la(f, x)
    return f


def _lams(*ps):
    def wrap(b):
        for p in reversed(ps):
            b = ll(p, b)
        return b
    return wrap


def _lfree(e, x, _m=None):
    if _m is None:
        _m = {}
    i = id(e)
    r = _m.get(i)
    if r is not None:
        return r
    k = e[0]
    if k == "v":
        r = e[1] == x
    elif k == "a":
        r = _lfree(e[1], x, _m) or _lfree(e[2], x, _m)
    elif k == "l":
        r = e[1] != x and _lfree(e[2], x, _m)
    else:
        r = False
    _m[i] = r
    return r


def _abs0(x, b):
    # abstract0: I/K/S only - no eta, no B/C (host LambdaFragment shape).
    if b[0] == "l":
        # lambda under abstraction: convert the inner binder first.
        return _abs0(x, _abs0(b[1], b[2]))
    if b[0] == "v" and b[1] == x:
        return lc(cI)
    if not _lfree(b, x):
        return la(lc(cK), b)
    if b[0] == "a":
        return la(la(lc(cS), _abs0(x, b[1])), _abs0(x, b[2]))
    return la(lc(cK), b)


_PRE: Dict[str, int] = {}


def bracket0(e) -> int:
    """mixed IR -> substrate node id (open terms refuse)."""
    k = e[0]
    if k == "a":
        return sapp(bracket0(e[1]), bracket0(e[2]))
    if k == "c":
        return e[1]
    if k == "p":
        return _PRE[e[1]]
    if k == "v":
        raise EvalError(f"encode: open term, unbound {e[1]!r}")
    return bracket0(_abs0(e[1], e[2]))


def _s_apps(f, *xs):
    for x in xs:
        f = sapp(f, x)
    return f


def _def_prelude(name: str, ltree) -> int:
    i = bracket0(ltree)
    _PRE[name] = i
    return i


def _init_prelude():
    if _PRE:
        return
    v, a = lv, la
    L = _lams
    _def_prelude("p2",  L("a", "b", "f")(a(a(v("f"), v("a")), v("b"))))
    _def_prelude("fst", L("p")(a(v("p"), L("a", "b")(v("a")))))
    _def_prelude("snd", L("p")(a(v("p"), L("a", "b")(v("b")))))
    _def_prelude("tt",  L("t", "f")(v("t")))
    _def_prelude("ff",  L("t", "f")(v("f")))
    _def_prelude("z",   L("z", "s")(v("z")))
    _def_prelude("sn",  L("n", "z", "s")(a(v("s"), v("n"))))
    _def_prelude("mkatom", L("b", "v", "ca", "cs", "cp")(
        a(v("ca"), _apps(lp("p2"), v("b"), v("v")))))
    _def_prelude("mksym", L("n", "ca", "cs", "cp")(a(v("cs"), v("n"))))
    _def_prelude("mkcell", L("a", "b", "ca", "cs", "cp")(
        a(v("cp"), _apps(lp("p2"), v("a"), v("b")))))
    _def_prelude("and", L("a", "b")(a(a(v("a"), v("b")), lp("ff"))))
    _def_prelude("not", L("b")(a(a(v("b"), lp("ff")), lp("tt"))))
    _def_prelude("pred", L("n")(a(a(v("n"), lp("z")),
                                   L("p")(v("p")))))
    _def_prelude("isz", L("n")(a(a(v("n"), lp("tt")),
                                  L("p")(lp("ff")))))
    # the data-nil marker (corpus NIL atom(0,0)) as a term id
    _PRE["dnil"] = _pre("mkatom", _nat(0), _nat(0))


def _pre(name, *args):
    return _s_apps(_PRE[name], *args)


DNIL = lc(-1)          # placeholder; real ref set in _init_prelude


def _dnil():
    return lc(_PRE["dnil"])


# --- declared name table: sym leaves intern to nats (encode data) ---
_SYMIDS: Dict[str, int] = {}
_SYMNAMES: List[str] = []


def _symid(name: str) -> int:
    i = _SYMIDS.get(name)
    if i is None:
        i = len(_SYMNAMES)
        _SYMNAMES.append(name)
        _SYMIDS[name] = i
    return i


def _nat(n: int) -> int:
    t = _PRE["z"]
    for _ in range(n):
        t = _s_apps(_PRE["sn"], t)
    return t


def enc_sub(t: int) -> int:
    """seed term id -> substrate data term (the corpus tree as
    union cells: atom leaf / sym leaf / pair cell)."""
    _init_prelude()
    k = _ND[_force(t, NIL)]
    if k[0] == "a":
        return _pre("mkatom", _nat(k[1]), _nat(k[2]))
    if k[0] == "s":
        return _pre("mksym", _nat(_symid(k[1])))
    if k[0] == "p":
        return _pre("mkcell", enc_sub(k[1]), enc_sub(k[2]))
    raise EvalError(f"encode: term {k!r} not lowerable")


# --- machine fn tuple: declared order (the T index) ----------------
_FNAMES = (
    "bind", "append", "take", "eq_nat", "eq_leaf", "eq_term",
    "isnil", "is_var", "is_nvar", "is_pair", "is_adyn",
    "subst_lookup", "walk", "unify_w", "unify_enc", "adyn_res",
    "natadd", "env_find", "next_id", "ren_find", "ren_fc",
    "inst", "inst_list", "reify", "reify_w", "unify_args",
    "eval", "eval_call", "eval_clauses", "eval_clause",
    "eval_body",
)
_FIDX = {n: i for i, n in enumerate(_FNAMES)}


def _selpath(i):
    """balanced-tree index path: 'fst'/'snd' steps to leaf i of the
    tup layout (lo+ (hi-lo)//2 splits, same as tup)."""
    path = []
    lo, hi = 0, len(_FNAMES)
    while hi - lo > 1:
        mid = lo + (hi - lo) // 2
        if i < mid:
            path.append("fst")
            hi = mid
        else:
            path.append("snd")
            lo = mid
    return path


def _sel(i, t):
    """IR: select fn i from the balanced p2 tuple t."""
    for step in _selpath(i):
        t = la(lp(step), t)
    return t


def _fcall(name, *args):
    """IR: machine call (sel name T) args..."""
    return _apps(_sel(_FIDX[name], lv("T")), *args)


def _case3(t, hA, hS, hP):
    return _apps(t, hA, hS, hP)


def _eqnat(x, y):
    return _fcall("eq_nat", x, y)


def _mkbot(arity):
    b = _dnil()
    for i in range(arity):
        b = ll(f"_b{i}", b)
    return b


def _p2(x, y):
    return _apps(lp("p2"), x, y)


def _mkcell(x, y):
    return _apps(lp("mkcell"), x, y)


def _nat_lc(name_or_int):
    """IR node for a scott nat literal."""
    n = _symid(name_or_int) if isinstance(name_or_int, str) \
        else name_or_int
    t = lp("z")
    for _ in range(n):
        t = la(lp("sn"), t)
    return t


def _mksym_id(name):
    return _apps(lp("mksym"), _nat_lc(name))


def _mkatom_l(b, v):
    return _apps(lp("mkatom"), _nat_lc(b), _nat_lc(v))


def _stream(x):
    """IR: singleton data-list [x]."""
    return _apps(lp("mkcell"), x, _dnil())


def _payload(t):
    """IR node: the p2 payload of a mkcell/mkatom term (I is the
    identity handler: it is applied to the payload)."""
    return _case3(t, lc(cI), lc(cI), _lams("cell")(lv("cell")))


def _varid(t):
    """IR node: 'var(i)'s id leaf = snd of the cell payload."""
    return _apps(lp("snd"), _payload(t))


def _cellpl_body(cellnode, h):
    """IR: apply a p2 payload to handler h (\a\b. body)."""
    return la(cellnode, h)


def _build_machine_lts():
    """unifier slice as IR sources - corpus eval.phi semantics,
    clause order preserved so divergence is reviewable."""
    _init_prelude()
    v, a = lv, la
    L = _lams
    lts = {}

    # bind : st f -> flatMap over data-list (streams)
    lts["bind"] = L("T", "st", "f")(
        _case3(v("st"),
               L("bv")(_dnil()),
               L("n")(_dnil()),
               L("cell")(_cellpl_body(v("cell"), L("h", "t")(
                   _fcall("append",
                          a(v("f"), v("h")),
                          _fcall("bind", v("t"), v("f"))))))))

    # append : a b -> list
    lts["append"] = L("T", "a", "b")(
        _case3(v("a"),
               L("bv")(v("b")),
               L("n")(v("b")),
               L("cell")(_cellpl_body(v("cell"), L("h", "t")(
                   _mkcell(v("h"),
                           _fcall("append", v("t"), v("b"))))))))

    # take : n st -> first n of stream (n = scott nat)
    lts["take"] = L("T", "n", "st")(
        _apps(v("n"),
              _dnil(),
              L("p")(_case3(v("st"),
                            L("bv")(_dnil()),
                            L("n2")(_dnil()),
                            L("cell")(_cellpl_body(v("cell"), L("h", "t")(
                                _mkcell(v("h"),
                                        _fcall("take",
                                               _apps(lp("pred"), v("p")),
                                               v("t"))))))))))

    # eq_nat : a b -> bool
    lts["eq_nat"] = L("T", "a", "b")(
        _apps(v("a"),
              _apps(v("b"), lp("tt"), L("x")(lp("ff"))),
              L("pa")(_apps(v("b"), lp("ff"),
                            L("pb")(_eqnat(v("pa"), v("pb")))))))

    # eq_leaf : a b -> bool (atoms by payload, syms by id, cell never)
    lts["eq_leaf"] = L("T", "a", "b")(
        _case3(v("a"),
               L("bv")(_case3(v("b"),
                              L("bv2")(_apps(v("bv"), L("b1", "v1")(
                                  _apps(v("bv2"), L("b2", "v2")(
                                      _apps(lp("and"),
                                            _eqnat(v("b1"), v("b2")),
                                            _eqnat(v("v1"), v("v2")))))))),
                              L("n")(lp("ff")),
                              L("c")(lp("ff")))),
               L("na")(_case3(v("b"),
                              L("bv")(lp("ff")),
                              L("nb")(_eqnat(v("na"), v("nb"))),
                              L("c")(lp("ff")))),
               L("c")(lp("ff"))))

    # eq_term : a b -> bool (structural, any leaf/cell)
    lts["eq_term"] = L("T", "a", "b")(
        _case3(v("a"),
               L("bv")(_fcall("eq_leaf", v("a"), v("b"))),
               L("na")(_fcall("eq_leaf", v("a"), v("b"))),
               L("ca")(_case3(v("b"),
                              L("bv")(lp("ff")),
                              L("nb")(lp("ff")),
                              L("cb")(_apps(
                                  lp("and"),
                                  _fcall("eq_term",
                                         _apps(lp("fst"), v("ca")),
                                         _apps(lp("fst"), v("cb"))),
                                  _fcall("eq_term",
                                         _apps(lp("snd"), v("ca")),
                                         _apps(lp("snd"), v("cb")))))))))

    # isnil : l -> bool  (mkatom(0,0) exactly)
    lts["isnil"] = L("T", "l")(
        _case3(v("l"),
               L("bv")(_apps(v("bv"), L("b", "v")(
                   _apps(lp("and"),
                         _eqnat(v("b"), _nat_lc(0)),
                         _eqnat(v("v"), _nat_lc(0)))))),
               L("n")(lp("ff")),
               L("c")(lp("ff"))))

    # _tagchk : t -> bool (cell whose car sym-leaf id = name)
    def _tagchk(t, name):
        return _case3(t,
                      L("bv")(lp("ff")),
                      L("n")(lp("ff")),
                      L("cell")(_case3(_apps(lp("fst"), v("cell")),
                                       L("bv")(lp("ff")),
                                       L("n")(_eqnat(v("n"),
                                                     _nat_lc(name))),
                                       L("c")(lp("ff")))))

    lts["is_var"] = L("T", "t")(_tagchk(v("t"), "var"))
    lts["is_nvar"] = L("T", "t")(_tagchk(v("t"), "nvar"))
    lts["is_adyn"] = L("T", "t")(_tagchk(v("t"), "adyn"))
    lts["is_pair"] = L("T", "t")(
        _case3(v("t"), L("bv")(lp("ff")), L("n")(lp("ff")),
               L("c")(lp("tt"))))

    # subst_lookup : k lst -> stream(term) - corpus clause order:
    # hit -> 'bound(v) ; key-miss -> recurse ; [] -> 'unbound
    lts["subst_lookup"] = L("T", "k", "lst")(
        _case3(v("lst"),
               L("bv")(_apps(
                   _fcall("isnil", v("lst")),
                   _stream(_mksym_id("unbound")),
                   _dnil())),
               L("n")(_dnil()),
               L("cell")(_cellpl_body(v("cell"), L("ent", "rest")(
                   _case3(v("ent"),
                          L("bv")(_dnil()),
                          L("n")(_dnil()),
                          L("kv")(_apps(v("kv"), L("k2", "vv")(
                              _apps(_fcall("eq_leaf", v("k"), v("k2")),
                                    _stream(_mkcell(_mksym_id("bound"),
                                                    v("vv"))),
                                    _fcall("subst_lookup",
                                           v("k"), v("rest"))))))))
               ))))

    # walk : t s -> stream(term); 'var -> bound?recurse:t ; else t
    _walk_hit = L("b")(_case3(v("b"),
        L("bv")(_dnil()),
        L("n")(_stream(v("t"))),
        L("cell")(_cellpl_body(v("cell"), L("tg", "vv")(
            _case3(v("tg"),
                   L("bv")(_dnil()),
                   L("n2")(_apps(_eqnat(v("n2"), _nat_lc("bound")),
                                 _fcall("walk", v("vv"), v("s")),
                                 _stream(v("t")))),
                   L("c")(_dnil())))))))
    lts["walk"] = L("T", "t", "s")(
        _apps(_fcall("is_var", v("t")),
              _fcall("bind",
                     _fcall("subst_lookup", _varid(v("t")), v("s")),
                     _walk_hit),
              _stream(v("t"))))

    # unify_w : u v s -> stream(subst) - corpus clause matrix by shape
    lts["unify_w"] = L("T", "u", "v", "s")(
        _apps(_fcall("is_var", v("u")),
              _apps(_fcall("is_var", v("v")),
                    _apps(_fcall("eq_leaf", _varid(v("u")),
                                 _varid(v("v"))),
                          _stream(v("s")),
                          _stream(_mkcell(_mkcell(_varid(v("u")),
                                                  v("v")),
                                          v("s")))),
                    _stream(_mkcell(_mkcell(_varid(v("u")), v("v")),
                                    v("s")))),
              _apps(_fcall("is_var", v("v")),
                    _stream(_mkcell(_mkcell(_varid(v("v")), v("u")),
                                    v("s"))),
                    _apps(_fcall("is_pair", v("u")),
                          _apps(_fcall("is_pair", v("v")),
                                _fcall("bind",
                                       _fcall("unify_enc",
                                              _apps(lp("fst"),
                                                    _payload(v("u"))),
                                              _apps(lp("fst"),
                                                    _payload(v("v"))),
                                              v("s")),
                                       L("s1")(_fcall(
                                           "unify_enc",
                                           _apps(lp("snd"),
                                                 _payload(v("u"))),
                                           _apps(lp("snd"),
                                                 _payload(v("v"))),
                                           v("s1")))),
                                _dnil()),
                          _apps(_fcall("eq_leaf", v("u"), v("v")),
                                _stream(v("s")),
                                _dnil())))))

    # unify_enc : u v s -> stream(subst) = walk both, adyn_res, unify_w
    lts["unify_enc"] = L("T", "u", "v", "s")(
        _fcall("bind", _fcall("walk", v("u"), v("s")),
               L("uw")(_fcall("bind", _fcall("walk", v("v"), v("s")),
                              L("vw")(_fcall(
                                  "bind",
                                  _fcall("adyn_res", v("uw"), v("s")),
                                  L("u2")(_fcall(
                                      "bind",
                                      _fcall("adyn_res", v("vw"),
                                             v("s")),
                                      L("v2")(_fcall(
                                          "unify_w", v("u2"), v("v2"),
                                          v("s")))))))))))

    # adyn_res : t s -> stream(term); 'adyn(bt,dt) with both walked
    # to 'atom cells -> 'atom(bi, vi+dvi); otherwise t
    lts["adyn_res"] = L("T", "t", "s")(
        _apps(_fcall("is_adyn", v("t")),
              _case3(v("t"),
                     L("bv")(_dnil()),
                     L("n")(_dnil()),
                     L("cell")(_apps(
                         _payload(_apps(lp("snd"), v("cell"))),
                         L("bt", "dt")(
                         _fcall("bind", _fcall("walk", v("bt"), v("s")),
                                L("wb")(_fcall(
                                    "bind",
                                    _fcall("walk", v("dt"), v("s")),
                                    L("wd")(_adyn_combine(
                                        v("wb"), v("wd")))))))))),
              _stream(v("t"))))

    # natadd : a b -> stream(atom leaf, a.bits, va+vb) - peano on va
    lts["natadd"] = L("T", "a", "b")(
        _case3(v("a"),
               L("bva")(_case3(v("b"),
                              L("bvb")(_natadd_body(v("bva"), v("b"))),
                              L("n")(_dnil()),
                              L("c")(_dnil()))),
               L("n")(_dnil()),
               L("c")(_dnil())))

    # env_find : name env -> stream(def) - 'sym-node keys, eq_term
    lts["env_find"] = L("T", "nm", "env")(
        _case3(v("env"),
               L("bv")(_dnil()),
               L("n")(_dnil()),
               L("cell")(_cellpl_body(v("cell"), L("ent", "rest")(
                   _case3(v("ent"),
                          L("bv")(_dnil()),
                          L("n")(_dnil()),
                          L("kv")(_apps(v("kv"), L("k2", "d")(
                              _apps(_fcall("eq_term", v("nm"), v("k2")),
                                    _stream(v("d")),
                                    _fcall("env_find",
                                           v("nm"), v("rest"))))))))
               ))))

    # ---- eval chain (eval.phi, clause order preserved) ----
    def _narg(t, i, last):
        """IR: i-th arg of a right-nested tagged node; the last
        arg is the improper tail itself."""
        r = _apps(lp("snd"), _payload(t))
        for _ in range(i):
            r = _apps(lp("snd"), _payload(r))
        return r if last else _apps(lp("fst"), _payload(r))

    def _o_fst(t):
        return _apps(lp("fst"), _payload(t))

    def _o_snd(t):
        return _apps(lp("snd"), _payload(t))

    def _o_mid(t):
        """PAIR(x, PAIR(y, z)) -> y"""
        return _apps(lp("fst"), _payload(_o_snd(t)))

    def _o_tail(t):
        """PAIR(x, PAIR(y, z)) -> z"""
        return _apps(lp("snd"), _payload(_o_snd(t)))

    # next_id : n -> stream[atom(8, v+1)]
    lts["next_id"] = L("T", "n")(
        _stream(_apps(lp("mkatom"), _nat_lc(8),
                      _apps(lp("sn"),
                            _apps(lp("snd"), _payload(v("n")))))))

    # ren_find : name ren -> stream[id] - corpus two-clause order:
    # hit AND recurse both derive
    lts["ren_find"] = L("T", "nm", "ren")(
        _case3(v("ren"),
               L("bv")(_dnil()),
               L("n")(_dnil()),
               L("cell")(_cellpl_body(v("cell"), L("ent", "rest")(
                   _case3(v("ent"),
                          L("bv")(_dnil()),
                          L("n")(_dnil()),
                          L("kv")(_apps(v("kv"), L("k2", "i2")(
                              _fcall("append",
                                     _apps(_fcall("eq_term", v("nm"),
                                                  v("k2")),
                                           _stream(v("i2")),
                                           _dnil()),
                                     _fcall("ren_find", v("nm"),
                                            v("rest"))))))))
               ))))

    # ren_fc : nm ren n -> stream[[id|[ren|n]] | miss-cons]
    # corpus: RUN(ren_find,1) -> res ; [id|_] -> [id|[ren|n]] ;
    #         [] -> next_id, [n|[[[nm|n]|ren]|n2]]
    _rf_res = _fcall("take", _nat_lc(1),
                     _fcall("ren_find", v("nm"), v("ren")))
    lts["ren_fc"] = L("T", "nm", "ren", "n")(
        _apps(_fcall("isnil", _rf_res),
              _fcall("bind", _fcall("next_id", v("n")),
                     L("n2")(_stream(_mkcell(
                         v("n"),
                         _mkcell(_mkcell(_mkcell(v("nm"), v("n")),
                                         v("ren")),
                                 v("n2")))))),
              _fcall("bind", _rf_res,
                     L("id")(_stream(_mkcell(
                         v("id"),
                         _mkcell(v("ren"), v("n"))))))))

    # inst : node ren n -> stream[[r2|[n2|node2]]] - corpus shapes:
    # 'nvar renames, other cells recurse structurally, leaves pass
    def _nvararg(t):
        return _apps(lp("snd"), _payload(t))

    _inst_hit = L("o")(_stream(
        _mkcell(_o_mid(v("o")),
                _mkcell(_o_tail(v("o")),
                        _mkcell(_mksym_id("var"), _o_fst(v("o")))))))
    _inst_cell = _fcall(
        "bind",
        _fcall("inst", _apps(lp("fst"), _payload(v("node"))),
               v("ren"), v("n")),
        L("o1")(_fcall(
            "bind",
            _fcall("inst", _apps(lp("snd"), _payload(v("node"))),
                   _o_fst(v("o1")), _o_mid(v("o1"))),
            L("o2")(_stream(
                _mkcell(_o_fst(v("o2")),
                        _mkcell(_o_mid(v("o2")),
                                _mkcell(_o_tail(v("o1")),
                                        _o_tail(v("o2"))))))))))
    lts["inst"] = L("T", "node", "ren", "n")(
        _apps(_fcall("is_nvar", v("node")),
              _fcall("bind",
                     _fcall("ren_fc", _nvararg(v("node")), v("ren"),
                            v("n")),
                     _inst_hit),
              _apps(_fcall("is_pair", v("node")),
                    _inst_cell,
                    _stream(_mkcell(v("ren"),
                                    _mkcell(v("n"), v("node")))))))

    # inst_list : lst ren n -> stream[[r2|[n2|lst2]]]
    _ilst_tail = _lams("o1")(_fcall(
        "bind",
        _fcall("inst_list", v("_rest"), _o_fst(v("o1")),
               _o_mid(v("o1"))),
        _lams("o2")(_stream(
            _mkcell(_o_fst(v("o2")),
                    _mkcell(_o_mid(v("o2")),
                            _mkcell(_o_tail(v("o1")),
                                    _o_tail(v("o2")))))))))
    lts["inst_list"] = L("T", "lst", "ren", "n")(
        _case3(v("lst"),
               L("bv")(_apps(_fcall("isnil", v("lst")),
                             _stream(_mkcell(v("ren"),
                                             _mkcell(v("n"),
                                                     _dnil()))),
                             _dnil())),
               L("n")(_dnil()),
               L("cell")(_cellpl_body(v("cell"), L("_h", "_rest")(
                   _fcall("bind",
                          _fcall("inst", v("_h"), v("ren"), v("n")),
                          _ilst_tail))))))

    # reify : t s -> stream[r] = walk then reify_w (deep walk)
    lts["reify"] = L("T", "t", "s")(
        _fcall("bind", _fcall("walk", v("t"), v("s")),
               L("w")(_fcall("reify_w", v("w"), v("s")))))
    lts["reify_w"] = L("T", "w", "s")(
        _apps(_fcall("is_pair", v("w")),
              _fcall("bind",
                     _fcall("reify",
                            _apps(lp("fst"), _payload(v("w"))), v("s")),
                     L("ra")(_fcall(
                         "bind",
                         _fcall("reify",
                                _apps(lp("snd"), _payload(v("w"))),
                                v("s")),
                         L("rb")(_stream(_mkcell(v("ra"), v("rb"))))))),
              _stream(v("w"))))

    # unify_args : ins at s -> stream[s1] - corpus pair-wise
    lts["unify_args"] = L("T", "ins", "at", "s")(
        _apps(_fcall("isnil", v("ins")),
              _apps(_fcall("isnil", v("at")), _stream(v("s")), _dnil()),
              _case3(v("ins"),
                     L("bv")(_dnil()),
                     L("n")(_dnil()),
                     L("cell")(_cellpl_body(v("cell"), L("p", "prest")(
                         _case3(v("at"),
                                L("bv")(_dnil()),
                                L("n")(_dnil()),
                                L("c2")(_cellpl_body(v("c2"),
                                    L("a", "arest")(
                                    _fcall("bind",
                                           _fcall("unify_enc", v("p"),
                                                  v("a"), v("s")),
                                           L("s0")(_fcall("unify_args",
                                                          v("prest"),
                                                          v("arest"),
                                                          v("s0")))))))
                         )))))))

    # eval_body : env goals s n -> stream[[s|n]]
    lts["eval_body"] = L("T", "env", "goals", "s", "n")(
        _apps(_fcall("isnil", v("goals")),
              _stream(_mkcell(v("s"), v("n"))),
              _case3(v("goals"),
                     L("bv")(_dnil()),
                     L("n")(_dnil()),
                     L("cell")(_cellpl_body(v("cell"), L("g", "rest")(
                         _fcall("bind",
                                _fcall("eval", v("env"), v("g"), v("s"),
                                       v("n")),
                                L("o")(_fcall("eval_body", v("env"),
                                              v("rest"),
                                              _o_fst(v("o")),
                                              _o_snd(v("o")))))))
                     ))))

    # eval_clause : env cl ins outP at ot s n -> stream[o]
    # corpus 'clause(goals) is a match pattern — wrong tag refuses
    lts["eval_clause"] = L("T", "env", "cl", "ins", "outP", "at",
                           "ot", "s", "n")(
        _apps(_tagchk(v("cl"), "clause"),
              _fcall("bind",
                     _fcall("inst_list", v("ins"), _dnil(), v("n")),
               L("o1")(_fcall(
                   "bind",
                   _fcall("inst", v("outP"), _o_fst(v("o1")),
                          _o_mid(v("o1"))),
                   L("o2")(_fcall(
                       "bind",
                       _fcall("inst_list",
                              _apps(lp("snd"), _payload(v("cl"))),
                              _o_fst(v("o2")), _o_mid(v("o2"))),
                       L("o3")(_fcall(
                           "bind",
                           _fcall("unify_args", _o_tail(v("o1")),
                                  v("at"), v("s")),
                           L("s1")(_fcall(
                               "bind",
                               _fcall("unify_enc", v("ot"),
                                      _o_tail(v("o2")), v("s1")),
                               L("s3")(_fcall("eval_body", v("env"),
                                             _o_tail(v("o3")), v("s3"),
                                             _o_mid(v("o3")))))))
                       )))
               ))),
              _dnil()))

    # eval_clauses : try each clause, append results (disjunction)
    lts["eval_clauses"] = L("T", "env", "cls", "ins", "outP", "at",
                            "ot", "s", "n")(
        _case3(v("cls"),
               L("bv")(_dnil()),
               L("n")(_dnil()),
               L("cell")(_cellpl_body(v("cell"), L("cl", "rest")(
                   _fcall("append",
                          _fcall("eval_clause", v("env"), v("cl"),
                                 v("ins"), v("outP"), v("at"), v("ot"),
                                 v("s"), v("n")),
                          _fcall("eval_clauses", v("env"), v("rest"),
                                 v("ins"), v("outP"), v("at"), v("ot"),
                                 v("s"), v("n"))))
               ))))

    # eval_call : env def at ot s n -> stream[o]  'def(ins,outP,cls)
    lts["eval_call"] = L("T", "env", "def", "at", "ot", "s", "n")(
        _apps(_tagchk(v("def"), "def"),
              _fcall("eval_clauses", v("env"), _narg(v("def"), 2, True),
                     _narg(v("def"), 0, False), _narg(v("def"), 1, False),
                     v("at"), v("ot"), v("s"), v("n")),
              _dnil()))

    # eval : env goal s n -> stream[[s2|n]] - open-tag dispatch
    ATOM00 = _mkcell(_mksym_id("atom"),
                     _mkcell(_mkatom_l(8, 0), _mkatom_l(8, 0)))
    SYMNE = _mkcell(_mksym_id("sym"), _mksym_id("nonempty"))
    lts["eval"] = L("T", "env", "goal", "s", "n")(
        _apps(_tagchk(v("goal"), "unify"),
              _fcall("bind",
                     _fcall("unify_enc", _narg(v("goal"), 0, False),
                            _narg(v("goal"), 1, True), v("s")),
                     L("s2")(_stream(_mkcell(v("s2"), v("n"))))),
              _apps(_tagchk(v("goal"), "cmp"),
                    # 'cmp(op,a,b): walk both; neq = not-unifiable,
                    # eq = unifiable (eq_t probe, bindings stay local)
                    _fcall("bind",
                           _fcall("walk", _narg(v("goal"), 1, False),
                                  v("s")),
                           L("wa")(_fcall(
                               "bind",
                               _fcall("walk", _narg(v("goal"), 2, True),
                                      v("s")),
                               L("wb")(_apps(
                                   _fcall("eq_leaf",
                                          _narg(v("goal"), 0, False),
                                          _mksym_id("neq")),
                                   _apps(_fcall("isnil",
                                                _fcall("unify_enc",
                                                       v("wa"), v("wb"),
                                                       v("s"))),
                                         _stream(_mkcell(v("s"),
                                                         v("n"))),
                                         _dnil()),
                                   _apps(_fcall("isnil",
                                                _fcall("unify_enc",
                                                       v("wa"), v("wb"),
                                                       v("s"))),
                                         _dnil(),
                                         _stream(_mkcell(v("s"),
                                                         v("n"))))))))),
                    _apps(_tagchk(v("goal"), "run"),
                          # 'run(g,n,ot): RUN(eval,1) -> run_res
                          _apps(_fcall("isnil",
                                       _fcall("take", _nat_lc(1),
                                              _fcall("eval", v("env"),
                                                     _narg(v("goal"), 0,
                                                           False),
                                                     v("s"), v("n")))),
                                _fcall("bind",
                                       _fcall("unify_enc",
                                              _narg(v("goal"), 2, True),
                                              ATOM00, v("s")),
                                       L("s3")(_stream(
                                           _mkcell(v("s3"), v("n"))))),
                                _fcall("bind",
                                       _fcall("unify_enc",
                                              _narg(v("goal"), 2, True),
                                              SYMNE, v("s")),
                                       L("s3")(_stream(
                                           _mkcell(v("s3"), v("n")))))),
                          _apps(_tagchk(v("goal"), "call"),
                                _fcall("bind",
                                       _fcall("env_find",
                                              _narg(v("goal"), 0, False),
                                              v("env")),
                                       L("def")(_fcall(
                                           "eval_call", v("env"),
                                           v("def"),
                                           _narg(v("goal"), 1, False),
                                           _narg(v("goal"), 2, True),
                                           v("s"), v("n")))),
                                _dnil())))))

    return lts


def _natadd_body(bva, bterm):
    """IR: a.payload=p2(ba,va); b is the whole atom-leaf term.
    peano on va: z -> b ; s k -> succ(natadd(mkatom(0,k), b).val)
    wrapped back in a's bits."""
    v, a = lv, la
    L = _lams
    return _apps(bva, L("ba", "va")(
        _apps(v("va"),
              _stream(_apps(lp("mkatom"), v("ba"),
                            _apps(lp("snd"), _payload(bterm)))),
              L("k")(_fcall("bind",
                            _fcall("natadd",
                                   _apps(lp("mkatom"), _nat_lc(0),
                                         v("k")),
                                   v("b")),
                            L("r")(_stream(_apps(
                                lp("mkatom"), v("ba"),
                                _apps(lp("sn"),
                                      _apps(lp("snd"), _payload(
                                          v("r"))))))))))))


def _adyn_combine(wb, wd):
    """IR: wb/wd 'atom cells -> stream['atom(bi, va+vd)] via natadd.
    'atom-node = cell(mksym'atom', cell(bi,vi)); the inner cell's
    payload is p2(bi,vi)."""
    v, a = lv, la
    L = _lams
    bi = _apps(lp("fst"), _payload(_apps(lp("snd"), _payload(wb))))
    vi = _apps(lp("snd"), _payload(_apps(lp("snd"), _payload(wb))))
    dvi = _apps(lp("snd"), _payload(_apps(lp("snd"), _payload(wd))))
    return _fcall("bind",
                  _fcall("natadd", vi, dvi),
                  L("nv2")(_stream(_apps(
                      lp("mkcell"), _mksym_id("atom"),
                      _mkcell(bi, v("nv2"))))))


def machine_term(fuel: int) -> int:
    """the unrolled fn-tuple: F^fuel(BOT) as a substrate node."""
    lts = _build_machine_lts()
    ar = {"bind": 2, "append": 2, "take": 2, "eq_nat": 2,
          "eq_leaf": 2, "eq_term": 2, "isnil": 1, "is_var": 1,
          "is_nvar": 1, "is_pair": 1, "is_adyn": 1,
          "subst_lookup": 2, "walk": 2, "unify_w": 3, "unify_enc": 3,
          "adyn_res": 2, "natadd": 2, "env_find": 2, "next_id": 1,
          "ren_find": 2, "ren_fc": 3, "inst": 3, "inst_list": 3,
          "reify": 2, "reify_w": 2, "unify_args": 3, "eval": 4,
          "eval_call": 6, "eval_clauses": 7, "eval_clause": 7,
          "eval_body": 4}

    def tup(elems):
        """balanced p2 tree — _selpath indexes it in ~log2(N) hops
        instead of a linear spine walk."""
        if len(elems) == 1:
            return elems[0]
        mid = len(elems) // 2
        return _p2(tup(elems[:mid]), tup(elems[mid:]))

    F = bracket0(ll("T", tup([la(lts[n], lv("T"))
                              for n in _FNAMES])))
    t = bracket0(tup([_mkbot(ar[n]) for n in _FNAMES]))
    for _ in range(fuel):
        t = sapp(F, t)
    return t


def mcall(t: int, name: str, *args: int) -> int:
    """substrate: (sel_i T) applied to substrate data args."""
    _init_prelude()
    f = t
    for step in _selpath(_FIDX[name]):
        f = _s_apps(_PRE[step], f)
    return _s_apps(f, *args)


def sub_size(t: int, _seen=None) -> int:
    if _seen is None:
        _seen = set()
    if t in _seen:
        return 0
    _seen.add(t)
    k = _SD[t]
    if k[0] == "a":
        return 1 + sub_size(k[1], _seen) + sub_size(k[2], _seen)
    return 1


def _parse_arg(text: str):
    """CLI arg surface: 42 -> ATOM(8,42); 'n -> sym; (a,b) -> pair;
    [x,y,..] -> NIL-terminated list."""
    text = text.strip()
    if text == "[]":
        return NIL
    if text.startswith("[") and text.endswith("]"):
        out = NIL
        for x in reversed(text[1:-1].split(",")):
            out = t_pair(_parse_arg(x), out)
        return out
    if text.startswith("(") and text.endswith(")"):
        a, b = text[1:-1].split(",", 1)
        return t_pair(_parse_arg(a), _parse_arg(b))
    if text.startswith("'"):
        return t_sym(text[1:])
    return t_atom(8, int(text))


def main(argv: List[str]) -> int:
    # meta-circular eval stacks ~10 frames per step — fuel is the
    # semantic bound, the C-level limit is only an implementation
    # parameter (honest divergence stays an empty stream)
    sys.setrecursionlimit(100_000)
    args = argv[1:]
    if not args:
        return _selftest()
    if args[0] == "run" and len(args) >= 3:
        files, call = args[1].split(","), args[2]
        n = 1
        rest = args[3:]
        if rest and rest[0] == "--n":
            n, rest = int(rest[1]), rest[2:]
        g = load_corpus(files)
        name, _, arg_s = call.partition("<")
        rel_args = [a for a in arg_s.rstrip(">").split(",") if a] \
            if arg_s else []
        ov = fresh()
        sols = run(g, name, [_parse_arg_node(a) for a in rel_args],
                   lit(ov), n=n)
        for s in sols:
            print(term_str(reify(ov, s)))
        return 0 if sols else 1
    if args[0] == "kernel" and len(args) >= 2:
        open(args[1], "wb").write(kernel_bundle())
        return 0
    if args[0] in ("gate", "--gate"):
        return _gate()
    return _selftest()


def _gate() -> int:
    """Congruence witness vs the donor oracle (host/rel_eval.py).
    Staged dependency: while host/ exists the gate runs both
    machines on the same queries and demands identical streams;
    after host/ -> attic/ it degrades to the corpus selftest."""
    here = os.path.dirname(os.path.abspath(__file__))
    host = os.path.join(here, os.pardir, "host")
    files = [os.path.join(here, "std", f)
             for f in sorted(os.listdir(os.path.join(here, "std")))
             if f.endswith(".plex")]
    cg = load_corpus(files)
    try:
        sys.path.insert(0, os.path.abspath(host))
        import rel_eval                        # donor oracle
        import phi_rel
    except ImportError:
        print("gate: oracle absent (host/ retired) - "
              "corpus selftest stands")
        return _selftest()
    og = phi_rel.parse_rel(open(os.path.join(
        host, "corpus", "stdlib.phi"), encoding="utf-8").read())
    # queries are built in the oracle's tuple domain; our side
    # interns them at the lit() boundary
    A = lambda v, b=8: ("atom", b, v)
    P = lambda a, b: ("pair", a, b)
    S = lambda x: ("sym", x)
    NILt = ("atom", 0, 0)

    def L(*xs):
        o = NILt
        for x in reversed(xs):
            o = P(x, o)
        return o

    queries = [
        ("add", [A(2), A(3)]),
        ("fib", [A(5)]),
        ("append", [L(A(1)), L(A(2))]),
        ("head", [L(A(9))]),
        ("call", [S("succ"), A(2)]),
        ("map", [S("succ"), L(A(1), A(2))]),
        ("fold", [S("add"), A(0), L(A(1), A(2), A(3))]),
        ("nibble_half_add", [A(15, 4), A(2, 4), A(1, 4)]),
        ("nibble_add", [L(A(1, 4), A(2, 4)),
                        L(A(3, 4), A(0, 4)), A(0, 4)]),
        ("norm", [("goalterm", "append", [L(A(9)), NILt])]),
        ("assoc", [S("b"), L(P(S("a"), A(10)), P(S("b"), A(20)))]),
        ("assoc_id", [A(7), L(P(A(7), S("first")),
                              P(A(7), S("second")))]),
    ]
    for rel, args in queries:
        _reset_fresh()
        a = run_value(cg, rel, args, n=1)
        rel_eval._reset_fresh()
        b = rel_eval.run_value(og, rel, args, n=1)
        assert [thaw(x) for x in a] == b, (rel, a, b)
    # backward stream: append splits - same order, observational
    _reset_fresh()
    qx, qy = fresh(), fresh()
    ours = [(reify(qx, s), reify(qy, s)) for s in run_solutions(
        cg, "append", [qx, qy], L(A(1), A(2)), n=3)]
    rel_eval._reset_fresh()
    qx, qy = rel_eval.fresh(), rel_eval.fresh()
    theirs = [(rel_eval.reify(qx, s), rel_eval.reify(qy, s))
              for s in rel_eval.run_solutions(
                  og, "append", [qx, qy],
                  rel_eval.t_pair(rel_eval.t_atom(8, 1),
                                  rel_eval.t_pair(
                                      rel_eval.t_atom(8, 2),
                                      rel_eval.NIL)), n=3)]
    assert [(thaw(x), thaw(y)) for x, y in ours] == theirs, \
        (ours, theirs)
    # member enumeration: open arg over [1,2,3] — order is observable
    _reset_fresh()
    mx = fresh()
    ours = [reify(mx, s) for s in run_solutions(
        cg, "member", [mx, L(A(1), A(2), A(3))], mx, n=5)]
    rel_eval._reset_fresh()
    mx = rel_eval.fresh()
    theirs = [rel_eval.reify(mx, s) for s in rel_eval.run_solutions(
        og, "member", [mx, rel_eval.t_pair(
            rel_eval.t_atom(8, 1), rel_eval.t_pair(
                rel_eval.t_atom(8, 2), rel_eval.t_pair(
                    rel_eval.t_atom(8, 3), rel_eval.NIL)))],
        mx, n=5)]
    assert [thaw(x) for x in ours] == theirs, (ours, theirs)
    # both machines refuse compose identically (declared-not-realized)
    for eng, g, tag in ((run_value, cg, "seed"),
                        (rel_eval.run_value, og, "oracle")):
        try:
            eng(g, "compose", [A(0, 4), A(1, 4)], n=1)
        except Exception:
            pass
        else:
            raise AssertionError(f"{tag} ran compose - must refuse")
    print(f"seed gate: {len(queries) + 3} congruence checks vs "
          f"oracle - identical streams, identical refusals: pass")
    return 0


def _parse_arg_node(text: str) -> dict:
    return {"var_lit": _parse_arg(text)}


def _selftest() -> int:
    _reset_fresh()
    here = os.path.dirname(os.path.abspath(__file__))
    # kernel: write -> read -> slices check
    kb = kernel_bundle()
    ker = read_kernel(kb)
    assert set(ker["matrices"]) == {"I", "R", "A", "S"}
    assert ker["ops"] == OPS
    # rel-graph bundle round-trip
    g = {"format": "phi.rel/1",
         "rels": [{"name": "equal", "dir": "<->",
                   "in": [{"var": "a"}, {"var": "b"}],
                   "out": [{"var": "a"}], "shape": None,
                   "clauses": [{"fresh": [], "guard": [],
                                "goals": [{"unify": [{"var": "a"},
                                                     {"var": "b"}]}]}]}]}
    g2 = read_graph_bundle(graph_bundle(g))
    assert g2 == g
    # the stepper on a corpus-shaped program
    corpus = {"format": "phi.rel/1", "rels": [
        {"name": "equal", "dir": "<->",
         "in": [{"var": "a"}, {"var": "b"}], "out": [{"var": "a"}],
         "shape": None,
         "clauses": [{"fresh": [], "guard": [],
                      "goals": [{"unify": [{"var": "a"},
                                           {"var": "b"}]}]}]},
        {"name": "cons", "dir": "<->",
         "in": [{"var": "car"}, {"var": "cdr"}],
         "out": [{"pair": [{"var": "car"}, {"var": "cdr"}]}],
         "shape": None, "clauses": None},
        {"name": "head", "dir": "<->",
         "in": [{"pair": [{"var": "h"}, {"wild": True}]}],
         "out": [{"var": "h"}], "shape": None, "clauses": None},
        {"name": "append", "dir": "<->", "shape": "self",
         "in": [{"var": "xs"}, {"var": "ys"}],
         "out": [{"var": "zs"}],
         "clauses": [
             {"fresh": [], "guard": [],
              "goals": [{"unify": [{"var": "xs"},
                                   {"atom": [0, 0]}]},
                        {"unify": [{"var": "zs"},
                                   {"var": "ys"}]}]},
             {"fresh": ["h", "t", "r"], "guard": [],
              "goals": [
                  {"call": {"rel": "cons",
                            "args": [{"var": "h"}, {"var": "t"}],
                            "out": {"var": "xs"}}},
                  {"call": {"rel": "append",
                            "args": [{"var": "t"}, {"var": "ys"}],
                            "out": {"var": "r"}}},
                  {"call": {"rel": "cons",
                            "args": [{"var": "h"}, {"var": "r"}],
                            "out": {"var": "zs"}}}]}]}]}
    la = t_pair(t_atom(8, 1), NIL)
    lb = t_pair(t_atom(8, 2), NIL)
    want = t_pair(t_atom(8, 1), t_pair(t_atom(8, 2), NIL))
    assert run_value(corpus, "append", [la, lb], n=1) == [want]
    xs, ys = fresh(), fresh()
    sols = run_solutions(corpus, "append", [xs, ys], want, n=3)
    got = [(reify(xs, s), reify(ys, s)) for s in sols]
    assert len(got) == 3
    assert got[0] == (NIL, want) and got[-1] == (want, NIL)
    assert run_value(corpus, "head", [want], n=1) == [t_atom(8, 1)]
    # refusals
    try:
        run_value(corpus, "nosuchrel", [la], n=1)
    except EvalError as e:
        assert "unbound rel" in str(e)
    else:
        raise AssertionError("unbound rel ran")
    # eval.plex — the meta-circular check: the evaluator as data
    # runs an encoded append def and must produce the stepper's own
    # splits, in the same order (observational equivalence).
    evp = os.path.join(here, "eval.plex")
    metacirc = "absent"
    if os.path.exists(evp):
        eg = load_graph(evp)
        S = t_sym

        def eAtom(b, v):
            return t_pair(S("atom"), t_pair(t_atom(8, b),
                                           t_atom(8, v)))

        def eVar(i):
            return t_pair(S("var"), t_atom(8, i))

        def eNvar(x):
            return t_pair(S("nvar"), S(x))

        def ePair(a, b):
            return t_pair(S("pair"), t_pair(a, b))

        def eSym(x):
            return t_pair(S("sym"), S(x))

        def eList(*xs):
            o = NIL
            for x in reversed(xs):
                o = t_pair(x, o)
            return o

        def dec(e):
            if e[0] == "pair" and e[1][0] == "sym":
                k = e[1][1]
                if k == "atom":
                    return ("atom", e[2][1][2], e[2][2][2])
                if k == "pair":
                    return ("pair", dec(e[2][1]), dec(e[2][2]))
                if k == "var":
                    return ("var", e[2][2])
                if k == "sym":
                    return ("sym", e[2][1])
            raise ValueError(e)

        NILe = eAtom(0, 0)
        nv = eNvar
        ins = eList(nv("xs"), nv("ys"))
        outP = nv("zs")
        c1 = t_pair(S("clause"), eList(
            t_pair(S("unify"), t_pair(nv("xs"), NILe)),
            t_pair(S("unify"), t_pair(nv("zs"), nv("ys")))))
        c2 = t_pair(S("clause"), eList(
            t_pair(S("unify"),
                   t_pair(nv("xs"), ePair(nv("h"), nv("t")))),
            t_pair(S("call"), t_pair(
                eSym("append"),
                t_pair(eList(nv("t"), nv("ys")), nv("r")))),
            t_pair(S("unify"),
                   t_pair(nv("zs"), ePair(nv("h"), nv("r"))))))
        appendDef = t_pair(S("def"), t_pair(
            ins, t_pair(outP, eList(c1, c2))))
        env = eList(t_pair(eSym("append"), appendDef))
        ewant = ePair(eAtom(8, 1), ePair(eAtom(8, 2), NILe))
        goal = t_pair(S("call"), t_pair(
            eSym("append"),
            t_pair(eList(eVar(90), eVar(91)), ewant)))
        _reset_fresh()
        sols = run_value(eg, "eval", [env, goal, NIL,
                                      t_atom(8, 1)], n=3)
        splits = []
        for sp in sols:
            s2 = _ND[sp][1]
            rx = run_value(eg, "reify", [eVar(90), s2], n=1)[0]
            ry = run_value(eg, "reify", [eVar(91), s2], n=1)[0]
            splits.append((dec(thaw(rx)), dec(thaw(ry))))
        assert len(splits) == 3, splits
        assert splits[0][0] == ("atom", 0, 0) and \
            splits[-1][1] == ("atom", 0, 0), splits
        metacirc = f"{len(splits)} splits congruent"
    # specialize.plex — Futamura-1: subst_env bakes 'xs=[1] into
    # the def; the residual goes in under a fresh name (the static
    # arg is a boundary, not recursive) and must eval congruently.
    spp = os.path.join(here, "specialize.plex")
    specr = "absent"
    if metacirc != "absent" and os.path.exists(spp):
        sg = load_corpus([
            os.path.join(here, "std", "lists_member_assoc.plex"),
            spp, evp])
        senv = eList(t_pair(S("xs"), ePair(eAtom(8, 1), NILe)))
        rd = run_value(sg, "specialize", [appendDef, senv], n=1)[0]
        env2 = eList(t_pair(eSym("append_1"), rd),
                     t_pair(eSym("append"), appendDef))
        goal = t_pair(S("call"), t_pair(
            eSym("append_1"),
            t_pair(eList(ePair(eAtom(8, 1), NILe),
                         ePair(eAtom(8, 2), NILe)), eVar(97))))
        _reset_fresh()
        rs = run_value(sg, "eval", [env2, goal, NIL,
                                    t_atom(8, 1)], n=1)
        assert len(rs) == 1
        rout = run_value(sg, "reify", [eVar(97), _ND[rs[0]][1]],
                         n=1)[0]
        env1 = eList(t_pair(eSym("append"), appendDef))
        goal = t_pair(S("call"), t_pair(
            eSym("append"),
            t_pair(eList(ePair(eAtom(8, 1), NILe),
                         ePair(eAtom(8, 2), NILe)), eVar(98))))
        _reset_fresh()
        oos = run_value(sg, "eval", [env1, goal, NIL,
                                     t_atom(8, 1)], n=1)
        oout = run_value(sg, "reify", [eVar(98),
                                       _ND[oos[0]][1]], n=1)[0]
        assert rout == oout, (rout, oout)
        specr = "F1 square closed"
    # realize.plex — the spec fold: maps resolve through qmaps
    # (assoc), each applied through the corpus eval.  Order is
    # data; missing maps refuse as empty streams.
    rzp = os.path.join(here, "realize.plex")
    realr = "absent"
    if metacirc != "absent" and os.path.exists(rzp):
        rg = load_corpus([
            os.path.join(here, "std", "lists_member_assoc.plex"),
            evp, rzp])

        def markDef(tag):
            return t_pair(S("def"), t_pair(
                eList(nv("x")), t_pair(
                    ePair(eSym(tag), nv("x")),
                    eList(t_pair(S("clause"), NIL)))))

        def mapT(tag):
            return t_pair(S("map"), t_pair(
                eList(t_pair(eSym("mark"), markDef(tag))),
                S("mark")))

        qmaps = eList(t_pair(S("m1"), mapT("s1")),
                      t_pair(S("m2"), mapT("s2")))

        def mkSpec(maps):
            return t_pair(S("spec"), t_pair(
                eSym("src"),
                t_pair(maps, t_pair(
                    qmaps, t_pair(eSym("operEq"), eSym("ctx"))))))

        _reset_fresh()
        o1 = run_value(rg, "realize", [mkSpec(
            eList(S("m1"), S("m2")))], n=1)
        assert len(o1) == 1
        s1s2 = dec(thaw(o1[0]))
        _reset_fresh()
        o2 = run_value(rg, "realize", [mkSpec(
            eList(S("m2"), S("m1")))], n=1)
        s2s1 = dec(thaw(o2[0]))
        assert s1s2 == ("pair", ("sym", "s2"),
                        ("pair", ("sym", "s1"), ("sym", "src"))), \
            s1s2
        assert s2s1 == ("pair", ("sym", "s1"),
                        ("pair", ("sym", "s2"), ("sym", "src"))), \
            s2s1
        missing = run_value(rg, "realize", [mkSpec(
            eList(S("m9")))], n=1)
        assert missing == []
        realr = "fold ordered, refusal honest"
    # S2d/e documents — toolchain catalog, comp spec, runtime
    # contract, and the first real map (x86 assemble rows)
    docr = "absent"
    tcp = os.path.join(here, "toolchain.plex")
    cpp = os.path.join(here, "comp.plex")
    rtp = os.path.join(here, "runtime.plex")
    cgp = os.path.join(here, "cogen.plex")
    amp = os.path.join(here, "maps", "assemble_rules_x86.plex")
    if metacirc != "absent" and all(os.path.exists(p) for p in
                                    (tcp, cpp, rtp, cgp, amp)):
        std_dir = os.path.join(here, "std")
        dg = load_corpus(
            [os.path.join(std_dir, f)
             for f in sorted(os.listdir(std_dir))
             if f.endswith(".plex")]
            + [evp, rzp, cgp, tcp, cpp, rtp, amp])

        def eT(tag, *xs):
            o = xs[-1] if xs else NIL
            for x in reversed(xs[:-1]):
                o = t_pair(x, o)
            return t_pair(t_sym(tag), o)

        cat = run_value(dg, "toolchain", [], n=1)[0]
        m = run_value(dg, "map_of", [S("assemble_x86"), cat], n=1)
        assert len(m) == 1
        t = run_value(dg, "target_of",
                      [S("win64_x86_64_pe"), cat], n=1)
        assert len(t) == 1
        # the assemble map emits real x86 bytes and refuses on
        # every unlisted axis
        ops = eList(eT("op", S("push"), S("rax")),
                    eT("op", S("pop"), S("rbx")),
                    eT("op", S("ret")))
        b = run_value(dg, "assemble", [ops], n=1)
        assert b == [eList(t_atom(8, 0x50), t_atom(8, 0x5B),
                           t_atom(8, 0xC3))], b
        assert run_value(dg, "assemble", [eList(
            eT("op", S("push"), S("r8")))], n=1) == []
        assert run_value(dg, "assemble", [eList(
            eT("op", S("xyz")))], n=1) == []
        # comp emits the spec document; cogen refuses honestly on
        # the deferred qmaps until a loader binds them
        sp = run_value(dg, "comp", [], n=1)[0]
        assert run_value(dg, "cogen", [sp], n=1) == []
        # runtime: 'graph loader runs an img through corpus eval;
        # an unbound loader family refuses
        iddef = t_pair(S("def"), t_pair(
            eList(nv("x")), t_pair(nv("x"),
                                  eList(t_pair(S("clause"), NIL)))))
        img = eT("img", eList(t_pair(eSym("id"), iddef)), S("id"))
        r = run_value(dg, "runtime", [img, NIL, eAtom(8, 42)], n=1)
        assert r == [eAtom(8, 42)], r
        caps = eList(t_pair(S("loader"), S("fasm")))
        assert run_value(dg, "runtime", [img, caps, eAtom(8, 42)],
                         n=1) == []
        docr = "catalog+spec+runtime+map, refusals hold"
    # self-description foothold: eval on enc'd defs (double meta).
    # 'cmp/'run goal forms + inst coverage — an enc'd subst_lookup
    # evaluated by the corpus eval against an enc'd env.
    sd = "absent"
    if metacirc != "absent":
        def eT(tag, *xs):
            o = xs[-1] if xs else NIL
            for x in reversed(xs[:-1]):
                o = t_pair(x, o)
            return t_pair(t_sym(tag), o)

        sl_def = eT("def",
                    eList(nv("k"), nv("lst")), nv("r"),
                    eList(
                        eT("clause", eList(
                            eT("unify", nv("lst"),
                               eT("pair",
                                  eT("pair", nv("k"), nv("v")),
                                  nv("rest"))),
                            eT("unify", nv("r"),
                               eT("pair", eSym("bound"), nv("v"))))),
                        eT("clause", eList(
                            eT("unify", nv("lst"),
                               eT("pair",
                                  eT("pair", nv("k2"), nv("_w")),
                                  nv("rest"))),
                            eT("cmp", t_sym("neq"), nv("k"),
                               nv("k2")),
                            eT("call", eSym("subst_lookup"),
                               eList(nv("k"), nv("rest")),
                               nv("r")))),
                        eT("clause", eList(
                            eT("unify", nv("lst"), eAtom(0, 0)),
                            eT("unify", nv("r"), eSym("unbound"))))))
        senv = eList(t_pair(eSym("subst_lookup"), sl_def))
        elist = eT("pair", eT("pair", eAtom(8, 1), eAtom(8, 7)),
                   eT("pair", eT("pair", eAtom(8, 2), eAtom(8, 8)),
                      eAtom(0, 0)))
        goal = eT("call", eSym("subst_lookup"),
                  eList(eAtom(8, 1), elist), eVar(0))
        _reset_fresh()
        hit = run_value(eg, "eval", [senv, goal, NIL,
                                     t_atom(8, 1)], n=1)
        assert len(hit) == 1
        o = run_value(eg, "reify", [eVar(0), _ND[hit[0]][1]], n=1)
        assert o == [eT("pair", eSym("bound"), eAtom(8, 7))], o
        goal2 = eT("call", eSym("subst_lookup"),
                   eList(eAtom(8, 9), elist), eVar(0))
        _reset_fresh()
        miss = run_value(eg, "eval", [senv, goal2, NIL,
                                      t_atom(8, 1)], n=1)
        assert len(miss) == 1
        o2 = run_value(eg, "reify", [eVar(0), _ND[miss[0]][1]],
                       n=1)
        assert o2 == [eSym("unbound")], o2
        # enc'er: a real .plex graph -> enc'd env, run by corpus
        # eval — any bundle becomes program data, no hand-built
        # terms.  assoc<'b> hits 'atom(8,20) inside an enc'd spine.
        ma = load_graph(os.path.join(
            here, "std", "lists_member_assoc.plex"))
        menv = enc_env(ma)
        alist = eT("pair",
                   eT("pair", eSym("a"), eAtom(8, 1)),
                   eT("pair",
                      eT("pair", eSym("b"), eAtom(8, 20)),
                      eAtom(0, 0)))
        mg = eT("call", eSym("assoc"),
                eList(eSym("b"), alist), eVar(0))
        _reset_fresh()
        mh = run_value(eg, "eval", [menv, mg, NIL,
                                    t_atom(8, 1)], n=1)
        assert len(mh) == 1
        mo = run_value(eg, "reify", [eVar(0), _ND[mh[0]][1]], n=1)
        assert mo == [eAtom(8, 20)], mo
        # whole eval.plex enc's as data too — the 25-rel env is
        # the self-description substrate for L2 interpretation
        env1 = enc_env(eg)
        # L2 foothold: enc'd eval interprets a grammar-2 'unify
        # goal over the fully enc'd self-env.  Level law: inner
        # env is a 'pair-spine of 'pair('sym-key, enc_t(def))
        # cells ending the enc'd empty list ('atom(0,0)-node);
        # goal nodes are 'pair('sym'tag', right-nested-args);
        # top-level out slots stay corpus-level 'var nodes.
        def eP(a, b): return t_pair(S("pair"), t_pair(a, b))
        def eSym2(x): return t_pair(S("sym"), S(x))
        def eAtom2(b, v): return t_pair(S("atom"),
                                        t_pair(t_atom(8, b),
                                               t_atom(8, v)))
        NILe = eAtom2(0, 0)
        def enc_t(t):
            t = _force(t, NIL)
            k = _ND[t]
            if k[0] == "p":
                return eP(enc_t(k[1]), enc_t(k[2]))
            if k[0] == "s":
                return eSym2(k[1])
            if k[0] == "a":
                return eAtom2(k[1], k[2])
            raise AssertionError("enc_t " + str(k))
        ienv = NILe
        ents = []
        cur = env1
        while _ND[cur][0] == "p":
            e = _ND[_ND[cur][1]]
            ents.append((e[1], enc_t(e[2])))
            cur = _ND[cur][2]
        for k, d in reversed(ents):
            ienv = eP(eP(k, d), ienv)
        gvar = eP(eSym2("var"), eAtom2(8, 90))
        g2 = eP(eSym2("unify"), eP(eAtom2(8, 5), gvar))
        at = NIL
        for x in reversed([ienv, g2, NILe, t_atom(8, 1)]):
            at = t_pair(x, at)
        g1 = t_pair(S("call"),
                    t_pair(eSym("eval"), t_pair(at, eVar(91))))
        _reset_fresh()
        l2 = run_value(eg, "eval", [env1, g1, NIL,
                                    t_atom(8, 1)], n=1,
                       fuel=500000)
        assert len(l2) == 1, "L2 'unify through enc'd eval"
        sd = ("enc'd subst_lookup hit+miss, enc'er bundle->env, "
              "L2 'unify via enc'd eval")
        # H0 foothold: the combinator machine (lowered rels,
        # bracketed I/K/S, F^fuel(BOT) tuple) through the host
        # graph runtime, observational decode.  Cheap leaves so
        # the machine path has a standing check.
        assert h0_call("next_id", [enc_sub(t_atom(8, 0))],
                       mfuel=8) == [("a", 8, 1)]
        assert h0_call("subst_lookup",
                       [enc_sub(t_atom(8, 7)),
                        enc_sub(t_atom(0, 0))],
                       mfuel=8) == [("s", "unbound")]
        sd += ", H0 next_id+subst_lookup"
    # corpus files if present
    std = os.path.join(here, "std")
    if os.path.isdir(std):
        files = sorted(os.path.join(std, f)
                       for f in os.listdir(std)
                       if f.endswith(".plex"))
        if files:
            cg = load_corpus(files)
            assert run_value(cg, "add", [t_atom(8, 2),
                                         t_atom(8, 3)],
                             n=1) == [t_atom(8, 5)]
            assert run_value(cg, "append", [la, lb],
                             n=1) == [want]
            nstd = len(cg["rels"])
        else:
            nstd = 0
    else:
        nstd = 0
    print(f"seed selftest: kernel {len(kb)}B (slices I=5 A=0 "
          f"S.row0=3, K^2=0), rel-bundle round-trip, stepper "
          f"append fwd/bwd + head, refusals, corpus rels={nstd}, "
          f"meta-circular eval [{metacirc}], "
          f"specialize [{specr}], realize [{realr}], "
          f"docs [{docr}], self-desc [{sd}]: pass")
    return 0


# --- H0 witness driver: substrate term -> host Graph.cd -> decode ---
# Observational decode: data terms are probed by applying selector
# combinators (q K -> fst, q KI -> snd, case markers), never by
# inspecting the implementation.  The oracle comparison is on
# decoded shapes, same discipline as the lit() gate boundary.

_HT_MEMO: Dict[int, object] = {}


def _host():
    here = os.path.dirname(os.path.abspath(__file__))
    hp = os.path.abspath(os.path.join(here, os.pardir, "host"))
    if hp not in sys.path:
        sys.path.insert(0, hp)
    import reduce as R  # noqa: E402
    import graph_runtime as G  # noqa: E402
    return R, G


def _to_host_T(t: int):
    r = _HT_MEMO.get(t)
    if r is not None:
        return r
    R, _ = _host()
    k = _SD[t]
    if k[0] == "a":
        r = R.app(_to_host_T(k[1]), _to_host_T(k[2]))
    else:
        r = {"I": R.I, "K": R.KK, "S": R.S}[k[0]]
    _HT_MEMO[t] = r
    return r


def _happ(g, i, *xs):
    for x in xs:
        i = g.mk_app(i, g.import_tree(x))
    return i


def _hnf(g, i, fuel):
    nf, _ = g.reduce_cd(i, fuel=fuel)
    return g.repr(nf)


def _dec_nat(g, i, fuel, mz):
    """scott nat -> int: probe t MZ I; z -> MZ marker, sn k -> k."""
    R, _ = _host()
    mzid = g.repr(g.import_tree(mz))
    n = 0
    while True:
        r = _hnf(g, _happ(g, i, mz, R.I), fuel)
        if r == mzid:
            return n
        i = r
        n += 1
        if n > 10000:
            raise EvalError("encode/decode: nat probe diverged")


def _dec_term(g, i, fuel, marks):
    """union data term -> ('a',b,v) | ('s',name) | ('p',a,b)."""
    R, _ = _host()
    MA, MS, MP, KI = marks
    probe = _hnf(g, _happ(g, i, R.app(R.KK, MA),
                          R.app(R.KK, MS), R.app(R.KK, MP)), fuel)
    gMA = g.repr(g.import_tree(MA))
    gMS = g.repr(g.import_tree(MS))
    gMP = g.repr(g.import_tree(MP))
    if probe == gMA:
        q = _hnf(g, _happ(g, i, R.I, R.KK, R.KK), fuel)
        b = _dec_nat(g, _hnf(g, _happ(g, q, R.KK), fuel), fuel, MA)
        v = _dec_nat(g, _hnf(g, _happ(g, q, KI), fuel), fuel, MA)
        return ("a", b, v)
    if probe == gMS:
        n = _dec_nat(g, _hnf(g, _happ(g, i, R.KK, R.I, R.KK), fuel),
                     fuel, MA)
        return ("s", _SYMNAMES[n] if n < len(_SYMNAMES) else f"#{n}")
    if probe == gMP:
        q = _hnf(g, _happ(g, i, R.KK, R.KK, R.I), fuel)
        a = _dec_term(g, _hnf(g, _happ(g, q, R.KK), fuel), fuel, marks)
        b = _dec_term(g, _hnf(g, _happ(g, q, KI), fuel), fuel, marks)
        return ("p", a, b)
    raise EvalError("encode/decode: term not a union value")


def _dec_stream(g, i, fuel, marks, limit=1000):
    """stream (mkcell spine / dnil) -> list of decoded terms."""
    R, _ = _host()
    MA, MS, MP, KI = marks
    out = []
    while len(out) < limit:
        probe = _hnf(g, _happ(g, i, R.app(R.KK, MA),
                              R.app(R.KK, MS), R.app(R.KK, MP)), fuel)
        if probe == g.repr(g.import_tree(MA)):
            q = _hnf(g, _happ(g, i, R.I, R.KK, R.KK), fuel)
            b = _dec_nat(g, _hnf(g, _happ(g, q, R.KK), fuel), fuel, MA)
            v = _dec_nat(g, _hnf(g, _happ(g, q, KI), fuel), fuel, MA)
            if b == 0 and v == 0:
                return out
            raise EvalError("encode/decode: stream tail is atom "
                            f"({b},{v})")
        if probe != g.repr(g.import_tree(MP)):
            raise EvalError("encode/decode: stream tail is sym")
        q = _hnf(g, _happ(g, i, R.KK, R.KK, R.I), fuel)
        out.append(_dec_term(g, _hnf(g, _happ(g, q, R.KK), fuel),
                             fuel, marks))
        i = _hnf(g, _happ(g, q, KI), fuel)
    raise EvalError("encode/decode: stream probe diverged")


def h0_call(name: str, args: list, mfuel: int, rfuel: int = 500_000):
    """lowered machine call -> decoded stream (the H0 witness path)."""
    _init_prelude()
    R, G = _host()
    M = machine_term(mfuel)
    call = mcall(M, name, *args)
    g = G.Graph()
    root = g.import_tree(_to_host_T(call))
    nf = _hnf(g, root, rfuel)
    marks = (R.I, R.app(R.KK, R.I), R.app(R.KK, R.KK),
             R.app(R.KK, R.I))
    return _dec_stream(g, nf, rfuel, marks)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
