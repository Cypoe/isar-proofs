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

def t_atom(bits: int, v: int) -> tuple:
    return ("atom", bits, v)


def t_pair(a, b) -> tuple:
    return ("pair", a, b)


def t_var(i) -> tuple:
    return ("var", i)


def t_sym(name: str) -> tuple:
    return ("sym", name)


NIL = t_atom(0, 0)
_fresh_i = itertools.count(1)


def fresh() -> tuple:
    return t_var(next(_fresh_i))


def _reset_fresh() -> None:
    global _fresh_i
    _fresh_i = itertools.count(1)
    _FIELDS.clear()


_FIELDS: Dict[int, Tuple[tuple, str]] = {}


def term_str(t) -> str:
    if not isinstance(t, tuple):
        return repr(t)
    if t[0] == "atom":
        return f"ATOM({t[1]},{t[2]})" if t[1] else "[]"
    if t[0] == "pair":
        items, cur = [], t
        while isinstance(cur, tuple) and cur[0] == "pair":
            items.append(term_str(cur[1]))
            cur = cur[2]
        if cur == NIL:
            return "[" + ", ".join(items) + "]"
        return f"({term_str(t[1])} · {term_str(t[2])})"
    if t[0] == "var":
        return f"?{t[1]}"
    if t[0] == "sym":
        return f"'{t[1]}"
    if t[0] == "reldef":
        return f"<reldef {t[1]}>"
    if t[0] == "goalterm":
        return f"<goal {t[1]}/>"
    if t[0] == "pat":
        return f"<pat {t[1]}>"
    if t[0] == "bodycall":
        return f"<body {t[1]}>"
    return repr(t)


Subst = Dict[object, tuple]


def walk(t, s: Subst):
    while isinstance(t, tuple) and t[0] == "var" and t[1] in s:
        t = s[t[1]]
    if isinstance(t, tuple) and t[0] == "var" and t[1] in _FIELDS:
        root, fld = _FIELDS[t[1]]
        rv = _force(walk(root, s), s)
        if isinstance(rv, tuple) and rv[0] == "reldef":
            return ("pat", rv[1]) if fld == "pat" else \
                ("bodycall", rv[1])
    return t


def unify(u, v, s: Subst) -> Optional[Subst]:
    u, v = _force(walk(u, s), s), _force(walk(v, s), s)
    if u == v:
        return s
    if isinstance(u, tuple) and u[0] == "var":
        return {**s, u[1]: v}
    if isinstance(v, tuple) and v[0] == "var":
        return {**s, v[1]: u}
    if isinstance(u, tuple) and isinstance(v, tuple) and \
            u[0] == "pair" and v[0] == "pair":
        s2 = unify(u[1], v[1], s)
        return unify(u[2], v[2], s2) if s2 is not None else None
    return None


def reify(t, s: Subst):
    t = _force(walk(t, s), s)
    if isinstance(t, tuple) and t[0] == "pair":
        return t_pair(reify(t[1], s), reify(t[2], s))
    return t


class EvalError(ValueError):
    """Runtime refusal: unbound names, unexecutable forms, undeclared
    recursion.  Fuel exhaustion is NOT here: it is an observable
    empty stream."""


# ---------------------------------------------------------------------------
# lift - rel-graph node -> runtime term (ren = this scope's renaming)
# ---------------------------------------------------------------------------

def lift(node, ren: Dict[str, tuple]):
    if node is None:
        return NIL
    if "var" in node:
        n = node["var"]
        if n not in ren:
            ren[n] = fresh()
            if "." in n:
                root = lift({"var": n.split(".", 1)[0]}, ren)
                _FIELDS[ren[n][1]] = (root, n.split(".", 1)[1])
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
        return ("atom_lazy", _lazy_e(be, ren), _lazy_e(pe, ren))
    if "pair" in node:
        return t_pair(lift(node["pair"][0], ren),
                      lift(node["pair"][1], ren))
    if "typed" in node:
        return lift(node["typed"][0], ren)
    if "type" in node:
        return fresh()
    if "var_lit" in node:
        return node["var_lit"]
    if "sym" in node:
        return t_sym(node["sym"])
    if "call_term" in node:
        name, args = node["call_term"]
        return ("goalterm", name, [lift(a, ren) for a in args])
    if "__term" in node:
        return node["__term"]
    raise EvalError(f"seed: unliftable term node {node!r}")


def _aval(e: dict, ren) -> Optional[int]:
    if "const" in e:
        return e["const"]
    name, d = e["var_delta"]
    v = ren.get(name)
    if isinstance(v, tuple) and v[0] == "atom":
        return v[2] + d
    return None


def _lazy_e(e: dict, ren):
    if "const" in e:
        return ("const", e["const"])
    name, d = e["var_delta"]
    if name not in ren:
        ren[name] = fresh()
    return ("delta", ren[name], d)


def _force(t, s: Subst):
    if not (isinstance(t, tuple) and t[0] == "atom_lazy"):
        return t
    out = []
    for e in t[1:]:
        if e[0] == "const":
            out.append(e[1])
            continue
        v = walk(e[1], s)
        v = _force(v, s) if isinstance(v, tuple) else v
        if not (isinstance(v, tuple) and v[0] == "atom"):
            return t
        out.append(v[2] + e[2])
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
        va = a[2] if isinstance(a, tuple) and a[0] == "atom" else None
        vb = b[2] if isinstance(b, tuple) and b[0] == "atom" else None
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
    if isinstance(gt, tuple) and gt[0] == "goalterm":
        return gt[1], [{"__term": a} for a in gt[2]]
    raise EvalError(
        f"goal must be a call_term or goalterm, got "
        f"{term_str(gt) if isinstance(gt, tuple) else gnode!r}")


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
    nlim = n[2] if isinstance(n, tuple) and n[0] == "atom" else 0
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
        return ("var", node["var"])
    if "wild" in node:
        return fresh()
    if "atom" in node:
        return t_atom(node["atom"][0], node["atom"][1])
    if "atom_dyn" in node:
        be, pe = node["atom_dyn"]
        out = []
        for e in (be, pe):
            if "const" in e:
                out.append(("const", e["const"]))
            else:
                name, d = e["var_delta"]
                out.append(("delta", ("var", name), d))
        return ("atom_lazy", *out)
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


def _tvars(t) -> Iterator[tuple]:
    if isinstance(t, tuple):
        if t[0] == "var" and isinstance(t[1], str):
            yield t
        elif t[0] == "pair":
            yield from _tvars(t[1])
            yield from _tvars(t[2])
        elif t[0] == "atom_lazy":
            for e in t[1:]:
                if e[0] == "delta":
                    yield from _tvars(e[1])


def _rtuple(terms: list):
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = t_pair(t, out)
    return out


def _decode_binds(lst, s: Subst) -> Dict[str, tuple]:
    out: Dict[str, tuple] = {}
    cur = _force(lst, s)
    while isinstance(cur, tuple) and cur[0] == "pair":
        ent = cur[1]
        if isinstance(ent, tuple) and ent[0] == "pair" and \
                isinstance(ent[1], tuple) and ent[1][0] == "var":
            out[ent[1][1]] = _force(walk(ent[2], s), s)
        cur = _force(walk(cur[2], s), s)
    return out


def _instantiate(node, binds: Dict[str, tuple]):
    if "var" in node:
        return binds.get(node["var"], ("var", node["var"]))
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
            if isinstance(v, tuple) and v[0] == "atom":
                out.append(v[2] + d)
            else:
                ok = False
        if ok:
            return t_atom(out[0], out[1])
        return ("atom_lazy", *[
            ("const", e["const"]) if "const" in e else
            ("delta", binds.get(e["var_delta"][0],
                                ("var", e["var_delta"][0])),
             e["var_delta"][1])
            for e in (be, pe)])
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
        if isinstance(pat, tuple) and pat[0] == "pat":
            rname = pat[1]
            rel = env["rels"].get(rname)
            if rel is None:
                raise EvalError(f"MATCH: unbound rel {rname!r}")
            ins = [_pat_lift(n) for n in rel["in"]]
            shadow = {v[1] for n in ins for v in _tvars(n)}
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
        if isinstance(t, tuple) and t[0] == "bodycall":
            rel = env["rels"].get(t[1])
            if rel is None:
                raise EvalError(f"APPLY: unbound rel {t[1]!r}")
            binds = _decode_binds(
                _force(walk(lift(args[0], ren), s), s), s)
            argnodes = [{"__term": _instantiate(n, binds)}
                        for n in rel["in"]]
            ov = fresh()
            for sx in _rel_call(t[1], argnodes, {"var_lit": ov},
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
        if not (isinstance(nm, tuple) and nm[0] == "sym"):
            raise EvalError(
                f"env_lookup: rel name must be a symbol, got "
                f"{term_str(nm)}")
        if nm[1] not in env["rels"]:
            raise EvalError(f"env_lookup: unbound rel {nm[1]!r}")
        s2 = unify(lift(out, ren), ("reldef", nm[1]), s) \
            if out is not None else s
        if s2 is not None:
            yield s2
        return
    if name == "call":
        if not args:
            raise EvalError("call<f, args..> = out")
        f = walk(lift(args[0], ren), s)
        if not (isinstance(f, tuple) and f[0] == "reldef"):
            raise EvalError(
                f"call: first arg must reify to a reldef, got "
                f"{term_str(f)}")
        yield from _rel_call(f[1], args[1:], out, env, s, fuel,
                             ren)
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


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

def _env(graph: dict) -> dict:
    return {"rels": {r["name"]: r for r in graph["rels"]}}


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
    A = lambda v, b=8: ("atom", b, v)
    P, S = t_pair, t_sym

    def L(*xs):
        o = NIL
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
        ("norm", [("goalterm", "append", [L(A(9)), NIL])]),
        ("assoc", [S("b"), L(P(S("a"), A(10)), P(S("b"), A(20)))]),
        ("assoc_id", [A(7), L(P(A(7), S("first")),
                              P(A(7), S("second")))]),
    ]
    for rel, args in queries:
        _reset_fresh()
        a = run_value(cg, rel, args, n=1)
        rel_eval._reset_fresh()
        b = rel_eval.run_value(og, rel, args, n=1)
        assert a == b, (rel, a, b)
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
    assert ours == theirs, (ours, theirs)
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
    assert ours == theirs, (ours, theirs)
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
        env = eList(t_pair(S("append"), appendDef))
        ewant = ePair(eAtom(8, 1), ePair(eAtom(8, 2), NILe))
        goal = t_pair(S("call"), t_pair(
            eSym("append"),
            t_pair(eList(eVar(90), eVar(91)), ewant)))
        _reset_fresh()
        sols = run_value(eg, "eval", [env, goal, NIL,
                                      t_atom(8, 1)], n=3)
        splits = []
        for sp in sols:
            s2 = sp[1]
            rx = run_value(eg, "reify", [eVar(90), s2], n=1)[0]
            ry = run_value(eg, "reify", [eVar(91), s2], n=1)[0]
            splits.append((dec(rx), dec(ry)))
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
        env2 = eList(t_pair(S("append_1"), rd),
                     t_pair(S("append"), appendDef))
        goal = t_pair(S("call"), t_pair(
            eSym("append_1"),
            t_pair(eList(ePair(eAtom(8, 1), NILe),
                         ePair(eAtom(8, 2), NILe)), eVar(97))))
        _reset_fresh()
        rs = run_value(sg, "eval", [env2, goal, NIL,
                                    t_atom(8, 1)], n=1)
        assert len(rs) == 1
        rout = run_value(sg, "reify", [eVar(97), rs[0][1]], n=1)[0]
        env1 = eList(t_pair(S("append"), appendDef))
        goal = t_pair(S("call"), t_pair(
            eSym("append"),
            t_pair(eList(ePair(eAtom(8, 1), NILe),
                         ePair(eAtom(8, 2), NILe)), eVar(98))))
        _reset_fresh()
        oos = run_value(sg, "eval", [env1, goal, NIL,
                                     t_atom(8, 1)], n=1)
        oout = run_value(sg, "reify", [eVar(98), oos[0][1]], n=1)[0]
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
                eList(t_pair(S("mark"), markDef(tag))),
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
        s1s2 = dec(o1[0])
        _reset_fresh()
        o2 = run_value(rg, "realize", [mkSpec(
            eList(S("m2"), S("m1")))], n=1)
        s2s1 = dec(o2[0])
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
        img = eT("img", eList(t_pair(S("id"), iddef)), S("id"))
        r = run_value(dg, "runtime", [img, NIL, eAtom(8, 42)], n=1)
        assert r == [eAtom(8, 42)], r
        caps = eList(t_pair(S("loader"), S("fasm")))
        assert run_value(dg, "runtime", [img, caps, eAtom(8, 42)],
                         n=1) == []
        docr = "catalog+spec+runtime+map, refusals hold"
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
          f"docs [{docr}]: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
