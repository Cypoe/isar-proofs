"""
phi_rel — surface/phi.rel: the relational surface parser.

bytes -> rel-graph ("phi.rel/1"), the 13th contract file
(host/specs/surface-phi.rel.json).  Grammar is the patent
phi-lang verbatim (isa-physics patent/phi-lang/*.phi):

    name : <a: T[8], b> <-> <r> where { | guard { goals } }
    name : <pat> <-> <pat>                     (direct extension)
    name : <a> -> <r> where { ... }            (directed mode)
    name : <a> <=> <r> where { ... }           (contraction)

Clauses are relation EXTENSIONS (guarded union of alternatives),
not function bodies.  Sig slots are term patterns (PAIR(h, _) is
legal in a sig).  `| guard { body }`, `| fresh (v..) { body }`,
`when c & c { body }` and a bare where-body are all clause forms.
`shape self|pairwise|step|reduce` may be declared after the out-sig
(the lowering contract, data not syntax — see surface spec).

Goals: term = term unification, term cmp term guards, rel<a> = out
calls, builtin(a..) = out kernel ops ({UNIFY,MATCH,APPLY,CHOICE,
RUN,FRESH}, env_lookup, call), nested fresh-blocks, `! term` emit.

The rel-graph is declared data: JSON-serializable, persists through
plex_bundle sections (REALIZATION dialect=phi.rel/1 + BYTES blob).
Evaluation (rel_eval) and admissible-construction checks
(rel_schema) consume the graph — the parser only builds it.
"""
from __future__ import annotations

import json
import os
import re
import sys
from typing import List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

import plex_bundle as pb  # noqa: E402

FORMAT = "phi.rel/1"

# ---------------------------------------------------------------------------
# rel-graph node helpers (plain JSON shapes)
# ---------------------------------------------------------------------------

def var(name: str) -> dict:
    return {"var": name}


def atom(bits: int, value: int) -> dict:
    return {"atom": [bits, value]}


def atom_dyn(bits: dict, payload: dict) -> dict:
    """ATOM with non-const fields: bits/payload as {const:v} or
    {var_delta:[name, d]} (patent's ATOM(n, data) / ATOM(4, n+1))."""
    return {"atom_dyn": [bits, payload]}


def pair(a: dict, b: dict) -> dict:
    return {"pair": [a, b]}


NIL = atom(0, 0)
WILD = {"wild": True}

DIRS = ("<->", "<=>", "->")
CMPS = ("=", "!=", ">=", "<=", ">", "<")
SHAPES = ("self", "pairwise", "step", "reduce")


class RelError(ValueError):
    """Surface refuses: form outside the clause vocabulary."""


# ---------------------------------------------------------------------------
# tokenizer
# ---------------------------------------------------------------------------

_TOK = re.compile(r"""
    (?P<comment>;;[^\n]*)          |
    (?P<dir><->|<=>|->|>=|<=|!=)   |
    (?P<int>-?0x[0-9a-fA-F]+|-?\d+)  |
    (?P<punct>[<>{}()\[\]:|&,=!\+\-\*])  |
    (?P<ident>[A-Za-z_][A-Za-z0-9_'.?]*)  |
    (?P<ws>\s+)                    |
    (?P<bad>.)
""", re.X)


def tokenize(src: str) -> List[Tuple[str, str, int]]:
    out: List[Tuple[str, str, int]] = []
    for m in _TOK.finditer(src):
        kind = m.lastgroup
        if kind in ("comment", "ws"):
            continue
        if kind == "bad":
            line = src.count("\n", 0, m.start()) + 1
            raise RelError(
                f"phi.rel: unexpected character {m.group()!r} "
                f"at line {line}")
        out.append((kind, m.group(), src.count("\n", 0, m.start()) + 1))
    return out


class _P:
    def __init__(self, toks):
        self.toks, self.i = toks, 0

    def peek(self) -> Optional[Tuple[str, str, int]]:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self) -> Tuple[str, str, int]:
        t = self.peek()
        if t is None:
            raise RelError("phi.rel: unexpected end of input")
        self.i += 1
        return t

    def want(self, text: str) -> Tuple[str, str, int]:
        t = self.next()
        if t[1] != text:
            raise RelError(
                f"phi.rel: expected {text!r}, got {t[1]!r} "
                f"at line {t[2]}")
        return t

    def at(self, text: str) -> bool:
        t = self.peek()
        return t is not None and t[1] == text


# ---------------------------------------------------------------------------
# terms
# ---------------------------------------------------------------------------

def _to_int(s: str) -> int:
    if s.lstrip("-").startswith("0x"):
        return int(s, 16)
    return int(s)


def _aexpr(p: _P) -> dict:
    """ATOM payload: int | var | var±int (patent's n+1 idiom)."""
    t = p.next()
    if t[0] == "int":
        return {"const": _to_int(t[1])}
    if t[0] == "ident":
        name = t[1]
        nx = p.peek()
        if nx is not None and nx[0] == "int" and nx[1].startswith("-"):
            # n-1 lexes as ident + int(-1) — the unspaced delta idiom
            return {"var_delta": [name, _to_int(p.next()[1])]}
        if p.at("+") or p.at("-"):
            sign = 1 if p.next()[1] == "+" else -1
            n = p.next()
            if n[0] != "int":
                raise RelError(
                    f"phi.rel: atom expr {name}±{n[1]!r} — "
                    f"expected int")
            return {"var_delta": [name, sign * _to_int(n[1])]}
        return {"var_delta": [name, 0]}
    raise RelError(f"phi.rel: bad ATOM payload {t[1]!r} "
                   f"at line {t[2]}")


def _term(p: _P) -> dict:
    t = p.next()
    kind, txt = t[0], t[1]
    if kind == "int":
        return atom(8, _to_int(txt))      # bare int -> T[8] scalar
    if txt == "[":
        items = []
        if not p.at("]"):
            items.append(_term(p))
            while p.at(","):
                p.next()
                items.append(_term(p))
        p.want("]")
        out = NIL
        for it in reversed(items):
            out = pair(it, out)
        return out
    if txt == "_":
        return dict(WILD)
    if kind == "ident":
        if txt == "ATOM":
            p.want("(")
            be = _aexpr(p)
            p.want(",")
            e = _aexpr(p)
            p.want(")")
            if "const" in be and "const" in e:
                return atom(be["const"], e["const"])
            return {"atom_dyn": [be, e]}
        if txt == "PAIR":
            p.want("(")
            a = _term(p)
            p.want(",")
            b = _term(p)
            p.want(")")
            return pair(a, b)
        if p.at("("):
            # compound op-term: APPLY(MATCH(rule, t), rule.body)
            args = _fn_args(p)
            return {"op": [txt, args]}
        if p.at("<"):
            # call-term: norm<call<code, input>>
            args = _call_args(p)
            return {"call_term": [txt, args]}
        return var(txt)


def _sig(p: _P) -> List[dict]:
    """< term [: TYPE] , ... > — sig slots are patterns."""
    p.want("<")
    out = []
    if p.at(">"):
        p.next()
        return out
    while True:
        t = _term(p)
        if isinstance(t, dict) and t.get("var", "").startswith("T") \
                and p.at("["):
            # bare type slot: <T[8]> — output declares its shape
            p.next()
            parts = []
            while not p.at("]"):
                parts.append(p.next()[1])
            p.want("]")
            out.append({"type": f"{t['var']}[{''.join(parts)}]"})
        else:
            if p.at(":"):
                p.next()
                ty = p.next()
                if ty[0] != "ident" or not ty[1].startswith("T"):
                    raise RelError(
                        f"phi.rel: bad type annotation {ty[1]!r}")
                p.want("[")
                depth = 1
                parts = []
                while depth:
                    x = p.next()
                    if x[1] == "[":
                        depth += 1
                    elif x[1] == "]":
                        depth -= 1
                        if depth == 0:
                            break
                    parts.append(x[1])
                t = {"typed": [t, f"T[{''.join(parts)}]"]}
            out.append(t)
        if p.at(","):
            p.next()
            continue
        break
    p.want(">")
    return out


# ---------------------------------------------------------------------------
# goals / clauses
# ---------------------------------------------------------------------------

def _call_args(p: _P) -> List[dict]:
    p.want("<")
    xs = [_term(p)]
    while p.at(","):
        p.next()
        xs.append(_term(p))
    p.want(">")
    return xs


def _fn_args(p: _P) -> List[dict]:
    p.want("(")
    xs = []
    if not p.at(")"):
        xs.append(_term(p))
        while p.at(","):
            p.next()
            xs.append(_term(p))
    p.want(")")
    return xs


def _eq_or_cmp(p: _P) -> dict:
    a = _term(p)
    op = p.next()
    if op[1] not in CMPS:
        raise RelError(
            f"phi.rel: expected = or comparison, got {op[1]!r} "
            f"at line {op[2]}")
    b = _term(p)
    if op[1] == "=":
        return {"unify": [a, b]}
    return {"cmp": [op[1], a, b]}


def _goal(p: _P) -> dict:
    t = p.peek()
    if t is None:
        raise RelError("phi.rel: unexpected end in goal")
    if t[1] == "fresh":
        p.next()
        names = _names(p)
        p.want("{")
        gs = _goals(p)
        return {"fresh": {"vars": names, "goals": gs}}
    if t[1] == "!":
        p.next()
        return {"emit": _term(p)}
    if t[0] == "ident" and t[1].isupper() \
            and (p.toks[p.i + 1:p.i + 2] or [None])[0] is not None \
            and p.toks[p.i + 1][1] not in ("(", "<", "=", "}", "|"):
        # bare kernel op: `UNIFY a b` — args on the same line, no
        # parens (patent's where-body idiom)
        name = p.next()[1]
        line = t[2]
        args = []
        while p.peek() is not None and p.peek()[2] == line \
                and p.peek()[1] != "=":
            args.append(_term(p))
        out = None
        if p.at("="):
            p.next()
            out = _term(p)
        if name == "UNIFY" and len(args) == 2 and out is None:
            return {"unify": args}
        return {"builtin": {"name": name, "args": args, "out": out}}
    if t[0] == "ident":
        nxt = p.toks[p.i + 1] if p.i + 1 < len(p.toks) else None
        if nxt and nxt[1] == "<":
            name = p.next()[1]
            args = _call_args(p)
            p.want("=")
            out = _term(p)
            return {"call": {"rel": name, "args": args, "out": out}}
        if nxt and nxt[1] == "(":
            name = p.next()[1]
            args = _fn_args(p)
            out = None
            if p.at("="):
                p.next()
                out = _term(p)
            if name == "RUN":
                if len(args) != 2 or out is None:
                    raise RelError(
                        "phi.rel: RUN(goal, n) = out expected")
                return {"run": {"goal": args[0], "n": args[1],
                                "out": out}}
            if name == "CHOICE":
                if len(args) != 2 or out is None:
                    raise RelError(
                        "phi.rel: CHOICE(g1, g2) = out expected")
                return {"choice": {"a": args[0], "b": args[1],
                                   "out": out}}
            if name == "UNIFY":
                if len(args) != 2 or out is not None:
                    raise RelError("phi.rel: UNIFY a b (no out)")
                return {"unify": args}
            return {"builtin": {"name": name, "args": args,
                                "out": out}}
    save = p.i
    try:
        return _eq_or_cmp(p)
    except RelError:
        # bare term in goal position = the clause's extension
        # (`when c { [] }` — emit shorthand, same as `! t`)
        p.i = save
        return {"emit": _term(p)}


def _names(p: _P) -> List[str]:
    p.want("(")
    out = []
    if not p.at(")"):
        t = p.next()
        if t[0] != "ident":
            raise RelError(f"phi.rel: fresh var name {t[1]!r}")
        out.append(t[1])
        while p.at(","):
            p.next()
            out.append(p.next()[1])
    p.want(")")
    return out


def _goals(p: _P) -> List[dict]:
    out = []
    while not p.at("}"):
        out.append(_goal(p))
    p.want("}")
    return out


def _eq_list(p: _P) -> List[dict]:
    out = [_eq_or_cmp(p)]
    while p.at("&"):
        p.next()
        out.append(_eq_or_cmp(p))
    return out


def _clause(p: _P) -> dict:
    """Clause alternatives: `| guard { g }`, `| fresh (v) { g }`,
    `when c & c { g }`, `fresh (v) { g }`, or a bare goal."""
    guard, fresh = None, None
    if p.at("|"):
        p.next()
        if p.at("when"):
            p.next()
            guard = _eq_list(p)
        elif p.at("fresh"):
            p.next()
            fresh = _names(p)
        else:
            save = p.i
            try:
                g = _eq_list(p)
            except RelError:
                p.i = save
            else:
                if p.at("{"):
                    guard = g
                else:
                    p.i = save            # it was a goal clause
        if p.at("{"):
            p.next()
            return {"guard": guard, "fresh": fresh,
                    "goals": _goals(p)}
        return {"guard": guard, "fresh": fresh,
                "goals": [_goal(p)]}
    if p.at("when"):
        p.next()
        guard = _eq_list(p)
    elif p.at("fresh"):
        p.next()
        fresh = _names(p)
    if guard is not None or fresh is not None:
        p.want("{")
        return {"guard": guard, "fresh": fresh,
                "goals": _goals(p)}
    # bare single-goal clause (no braces)
    return {"guard": None, "fresh": None, "goals": [_goal(p)]}


# ---------------------------------------------------------------------------
# rel declarations
# ---------------------------------------------------------------------------

def _rel(p: _P) -> dict:
    t = p.next()
    if t[0] != "ident":
        raise RelError(
            f"phi.rel: rel name expected, got {t[1]!r} "
            f"at line {t[2]}")
    name = t[1]
    p.want(":")
    ins = _sig(p)
    d = p.next()
    if d[1] not in DIRS:
        raise RelError(
            f"phi.rel: direction expected (<-> | <=> | ->), "
            f"got {d[1]!r} at line {d[2]}")
    outs = _sig(p)
    shape = None
    if p.at("shape"):
        p.next()
        s = p.next()
        if s[1] not in SHAPES:
            raise RelError(
                f"phi.rel: shape {s[1]!r} not in {SHAPES}")
        shape = s[1]
    clauses = None
    if p.at("where"):
        p.next()
        if p.at("{"):
            p.next()
            clauses = []
            in_bare = False
            while not p.at("}"):
                if p.at("|") or p.at("when") or p.at("fresh"):
                    clauses.append(_clause(p))
                    in_bare = False
                else:
                    # a run of bare goals is ONE conjunctive clause
                    # (patent `call`: env_lookup; MATCH; APPLY —
                    # sequence, not alternatives)
                    if not in_bare:
                        clauses.append({"guard": None, "fresh": None,
                                        "goals": []})
                        in_bare = True
                    clauses[-1]["goals"].append(_goal(p))
            p.want("}")
        else:
            # `where UNIFY a b` — bare goal list, one clause
            clauses = [{"guard": None, "fresh": None,
                        "goals": [_goal(p)]}]
    return {"name": name, "dir": d[1],
            "in": ins, "out": outs, "shape": shape,
            "clauses": clauses}


def parse_rel(src: str) -> dict:
    """surface bytes -> phi.rel/1 rel-graph."""
    if isinstance(src, bytes):
        src = src.decode("utf-8")
    p = _P(tokenize(src))
    rels = []
    while p.peek() is not None:
        rels.append(_rel(p))
    return {"format": FORMAT, "rels": rels}


# ---------------------------------------------------------------------------
# bundle persistence — the rel-graph is a storable artifact
# ---------------------------------------------------------------------------

def graph_bundle(graph: dict) -> bytes:
    """phi.rel/1 rel-graph -> .plex archive (STRINGS + REALIZATION
    + the JSON graph as BYTES)."""
    if graph.get("format") != FORMAT:
        raise RelError(
            f"rel-graph format {graph.get('format')!r} — "
            f"need {FORMAT}")
    import struct
    pool = pb._Pool()
    secs = [pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0, b"")]
    real = {"dialect": FORMAT,
            "rels": str(len(graph.get("rels", [])))}
    rrows = [pool.ref(str(k)) + pool.ref(str(v))
             for k, v in sorted(real.items())]
    secs.append(pb.Section(
        pb.KIND_REALIZATION, pb.U64, 4, len(rrows),
        b"".join(struct.pack(f"<{len(r)}Q", *r) for r in rrows)))
    blob = json.dumps(graph, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")
    secs.append(pb.Section(pb.KIND_BYTES, pb.U8, 1, 0, blob))
    secs[-1].rows = secs[-1].length
    secs[0] = pb.Section(pb.KIND_STRINGS, pb.U8, 1, 0,
                         bytes(pool.buf))
    secs[0].rows = secs[0].length
    return pb.pack_bundle(secs)


def read_graph_bundle(data: bytes) -> dict:
    b = pb.read_bundle(data)
    real = b.kv_rows(pb.KIND_REALIZATION)
    if real.get("dialect") != FORMAT:
        raise RelError(
            f"rel bundle dialect {real.get('dialect')!r} — "
            f"need {FORMAT}")
    blob = b.bytes_pool()
    if not blob:
        raise RelError("rel bundle: no rel-graph blob")
    return json.loads(blob)


# ---------------------------------------------------------------------------
# selftest
# ---------------------------------------------------------------------------

_CORPUS = """\
;; parsed from the patent corpus verbatim shapes
equal : <a, b> <-> <a> where UNIFY a b

cons  : <car, cdr> <-> <PAIR(car, cdr)>
head  : <PAIR(h, _)> <-> <h>
empty : <ATOM(0,0)> <-> <[]>

norm : <goal> <-> <result> where {
  RUN(goal, 1) = PAIR(result, _)
}

find : <goal, n> <-> <results> where {
  RUN(goal, n) = results
}

any : <g1, g2> <-> <result> where {
  CHOICE(g1, g2) = result
}

succ  : <n: T[8]> <-> <ATOM(8, n+1)>
pred  : <n: T[8]> <-> <ATOM(8, n-1)>

;; relational add via succ/pred chain — carry chains are a later
;; lowering (nibble_add is called-but-undefined in the patent corpus;
;; the schema refuses it there.  Complete edges or no rel.)
add : <a: T[8], b: T[8]> <=> <sum: T[8]> shape self where {
  | b = ATOM(8,0) { sum = a }
  | fresh (b1, s1) {
      pred<b> = b1
      add<a, b1> = s1
      succ<s1> = sum
    }
}

append : <xs, ys> <-> <zs> shape self where {
  | xs = [] { zs = ys }
  | fresh (h, t, r) {
      cons<h,t> = xs
      append<t, ys> = r
      cons<h,r> = zs
    }
}

fib : <n: T[8]> <-> <r: T[8]> shape pairwise where {
  | n = ATOM(8,0) { r = ATOM(8,0) }
  | n = ATOM(8,1) { r = ATOM(8,1) }
  | fresh (n1, n2, r1, r2) {
      pred<n> = n1
      pred<n1> = n2
      fib<n1> = r1
      fib<n2> = r2
      add<r1, r2> = r
    }
}
"""


def main() -> int:
    g = parse_rel(_CORPUS)
    names = [r["name"] for r in g["rels"]]
    assert len(names) == 12, names
    app = [r for r in g["rels"] if r["name"] == "append"][0]
    assert app["dir"] == "<->" and len(app["clauses"]) == 2
    assert app["clauses"][1]["fresh"] == ["h", "t", "r"]
    assert app["clauses"][1]["goals"][1]["call"]["rel"] == "append"
    fib = [r for r in g["rels"] if r["name"] == "fib"][0]
    assert fib["shape"] == "pairwise"
    add = [r for r in g["rels"] if r["name"] == "add"][0]
    assert add["dir"] == "<=>"
    succ = [r for r in g["rels"] if r["name"] == "succ"][0]
    assert succ["in"][0] == {"typed": [{"var": "n"}, "T[8]"]}
    assert succ["out"][0] == {"atom_dyn": [{"const": 8},
                                          {"var_delta": ["n", 1]}]}
    pred = [r for r in g["rels"] if r["name"] == "pred"][0]
    assert pred["out"][0] == {"atom_dyn": [{"const": 8},
                                          {"var_delta": ["n", -1]}]}
    add = [r for r in g["rels"] if r["name"] == "add"][0]
    assert add["dir"] == "<=>" and add["shape"] == "self"
    # refusals
    for bad, frag in (("fib : <n> <-> <r> where { | n = ATOM(8,0) "
                       "{ r = ATOM(8,0) }", None),
                      ("x : <a> |> <b>", "direction expected"),
                      ("y : <a> <-> <b> where { RUN(g) = o }",
                       "RUN(goal, n) = out"),):
        try:
            parse_rel(bad)
        except RelError as e:
            assert frag is None or frag in str(e), (frag, e)
        else:
            if frag is not None:
                raise AssertionError(f"no refusal: {bad!r}")
    # bundle round-trip
    data = graph_bundle(g)
    g2 = read_graph_bundle(data)
    assert g2 == g, "rel-graph bundle round-trip drifted"
    print(f"phi_rel selftest: {len(names)} rels parsed, "
          f"bundle {len(data)}B round-trips: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
