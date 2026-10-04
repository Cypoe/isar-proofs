#!/usr/bin/env python3
"""dialect — the routing bridge: every stage file projected
through the toolchain, as JSON.

The editor (and any other downstream consumer) never parses a
dialect itself — it asks the toolchain.  One truth, one grammar,
no forked semantics:

    python host/dialect.py --list
    python host/dialect.py --file X --as phi.rel
    python host/dialect.py --file X --as auto     # by extension
    python host/dialect.py --file X --as eval --call append \
        --args '[{"atom":[8,1]}]'

Projections (dialect names):

  phi.rel      .phi source -> rel-graph (phi_rel.parse_rel)
  rel-graph    a parsed rel-graph document (JSON in, rel-graph out)
  schema       admissibility verdict {admissible | refused, why}
  eval         RUN a rel: --call NAME --args '[<term nodes>]' → outs
  bundle       .plex archive -> section inventory + REALIZATION rows
  spec         a spec/toolchain json -> status card
  dialects     the toolchain dialect inventory
  file         raw summary (bytes, ext, detected dialect)

Output contract: {"dialect": d, "ok": true|false,
                  "data": {...} | "error": "..."}
"""

from __future__ import annotations

import json
import os
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

import plex_bundle  # noqa: E402


def _out(dialect: str, ok: bool, data=None, error=None) -> int:
    doc = {"dialect": dialect, "ok": ok}
    if ok:
        doc["data"] = data
    else:
        doc["error"] = error
    json.dump(doc, sys.stdout, indent=1, ensure_ascii=False)
    sys.stdout.write("\n")
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# projections
# ---------------------------------------------------------------------------

def p_phi_rel(path: str) -> dict:
    import phi_rel
    g = phi_rel.parse_rel(open(path, encoding="utf-8").read())
    return {"graph": g, "rels": [r["name"] for r in g["rels"]]}


def p_rel_graph(path: str) -> dict:
    g = json.load(open(path, encoding="utf-8"))
    if g.get("format") != "phi.rel/1":
        raise ValueError(
            f"not a phi.rel/1 graph (format={g.get('format')!r})")
    return {"graph": g, "rels": [r["name"] for r in g["rels"]]}


def p_schema(path: str) -> dict:
    """Admissibility of whatever --file points at: parse .phi (or
    read a rel-graph json) then rel_schema.check.  Refusals are
    data — the violated invariant, named."""
    import phi_rel
    import rel_schema
    if path.endswith(".json"):
        g = json.load(open(path, encoding="utf-8"))
    else:
        g = phi_rel.parse_rel(open(path, encoding="utf-8").read())
    try:
        rel_schema.check(g)
        return {"admissible": True, "rels": len(g["rels"])}
    except rel_schema.SchemaRefusal as e:
        return {"admissible": False, "refused": str(e),
                "rels": len(g["rels"])}


def p_eval(path: str, call: str, args_json: str,
           nlim: int = 1) -> dict:
    """Bounded RUN through rel_eval — args are rel-graph term
    nodes (the same JSON the parser emits), lifted through lift."""
    import phi_rel
    import rel_eval
    g = phi_rel.parse_rel(open(path, encoding="utf-8").read())
    arg_nodes = json.loads(args_json or "[]")
    rel_eval._reset_fresh()
    ren: dict = {}
    terms = [rel_eval.lift(n, ren) for n in arg_nodes]
    # committed read — n>1 on a single-solution rel searches
    # forever (honest divergence); callers wanting the stream
    # pass --n explicitly
    outs = rel_eval.run_value(g, call, terms, n=max(1, nlim))
    return {"call": call, "outs": [rel_eval.term_str(o)
                                   for o in outs],
            "n": len(outs)}


def p_bundle(path: str) -> dict:
    b = plex_bundle.read_bundle(open(path, "rb").read())
    names = getattr(plex_bundle, "_KIND_NAMES", {})
    secs = []
    for s in b.sections:
        secs.append({"kind": names.get(s.kind, f"kind{s.kind}"),
                     "type": s.type, "arity": s.arity,
                     "length": s.length, "rows": s.rows})
    real = {}
    try:
        real = b.kv_rows(plex_bundle.KIND_REALIZATION)
    except Exception:
        pass
    return {"sections": secs, "realization": real,
            "bytes": os.path.getsize(path)}


def p_spec(path: str) -> dict:
    d = json.load(open(path, encoding="utf-8"))
    return {k: d.get(k) for k in
            ("name", "layer", "in", "out", "axis", "status",
             "impl", "refuses") if k in d}


def p_dialects(_path: str) -> dict:
    tc = json.load(open(os.path.join(_HOST, "toolchain.json")))
    return {"dialects": tc.get("dialects", {}),
            "selftests": len(tc.get("selftests", []))}


def p_file(path: str) -> dict:
    return {"bytes": os.path.getsize(path),
            "ext": os.path.splitext(path)[1],
            "dialect": _detect(path)}


# ---------------------------------------------------------------------------
# routing
# ---------------------------------------------------------------------------

def _detect(path: str) -> str:
    base = os.path.basename(path)
    ext = os.path.splitext(path)[1].lower()
    if ext == ".phi":
        return "phi.rel"
    if ext == ".plex":
        return "bundle"
    if base == "toolchain.json":
        return "spec"
    if ext == ".json":
        try:
            d = json.load(open(path, encoding="utf-8"))
        except Exception:
            return "file"
        if d.get("format") == "phi.rel/1":
            return "rel-graph"
        if "layer" in d and "axis" in d:
            return "spec"
    return "file"


PROJECTIONS = {
    "phi.rel": lambda p, **_kw: p_phi_rel(p),
    "rel-graph": lambda p, **_kw: p_rel_graph(p),
    "schema": lambda p, **_kw: p_schema(p),
    "eval": lambda p, call=None, args="[]", nlim=1, **_kw:
        p_eval(p, call, args, nlim),
    "bundle": lambda p, **_kw: p_bundle(p),
    "spec": lambda p, **_kw: p_spec(p),
    "dialects": lambda p=None, **_kw: p_dialects(p),
    "file": lambda p, **_kw: p_file(p),
}

# which projections a detected file can take (the switchable set)
VIEWS = {
    "phi.rel": ["phi.rel", "schema", "eval", "file"],
    "rel-graph": ["rel-graph", "schema", "file"],
    "bundle": ["bundle", "file"],
    "spec": ["spec", "file"],
    "file": ["file"],
}


# ---------------------------------------------------------------------------
# selftest — every projection through the PROJECTIONS dispatch, the
# same code path the editor bridge shells out to.
# ---------------------------------------------------------------------------

def _selftest() -> int:
    import tempfile
    cor = os.path.join(_HOST, "corpus", "stdlib.phi")

    d = PROJECTIONS["phi.rel"](cor)
    assert d["graph"]["format"] == "phi.rel/1"
    assert len(d["rels"]) == 27 and "append" in d["rels"]

    d = PROJECTIONS["schema"](cor)
    assert d["admissible"] and d["rels"] == 27

    d = PROJECTIONS["eval"](cor, call="add",
                          args='[{"atom":[8,2]},{"atom":[8,3]}]')
    assert d["outs"] == ["ATOM(8,5)"]

    # bundle projection on a fresh .plex round-trip
    import phi_rel
    with tempfile.TemporaryDirectory() as td:
        bp = os.path.join(td, "g.plex")
        open(bp, "wb").write(phi_rel.graph_bundle(
            phi_rel.parse_rel(open(cor, encoding="utf-8").read())))
        d = PROJECTIONS["bundle"](bp)
        kinds = [s["kind"] for s in d["sections"]]
        assert kinds == ["STRINGS", "REALIZATION", "BYTES"], kinds
        assert d["realization"]["dialect"] == "phi.rel/1"
        assert _detect(bp) == "bundle"

    sp = os.path.join(_HOST, "specs", "surface-phi.rel.json")
    d = PROJECTIONS["spec"](sp)
    assert d["name"] == "phi.rel" and d["status"] == "declared"
    assert _detect(sp) == "spec"

    d = PROJECTIONS["dialects"](None)
    assert "phi.rel" in d["dialects"]

    # refusals surface as data, not crashes: a forged rel-graph
    # with an unbound call must be refused by the schema projection
    with tempfile.TemporaryDirectory() as td:
        bad = {"format": "phi.rel/1", "rels": [
            {"name": "x", "dir": "->", "in": [{"var": "a"}],
             "out": [{"var": "a"}], "shape": None,
             "clauses": [{"guard": None, "fresh": None, "goals": [
                 {"call": {"rel": "ghost", "args": [{"var": "a"}],
                           "out": {"var": "a"}}}]}]}]}
        bp = os.path.join(td, "bad.json")
        json.dump(bad, open(bp, "w"))
        d = PROJECTIONS["schema"](bp)
        assert not d["admissible"] and "ghost" in d["refused"], d

    print("dialect selftest: projections "
          f"{sorted(PROJECTIONS)} - pass")
    return 0


def main() -> int:
    file = None
    dialect = "auto"
    call = None
    args = "[]"
    nlim = 1
    i = 1
    while i < len(sys.argv):
        a = sys.argv[i]
        if a == "--list":
            return _out("dialects", True, {
                "projections": sorted(PROJECTIONS),
                "detect": sorted(VIEWS)})
        if a == "--file":
            file = sys.argv[i + 1]
            i += 2
            continue
        if a == "--as":
            dialect = sys.argv[i + 1]
            i += 2
            continue
        if a == "--call":
            call = sys.argv[i + 1]
            i += 2
            continue
        if a == "--args":
            args = sys.argv[i + 1]
            i += 2
            continue
        if a == "--n":
            nlim = int(sys.argv[i + 1])
            i += 2
            continue
        return _out(dialect, False, error=f"dialect: bad arg {a!r}")
    if dialect == "auto" and file is None:
        return _selftest()
    try:
        if dialect == "auto":
            d = _detect(file)
            views = VIEWS.get(d, ["file"])
            data = PROJECTIONS[d](file, call=call, args=args,
                                  nlim=nlim)
            data["views"] = views
            return _out(d, True, data)
        if dialect not in PROJECTIONS:
            return _out(dialect, False,
                        error=f"dialect: unknown {dialect!r} — "
                              f"choose from {sorted(PROJECTIONS)}")
        return _out(dialect, True,
                    PROJECTIONS[dialect](file, call=call, args=args,
                                         nlim=nlim))
    except Exception as e:
        return _out(dialect, False,
                    error=f"{type(e).__name__}: {e}")


if __name__ == "__main__":
    sys.exit(main())
