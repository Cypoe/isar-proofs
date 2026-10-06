#!/usr/bin/env python3
"""dialect — the routing bridge: every stage file projected
through the toolchain, as JSON.

The .plex bundle is the document of record; surface text (.phi)
is a derived, regenerable view.  The editor (and any other
downstream consumer) never parses a dialect itself — it asks the
toolchain.  One truth, one grammar, no forked semantics:

    python host/dialect.py --list
    python host/dialect.py --file X --as phi.rel    # .phi|.plex -> view
    python host/dialect.py --file X --as auto       # detect + views
    python host/dialect.py --file X --as eval --call append \
        --args '[{"atom":[8,1]}]'
    python host/dialect.py --file X.rel.plex --set phi.rel < surf.phi
    python host/dialect.py                          # selftest

This module is also the shape of the eventual emitted interpreter —
the program that opens a .plex, projects a view, accepts edits,
and rebundles.  Today the legs run on the Python host; when cogen
lands this dispatch table is what gets specialized and emitted —
the interpreter is the intermediary, not a separate tool.

Projections (dialect names):

  phi.rel      rel-graph -> surface text (+graph) — derived view
  rel-graph    the graph itself (from .phi, graph-json, or .plex)
  schema       admissibility verdict {admissible | refused, why}
  eval         RUN a rel: --call NAME --args '[<term nodes>]' → outs
  bundle       .plex archive -> section inventory + REALIZATION rows
  spec         a spec/toolchain json -> status card
  dialects     the toolchain dialect inventory
  file         raw summary (bytes, ext, detected dialect)

Write verbs (--set):

  phi.rel      stdin surface -> parse -> schema -> graph_bundle ->
               atomic replace of --file (.plex only).  Refusals
               leave the bundle untouched.

Output contract: {"dialect": d, "ok": true|false,
                  "data": {...} | "error": "..."}
"""

from __future__ import annotations

import json
import os
import re
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

def _graph_of(path: str) -> dict:
    """The rel-graph behind --file, whatever container it lives in:
    .phi surface, phi.rel/1 graph-json, or a .plex rel-bundle.
    Anything else refuses — the bridge does not guess."""
    import phi_rel
    if path.endswith(".plex"):
        return phi_rel.read_graph_bundle(
            open(path, "rb").read())
    if path.endswith(".json"):
        g = json.load(open(path, encoding="utf-8"))
        if g.get("format") != phi_rel.FORMAT:
            raise ValueError(
                f"not a {phi_rel.FORMAT} graph "
                f"(format={g.get('format')!r})")
        return g
    return phi_rel.parse_rel(open(path, encoding="utf-8").read())


def p_phi_rel(path: str) -> dict:
    import phi_rel
    g = _graph_of(path)
    return {"graph": g, "rels": [r["name"] for r in g["rels"]],
            "surface": phi_rel.render_rel(g)}


def p_rel_graph(path: str) -> dict:
    g = _graph_of(path)
    return {"graph": g, "rels": [r["name"] for r in g["rels"]]}


def p_schema(path: str) -> dict:
    """Admissibility of whatever --file points at (.phi, graph-json,
    .plex rel-bundle) — rel_schema.check on the graph.  Refusals
    are data — the violated invariant, named."""
    import rel_schema
    g = _graph_of(path)
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
    import rel_eval
    g = _graph_of(path)
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
        try:
            b = plex_bundle.read_bundle(open(path, "rb").read())
            real = b.kv_rows(plex_bundle.KIND_REALIZATION)
            if real.get("dialect") == "phi.rel/1":
                return "rel-bundle"
        except Exception:
            pass
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


_USES_RE = re.compile(r"^[ \t]*;;[ \t]*uses:[ \t]*(.+)$", re.M)


def s_phi_rel(path: str, surface: str) -> dict:
    """Write verb: surface text -> parse -> schema -> bundle ->
    atomic replace of --file.  The .plex is canonical; a refused
    surface leaves it byte-identical.

    `;; uses: a, b/c` declares the file's dep closure — bundles
    resolved relative to --file's dir (.plex implied) and merged
    for the schema check; a dep's own `uses` are followed, so the
    effective closure is transitive and stays enumerable per-file.
    The canonical graph records `uses`; a dep rel never shadows a
    local name (local wins, dup stays declared)."""
    import phi_rel
    import rel_schema
    if not path.endswith(".plex"):
        raise ValueError(
            f"--set writes .plex bundles, not {path!r}")
    g = phi_rel.parse_rel(surface)           # RelError = refused
    if not g["rels"]:
        raise ValueError(
            "refusing to write an empty rel-graph — "
            "an empty surface would destroy the bundle")
    uses = [u.strip() for m in _USES_RE.finditer(surface)
            for u in m.group(1).split(",") if u.strip()]
    if uses:
        g["uses"] = uses
        merged = {"format": g["format"], "rels": list(g["rels"])}
        names = {r["name"] for r in merged["rels"]}
        # transitive closure: a dep's own `uses` are resolved
        # against ITS dir; local rels always win over dep rels
        work = [(os.path.dirname(path), u) for u in uses]
        seen = set()
        while work:
            base, u = work.pop(0)
            up = u if u.endswith(".plex") else u + ".plex"
            cand = os.path.normpath(os.path.join(base, up))
            if cand in seen:
                continue
            seen.add(cand)
            if not os.path.exists(cand):
                raise ValueError(
                    f"uses: dep {u!r} not found at {cand}")
            dg = phi_rel.read_graph_bundle(
                open(cand, "rb").read())
            for r in dg["rels"]:
                if r["name"] not in names:
                    names.add(r["name"])
                    merged["rels"].append(r)
            for u2 in dg.get("uses", []):
                work.append((os.path.dirname(cand), u2))
        rel_schema.check(merged)             # SchemaRefusal
    else:
        rel_schema.check(g)                  # SchemaRefusal = refused
    blob = phi_rel.graph_bundle(g)
    tmp = path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(blob)
    os.replace(tmp, path)
    return {"written": path, "bytes": len(blob),
            "rels": len(g["rels"])}


SETTERS = {
    "phi.rel": s_phi_rel,
}

# which projections a detected file can take (the switchable set)
VIEWS = {
    "phi.rel": ["phi.rel", "rel-graph", "schema", "eval", "file"],
    "rel-bundle": ["phi.rel", "rel-graph", "schema", "eval",
                   "bundle", "file"],
    "rel-graph": ["phi.rel", "rel-graph", "schema", "file"],
    "bundle": ["bundle", "file"],
    "spec": ["spec", "file"],
    "file": ["file"],
}

# which views are writable back to the document (the surface set)
WRITABLE = {"phi.rel"}


# ---------------------------------------------------------------------------
# selftest — every projection through the PROJECTIONS dispatch, the
# same code path the editor bridge shells out to.
# ---------------------------------------------------------------------------

def _selftest() -> int:
    import tempfile
    import phi_rel
    cor = os.path.join(_HOST, "corpus", "stdlib.phi")

    d = PROJECTIONS["phi.rel"](cor)
    assert d["graph"]["format"] == "phi.rel/1"
    assert len(d["rels"]) == 30 and "append" in d["rels"]
    # surface is a derived view — it re-parses to the same graph
    assert phi_rel.parse_rel(d["surface"]) == d["graph"]

    d = PROJECTIONS["schema"](cor)
    assert d["admissible"] and d["rels"] == 30

    d = PROJECTIONS["eval"](cor, call="add",
                          args='[{"atom":[8,2]},{"atom":[8,3]}]')
    assert d["outs"] == ["ATOM(8,5)"]

    # .plex rel-bundle: the canonical document — every view
    # projects through the bundle, not the surface file
    with tempfile.TemporaryDirectory() as td:
        bp = os.path.join(td, "g.plex")
        open(bp, "wb").write(phi_rel.graph_bundle(
            phi_rel.parse_rel(open(cor, encoding="utf-8").read())))
        assert _detect(bp) == "rel-bundle"
        d = PROJECTIONS["bundle"](bp)
        kinds = [s["kind"] for s in d["sections"]]
        assert kinds == ["STRINGS", "REALIZATION", "BYTES"], kinds
        assert d["realization"]["dialect"] == "phi.rel/1"
        assert PROJECTIONS["schema"](bp)["admissible"]
        d = PROJECTIONS["eval"](bp, call="add",
                              args='[{"atom":[8,1]},{"atom":[8,1]}]')
        assert d["outs"] == ["ATOM(8,2)"]
        # the surface view of the bundle re-parses to its graph
        d = PROJECTIONS["phi.rel"](bp)
        assert phi_rel.parse_rel(d["surface"]) == \
            phi_rel.read_graph_bundle(open(bp, "rb").read())

        # --set: the write path — parse -> schema -> bundle ->
        # atomic replace.  A refused surface leaves the bundle
        # byte-identical.
        before = open(bp, "rb").read()
        surf = phi_rel.render_rel(
            phi_rel.read_graph_bundle(before))
        d = SETTERS["phi.rel"](bp, surf)
        assert d["written"] == bp and d["rels"] == 30
        # graph_bundle is deterministic — an identical surface
        # rewrites identical bytes
        assert open(bp, "rb").read() == before
        bad_surf = surf + "\nx : <a> -> <a> where ghost<a> = a\n"
        try:
            SETTERS["phi.rel"](bp, bad_surf)
            raise AssertionError("unbound call accepted")
        except AssertionError:
            raise
        except Exception:
            pass
        assert open(bp, "rb").read() == before, \
            "bundle changed after refusal"

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
          f"{sorted(PROJECTIONS)}, setters {sorted(SETTERS)} - pass")
    return 0


def main() -> int:
    file = None
    dialect = "auto"
    setter = None
    call = None
    args = "[]"
    nlim = 1
    i = 1
    while i < len(sys.argv):
        a = sys.argv[i]
        if a == "--list":
            return _out("dialects", True, {
                "projections": sorted(PROJECTIONS),
                "setters": sorted(SETTERS),
                "detect": sorted(VIEWS)})
        if a == "--set":
            setter = sys.argv[i + 1]
            i += 2
            continue
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
    if dialect == "auto" and file is None and setter is None:
        return _selftest()
    try:
        if setter is not None:
            if file is None:
                return _out(setter, False,
                            error="dialect: --set needs --file")
            if setter not in SETTERS:
                return _out(setter, False,
                            error=f"dialect: {setter!r} is not "
                                  f"writable — choose from "
                                  f"{sorted(SETTERS)}")
            surface = sys.stdin.read()
            return _out(setter, True,
                        SETTERS[setter](file, surface))
        if dialect == "auto":
            d = _detect(file)
            views = VIEWS.get(d, ["file"])
            primary = "phi.rel" if d == "rel-bundle" else d
            data = PROJECTIONS[primary](file, call=call, args=args,
                                        nlim=nlim)
            data["views"] = views
            data["writable"] = sorted(
                v for v in views if v in WRITABLE)
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
