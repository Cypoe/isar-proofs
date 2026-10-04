#!/usr/bin/env python3
"""rel_schema — admissible construction for phi.rel/1 rel-graphs.

The static half of the IDCC contract:

    semantic relation → admissible construction → runtime capability

`check(rel_graph)` is the phantom stage: a rel-graph that fails never
reaches the evaluator.  Refusals name the violated invariant — the same
"refuse the dishonest lowering" discipline as the emit path.

Checks (each a named refusal):

  direction   dir ∈ {<->, <=>, ->};  sig out is a single term
  arity       rel<args> = out: len(args) == len(callee.in); callee bound
  builtin     builtin name in registry; arity matches
  grounding   every var declared (sig/fresh) or bound by an earlier
              binding occurrence (unify operand / call out / run out /
              choice out / builtin out);  guard vars are sig vars only
  mode        calling a `->` or `<=>` rel requires args already bound
              (grounded) at that point in the clause
  recursion   any rel on a call cycle must declare
              shape ∈ {self, pairwise, step, reduce}
  emit        emit-term vars bound/declared
  run         RUN(g, n): n is an atom literal or a bound var

The per-rel SCHEMAS rows are the declared program-schema format —
{relation, domain, invariant, target_class, refusal} — the
"semantic relation → admissible construction → runtime-observable
capability" shape as data (spec: host/specs/schema-rel.json).
"""

import sys
from typing import Dict, Set

import phi_rel

SHAPES = ("self", "pairwise", "step", "reduce")
DIRS = ("<->", "<=>", "->")

# builtin name -> arity (None = variadic ≥1)
BUILTIN_ARITY = {
    "FRESH": 0,
    "PAIR": 2,
    "MATCH": 2,
    "APPLY": 2,
    "env_lookup": 1,
    "call": None,
}

# kernel ops usable as compound terms (APPLY(MATCH(..), ..) in sigs)
OP_ARITY = {"FRESH": 0, "UNIFY": 2, "MATCH": 2, "APPLY": 2,
            "CHOICE": 2, "RUN": 2, "PAIR": 2}


class SchemaRefusal(Exception):
    """The violated invariant is the message."""


# ---------------------------------------------------------------------------
# term walking
# ---------------------------------------------------------------------------

def term_vars(t) -> Set[str]:
    """All var names occurring anywhere in a term node."""
    out = set()
    if isinstance(t, dict):
        if "var" in t:
            out.add(t["var"])
        for v in t.values():
            if isinstance(v, (dict, list)):
                out |= term_vars(v)
    elif isinstance(t, list):
        for v in t:
            out |= term_vars(v)
    return out


def _root(v: str) -> str:
    """def.pat is a projection of def — grounding compares roots."""
    return v.split(".", 1)[0]


def term_roots(t) -> Set[str]:
    return {_root(v) for v in term_vars(t)}


def _check_term(t, where: str):
    """Structural sanity on a term node — malformed nodes refuse."""
    if not isinstance(t, dict) or len(t) != 1:
        raise SchemaRefusal(
            f"{where}: term node must be a single-key map, got {t!r}")
    k, v = next(iter(t.items()))
    if k == "var":
        if not isinstance(v, str):
            raise SchemaRefusal(f"{where}: var name not a string: {v!r}")
    elif k == "atom":
        if not (isinstance(v, list) and len(v) == 2
                and all(isinstance(x, int) for x in v)):
            raise SchemaRefusal(f"{where}: atom wants [bits, val] ints")
    elif k in ("pair", "unify"):
        if not (isinstance(v, list) and len(v) == 2):
            raise SchemaRefusal(f"{where}: {k} wants 2 subterms")
        _check_term(v[0], where)
        _check_term(v[1], where)
    elif k == "atom_dyn":
        _check_term(v[0], where)
        _check_term(v[1], where)
    elif k == "var_delta":
        if not (isinstance(v, list) and len(v) == 2
                and isinstance(v[0], str) and isinstance(v[1], int)):
            raise SchemaRefusal(
                f"{where}: var_delta wants [name, int], got {v!r}")
    elif k == "const":
        if not isinstance(v, int):
            raise SchemaRefusal(f"{where}: const not int: {v!r}")
    elif k == "wild":
        if v is not True:
            raise SchemaRefusal(f"{where}: wild wants true")
    elif k == "typed":
        if not (isinstance(v, list) and len(v) == 2
                and isinstance(v[1], str)):
            raise SchemaRefusal(f"{where}: typed wants [term, T]")
        _check_term(v[0], where)
    elif k == "type":
        if not isinstance(v, str):
            raise SchemaRefusal(f"{where}: type wants T[n] string")
    elif k == "call_term":
        if not (isinstance(v, list) and len(v) == 2
                and isinstance(v[0], str) and isinstance(v[1], list)):
            raise SchemaRefusal(
                f"{where}: call_term wants [name, args]")
        for a in v[1]:
            _check_term(a, where)
    elif k == "op":
        if not (isinstance(v, list) and len(v) == 2
                and isinstance(v[0], str) and isinstance(v[1], list)):
            raise SchemaRefusal(f"{where}: op wants [NAME, args]")
        if v[0] not in OP_ARITY:
            raise SchemaRefusal(
                f"{where}: op {v[0]!r} not in kernel vocabulary "
                f"{sorted(OP_ARITY)}")
        ar = OP_ARITY[v[0]]
        if ar is not None and len(v[1]) != ar:
            raise SchemaRefusal(
                f"{where}: op {v[0]} arity {len(v[1])} != {ar}")
        for a in v[1]:
            _check_term(a, where)
    elif k == "sym":
        if not isinstance(v, str):
            raise SchemaRefusal(f"{where}: sym wants a string")
    else:
        raise SchemaRefusal(f"{where}: unknown term form {k!r}")


def _sig_vars(terms) -> Set[str]:
    out = set()
    for t in terms or []:
        out |= term_roots(t)
    return out


def _bind_vars(t) -> Set[str]:
    """Vars a term BINDS (out-position / unify-operand)."""
    return term_roots(t)


# ---------------------------------------------------------------------------
# goal checks — one pass per clause, tracking bound vars
# ---------------------------------------------------------------------------

def _require_bound(t, bound: Set[str], where: str):
    """Every var in t must already be bound (grounded)."""
    unbound = term_roots(t) - bound
    if unbound:
        raise SchemaRefusal(
            f"{where}: unbound vars {sorted(unbound)} — directed/"
            f"consuming position requires grounding")


def _check_goal(g: dict, rels: Dict[str, dict], me: str,
                bound: Set[str], declared: Set[str], where: str):
    if not isinstance(g, dict) or len(g) != 1:
        raise SchemaRefusal(
            f"{me}: goal node must be a single-key map, got {g!r}")
    k, v = next(iter(g.items()))

    if k == "unify":
        a, b = v
        _check_term(a, where)
        _check_term(b, where)
        undecl = (term_roots(a) | term_roots(b)) - declared - bound
        if undecl:
            raise SchemaRefusal(
                f"{where}: vars {sorted(undecl)} undeclared — not in "
                f"sig or fresh")
        bound |= _bind_vars(a) | _bind_vars(b)

    elif k == "cmp":
        op, a, b = v
        _check_term(a, where)
        _check_term(b, where)
        _require_bound(a, bound, f"{where}: cmp {op}")
        _require_bound(b, bound, f"{where}: cmp {op}")

    elif k == "emit":
        _check_term(v, where)
        undecl = term_roots(v) - declared - bound
        if undecl:
            raise SchemaRefusal(
                f"{where}: emit vars {sorted(undecl)} undeclared")
        _require_bound(v, bound, f"{where}: emit")

    elif k == "call":
        name = v["rel"]
        if name not in rels:
            raise SchemaRefusal(f"{where}: unbound rel {name!r}")
        callee = rels[name]
        if len(v["args"]) != len(callee["in"]):
            raise SchemaRefusal(
                f"{where}: {name} arity {len(v['args'])} != "
                f"{len(callee['in'])}")
        for a in v["args"]:
            _check_term(a, where)
        undecl = term_roots(v["args"]) - declared - bound
        if undecl:
            raise SchemaRefusal(
                f"{where}: {name} args {sorted(undecl)} undeclared")
        if callee["dir"] in ("->", "<=>"):
            for a in v["args"]:
                _require_bound(a, bound,
                               f"{where}: {name} ({callee['dir']})")
        if v.get("out") is not None:
            _check_term(v["out"], where)
            bound |= _bind_vars(v["out"])
        # <-> calls may bind args too — relationally they are outputs
        if callee["dir"] == "<->":
            for a in v["args"]:
                bound |= _bind_vars(a)

    elif k == "run":
        _check_term(v["n"], where)
        n = v["n"]
        if "atom" not in n:
            _require_bound(n, bound, f"{where}: RUN n")
        _require_bound(v["goal"], bound, f"{where}: RUN goal")
        if v.get("out") is not None:
            _check_term(v["out"], where)
            bound |= _bind_vars(v["out"])

    elif k == "choice":
        _require_bound(v["a"], bound, f"{where}: CHOICE a")
        _require_bound(v["b"], bound, f"{where}: CHOICE b")
        if v.get("out") is not None:
            _check_term(v["out"], where)
            bound |= _bind_vars(v["out"])

    elif k == "builtin":
        name = v["name"]
        if name not in BUILTIN_ARITY:
            raise SchemaRefusal(
                f"{where}: builtin {name!r} not in registry "
                f"{sorted(BUILTIN_ARITY)}")
        ar = BUILTIN_ARITY[name]
        args = v.get("args") or []
        if ar is not None and len(args) != ar:
            raise SchemaRefusal(
                f"{where}: builtin {name} arity {len(args)} != {ar}")
        if ar is None and not args:
            raise SchemaRefusal(f"{where}: builtin {name} needs args")
        for a in args:
            _check_term(a, where)
        undecl = term_roots(args) - declared - bound
        if undecl:
            raise SchemaRefusal(
                f"{where}: builtin {name} args "
                f"{sorted(undecl)} undeclared")
        if v.get("out") is not None:
            _check_term(v["out"], where)
            bound |= _bind_vars(v["out"])

    else:
        raise SchemaRefusal(f"{where}: unknown goal form {k!r}")


# ---------------------------------------------------------------------------
# call-graph / recursion
# ---------------------------------------------------------------------------

def _goal_calls(g, acc: Set[str]):
    for k, v in g.items():
        if k == "call":
            acc.add(v["rel"])
        elif k == "builtin" and v["name"] == "call":
            pass  # dynamic call — target is data, not a static edge
        elif isinstance(v, dict):
            for gg in v.get("goals") or []:
                _goal_calls(gg, acc)


def _call_edges(rel: dict) -> Set[str]:
    out = set()
    for cl in rel.get("clauses") or []:
        for g in (cl.get("guard") or []) + (cl.get("goals") or []):
            _goal_calls(g, out)
    return out


def _cyclic(rels: Dict[str, dict]) -> Set[str]:
    """Rels on a call cycle — transitive reachability fixpoint."""
    edges = {n: _call_edges(r) & set(rels) for n, r in rels.items()}
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


# ---------------------------------------------------------------------------
# the check
# ---------------------------------------------------------------------------

def check(graph: dict) -> dict:
    """rel-graph -> same graph (admissible) or SchemaRefusal.

    The phantom stage: nothing the evaluator runs has skipped this."""
    if graph.get("format") != "phi.rel/1":
        raise SchemaRefusal(
            f"rel-schema: format {graph.get('format')!r} — "
            f"expected 'phi.rel/1'")
    rels = {r["name"]: r for r in graph["rels"]}
    if len(rels) != len(graph["rels"]):
        raise SchemaRefusal("rel-schema: duplicate rel names")

    for name, rel in rels.items():
        where = f"rel {name}"
        if rel["dir"] not in DIRS:
            raise SchemaRefusal(
                f"{where}: dir {rel['dir']!r} not in {DIRS}")
        if rel.get("shape") is not None \
                and rel["shape"] not in SHAPES:
            raise SchemaRefusal(
                f"{where}: shape {rel['shape']!r} not in {SHAPES}")
        if len(rel.get("out") or []) != 1:
            raise SchemaRefusal(
                f"{where}: sig out must be a single term, "
                f"got {len(rel.get('out') or [])}")
        for t in (rel.get("in") or []) + (rel.get("out") or []):
            _check_term(t, where)
        sig_declared = _sig_vars(rel.get("in")) | _sig_vars(rel.get("out"))

        for i, cl in enumerate(rel.get("clauses") or []):
            cw = f"{where} clause {i}"
            declared = set(sig_declared)
            if cl.get("fresh"):
                for v in cl["fresh"]:
                    if not isinstance(v, str):
                        raise SchemaRefusal(
                            f"{cw}: fresh name not a string: {v!r}")
                    if v in declared:
                        raise SchemaRefusal(
                            f"{cw}: fresh {v!r} shadows a sig var")
                declared |= set(cl["fresh"])

            # guards see only sig vars — fresh is a body scope
            bound = set(_sig_vars(rel.get("in")))
            for g in cl.get("guard") or []:
                gv = set()
                _collect_guard_vars(g, gv)
                undecl = gv - sig_declared
                if undecl:
                    raise SchemaRefusal(
                        f"{cw}: guard vars {sorted(undecl)} not in "
                        f"sig — guards cannot introduce vars")
                _check_goal(g, rels, name, bound, sig_declared, cw)
            for g in cl.get("goals") or []:
                _check_goal(g, rels, name, bound, declared, cw)

            # directed rels must bind their out by clause end
            if rel["dir"] in ("->", "<=>"):
                outv = _sig_vars(rel.get("out"))
                miss = outv - bound
                if miss:
                    raise SchemaRefusal(
                        f"{cw}: dir {rel['dir']} — out vars "
                        f"{sorted(miss)} never bound")

    # recursion shape — declared, never inferred
    for name in sorted(_cyclic(rels)):
        if rels[name].get("shape") is None:
            raise SchemaRefusal(
                f"rel {name}: recursive rel declares no shape — "
                f"admissible construction requires "
                f"shape ∈ {SHAPES} (never inferred)")
    return graph


def _collect_guard_vars(g: dict, acc: Set[str]):
    for k, v in g.items():
        if k in ("unify",):
            for t in v:
                acc |= term_roots(t)
        elif k == "cmp":
            acc |= term_roots(v[1]) | term_roots(v[2])
        elif k == "call":
            acc |= term_roots(v["args"])
            if v.get("out") is not None:
                acc |= term_roots(v["out"])
        elif isinstance(v, dict):
            for gg in v.get("goals") or []:
                _collect_guard_vars(gg, acc)


# ---------------------------------------------------------------------------
# declared program-schema rows — {relation, domain, invariant,
# target_class, refusal} — the IDCC shape as data
# ---------------------------------------------------------------------------

SCHEMAS = {
    "append": {
        "relation": "append<xs, ys> = zs",
        "domain": "xs, ys, zs PAIR-lists of terms; both directions "
                  "admissible (<->)",
        "invariant": "zs ≡ xs ++ ys; backward enumerates splits; "
                     "run* diverges past |splits|+1 — RUN(n) commits",
        "target_class": "basis-term evaluator (rel_eval) — "
                        "shape self → fueled recursive unfold",
        "refusal": "undeclared shape; ungrounded -> call; fuel is "
                   "declared data — exhaustion is an empty stream",
    },
    "fib": {
        "relation": "fib<n> = r",
        "domain": "n, r atoms; n bounded by declared fuel",
        "invariant": "r ≡ fib(n); pairwise decomposition is a "
                     "declared shape, scheduling-eligible per "
                     "schedule.min_parallel_roots (declared, not wired)",
        "target_class": "basis-term evaluator — shape pairwise → "
                        "declared split lowering",
        "refusal": "step|reduce shapes declared but lowering not "
                   "realized — honest K contract",
    },
    "norm": {
        "relation": "norm<goal> = result",
        "domain": "goal a goal-term; result first solution",
        "invariant": "norm ≡ RUN(goal,1) — committed read quotient",
        "target_class": "basis-term evaluator — RUN bounded take",
        "refusal": "RUN n must be atom or bound var",
    },
    "map": {
        "relation": "map<f, xs> = ys",
        "domain": "f a reldef/sym resolved via env_lookup; "
                  "xs, ys PAIR-lists",
        "invariant": "len(ys) = len(xs); ys[i] ≡ f(xs[i])",
        "target_class": "basis-term evaluator — shape self",
        "refusal": "env_lookup on unbound rel name",
    },
    "fold": {
        "relation": "fold<f, acc, xs> = acc'",
        "domain": "f reldef; acc term; xs PAIR-list",
        "invariant": "acc' ≡ xs folded left through f",
        "target_class": "basis-term evaluator — shape self",
        "refusal": "call arg must reify to a reldef",
    },
}


def schemas() -> dict:
    """The declared program-schema rows (spec: specs/schema-rel.json)."""
    return dict(SCHEMAS)


# ---------------------------------------------------------------------------
# selftest
# ---------------------------------------------------------------------------

def main() -> int:
    g = phi_rel.parse_rel(phi_rel._CORPUS)
    check(g)

    # patent corpus — one merged program (stdlib uses phi-lang's
    # head/tail/cons across files).  nibble_half_add is called-but-
    # undefined in the patent — the schema refusal IS the evidence
    # that the sketch is not admissible as-is.
    import os
    pat = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       os.pardir, os.pardir, "isa-physics",
                       "patent", "phi-lang")
    merged = {"format": "phi.rel/1", "rels": []}
    for fn in ("phi-lang.phi", "phi-stdlib.phi", "phi-runtime.phi"):
        p = os.path.join(pat, fn)
        if os.path.exists(p):
            merged["rels"] += \
                phi_rel.parse_rel(open(p, encoding="utf-8").read())["rels"]
    pat_msg = "no patent corpus found"
    if merged["rels"]:
        try:
            check(merged)
            pat_msg = f"patent corpus admissible ({len(merged['rels'])} rels)"
        except SchemaRefusal as e:
            pat_msg = (f"patent corpus refuses as-is: {e} "
                       f"— the sketch is not admissible construction")
    print(f"  {pat_msg}", file=sys.stderr)

    # named refusals — forged graphs must refuse, naming the invariant
    def refuses(src, frag):
        try:
            check(phi_rel.parse_rel(src))
        except SchemaRefusal as e:
            assert frag in str(e), f"{frag!r} not in {e}"
            return
        raise AssertionError(f"no refusal for {frag!r}")

    refuses("r : <x> -> <y> where UNIFY x x",
            "never bound")
    refuses("r : <x> <-> <y> where { | x = z { y = x } }",
            "guards cannot introduce")
    refuses("r : <x> <-> <y> where { | x = x { y = z } }",
            "undeclared")
    refuses("a : <x> <-> <y> where { a<x> = y }",
            "declares no shape")
    bad_shape = phi_rel.parse_rel(
        "a : <x> <-> <y> where { y = x }")
    bad_shape["rels"][0]["shape"] = "bogus"
    try:
        check(bad_shape)
    except SchemaRefusal as e:
        assert "shape 'bogus'" in str(e), e
    else:
        raise AssertionError("bogus shape not refused")
    refuses("a : <x> <-> <y> where { nosuch<x> = y }",
            "unbound rel 'nosuch'")
    refuses("a : <x> <-> <y> shape self where { a<x, x> = y }",
            "arity")
    refuses("a : <x> <-> <y> where { | fresh (x) { y = x } }",
            "shadows a sig var")
    refuses("a : <x> <-> <y, z> where { y = x }",
            "single term")
    bad_dir = phi_rel.parse_rel("a : <x> <-> <y> where { y = x }")
    bad_dir["rels"][0]["dir"] = "=>"
    try:
        check(bad_dir)
    except SchemaRefusal as e:
        assert "dir" in str(e), e
    else:
        raise AssertionError("bogus dir not refused")
    refuses("a : <x> <-> <y> where { RUN(g, x) = y }",
            "RUN goal")
    refuses("a : <x> <-> <y> where { frobnicate<x> = y }",
            "unbound rel")

    print("rel_schema selftest: corpus admissible, patent refusal "
          "recorded, 12 forged refusals named: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
