"""
rel_eval — the substrate evaluator for phi.rel/1 rel-graphs.

The kernel vocabulary {FRESH, UNIFY, MATCH, APPLY, CHOICE, RUN}
executed as relational semantics over the parsed graph: clauses
are relation EXTENSIONS (guarded union), non-determinism is a
stream of substitutions, determinism is a per-call quotient
(RUN(g,1) committed read vs RUN(g,0) full stream — the same
norm/find/stream split as the patent phi-lang).

This is the host-side executable semantics — the reference the
emitted basis-term leg must simulate (declared contract, see
host/specs/surface-phi.rel.json and docs/frags/0005).  It is NOT
a different substrate: the same structures (substitutions,
adjacency PAIRs, atom payloads) are what the basis-term encoding
carries; the Python is residue like run_emit_bundle's subprocess
per runner.

Terms (runtime):  ("atom", bits, payload:int)
                  ("pair", a, b)
                  ("var", id)
                  ("sym", name)         — rel/name symbol
                  ("reldef", name)      — env_lookup result
Goals thread a renaming (surface name -> fresh var) per clause
instantiation — that scoping IS the clause-extension semantics.
Fuel is the declared termination invariant: exhaustion is an
observable empty stream, never a timeout or exception.

Direction is data, not engine semantics: the evaluator is fully
relational — `<->`, `<=>`, `->` restrict which CALLS are
admissible (rel_schema mode check); evaluation just unifies.
"""
from __future__ import annotations

import itertools
import os
import sys
from typing import Dict, Iterator, List, Optional

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

import phi_rel  # noqa: E402


class EvalError(ValueError):
    """Runtime refusal: unbound names, unexecutable forms,
    undeclared recursion — each names the violated invariant.
    Fuel exhaustion is NOT here: it is an observable empty
    stream."""


# ---------------------------------------------------------------------------
# runtime terms
# ---------------------------------------------------------------------------

def t_atom(bits: int, v: int) -> tuple:
    return ("atom", bits, v)


def t_pair(a, b) -> tuple:
    return ("pair", a, b)


def t_var(i: int) -> tuple:
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
    return repr(t)


# ---------------------------------------------------------------------------
# subst / unify
# ---------------------------------------------------------------------------

Subst = Dict[int, tuple]


def walk(t, s: Subst):
    while isinstance(t, tuple) and t[0] == "var" and t[1] in s:
        t = s[t[1]]
    return t


def unify(u, v, s: Subst) -> Optional[Subst]:
    u, v = _force(walk(u, s), s), _force(walk(v, s), s)
    if u == v:
        return s
    if u[0] == "var":
        return {**s, u[1]: v}
    if v[0] == "var":
        return {**s, v[1]: u}
    if u[0] == "pair" and v[0] == "pair":
        s2 = unify(u[1], v[1], s)
        return unify(u[2], v[2], s2) if s2 is not None else None
    return None


def reify(t, s: Subst):
    t = _force(walk(t, s), s)
    if isinstance(t, tuple) and t[0] == "pair":
        return t_pair(reify(t[1], s), reify(t[2], s))
    return t


# ---------------------------------------------------------------------------
# rel-graph node -> runtime term (`ren` = this scope's renaming)
# ---------------------------------------------------------------------------

def lift(node, ren: Dict[str, tuple]):
    if node is None:
        return NIL
    if "var" in node:
        n = node["var"]
        if n not in ren:
            ren[n] = fresh()
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
        # self-contained lazy: the var tuple travels inside —
        # any subst resolves it, no ren needed at walk time
        return ("atom_lazy", _lazy_e(be, ren), _lazy_e(pe, ren))
    if "pair" in node:
        return t_pair(lift(node["pair"][0], ren),
                      lift(node["pair"][1], ren))
    if "typed" in node:
        return lift(node["typed"][0], ren)
    if "type" in node:
        return fresh()                           # bare type slot
    if "var_lit" in node:
        return node["var_lit"]
    raise EvalError(f"rel_eval: unliftable term node {node!r}")


def _aval(e: dict, ren) -> Optional[int]:
    if "const" in e:
        return e["const"]
    name, d = e["var_delta"]
    v = ren.get(name)
    if isinstance(v, tuple) and v[0] == "atom":
        return v[2] + d
    return None


def _lazy_e(e: dict, ren):
    """atom_dyn field -> self-contained lazy expr."""
    if "const" in e:
        return ("const", e["const"])
    name, d = e["var_delta"]
    if name not in ren:
        ren[name] = fresh()
    return ("delta", ren[name], d)


def _force(t, s: Subst):
    """Resolve a lazy atom under s — stays lazy if vars are free."""
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
# goals
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
        return                                    # fuel: empty stream
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
                "emit (! t): no relation output in scope — "
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
        outs = _choice_out(c["out"], ren)
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
    raise EvalError(f"rel_eval: goal {g!r} not executable")


def _choice_out(node, ren):
    return lift(node, ren) if node is not None else None


def _branch(node, env, out_t, s, fuel, ren) -> Iterator[Subst]:
    """CHOICE branch: a call_term — each solution's out unifies
    with the choice's declared out."""
    if "call_term" not in node:
        raise EvalError(
            f"CHOICE branch must be a call_term, got {node!r}")
    name, args = node["call_term"]
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
    if "call_term" not in gnode:
        raise EvalError(
            f"RUN: goal must be a call_term, got {gnode!r}")
    name, args = gnode["call_term"]
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
        s2 = unify(lift(args[0], ren), lift(args[1], ren), s)
        if s2 is None:
            return
        if out is None:
            yield s2
            return
        binds = NIL
        for k, v in sorted(s2.items()):
            binds = t_pair(t_pair(t_var(k), reify(v, s2)), binds)
        s3 = unify(lift(out, ren), binds, s2)
        if s3 is not None:
            yield s3
        return
    if name == "APPLY":
        t = _force(walk(lift(args[-1], ren), s), s)
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
                f"env_lookup: rel name must be a symbol, "
                f"got {term_str(nm)}")
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
                f"call: first arg must reify to a reldef, "
                f"got {term_str(f)}")
        yield from _rel_call(f[1], args[1:], out, env, s, fuel,
                             ren)
        return
    raise EvalError(f"rel_eval: builtin {name!r} not realized")


# ---------------------------------------------------------------------------
# relation invocation — clauses are extensions (disj over them);
# each instantiation gets a fresh renaming
# ---------------------------------------------------------------------------

def _callers(rel: dict) -> set:
    """rel names this rel's clauses call — for the recursion/
    shape contract."""
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


def _rel_call(name: str, args: List[dict], out_node,
              env, s: Subst, fuel, caller_ren) -> Iterator[Subst]:
    rel = env["rels"].get(name)
    if rel is None:
        raise EvalError(f"rel_eval: unbound rel {name!r}")
    if name in _callers(rel) and rel.get("shape") is None:
        raise EvalError(
            f"rel_eval: recursive rel {name!r} declares no "
            f"shape — admissible construction refuses "
            f"(undeclared recursion contract)")
    if len(args) != len(rel["in"]):
        raise EvalError(
            f"rel_eval: {name} arity {len(rel['in'])} != "
            f"call args {len(args)}")
    targs = [lift(a, caller_ren) for a in args]
    tout = lift(out_node, caller_ren) if out_node is not None \
        else None
    clauses = rel["clauses"] if rel["clauses"] is not None \
        else [None]
    for cl in clauses:
        ren: Dict[str, tuple] = {}         # this instantiation
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
            yield s0                       # direct extension
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


def lit(t) -> dict:
    """runtime term -> a var_lit node (args already values)."""
    return {"var_lit": t}


def run(graph: dict, rel: str, args: List[dict], out: dict,
        n: int = 1, fuel: int = 100_000) -> List[Subst]:
    """RUN(rel<args> = out, n): the per-call quotient.
    n=1 committed read; n=0 the full stream."""
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
    """runtime-term args -> reified out per solution."""
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
    """Full substs — for backward queries (relational reads)."""
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
# selftest
# ---------------------------------------------------------------------------

def main() -> int:
    _reset_fresh()
    g = phi_rel.parse_rel(phi_rel._CORPUS)
    la = t_pair(t_atom(8, 1), NIL)
    lb = t_pair(t_atom(8, 2), NIL)
    # forward: append<[1],[2]> = zs
    sols = run_value(g, "append", [la, lb], n=1)
    want = t_pair(t_atom(8, 1), t_pair(t_atom(8, 2), NIL))
    assert sols == [want], [term_str(s) for s in sols]
    # backward: append<xs, ys> = [1,2] — the relational read.
    # n=3: the quotient commits at the count — run* would diverge
    # searching for a 4th split (honest divergence, not a bug)
    xs, ys = fresh(), fresh()
    sols = run_solutions(g, "append", [xs, ys], want, n=3)
    got = [(reify(xs, s), reify(ys, s)) for s in sols]
    assert len(got) == 3, [term_str(a) for a, _ in got]
    assert got[0] == (NIL, want) and got[-1] == (want, NIL)
    # head / equal direct extensions
    hp = run_value(g, "head", [want], n=1)
    assert hp == [t_atom(8, 1)], hp
    eq = run_value(g, "equal",
                   [t_atom(8, 7), t_atom(8, 7)], n=1)
    assert eq == [t_atom(8, 7)], eq
    # relational arithmetic — succ/pred chains, no Church shortcut
    assert run_value(g, "add", [t_atom(8, 2), t_atom(8, 3)],
                     n=1) == [t_atom(8, 5)]
    assert run_value(g, "fib", [t_atom(8, 5)], n=1) == [t_atom(8, 5)]
    # RUN quotient: n>1 enumerates, n=1 commits
    assert len(run_value(g, "add", [t_atom(8, 0), t_atom(8, 4)],
                         n=1)) == 1
    # unbound rel refuses by name
    try:
        run_value(g, "nosuchrel", [la], n=1)
    except EvalError as e:
        assert "unbound rel" in str(e)
    else:
        raise AssertionError("unbound rel ran")
    # fuel is data: exhaustion is an empty stream, never a hang
    assert run_value(g, "fib", [t_atom(8, 5)], n=1, fuel=40) == []
    print(f"rel_eval selftest: append fwd 1 sol, "
          f"bwd {[term_str(a) for a, _ in got]}, "
          f"head/equal ok, add/fib relational, unbound+fuel "
          f"refusals: pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
