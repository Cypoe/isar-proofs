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
from typing import Dict, Iterator, List, Optional, Tuple

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
    _FIELDS.clear()


# pending field projections: varid -> (root var term, field).
# `def.pat` lifts to a fresh var aliased to root `def`; when the
# root walks to a reldef, the field projects to its marker.
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


# ---------------------------------------------------------------------------
# subst / unify
# ---------------------------------------------------------------------------

Subst = Dict[int, tuple]


def walk(t, s: Subst):
    while isinstance(t, tuple) and t[0] == "var" and t[1] in s:
        t = s[t[1]]
    # pending field projection: a var aliased to root.field projects
    # once the root resolves to a reldef; stays a bindable var
    # until then (def.pat / def.body on an unbound def).
    if isinstance(t, tuple) and t[0] == "var" and t[1] in _FIELDS:
        root, fld = _FIELDS[t[1]]
        rv = walk(root, s)
        rv = _force(rv, s)
        if isinstance(rv, tuple) and rv[0] == "reldef":
            return ("pat", rv[1]) if fld == "pat" else ("bodycall", rv[1])
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
    if "sym" in node:
        return t_sym(node["sym"])
    if "call_term" in node:
        # a call in term position is a suspended goal — goals are
        # data: RUN(g,n)/CHOICE/any dispatch on goalterm values.
        name, args = node["call_term"]
        return ("goalterm", name, [lift(a, ren) for a in args])
    if "__term" in node:
        return node["__term"]
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


def _goal_parts(gnode, env, s, ren):
    """Resolve a goal to (name, arg-nodes).  Two encodings: a
    {"call_term"} node directly, or a term that walks to a
    ("goalterm", name, argterms) — goals are data: any/norm/stream
    forward them through rel args."""
    if isinstance(gnode, dict) and "call_term" in gnode:
        name, args = gnode["call_term"]
        return name, args
    gt = _force(walk(lift(gnode, ren), s), s)
    if isinstance(gt, tuple) and gt[0] == "goalterm":
        return gt[1], [{"__term": a} for a in gt[2]]
    raise EvalError(f"goal must be a call_term or goalterm, "
                    f"got {term_str(gt) if isinstance(gt, tuple) else gnode!r}")


def _branch(node, env, out_t, s, fuel, ren) -> Iterator[Subst]:
    """CHOICE branch: each solution's out unifies with the
    choice's declared out."""
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


def _pat_lift(node):
    """Lift an in-pattern node to a term with SURFACE var names —
    a rel's declared pattern is data; its vars bind in the caller's
    subst under the declared names."""
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
    raise EvalError(f"rel_eval: unliftable pattern node {node!r}")


def _tvars(t) -> Iterator[tuple]:
    """Var terms in a pattern term — surface names only (pat vars
    are match-scoped; caller vars are fresh ints, never shadowed)."""
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
    """Right-nested PAIR tuple, no NIL tail — the k-arg convention:
    PAIR(a1, PAIR(a2, ... ak))."""
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = t_pair(t, out)
    return out


def _decode_binds(lst, s: Subst) -> Dict[str, tuple]:
    """MATCH's subst term — PAIR(PAIR('name, value), ...) spine —
    back to a surface-name dict for instantiate."""
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
    """Apply a decoded subst to an in-pattern node — the term
    APPLY hands to the dispatched rel call."""
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
    raise EvalError(f"rel_eval: uninstantiable node {node!r}")


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
            # def.pat — the rel's declared in-pattern as data.
            # Pat vars are match-scoped: shadow any stale surface
            # binding rather than colliding with an earlier MATCH
            # on the same names (map/fold recursion calls MATCH
            # per element — the second 'n' must re-bind).
            rname = pat[1]
            rel = env["rels"].get(rname)
            if rel is None:
                raise EvalError(f"MATCH: unbound rel {rname!r}")
            ins = [_pat_lift(n) for n in rel["in"]]
            shadow = {v[1] for n in ins for v in _tvars(n)}
            s_sh = {k: v for k, v in s.items() if k not in shadow}
            # arg-tuple convention (patent): 1 arg = the term;
            # k args = PAIR(a1, PAIR(a2, ... ak)) right-nested,
            # no NIL tail — call<f, PAIR(acc,h)> for 2-arg f.
            target = ins[0] if len(ins) == 1 else \
                _rtuple(ins)
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
            # APPLY(subst, def.body) — instantiate the rel's
            # in-pattern under the subst MATCH produced and
            # dispatch: the meta-level call is a rel call.
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


def _cyclic(rels: Dict[str, dict]) -> set:
    """Rels on a call cycle — transitive fixpoint.  The schema does
    this check at construction; the evaluator repeats it because
    forged rel-graphs can reach _rel_call unchecked."""
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


# declared lowering forms the evaluator can honor — the koru
# contract: a shape names a kernel form, and a form without an
# implementation refuses rather than silently substituting unfold.
LOWERINGS = {
    "self": "depth-fueled recursive unfold",
    "pairwise": "unfold — split scheduling declared-not-wired "
                "(schedule.min_parallel_roots contract)",
}


def _rel_call(name: str, args: List[dict], out_node,
              env, s: Subst, fuel, caller_ren) -> Iterator[Subst]:
    rel = env["rels"].get(name)
    if rel is None:
        raise EvalError(f"rel_eval: unbound rel {name!r}")
    if "cyc" not in env:
        env["cyc"] = _cyclic(env["rels"])
    if name in env["cyc"]:
        shape = rel.get("shape")
        if shape is None:
            raise EvalError(
                f"rel_eval: recursive rel {name!r} declares no "
                f"shape — admissible construction refuses "
                f"(undeclared recursion contract)")
        if shape not in LOWERINGS:
            raise EvalError(
                f"rel_eval: rel {name!r} declares shape "
                f"{shape!r} — lowering not realized "
                f"(realized: {sorted(LOWERINGS)}; a declared kernel "
                f"form without an implementation refuses before "
                f"silently substituting unfold)")
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
    # lowering contract: shape step is declared, not realized —
    # refuses rather than silently substituting unfold
    g2 = phi_rel.parse_rel(
        "r : <x> <-> <y> shape step where { r<x> = y }")
    try:
        run_value(g2, "r", [t_atom(8, 0)], n=1)
    except EvalError as e:
        assert "lowering not realized" in str(e), e
    else:
        raise AssertionError("shape step ran")
    # transitive cycle without shape — forged graphs refuse too
    g3 = phi_rel.parse_rel(
        "a : <x> <-> <y> shape self where { b<x> = y }\n"
        "b : <x> <-> <y> where { a<x> = y }")
    try:
        run_value(g3, "a", [t_atom(8, 0)], n=1)
    except EvalError as e:
        assert "declares no shape" in str(e), e
    else:
        raise AssertionError("unshaped cycle ran")
    # ---- 10e: the admissible stdlib corpus, exercised end-to-end
    corpus = os.path.join(os.path.dirname(__file__), "corpus",
                          "stdlib.phi")
    cg = phi_rel.parse_rel(open(corpus, encoding="utf-8").read())
    import rel_schema
    rel_schema.check(cg)                      # every edge bound
    _reset_fresh()

    def L(*xs):
        out = NIL
        for x in reversed(xs):
            out = t_pair(x, out)
        return out

    def A(v, bits=8):
        return t_atom(bits, v)

    assert run_value(cg, "call", [t_sym("succ"), A(2)], n=1) == [A(3)]
    assert run_value(cg, "map", [t_sym("succ"), L(A(1), A(2))],
                     n=1) == [L(A(2), A(3))]
    assert run_value(cg, "fold", [t_sym("add"), A(0),
                                  L(A(1), A(2), A(3))], n=1) == [A(6)]
    assert run_value(cg, "nibble_half_add",
                     [A(15, 4), A(2, 4), A(1, 4)], n=1) == \
        [t_pair(A(2, 4), A(1, 4))]
    assert run_value(cg, "nibble_add",
                     [L(A(1, 4), A(2, 4)), L(A(3, 4), A(0, 4)),
                      A(0, 4)], n=1) == [L(A(4, 4), A(2, 4))]
    assert run_value(cg, "add", [A(2), A(3)], n=1) == [A(5)]
    assert run_value(cg, "fib", [A(5)], n=1) == [A(5)]
    assert run_value(cg, "norm",
                     [("goalterm", "append", [L(A(9)), NIL])],
                     n=1) == [L(A(9))]

    # ---- congruence vs the patent boot engine (same program,
    # both machines, same solutions in the same order)
    cong = "absent"
    boot_dir = os.path.join(os.path.dirname(__file__), os.pardir,
                            os.pardir, "isa-physics", "patent",
                            "phi-lang")
    boot_py = os.path.join(boot_dir, "phi_boot.py")
    if os.path.exists(boot_py):
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "phi_boot", boot_py)
        B = importlib.util.module_from_spec(spec)
        sys.modules["phi_boot"] = B      # dataclass needs the
        spec.loader.exec_module(B)       # module registered first

        def appendo(xs, ys, zs):
            def goal(s):
                for s1 in B.conj(
                        B.eq(xs, B.Atom.of(0, bits=0)),
                        B.eq(zs, ys))(s):
                    yield s1
                h, t, r = B.fresh(), B.fresh(), B.fresh()
                for s1 in B.conj(
                        B.eq(xs, B.Pair(h, t)),
                        B.conj(appendo(t, ys, r),
                               B.eq(zs, B.Pair(h, r))))(s):
                    yield s1
            return goal

        def bL(*xs):
            out = B.Atom.of(0, bits=0)
            for x in reversed(xs):
                out = B.Pair(x, out)
            return out

        bxs, bys = B.fresh(), B.fresh()
        bwant = bL(B.Atom.of(1), B.Atom.of(2))
        bres = B.run(appendo(bxs, bys, bwant), n=3)
        bsplits = [(B.reify(bxs, s), B.reify(bys, s)) for s in bres]
        _reset_fresh()
        qx, qy = fresh(), fresh()
        want = L(A(1), A(2))
        sols = run_solutions(cg, "append", [qx, qy], want, n=3)
        ours = [(reify(qx, s), reify(qy, s)) for s in sols]
        assert len(bsplits) == len(ours) == 3
        # same splits in the same order (observational equivalence)
        for (bx, by), (ox, oy) in zip(bsplits, ours):
            assert _boot_term(bx) == ox and _boot_term(by) == oy, \
                (bx, ox)
        cong = "3 splits identical"
    print(f"rel_eval selftest: append fwd 1 sol, "
          f"bwd {[term_str(a) for a, _ in got]}, "
          f"head/equal ok, add/fib relational, unbound+fuel "
          f"refusals, lowering+cycle contracts, "
          f"stdlib corpus (call/map/fold/nibble-add/norm), "
          f"phi_boot congruence [{cong}]: pass")
    return 0


def _boot_term(bt):
    """phi_boot Atom/Pair -> our term encoding (duck-typed —
    phi_boot is loaded via spec_from_file_location, not sys.path)."""
    if type(bt).__name__ == "Atom":
        return t_atom(bt.bits, bt.value()) if bt.bits else NIL
    if type(bt).__name__ == "Pair":
        return t_pair(_boot_term(bt.car), _boot_term(bt.cdr))
    return bt


if __name__ == "__main__":
    sys.exit(main())
