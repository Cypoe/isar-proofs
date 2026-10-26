#!/usr/bin/env python3
"""host2.run — the runK witness twin.

The one piece of logic host2 owns: a Python transcription of
ISAR.FlowDialect runK/evalKE/evalKBin/evalKUn/evalKBuiltin, operating
directly on .kv wire values (the JSON form DumpKoruFixtures writes —
one object per grammar node: {"<ctor>": payload}).

Faithfulness obligations (each mirrors a Lean arm, same refusal shapes):
  * floats are exact rationals num/den; d=0 refuses at asKRat; / refuses
    a zero quotient denominator; % on floats refuses outright.
  * ints unbounded (Python ints — same as Lean Int).
  * `and`/`or`/`cond` short-circuit; guards must eval to bool.
  * env lookup = first binding wins; cell field = last binding wins.
  * fuel is a resource cap: every call frame costs one; 0 -> None.
  * oracle = asserted thunk leaves keyed by (name, args) — the trust
    boundary; missing leaf refuses.

This is a WITNESS: it exists to be checked against runK's decisions on
declared fixtures (host2/fixtures.py), never to be trusted alone.
"""
from __future__ import annotations

import json
import sys

sys.setrecursionlimit(100_000)


# ----- values -----

def is_bool(v):
    return isinstance(v, dict) and "bool" in v


def is_int(v):
    return isinstance(v, dict) and "int" in v


def as_krat(v):
    """KVal -> (num, den) | None — exact rational promotion."""
    if isinstance(v, dict) and "float" in v:
        n, d = v["float"]
        if d == 0:
            return None
        return (-n, -d) if d < 0 else (n, d)
    if isinstance(v, dict) and "int" in v:
        return (v["int"], 1)
    return None


def ktdiv(a, b):
    q = abs(a) // abs(b)
    return -q if (a < 0) != (b < 0) else q


def ktmod(a, b):
    return a - b * ktdiv(a, b)


def kfmod(a, b):
    return a - b * (a // b)


def kfloat_bin(op, ra, rb):
    n1, d1 = ra
    n2, d2 = rb
    if op == "add":
        return {"float": [n1 * d2 + n2 * d1, d1 * d2]}
    if op == "sub":
        return {"float": [n1 * d2 - n2 * d1, d1 * d2]}
    if op == "mul":
        return {"float": [n1 * n2, d1 * d2]}
    if op == "div":
        if d1 * n2 == 0:
            return None
        return {"float": [n1 * d2, d1 * n2]}
    if op == "mod":
        return None
    if op == "eq":
        return {"bool": n1 * d2 == n2 * d1}
    if op == "ne":
        return {"bool": n1 * d2 != n2 * d1}
    if op == "lt":
        return {"bool": n1 * d2 < n2 * d1}
    if op == "le":
        return {"bool": n1 * d2 <= n2 * d1}
    if op == "gt":
        return {"bool": n1 * d2 > n2 * d1}
    if op == "ge":
        return {"bool": n1 * d2 >= n2 * d1}
    return None


def eval_kbin(op, a, b):
    if (isinstance(a, dict) and "float" in a) or \
       (isinstance(b, dict) and "float" in b):
        ra, rb = as_krat(a), as_krat(b)
        if ra is None or rb is None:
            return None
        return kfloat_bin(op, ra, rb)
    if is_int(a) and is_int(b):
        x, y = a["int"], b["int"]
        if op == "add":
            return {"int": x + y}
        if op == "sub":
            return {"int": x - y}
        if op == "mul":
            return {"int": x * y}
        if op == "div":
            return None if y == 0 else {"int": ktdiv(x, y)}
        if op == "mod":
            return None if y == 0 else {"int": ktmod(x, y)}
        if op == "eq":
            return {"bool": x == y}
        if op == "ne":
            return {"bool": x != y}
        if op == "lt":
            return {"bool": x < y}
        if op == "le":
            return {"bool": x <= y}
        if op == "gt":
            return {"bool": x > y}
        if op == "ge":
            return {"bool": x >= y}
        return None
    if is_bool(a) and is_bool(b):
        if op == "eq":
            return {"bool": a["bool"] == b["bool"]}
        if op == "ne":
            return {"bool": a["bool"] != b["bool"]}
        return None
    if isinstance(a, dict) and "str" in a and \
       isinstance(b, dict) and "str" in b:
        if op == "eq":
            return {"bool": a["str"] == b["str"]}
        if op == "ne":
            return {"bool": a["str"] != b["str"]}
        if op == "concat":
            return {"str": a["str"] + b["str"]}
        return None
    return None


def eval_kun(op, v):
    if op == "not" and is_bool(v):
        return {"bool": not v["bool"]}
    if op == "neg" and is_int(v):
        return {"int": -v["int"]}
    if op == "neg" and isinstance(v, dict) and "float" in v:
        n, d = v["float"]
        return {"float": [-n, d]}
    return None


def eval_kbuiltin(env, name, args):
    if name == "as" and len(args) == 2:
        return eval_ke(env, args[1])
    if name in ("intCast", "truncate") and len(args) == 1:
        v = eval_ke(env, args[0])
        return v if is_int(v) else None
    if name in ("divTrunc", "rem", "mod") and len(args) == 2:
        va, vb = eval_ke(env, args[0]), eval_ke(env, args[1])
        if is_int(va) and is_int(vb):
            a, b = va["int"], vb["int"]
            if b == 0:
                return None
            if name == "divTrunc":
                return {"int": ktdiv(a, b)}
            if name == "rem":
                return {"int": ktmod(a, b)}
            return {"int": kfmod(a, b)}
        return None
    if name == "len" and len(args) == 1:
        v = eval_ke(env, args[0])
        if isinstance(v, dict) and "arr" in v:
            return {"int": len(v["arr"])}
        return None
    if name == "intToString" and len(args) == 1:
        v = eval_ke(env, args[0])
        return {"str": str(v["int"])} if is_int(v) else None
    return None


def eval_ke(env, e):
    """evalKE twin — Option<KVal>."""
    if "lit" in e:
        return e["lit"]
    if "var" in e:
        for n, v in env:
            if n == e["var"]:
                return v
        return None
    if "bin" in e:
        op, a, b = e["bin"]
        if op == "and":
            va = eval_ke(env, a)
            if not is_bool(va):
                return None
            if va["bool"] is False:
                return {"bool": False}
            vb = eval_ke(env, b)
            return vb if is_bool(vb) else None
        if op == "or":
            va = eval_ke(env, a)
            if not is_bool(va):
                return None
            if va["bool"] is True:
                return {"bool": True}
            vb = eval_ke(env, b)
            return vb if is_bool(vb) else None
        va, vb = eval_ke(env, a), eval_ke(env, b)
        if va is None or vb is None:
            return None
        return eval_kbin(op, va, vb)
    if "un" in e:
        op, a = e["un"]
        va = eval_ke(env, a)
        return None if va is None else eval_kun(op, va)
    if "cond" in e:
        c, t, f = e["cond"]
        vc = eval_ke(env, c)
        if vc == {"bool": True}:
            return eval_ke(env, t)
        if vc == {"bool": False}:
            return eval_ke(env, f)
        return None
    if "field" in e:
        o, name = e["field"]
        vo = eval_ke(env, o)
        if isinstance(vo, dict) and "cell" in vo:
            for n, v in reversed(vo["cell"]):
                if n == name:
                    return v
        return None
    if "index" in e:
        o, i = e["index"]
        vo, vi = eval_ke(env, o), eval_ke(env, i)
        if isinstance(vo, dict) and "arr" in vo and is_int(vi):
            idx = vi["int"]
            if idx < 0 or idx >= len(vo["arr"]):
                return None
            return vo["arr"][idx]
        return None
    if "builtin" in e:
        name, args = e["builtin"]
        return eval_kbuiltin(env, name, args)
    return None


def eval_kargs(env, named_exprs):
    """evalKArgs twin — every arg named, evaluated at the call site."""
    out = []
    for n, e in named_exprs:
        v = eval_ke(env, e)
        if v is None:
            return None
        out.append([n, v])
    return out


# ----- the call machine -----

def oracle_lookup(o, name, args):
    for (n, a), r in o:
        if n == name and a == args:
            return r
    return None


def graph_lookup(g, name):
    for n, c in g:
        if n == name:
            return c
    return None


def bind_karm_env(arm, env, r):
    b = arm["arm"]["bind"]
    if b is not None:
        if r["payload"] is None:
            return None
        return [[b, r["payload"]]] + env
    return env


def eval_kguard(env, arm):
    c = arm["arm"]["cond"]
    if c is None:
        return True
    v = eval_ke(env, c)
    if is_bool(v):
        return v["bool"]
    return None


def as_kresult(outcome):
    """asKResult twin — unwrap .result, everything else refuses."""
    if isinstance(outcome, tuple) and outcome[0] == "result":
        return outcome[1]
    return None


def run_k(g, o, fuel, call):
    """runK twin — Option<KOutcome>: ("result", r) | ("jump", l, a)
    | "done" | "skip" | None."""
    if fuel <= 0:
        return None
    fuel -= 1
    tag = call[0]

    if tag == "invoke":
        _, name, args = call
        c = graph_lookup(g, name)
        if c is None:
            return None
        if "thunk" in c:
            r = oracle_lookup(o, name, args)
            return ("result", r) if r is not None else None
        if "bare" in c:
            v = eval_ke(args, c["bare"])
            if v is None:
                return None
            return ("result", {"branch": None, "payload": v})
        if "subflow" in c:
            return run_k(g, o, fuel, ("flow", c["subflow"], args))
        return None

    if tag == "flow":
        _, fl, call_args = call
        f = fl["flow"]
        hargs = eval_kargs(call_args, f["head"][1])
        if hargs is None:
            return None
        return run_k(g, o, fuel, ("loop", fl, call_args, hargs))

    if tag == "loop":
        _, fl, env, hargs = call
        f = fl["flow"]
        inner = run_k(g, o, fuel, ("invoke", f["head"][0], hargs))
        if not (isinstance(inner, tuple) and inner[0] == "result"):
            return None
        r = inner[1]
        if not f["arms"]:
            return ("result", r)
        if r["branch"] is not None:
            d = run_k(g, o, fuel, ("dispatchTag", env, f["arms"], r["branch"], r))
        else:
            d = run_k(g, o, fuel, ("dispatchBare", env, f["arms"], r))
        if d is None or d == "skip":
            return None
        if d == "done":
            return ("result", {"branch": None, "payload": None})
        if d[0] == "jump":
            if f["preLabel"] == d[1]:
                return run_k(g, o, fuel, ("loop", fl, env, d[2]))
            return None
        return d

    if tag == "dispatchTag":
        _, env, arms, b, r = call
        for a in arms:
            if a["arm"]["branch"] != b:
                continue
            o1 = run_k(g, o, fuel, ("armTry", env, a, r))
            if o1 is None:
                return None
            if o1 == "skip":
                continue
            return o1
        return None

    if tag == "dispatchBare":
        _, env, arms, r = call
        if r["payload"] is None:
            return None
        for a in arms:
            if a["arm"]["catchall"] or a["arm"]["branch"] == "":
                return None
            o1 = run_k(g, o, fuel, ("armTry", env, a, r))
            if o1 is None:
                return None
            if o1 == "skip":
                continue
            return o1
        return None

    if tag == "armTry":
        _, env, a, r = call
        env2 = bind_karm_env(a, env, r)
        if env2 is None:
            return None
        gp = eval_kguard(env2, a)
        if gp is None:
            return None
        if not gp:
            return "skip"
        return run_k(g, o, fuel, ("armWalk", env2, a, r))

    if tag == "armWalk":
        _, env, a, _r = call
        node = a["arm"]["node"]
        if node is None or "terminal" in node:
            return "done"
        if "jump" in node:
            lbl, aexprs = node["jump"]
            hargs = eval_kargs(env, aexprs)
            return ("jump", lbl, hargs) if hargs is not None else None
        if "invoke" in node:
            name, aexprs = node["invoke"]
            hargs = eval_kargs(env, aexprs)
            if hargs is None:
                return None
            inner = run_k(g, o, fuel, ("invoke", name, hargs))
            if not (isinstance(inner, tuple) and inner[0] == "result"):
                return None
            r = inner[1]
            conts = a["arm"]["conts"]
            if not conts:
                return ("result", r)
            if r["branch"] is not None:
                return run_k(g, o, fuel, ("dispatchTag", env, conts, r["branch"], r))
            return run_k(g, o, fuel, ("dispatchBare", env, conts, r))
        if "produce" in node:
            v = eval_ke(env, node["produce"])
            if v is None:
                return None
            return ("result", {"branch": None, "payload": v})
        if "retCtor" in node:
            br, e = node["retCtor"]
            v = eval_ke(env, e)
            if v is None:
                return None
            return ("result", {"branch": br, "payload": v})
        return None

    return None


def eval_prog(prog, oracle, fuel):
    """evalKProg twin — Option<KResult>."""
    return as_kresult(
        run_k(prog["graph"], oracle, fuel,
              ("invoke", prog["entry"], prog["args"])))


def main(argv):
    """python host2/run.py PROG.kv [--fuel N] [--oracle ORACLE.kv]"""
    import argparse
    ap = argparse.ArgumentParser(prog="host2.run")
    ap.add_argument("prog")
    ap.add_argument("--fuel", type=int, default=64)
    ap.add_argument("--oracle", default=None)
    ns = ap.parse_args(argv)
    prog = json.load(open(ns.prog, encoding="utf-8"))
    oracle = []
    if ns.oracle:
        oracle = json.load(open(ns.oracle, encoding="utf-8"))
    r = eval_prog(prog, oracle, ns.fuel)
    print(json.dumps(r) if r is not None else "REFUSED")
    return 0 if r is not None else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
