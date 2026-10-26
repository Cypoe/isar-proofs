#!/usr/bin/env python3
"""host2.quote — the quoteProg twin.

KProg (.kv dict form) -> KVal (.kv dict form): the calling convention
that presents a source program to a compiler program as inspectable
data.  Mirrors ISAR.KoruEmit.quoteProg — same tag table (1..31, with
encBinOpN/encUnOpN op numbering), nodes are {"cell": [["tag",int],
["kids",arr]]}, pairs are {"cell":[["name",str],["v",_]]}, Option is
tags 23/24.
"""

BINOP_N = {"add": 0, "sub": 1, "mul": 2, "div": 3, "mod": 4,
           "eq": 5, "ne": 6, "lt": 7, "le": 8, "gt": 9, "ge": 10,
           "and": 11, "or": 12, "concat": 13}
UNOP_N = {"neg": 0, "not": 1}


def qnode(tag, kids):
    return {"cell": [["tag", {"int": tag}], ["kids", {"arr": kids}]]}


def qpair(n, v):
    return {"cell": [["name", {"str": n}], ["v", v]]}


def qopt(v):
    return qnode(23, []) if v is None else qnode(24, [v])


def quote_val(v):
    if "int" in v:
        return qnode(1, [{"int": v["int"]}])
    if "float" in v:
        n, d = v["float"]
        return qnode(2, [{"int": n}, {"int": d}])
    if "bool" in v:
        return qnode(3, [{"int": 1 if v["bool"] else 0}])
    if "str" in v:
        return qnode(4, [{"str": v["str"]}])
    if "arr" in v:
        return qnode(5, [{"arr": [quote_val(x) for x in v["arr"]]}])
    if "cell" in v:
        return qnode(6, [{"arr": [qpair(n, quote_val(x)) for n, x in v["cell"]]}])
    raise ValueError(f"malformed kval node: {v!r}")


def quote_expr(e):
    if "lit" in e:
        return qnode(8, [quote_val(e["lit"])])
    if "var" in e:
        return qnode(9, [{"str": e["var"]}])
    if "bin" in e:
        op, a, b = e["bin"]
        return qnode(10, [{"int": BINOP_N[op]}, quote_expr(a), quote_expr(b)])
    if "un" in e:
        op, a = e["un"]
        return qnode(11, [{"int": UNOP_N[op]}, quote_expr(a)])
    if "cond" in e:
        c, t, f = e["cond"]
        return qnode(12, [quote_expr(c), quote_expr(t), quote_expr(f)])
    if "field" in e:
        o, n = e["field"]
        return qnode(13, [quote_expr(o), {"str": n}])
    if "index" in e:
        o, i = e["index"]
        return qnode(14, [quote_expr(o), quote_expr(i)])
    if "builtin" in e:
        n, args = e["builtin"]
        return qnode(15, [{"str": n}, {"arr": [quote_expr(a) for a in args]}])
    raise ValueError(f"malformed kexpr node: {e!r}")


def quote_named_exprs(xs):
    return [qpair(n, quote_expr(e)) for n, e in xs]


def quote_arm_node(node):
    if "terminal" in node:
        return qnode(16, [])
    if "jump" in node:
        t, args = node["jump"]
        return qnode(17, [{"str": t}, {"arr": quote_named_exprs(args)}])
    if "invoke" in node:
        t, args = node["invoke"]
        return qnode(18, [{"str": t}, {"arr": quote_named_exprs(args)}])
    if "produce" in node:
        return qnode(19, [quote_expr(node["produce"])])
    if "retCtor" in node:
        c, e = node["retCtor"]
        return qnode(20, [{"str": c}, quote_expr(e)])
    raise ValueError(f"malformed karmnode: {node!r}")


def quote_arm(a):
    arm = a["arm"]
    return qnode(22, [
        {"str": arm["branch"]},
        {"int": 1 if arm["catchall"] else 0},
        qopt({"str": arm["bind"]} if arm["bind"] is not None else None),
        qopt(quote_expr(arm["cond"]) if arm["cond"] is not None else None),
        qopt(quote_arm_node(arm["node"]) if arm["node"] is not None else None),
        {"arr": [quote_arm(c) for c in arm["conts"]]}])


def quote_head(h):
    name, args = h
    return qnode(26, [{"str": name}, {"arr": quote_named_exprs(args)}])


def quote_flow(f):
    fl = f["flow"]
    return qnode(25, [
        qopt({"str": fl["preLabel"]} if fl["preLabel"] is not None else None),
        quote_head(fl["head"]),
        {"arr": [quote_arm(a) for a in fl["arms"]]}])


def quote_callable(c):
    if "bare" in c:
        return qnode(27, [quote_expr(c["bare"])])
    if "thunk" in c:
        return qnode(28, [])
    if "subflow" in c:
        return qnode(29, [quote_flow(c["subflow"])])
    raise ValueError(f"malformed kcallable: {c!r}")


def quote_prog(p):
    return qnode(30, [
        {"arr": [qpair(n, quote_callable(c)) for n, c in p["graph"]]},
        {"str": p["entry"]},
        {"arr": [qpair(n, quote_val(v)) for n, v in p["args"]]}])
