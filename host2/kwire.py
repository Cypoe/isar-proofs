#!/usr/bin/env python3
"""host2.kwire — the .kv wire: load + validate.

.kv is the host2 wire form of the FlowView grammar: JSON, one object
per grammar node, {"<ctor>": payload}.  The canonical WRITER is
tools/DumpKoruFixtures.lean (generated files say so); this module is
the reader + structural check — no silent success on malformed input:
every unknown ctor or wrong field shape refuses at load, naming the
node and the path.

Known ctors:
  KVal:      int | float | bool | str | arr | cell
  KExpr:     lit | var | bin | un | cond | field | index | builtin
  KArmNode:  terminal | jump | invoke | produce | retCtor
  KArm:      arm {branch,catchall,bind,cond,node,conts}
  KFlow:     flow {preLabel,head,arms}
  KCallable: bare | thunk | subflow
  KProg:     {graph,entry,args}
  KResult:   {branch,payload}
"""
from __future__ import annotations

import json
import os
import sys

_HOST2 = os.path.dirname(os.path.abspath(__file__))
_HOST = os.path.join(os.path.dirname(_HOST2), "host")
for _p in (_HOST2, _HOST):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from toolchain import NotRealized  # noqa: E402

_BINOPS = {"add", "sub", "mul", "div", "mod", "eq", "ne", "lt", "le",
           "gt", "ge", "and", "or", "concat"}
_UNOPS = {"not", "neg"}


def load(path):
    """Load a .kv JSON file; refuse unreadable/invalid JSON by name."""
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        raise NotRealized(f"koru wire: cannot load {path!r}: {e}")


def _ctor(node, path):
    if not isinstance(node, dict) or len(node) != 1:
        raise NotRealized(f"koru wire: {path}: node must be a single-"
                          f"ctor object, got {node!r:.60}")
    return next(iter(node))


def validate_val(v, path="val"):
    c = _ctor(v, path)
    if c == "int":
        assert isinstance(v["int"], int) and not isinstance(v["int"], bool), \
            f"{path}.int not an int"
    elif c == "float":
        n, d = v["float"]
        assert isinstance(n, int) and isinstance(d, int), f"{path}.float"
    elif c == "bool":
        assert isinstance(v["bool"], bool), f"{path}.bool"
    elif c == "str":
        assert isinstance(v["str"], str), f"{path}.str"
    elif c == "arr":
        for i, x in enumerate(v["arr"]):
            validate_val(x, f"{path}.arr[{i}]")
    elif c == "cell":
        for n, x in v["cell"]:
            assert isinstance(n, str), f"{path}.cell field name"
            validate_val(x, f"{path}.cell.{n}")
    else:
        raise NotRealized(f"koru wire: {path}: unknown KVal ctor {c!r}")


def validate_expr(e, path="expr"):
    c = _ctor(e, path)
    if c == "lit":
        validate_val(e["lit"], f"{path}.lit")
    elif c == "var":
        assert isinstance(e["var"], str), f"{path}.var"
    elif c == "bin":
        op, a, b = e["bin"]
        assert op in _BINOPS, f"{path}.bin op {op!r} not in {_BINOPS}"
        validate_expr(a, f"{path}.bin.l")
        validate_expr(b, f"{path}.bin.r")
    elif c == "un":
        op, a = e["un"]
        assert op in _UNOPS, f"{path}.un op {op!r} not in {_UNOPS}"
        validate_expr(a, f"{path}.un.e")
    elif c == "cond":
        for i, x in enumerate(e["cond"]):
            validate_expr(x, f"{path}.cond[{i}]")
    elif c == "field":
        o, n = e["field"]
        validate_expr(o, f"{path}.field.o")
        assert isinstance(n, str), f"{path}.field name"
    elif c == "index":
        o, i = e["index"]
        validate_expr(o, f"{path}.index.o")
        validate_expr(i, f"{path}.index.i")
    elif c == "builtin":
        n, args = e["builtin"]
        assert isinstance(n, str), f"{path}.builtin name"
        for i, x in enumerate(args):
            validate_expr(x, f"{path}.builtin[{n}][{i}]")
    else:
        raise NotRealized(f"koru wire: {path}: unknown KExpr ctor {c!r}")


def _named_exprs(xs, path):
    for n, e in xs:
        assert isinstance(n, str), f"{path}: arg name"
        validate_expr(e, f"{path}.{n}")


def validate_arm_node(node, path="armnode"):
    c = _ctor(node, path)
    if c == "terminal":
        pass
    elif c in ("jump", "invoke"):
        t, args = node[c]
        assert isinstance(t, str), f"{path}.{c} target"
        _named_exprs(args, f"{path}.{c}")
    elif c == "produce":
        validate_expr(node["produce"], f"{path}.produce")
    elif c == "retCtor":
        br, e = node["retCtor"]
        assert isinstance(br, str), f"{path}.retCtor branch"
        validate_expr(e, f"{path}.retCtor")
    else:
        raise NotRealized(f"koru wire: {path}: unknown KArmNode ctor {c!r}")


def validate_arm(a, path="arm"):
    c = _ctor(a, path)
    assert c == "arm", f"{path}: expected 'arm', got {c!r}"
    arm = a["arm"]
    assert isinstance(arm["branch"], str), f"{path}.branch"
    assert isinstance(arm["catchall"], bool), f"{path}.catchall"
    if arm["bind"] is not None:
        assert isinstance(arm["bind"], str), f"{path}.bind"
    if arm["cond"] is not None:
        validate_expr(arm["cond"], f"{path}.cond")
    if arm["node"] is not None:
        validate_arm_node(arm["node"], f"{path}.node")
    for i, x in enumerate(arm["conts"]):
        validate_arm(x, f"{path}.conts[{i}]")


def validate_callable(cnode, path="callable"):
    c = _ctor(cnode, path)
    if c == "bare":
        validate_expr(cnode["bare"], f"{path}.bare")
    elif c == "thunk":
        pass
    elif c == "subflow":
        fl = cnode["subflow"]["flow"]
        if fl["preLabel"] is not None:
            assert isinstance(fl["preLabel"], str), f"{path}.preLabel"
        hn, hargs = fl["head"]
        assert isinstance(hn, str), f"{path}.head name"
        _named_exprs(hargs, f"{path}.head")
        for i, a in enumerate(fl["arms"]):
            validate_arm(a, f"{path}.arms[{i}]")
    else:
        raise NotRealized(f"koru wire: {path}: unknown KCallable ctor {c!r}")


def validate_prog(p, path="prog"):
    assert isinstance(p, dict) and set(p) == {"graph", "entry", "args"}, \
        f"{path}: expected keys graph/entry/args"
    for n, c in p["graph"]:
        assert isinstance(n, str), f"{path}.graph name"
        validate_callable(c, f"{path}.graph[{n}]")
    assert isinstance(p["entry"], str), f"{path}.entry"
    for n, v in p["args"]:
        assert isinstance(n, str), f"{path}.args name"
        validate_val(v, f"{path}.args.{n}")


def validate_result(r, path="result"):
    assert isinstance(r, dict) and set(r) == {"branch", "payload"}, \
        f"{path}: expected keys branch/payload"
    if r["branch"] is not None:
        assert isinstance(r["branch"], str), f"{path}.branch"
    if r["payload"] is not None:
        validate_val(r["payload"], f"{path}.payload")
