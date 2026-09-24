import sys, os, json
sys.setrecursionlimit(200_000)
HOST = r"C:\Users\fabi0\repos\isar-proofs\host"
sys.path.insert(0, HOST)
from reduce import T, K, I, KK, B, S, C, D, app
from lambda_dialect import parse, bracket_abstract0
from host_pieces import GRAPH_PIECE, GRAPH_CD_PIECE

def appn(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t

CONS = bracket_abstract0(parse("\\h. \\t. \\n. \\c. c h t"))
NIL = KK

def sel(k):
    src = "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"
    return bracket_abstract0(parse(src))

SELS = [sel(k) for k in range(16)]

def nibbles_to_term(data: bytes) -> T:
    t = NIL
    nibs = []
    for b in data:
        nibs += [b >> 4, b & 15]
    for k in reversed(nibs):
        t = appn(CONS, SELS[k], t)
    return t

def bn_src(k):
    s = "I"
    for _ in range(k):
        s = f"(B {s})"
    return s

def to_lambda(xdu):
    states = list(xdu["states"].keys())
    idx = {s: i for i, s in enumerate(states)}
    N = len(states)
    sel_start = "(" + "".join(f"\\a{i}. " for i in range(N)) + f"a{idx[xdu['start']]})"
    sels = {s: "(" + "".join(f"\\a{i}. " for i in range(N)) + f"a{i})"
            for s, i in idx.items()}

    def spine_items(rule, pos_k):
        vals = []
        for it in rule["emit"]:
            vals.append(pos_k if it == "$in" else int(it, 16))
        return vals

    def spine(vals, tail):
        out = tail
        for v in reversed(vals):
            out = f"(C {bn_src(v)} {out})"
        return out

    A = []
    for s in states:
        st = xdu["states"][s]
        on = st["on"]
        eof = st["eof"]
        eof_src = spine([int(it, 16) for it in eof["emit"]],
                        f"(C {bn_src(eof['halt'])} K)")
        arms = []
        for k in range(16):
            key = f"{k:x}"
            rule = on.get(key, on.get("*"))
            cont = f"((self {sels[rule['next']]}) t)"
            arms.append(spine(spine_items(rule, k), cont))
        A.append("\\inp. inp " + eof_src +
                 " (\\h. \\t. h " + " ".join(arms) + ")")
    PHI = "(\\self. \\i. i " + " ".join(f"({a})" for a in A) + ")"
    Y = "(\\f. (\\x. f (x x)) (\\x. f (x x)))"
    return f"({Y} {PHI} {sel_start})"

def decode(t):
    nibs = []
    while (t.k == K.APP and t.l is not None and t.l.k == K.APP
           and t.l.l is not None and t.l.l.k == K.SWAP):
        h = t.l.r
        k = 0
        while (h.k == K.APP and h.l is not None and h.l.k == K.COMP):
            k += 1
            h = h.r
        assert h.k == K.NORM, f"bad nib {h}"
        nibs.append(k)
        t = t.r
    assert t.k == K.KONST, f"bad tail {t}"
    return nibs

def term_to_nibbles(nf):
    n = decode(nf)
    rc = n[-1]
    out = n[:-1]
    if len(out) & 1:
        rc = 3
        out = out[:-1]
    return bytes(out[i] << 4 | out[i + 1] for i in range(0, len(out), 2)), rc

def interpret(xdu, data):
    nibs = []
    for b in data:
        nibs += [b >> 4, b & 15]
    out = []
    st = xdu["start"]
    for k in nibs:
        rule = xdu["states"][st]["on"].get(f"{k:x}",
                 xdu["states"][st]["on"].get("*"))
        for it in rule["emit"]:
            out.append(k if it == "$in" else int(it, 16))
        st = rule["next"]
    eof = xdu["states"][st]["eof"]
    for it in eof["emit"]:
        out.append(int(it, 16))
    rc = eof["halt"]
    if len(out) & 1:
        rc = 3
        out = out[:-1]
    return bytes(out[i] << 4 | out[i + 1] for i in range(0, len(out), 2)), rc

XDUS = {
    "echo": {"name": "echo", "alphabet": "nibble", "start": "s0",
             "states": {"s0": {"on": {"*": {"emit": ["$in"], "next": "s0"}},
                               "eof": {"emit": [], "halt": 0}}}},
    "hexdump": {"name": "hexdump", "alphabet": "nibble", "start": "s0",
                "states": {"s0": {"on": {f"{k:x}": {"emit": ["3", f"{k:x}"], "next": "s0"}
                                        for k in range(10)} |
                                       {f"{k:x}": {"emit": ["6", f"{k-9:x}"], "next": "s0"}
                                        for k in range(10, 16)},
                                  "eof": {"emit": [], "halt": 0}}}},
    "drop0": {"name": "drop0", "alphabet": "nibble", "start": "s0",
              "states": {"s0": {"on": {"0": {"emit": [], "next": "s0"},
                                      "*": {"emit": ["$in"], "next": "s0"}},
                                "eof": {"emit": [], "halt": 0}}}},
    "toggle": {"name": "toggle", "alphabet": "nibble", "start": "s0",
               "states": {"s0": {"on": {"*": {"emit": ["$in"], "next": "s1"}},
                                 "eof": {"emit": [], "halt": 0}},
                          "s1": {"on": {"*": {"emit": [], "next": "s0"}},
                                 "eof": {"emit": [], "halt": 0}}}},
}

for name, xdu in XDUS.items():
    src = to_lambda(xdu)
    prog = bracket_abstract0(parse(src))
    for data in (b"Hi", b"AB"):
        term = app(prog, nibbles_to_term(data))
        nf, steps, alloc = GRAPH_PIECE.reduce(term, 5_000_000)
        got = term_to_nibbles(nf)
        exp = interpret(xdu, data)
        box = {}
        def _cd():
            box["r"] = GRAPH_CD_PIECE.reduce(term, 10_000)
        import threading
        threading.stack_size(64 << 20)
        th = threading.Thread(target=_cd)
        th.start(); th.join()
        nfcd, rounds, alloccd = box["r"]
        gotcd = term_to_nibbles(nfcd)
        print(f"{name} {data}: lo={got} exp={exp} {'OK' if got == exp else 'FAIL'} "
              f"steps={steps} alloc={alloc} | cd={gotcd} "
              f"{'OK' if gotcd == exp else 'FAIL'} rounds={rounds}")
    print(f"  src len {len(src)}")
