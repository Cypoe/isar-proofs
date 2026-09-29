import sys
sys.setrecursionlimit(10_000_000)
HOST = r"C:\Users\fabi0\repos\isar-proofs\host"
sys.path.insert(0, HOST)
from reduce import T, K, I, KK, B, S, C, D, app
from lambda_dialect import parse, bracket_abstract0
from host_pieces import GRAPH_PIECE, GRAPH_CD_PIECE
import threading

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

# church numeral, iterative: c_k = S A (S A (... (K I)))
_A = appn(S, app(KK, S), appn(S, app(KK, KK), I))
def church(k: int) -> T:
    t = app(KK, I)          # c_0 = K I = \f x. x
    for _ in range(k):
        t = appn(S, _A, t)
    return t

def bn_src(k):
    s = "I"
    for _ in range(k):
        s = f"(B {s})"
    return s

def spine(vals, tail):
    out = tail
    for v in reversed(vals):
        out = f"(C {bn_src(v)} {out})"
    return out

def nsel(N, i):
    return "(" + "".join(f"\\x{j}. " for j in range(N)) + f"x{i})"

def to_lambda(xdu):
    states = list(xdu["states"].keys())
    idx = {s: i for i, s in enumerate(states)}
    N = len(states)
    E, H = [], []
    for s in states:
        st = xdu["states"][s]
        on, eof = st["on"], st["eof"]
        spine_j = spine([int(it, 16) for it in eof["emit"]],
                        f"(C {bn_src(eof['halt'])} K)")
        E.append(f"(\\o2. o2 {spine_j})")
        arms = []
        for k in range(16):
            rule = on.get(f"{k:x}", on.get("*"))
            vals = [(k if it == "$in" else int(it, 16))
                    for it in rule["emit"]]
            out2 = "\\r. o " + spine(vals, "r")
            arms.append(f"(\\k2. k2 t {nsel(N, idx[rule['next']])} ({out2}))")
        H.append("(\\h. \\t. \\o. h " + " ".join(arms) + ")")
    E_sel = "(st " + " ".join(E) + ")"
    H_sel = "(st " + " ".join(H) + ")"
    STEP = ("\\acc. acc (\\tl. \\st. \\o. tl (" + E_sel + " o) "
            "(\\h. \\t. " + H_sel + " h t o))")
    return ("(\\l. \\n. n (" + STEP + ") "
            "(\\k. k l " + nsel(N, idx[xdu["start"]]) + " (\\r. r)))")

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
                "states": {"s0": {"on": {**{f"{k:x}": {"emit": ["3", f"{k:x}"], "next": "s0"}
                                        for k in range(10)},
                                       **{f"{k:x}": {"emit": ["6", f"{k-9:x}"], "next": "s0"}
                                        for k in range(10, 16)}},
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

threading.stack_size(64 << 20)
for name, xdu in XDUS.items():
    src = to_lambda(xdu)
    prog = bracket_abstract0(parse(src))
    for data in (b"Hi", b"AB", b""):
        n = 2 * len(data) + 1
        term = appn(prog, nibbles_to_term(data), church(n))
        nf, steps, alloc = GRAPH_PIECE.reduce(term, 5_000_000)
        got = term_to_nibbles(nf)
        exp = interpret(xdu, data)
        box = {}
        def _cd():
            box["r"] = GRAPH_CD_PIECE.reduce(term, 20_000)
        th = threading.Thread(target=_cd); th.start(); th.join()
        nfcd, rounds, alloccd = box["r"]
        gotcd = term_to_nibbles(nfcd)
        print(f"{name} {data}: lo={got} exp={exp} "
              f"{'OK' if got == exp else 'FAIL'} steps={steps} alloc={alloc} | "
              f"cd={gotcd} {'OK' if gotcd == exp else 'FAIL'} rounds={rounds}")
    print(f"  src len {len(src)}")
