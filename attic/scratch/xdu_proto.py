import sys, os
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

def bn(k):
    t = I
    for _ in range(k):
        t = app(B, t)
    return t

def bn_src(k):
    s = "I"
    for _ in range(k):
        s = f"(B {s})"
    return s

def emit_spine(items, tail_src):
    out = tail_src
    for v in reversed(items):
        out = f"(C {bn_src(v)} {out})"
    return out

def xdu_src_echo():
    arms = []
    for k in range(16):
        cont = "((self (\\a. a)) t)"
        arms.append(emit_spine([k], cont))
    A0 = ("\\inp. inp (C I K) "
          "(\\h. \\t. h " + " ".join(arms) + ")")
    PHI = f"(\\self. \\i. i ({A0}))"
    Y = "(\\f. (\\x. f (x x)) (\\x. f (x x)))"
    return f"({Y} {PHI} (\\a. a))"

src = xdu_src_echo()
print("src len:", len(src))
prog = bracket_abstract0(parse(src))
inp = nibbles_to_term(b"Hi")
term = app(prog, inp)
nf, steps, alloc = GRAPH_PIECE.reduce(term, 5_000_000)
print("lo steps", steps, "alloc", alloc)
print("nf:", nf)

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

n = decode(nf)
print("nibs:", [hex(x) for x in n])
rc = n[-1]; out = n[:-1]
print("rc", rc, "out", bytes(out[i] << 4 | out[i + 1]
                            for i in range(0, len(out) - 1, 2)))
