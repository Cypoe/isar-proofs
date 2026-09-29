import sys
sys.setrecursionlimit(10_000_000)
HOST = r"C:\Users\fabi0\repos\isar-proofs\host"
sys.path.insert(0, HOST)
from reduce import T, K, I, KK, B, S, C, D, app
from lambda_dialect import parse, bracket_abstract0
import threading
from host_pieces import GRAPH_CD_PIECE

def depth(t):
    # iterative depth
    best = 0
    stack = [(t, 1)]
    while stack:
        n, d = stack.pop()
        if d > best:
            best = d
        if n.k == K.APP:
            stack.append((n.l, d + 1))
            stack.append((n.r, d + 1))
    return best

def size(t):
    c = 0
    stack = [t]
    seen = set()
    while stack:
        n = stack.pop()
        i = id(n)
        if i in seen:
            continue
        seen.add(i)
        c += 1
        if n.k == K.APP:
            stack.append(n.l); stack.append(n.r)
    return c

src = "(\\f. (\\x. f (x x)) (\\x. f (x x)))"
t = bracket_abstract0(parse(src))
print("Y depth", depth(t), "size", size(t))

# minimal: Y applied to (\self. \i. i (\inp. inp (C I K) (\h.\t. h A..))) on tiny input
CONS = bracket_abstract0(parse("\\h. \\t. \\n. \\c. c h t"))
def appn(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t

def sel(k):
    s = "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"
    return bracket_abstract0(parse(s))

SEL0 = sel(0)
inp = appn(CONS, SEL0, KK)   # [nib0]
arm = "(C I ((self (\\a. a)) t))"
A0 = ("\\inp. inp (C I K) (\\h. \\t. h " + " ".join([arm] * 16) + ")")
PHI = f"(\\self. \\i. i ({A0}))"
Y = "(\\f. (\\x. f (x x)) (\\x. f (x x)))"
full = f"({Y} {PHI} (\\a. a))"
prog = bracket_abstract0(parse(full))
term = app(prog, inp)
print("prog depth", depth(prog), "size", size(prog))
print("term depth", depth(term), "size", size(term))

box = {}
def _cd():
    box["r"] = GRAPH_CD_PIECE.reduce(term, 10_000)
threading.stack_size(256 << 20)
th = threading.Thread(target=_cd)
th.start(); th.join()
if "r" in box:
    nf, rounds, alloc = box["r"]
    print("cd nf:", nf, "rounds", rounds, "alloc", alloc)
else:
    print("cd crashed")
