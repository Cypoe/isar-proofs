import sys
sys.setrecursionlimit(10_000_000)
HOST = r"C:\Users\fabi0\repos\isar-proofs\host"
sys.path.insert(0, HOST)
from reduce import T, K, I, KK, B, S, C, D, app
import reduce as hreduce
from lambda_dialect import parse, bracket_abstract0
import threading
from host_pieces import GRAPH_CD_PIECE, GRAPH_PIECE

def appn(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t

CONS = bracket_abstract0(parse("\\h. \\t. \\n. \\c. c h t"))

def sel(k):
    s = "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"
    return bracket_abstract0(parse(s))

SEL0 = sel(0)
inp = appn(CONS, SEL0, KK)
arm = "(C I ((self (\\a. a)) t))"
A0 = ("\\inp. inp (C I K) (\\h. \\t. h " + " ".join([arm] * 16) + ")")
PHI = f"(\\self. \\i. i ({A0}))"
Y = "(\\f. (\\x. f (x x)) (\\x. f (x x)))"
full = f"({Y} {PHI} (\\a. a))"
prog = bracket_abstract0(parse(full))
term = app(prog, inp)

# tree cd (reduce.py) — but note: tree cd knows S natively; the term has S atoms
# bracket-generated. tree cd's sβ exists, plus C/D are INERT (no rules) —
# different basis than graph.lo! Still tells us about divergence of Y under cd.
box = {}
def _cdt():
    box["r"] = hreduce.reduce_cd(term, fuel=2000)
threading.stack_size(64 << 20)
th = threading.Thread(target=_cdt); th.start(); th.join()
if "r" in box:
    nf, rounds = box["r"]
    print("tree cd nf:", nf, "rounds", rounds)
else:
    print("tree cd crashed/diverged")

# graph.lo on same term for reference
nf, steps, alloc = GRAPH_PIECE.reduce(term, 5_000_000)
print("lo nf:", nf, "steps", steps)
