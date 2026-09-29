import sys
sys.path.insert(0, ".")
import spec_term as st
from lambda_dialect import parse, bracket
from reduce import app, K, I, KK
from graph_runtime import Graph

def term(src):
    return bracket(parse(src))

def bytes4(v):
    return st.bytelist_term(v.to_bytes(4, "little"))

def dec_b4(t):
    return int.from_bytes(st._decode_bytecells(t), "little")

def dec_bytes(t):
    return st._decode_bytecells(t)

def run(src):
    g = Graph(); r = g.import_tree(term(src))
    nf, s = g.reduce(r, fuel=10_000_000)
    return g.export_tree(nf), s

# B4INC tests
for v in [0, 1, 255, 256, 0xFFFF, 0x1000, 0xFFFFFFFE, 0xFFFFFFFF]:
    nf, s = run(f"({st._B4INC} <V>)".replace("<V>", st._b4_src(v)))
    got = dec_b4(nf)
    exp = (v + 1) & 0xFFFFFFFF
    print(f"B4INC {v:#x} -> {got:#x} want {exp:#x} {'OK' if got==exp else 'FAIL'} ({s})")

# LENB4: length of a byte list
bl = st.bytelist_term(bytes(range(40)))
g = Graph(); r = g.import_tree(st._appn(term(st._LENB4), bl))
nf, s = g.reduce(r, fuel=10_000_000)
print("LENB4 40 ->", dec_b4(g.export_tree(nf)), "want 40", s)

# numeral add: k B4INC b4  (b4 + k)
nf, s = run(f"(N5 {st._B4INC} <V>)".replace("N5", st._church_src(7)).replace("<V>", st._b4_src(100)))
print("100+7 ->", dec_b4(nf), "want 107", s)

# NIBS2BYTES: nibble-string "AB" -> bytes
import lambda_dialect as ld
name = st.str_term("AB")   # nibble-string
g = Graph(); r = g.import_tree(st._appn(term(st._NIBS2BYTES), name))
nf, s = g.reduce(r, fuel=10_000_000)
print("NIBS2BYTES 'AB' ->", dec_bytes(g.export_tree(nf)), "want b'AB'", s)

# ZEROFILL 5
nf, s = run(f"({st._ZEROFILL} {st._church_src(5)})")
print("ZEROFILL 5 ->", len(dec_bytes(nf)), "cells", dec_bytes(nf), s)

# APPEND [1,2] [3,4]
a = st.bytelist_term([1,2]); b = st.bytelist_term([3,4])
g = Graph(); r = g.import_tree(st._appn(term(st._APPEND), a, b))
nf, s = g.reduce(r, fuel=10_000_000)
print("APPEND ->", dec_bytes(g.export_tree(nf)), "want [1,2,3,4]", s)

# U64 of 0x11223344
nf, s = run(f"({st._U64} {st._b4_src(0x11223344)})")
print("U64 0x11223344 ->", dec_bytes(nf).hex(), "want 4433221100000000", s)

# ALIGN512 / ALIGN4096
for v in [1, 511, 512, 513, 1000]:
    nf, s = run(f"({st._ALIGN512} {st._b4_src(v)})")
    exp = (v + 511) // 512 * 512
    print(f"ALIGN512 {v} -> {dec_b4(nf)} want {exp} {'OK' if dec_b4(nf)==exp else 'FAIL'} ({s})")
for v in [1, 0x1000, 0x1001, 0x2000, 0x2500]:
    nf, s = run(f"({st._ALIGN4096} {st._b4_src(v)})")
    exp = (v + 0xFFF) // 0x1000 * 0x1000
    print(f"ALIGN4096 {v:#x} -> {dec_b4(nf):#x} want {exp:#x} {'OK' if dec_b4(nf)==exp else 'FAIL'} ({s})")

# EQB4: apply bool to I / K markers -> I if true, K if false
for a, b, exp in [(5,5,True),(5,6,False),(0x12345678,0x12345678,True),(0x12345678,0x12345679,False)]:
    g2 = Graph()
    r2 = g2.import_tree(st._appn(term(f"({st._EQB4} {st._b4_src(a)} {st._b4_src(b)})"), I, KK))
    nf2, s2 = g2.reduce(r2, fuel=100000)
    got = g2.export_tree(nf2)
    is_true = (got.k == K.NORM)   # K=true picks I(NORM); KI=false picks KK(KONST)
    print(f"EQB4 {a:#x} {b:#x} -> is_true={is_true} want={exp} steps {s2}")

# PADTO tgt pos -> zeros(tgt-pos); APPEND acc (PADTO tgt pos) = acc++zeros
acc0 = st.bytelist_term([1, 2])
g3 = Graph()
pad_t = term(f"({st._PADTO} {st._b4_src(8)} {st._b4_src(5)})")
r3 = g3.import_tree(st._appn(term(st._APPEND), acc0, pad_t))
nf3, s3 = g3.reduce(r3, fuel=10_000_000)
got3 = dec_bytes(g3.export_tree(nf3))
print(f"APPEND [1,2] (PADTO 8 5) -> {list(got3)} want [1,2,0,0,0] steps {s3}")
# pos == tgt -> empty pad
g4 = Graph()
r4 = g4.import_tree(st._appn(term(f"({st._PADTO} {st._b4_src(4)} {st._b4_src(4)})")))
nf4, s4 = g4.reduce(r4, fuel=10_000_000)
print(f"PADTO 4 4 -> {list(dec_bytes(g4.export_tree(nf4)))} want [] steps {s4}")

# PADLIST len4 -> zeros(align512(len)-len); edge sweep incl. rem=0
for v in [0, 1, 511, 512, 513, 1024, 1991, 219]:
    g5 = Graph()
    r5 = g5.import_tree(term(f"({st._PADLIST} {st._b4_src(v)})"))
    nf5, s5 = g5.reduce(r5, fuel=10_000_000)
    got5 = len(dec_bytes(g5.export_tree(nf5)))
    want5 = (512 - (v % 512)) % 512
    print(f"PADLIST {v} -> {got5} want {want5} "
          f"{'OK' if got5 == want5 else 'FAIL'} ({s5})")

# JOIN over a list of byte-lists [[1,2],[3],[4,5,6]] -> [1..6]
lst = st._NIL
for ch in reversed([st.bytelist_term([1, 2]), st.bytelist_term([3]),
                    st.bytelist_term([4, 5, 6])]):
    lst = st._appn(st._CONS, ch, lst)
g6 = Graph()
r6 = g6.import_tree(st._appn(term(st._JOIN), lst))
nf6, s6 = g6.reduce(r6, fuel=10_000_000)
got6 = list(dec_bytes(g6.export_tree(nf6)))
print(f"JOIN [[1,2],[3],[4,5,6]] -> {got6} want [1,2,3,4,5,6] "
      f"{'OK' if got6 == [1,2,3,4,5,6] else 'FAIL'} ({s6})")
