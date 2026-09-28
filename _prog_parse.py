import sys
sys.path.insert(0, r'C:\Users\fabi0\repos\isar-proofs\host')
from lambda_dialect import NAbs, NApp, NVar, NComb
import spec_term as st
import seed, routines_x86_64_win64 as rts
import difflib

# walk program_expr()'s spine structure WITHOUT bracket
t = st.program_expr()

# peel the 5 lambdas
names = []
b = t
while isinstance(b, NAbs):
    names.append(b.param)
    b = b.body
print('binders:', names)

def spine(e):
    out = [e]
    while isinstance(out[0], NApp):
        out.insert(0, out[0].left)
        out[1] = out[1].right
    return out[0], out[1:]

def is_cons(e):
    return isinstance(e, NComb) and e.atom is st._CONS

def is_nil(e):
    return isinstance(e, NComb) and e.atom is st._NIL

# count outer cells
n_frag = n_fuse = 0
depth = 0
b0 = b
while True:
    depth += 1
    if depth > 30:
        print('deep!')
        break
    h, args = spine(b0)
    if is_cons(h):
        n_frag += 1
        # args = [frag, tail]
        print(f'cell {n_frag}: frag-head={type(args[0]).__name__}', )
        b0 = args[1]
    elif isinstance(h, NVar) and h.name == 'fs':
        n_fuse += 1
        ya, na, tail = args
        print(f'fs-select #{n_fuse}: yes={type(ya).__name__} no={type(na).__name__}')
        b0 = tail
    else:
        print('END at', type(b0).__name__, h.name if isinstance(h, NVar) else '')
        break
print('outer cells:', n_frag, 'fs-selects:', n_fuse)

# inner: walk one routine's item splice
