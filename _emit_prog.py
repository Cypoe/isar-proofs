"""Emit programOf as Lean: programT (5-lambda .var-form), progBodyOpen
(param-token form), progSegs (List OSeg model).  Python-side verifies
the segment decomposition rebuilds program_expr()'s spine exactly, so
`progBody_eq := rfl` is safe."""
import sys
sys.path.insert(0, r'C:\Users\fabi0\repos\isar-proofs\host')
from lambda_dialect import NAbs, NApp, NVar, NComb
from reduce import K, I, KK, S, B, C, D
import spec_term as st
import routines_x86_64_win64 as rts

ATOM_MAP = {id(st._CONS): 'conssL', id(st._NIL): 'nilL',
            id(st._PAIR): 'pairSrcL', id(K): 'klL', id(KK): 'klL',
            id(I): 'idL', id(S): 'sCombL', id(B): 'bCombL',
            id(C): 'cCombL', id(D): 'dCombL'}
for k, sel in enumerate(st._SELECTORS):
    ATOM_MAP[id(sel)] = f'(nibLit {k})'


def walkT(t):
    if id(t) in ATOM_MAP:
        return ATOM_MAP[id(t)]
    assert t.k == K.APP, f'unknown T atom {t}'
    return f'(aps {walkT(t.l)} [{walkT(t.r)}])'


REN = {'fs': 'fsT', 'fuel': 'fuelT', 'rbb': 'rbbT', 'cb': 'cbT',
       'nb': 'nbT'}


def emit(e, env, ren, depth=0):
    if isinstance(e, NAbs):
        return f'(.abs {emit(e.body, env + [e.param], ren, depth + 1)})'
    if isinstance(e, NApp):
        h, args = spine(e)
        return f'(aps {emit(h, env, ren, depth)} [' + \
            ', '.join(emit(a, env, ren, depth) for a in args) + '])'
    if isinstance(e, NVar):
        if e.name not in env:
            raise KeyError(f'free var {e.name}')
        i = env[::-1].index(e.name)
        if i >= depth:
            slot = env[len(env) - 1 - i]
            return ren[slot]
        return f'(.var {i})'
    if isinstance(e, NComb):
        return walkT(e.atom)
    raise TypeError(e)


def emit_var(e, env):
    """to_lean: all bound names -> .var index."""
    if isinstance(e, NAbs):
        return f'(.abs {emit_var(e.body, env + [e.param])})'
    if isinstance(e, NApp):
        h, args = spine(e)
        return f'(aps {emit_var(h, env)} [' + \
            ', '.join(emit_var(a, env) for a in args) + '])'
    if isinstance(e, NVar):
        return f'(.var {env[::-1].index(e.name)})'
    if isinstance(e, NComb):
        return walkT(e.atom)
    raise TypeError(e)


def spine(e):
    out = [e]
    while isinstance(out[0], NApp):
        out.insert(0, out[0].left)
        out[1] = out[1].right
    return out[0], out[1:]


def is_atom(e, atom):
    return isinstance(e, NComb) and e.atom is atom


def is_id_abs(f):
    return isinstance(f, NAbs) and isinstance(f.body, NVar) \
        and f.body.name == f.param


def cons_items(e):
    """walk a CONS-chain to its non-CONS tail; (items, tail_expr)."""
    items = []
    while True:
        h, args = spine(e)
        if is_atom(h, st._CONS):
            items.append(args[0])
            e = args[1]
            continue
        return items, e


def frag_items(f):
    """λt. cons-chain ending at bound t -> item-NExpr list."""
    assert isinstance(f, NAbs), f
    items, tail = cons_items(f.body)
    assert isinstance(tail, NVar) and tail.name == f.param, tail
    return items


def fj_items(fj):
    """λfv. λt. cons-chain -> item list."""
    assert isinstance(fj, NAbs)
    inner = fj.body
    assert isinstance(inner, NAbs)
    return frag_items(inner)


def decomp_frag(frag):
    """_splice result -> [ ('cell',it) | ('fuse',a,b) | ('fuelR',a) ]"""
    segs = []
    e = frag
    while True:
        h, args = spine(e)
        if is_atom(h, st._CONS):
            segs.append(('cell', args[0]))
            e = args[1]
            continue
        if is_atom(e, st._NIL):
            return segs
        if isinstance(h, NVar) and h.name == 'fs':
            ya, na, e = args
            segs.append(('fuse', frag_items(ya), frag_items(na)))
            continue
        if isinstance(h, NVar) and h.name == 'fuel':
            fn, fj, e = args
            segs.append(('fuelR', fj_items(fj)))
            continue
        raise AssertionError(('frag walk', type(e).__name__,
                              type(h).__name__))


# ---------- rebuild (Python mirror of osegChain) --------------------
def ncons(h, t):
    return NApp(NApp(NComb(st._CONS), h), t)


def rebuild_pseg(seg, tail):
    tag = seg[0]
    if tag == 'cell':
        return ncons(seg[1], tail)
    if tag == 'fuse':
        fa = NAbs('t', list_chain(seg[1], NVar('t')))
        fb = NAbs('t', list_chain(seg[2], NVar('t')))
        return NApp(NApp(NApp(NVar('fs'), fa), fb), tail)
    if tag == 'fuelR':
        fn = NAbs('t', NVar('t'))
        fj = NAbs('fv', NAbs('t', list_chain(seg[1], NVar('t'))))
        return NApp(NApp(NApp(NVar('fuel'), fn), fj), tail)
    raise AssertionError(seg)


def list_chain(items, tail):
    for it in reversed(items):
        tail = ncons(it, tail)
    return tail


def rebuild_pchain(segs, tail):
    for s in reversed(segs):
        tail = rebuild_pseg(s, tail)
    return tail


def rebuild_oseg(seg, tail):
    tag = seg[0]
    if tag == 'frag':
        return ncons(rebuild_pchain(seg[1], NComb(st._NIL)), tail)
    if tag == 'stS':
        yes = NAbs('t', ncons(list_chain(seg[1], NComb(st._NIL)),
                              NVar('t')))
        return NApp(NApp(NApp(NVar('fs'), yes),
                         NAbs('t', NVar('t'))), tail)
    if tag == 'bDS':
        no = NAbs('t', ncons(list_chain(seg[1], NComb(st._NIL)),
                             NVar('t')))
        return NApp(NApp(NApp(NVar('fs'), NAbs('t', NVar('t'))),
                         no), tail)
    raise AssertionError(seg)


def eq(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, NAbs):
        return eq(a.body, b.body)
    if isinstance(a, NApp):
        return eq(a.left, b.left) and eq(a.right, b.right)
    if isinstance(a, NVar):
        return a.name == b.name
    if isinstance(a, NComb):
        return a.atom is b.atom
    raise TypeError(a)


prog = st.program_expr()
b = prog
binders = []
while isinstance(b, NAbs):
    binders.append(b.param)
    b = b.body
assert binders == ['fs', 'fuel', 'rbb', 'cb', 'nb']

osegs = []
routine_names = []
nb = b
for name in rts.ROUTINES:
    h, args = spine(nb)
    if is_atom(h, st._CONS):
        frag, nb = args
        osegs.append(('frag', decomp_frag(frag)))
        routine_names.append(name)
    elif isinstance(h, NVar) and h.name == 'fs':
        ya, na, nb = args
        if is_id_abs(na):                    # st_s
            inner = frag_items(ya)
            assert len(inner) == 1
            its, t2 = cons_items(inner[0])
            assert is_atom(t2, st._NIL)
            osegs.append(('stS', its))
        elif is_id_abs(ya):                  # build_ds
            inner = frag_items(na)
            assert len(inner) == 1
            its, t2 = cons_items(inner[0])
            assert is_atom(t2, st._NIL)
            osegs.append(('bDS', its))
        else:
            raise AssertionError('outer fs shape')
        routine_names.append(name)
    else:
        raise AssertionError(('outer', name, type(h)))
assert is_atom(nb, st._NIL)
print('routines:', routine_names)

# round-trip check: rebuild must equal the emitted spine
rebuilt = nb = NComb(st._NIL)
for s in reversed(osegs):
    rebuilt = rebuild_oseg(s, rebuilt)
assert eq(rebuilt, b), 'rebuild mismatch'
print('round-trip OK; segs:', len(osegs),
      'cells:', sum(1 for s in osegs if s[0] == 'frag'),
      'inner segs:', sum(len(s[1]) for s in osegs if s[0] == 'frag'))

# ---------- serialize ----------------------------------------------
OUTER = ['fs', 'fuel', 'rbb', 'cb', 'nb']

def emit_item(e, local):
    return emit(e, OUTER + local, REN, len(local))


def emit_seg(seg):
    tag = seg[0]
    if tag == 'cell':
        return f'(.cell {emit_item(seg[1], [])})'
    if tag == 'fuse':
        a = ', '.join(emit_item(i, ['t']) for i in seg[1])
        bb = ', '.join(emit_item(i, ['t']) for i in seg[2])
        return f'(.fuse [{a}] [{bb}])'
    if tag == 'fuelR':
        a = ', '.join(emit_item(i, ['fv', 't']) for i in seg[1])
        return f'(.fuelR [{a}])'
    raise AssertionError(seg)


def emit_oseg(seg):
    tag = seg[0]
    if tag == 'frag':
        return '(PSeg.frag-x ' + 'placeholder' + ')'
    if tag == 'stS':
        its = ', '.join(emit_item(i, ['t']) for i in seg[1])
        return f'(.stS [{its}])'
    if tag == 'bDS':
        its = ', '.join(emit_item(i, ['t']) for i in seg[1])
        return f'(.bDS [{its}])'
    raise AssertionError(seg)


seg_lists = []
for seg in osegs:
    if seg[0] == 'frag':
        seg_lists.append('(.frag [' +
                         ', '.join(emit_seg(s) for s in seg[1]) + '])')
    else:
        seg_lists.append(emit_oseg(seg))

with open('_prog_emit.txt', 'w', encoding='utf-8') as f:
    f.write('def progSegs (rbbT cbT nbT : LTerm) : List OSeg :=\n')
    f.write('  [' + ',\n   '.join(seg_lists) + ']\n\n')
    f.write('def progBodyOpen (fsT fuelT rbbT cbT nbT : LTerm) : '
            'LTerm :=\n')
    f.write('  ' + emit(b, OUTER, REN) + '\n\n')
    f.write('def programT : LTerm :=\n')
    f.write('  ' + emit_var(prog, []) + '\n')
print('emitted', sum(len(s) for s in seg_lists), 'seg-chars')
