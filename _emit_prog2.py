"""Emit closed_progSegs as a generated proof TERM (forall_mem_cons +
closed_appD and-trees + closed_subst for fuelR subst-clauses) — no
simp over the giant literals.  Also emits progBodyVar / programT /
progBodyOpenShift / progBodyShift_eq / program_open.  Reuses the
osegs decomposition from _emit_prog."""
import sys
sys.path.insert(0, r'C:\Users\fabi0\repos\isar-proofs\host')
import _emit_prog as E
from lambda_dialect import NAbs, NApp, NVar, NComb
import spec_term as st

osegs = E.osegs
emit = E.emit
emit_var = E.emit_var
spine = E.spine
REN = E.REN
OUTER = E.OUTER
walkT = E.walkT

PARAM_HYP = {'fs': 'hfs', 'fuel': 'hfu', 'rbb': 'hr',
             'cb': 'hc', 'nb': 'hn'}
ATOM_CLEM = dict(E.ATOM_MAP)


def atom_cproof(atom, d):
    a = ATOM_CLEM[id(atom)]
    a = a.strip('()')
    if a.startswith('nibLit'):
        return f'(closed_nibLit_any {a.split()[1]} {d})'
    return f'(closed_{a}_any {d})'


def term_cproof(t, d):
    """closedness proof for a walkT'd SKI T-atom (mirrors walkT)."""
    if id(t) in ATOM_CLEM:
        return atom_cproof(t, d)
    assert t.k.name == 'APP', f'unmapped T leaf {t.k}'
    return (f'(closed_appD {d} {term_cproof(t.l, d)} '
            f'{term_cproof(t.r, d)})')


def emit_env(e, env, local):
    return emit(e, env, REN, len(local))


def cproof(e, env, local, d):
    """proof-term for `closed d <emit e under env>`."""
    if isinstance(e, NAbs):
        return cproof(e.body, env + [e.param],
                      local + [e.param], d + 1)
    if isinstance(e, NApp):
        h, args = spine(e)
        p = cproof(h, env, local, d)
        for a in args:
            p = f'(closed_appD {d} {p} {cproof(a, env, local, d)})'
        return p
    if isinstance(e, NVar):
        i = env[::-1].index(e.name)
        if i >= len(local):
            hyp = PARAM_HYP[env[len(env) - 1 - i]]
            return f'(closed_mono {hyp} (Nat.zero_le {d}))'
        return f'(by decide : closed {d} (.var {i}) = true)'
    if isinstance(e, NComb):
        return term_cproof(e.atom, d)
    raise TypeError(e)


# ---------- fuelR subst-clause -------------------------------------
class _ShiftV:
    pass


SHIFTV = _ShiftV()


def subst_fv(e):
    """NVar('fv') -> SHIFTV marker; assert no 't' refs."""
    if isinstance(e, NAbs):
        assert e.param != 'fv'
        return NAbs(e.param, subst_fv(e.body))
    if isinstance(e, NApp):
        return NApp(subst_fv(e.left), subst_fv(e.right))
    if isinstance(e, NVar):
        if e.name == 'fv':
            return SHIFTV
        assert e.name != 't', 'item references tail var'
        return e
    return e


def emitS(e, env, local):
    if e is SHIFTV:
        return '(shift 1 0 v)'
    if isinstance(e, NAbs):
        return f'(.abs {emitS(e.body, env + [e.param], local + [e.param])})'
    if isinstance(e, NApp):
        h, args = spine(e)
        return f'(aps {emitS(h, env, local)} [' + \
            ', '.join(emitS(a, env, local) for a in args) + '])'
    if isinstance(e, NVar):
        i = env[::-1].index(e.name)
        if i >= len(local):
            return REN[env[len(env) - 1 - i]]
        return f'(.var {i})'
    if isinstance(e, NComb):
        return walkT(e.atom)
    raise TypeError(e)


def cproofS(e, env, local, d):
    if e is SHIFTV:
        return ('(by show closed 0 (shift 1 0 v) = true; '
                'rw [shift_of_closed0 hv]; exact hv)')
    if isinstance(e, NAbs):
        return cproofS(e.body, env + [e.param],
                       local + [e.param], d + 1)
    if isinstance(e, NApp):
        h, args = spine(e)
        p = cproofS(h, env, local, d)
        for a in args:
            p = f'(closed_appD {d} {p} {cproofS(a, env, local, d)})'
        return p
    if isinstance(e, NVar):
        i = env[::-1].index(e.name)
        if i >= len(local):
            hyp = PARAM_HYP[env[len(env) - 1 - i]]
            return f'(closed_mono {hyp} (Nat.zero_le {d}))'
        return f'(by decide : closed {d} (.var {i}) = true)'
    if isinstance(e, NComb):
        return term_cproof(e.atom, d)
    raise TypeError(e)


# ---------- forall chains ------------------------------------------
def forall_chain(items, mk):
    t = 'fun x hx => nomatch hx'
    for i in reversed(range(len(items))):
        t = f'List.forall_mem_cons.mpr ⟨{mk(items[i])}, {t}⟩'
    return t


CELL_ENV = []
FUSE_ENV = ['t']
FUEL_ENV = ['fv', 't']


def pseg_proof(seg):
    tag = seg[0]
    if tag == 'cell':
        return cproof(seg[1], OUTER + CELL_ENV, CELL_ENV, 0)
    if tag == 'fuse':
        pa = forall_chain(
            seg[1], lambda i: cproof(i, OUTER + FUSE_ENV, FUSE_ENV, 0))
        pb = forall_chain(
            seg[2], lambda i: cproof(i, OUTER + FUSE_ENV, FUSE_ENV, 0))
        return f'⟨{pa}, {pb}⟩'
    if tag == 'fuelR':
        def mk(i):
            env = OUTER + FUEL_ENV
            p2 = cproof(i, env, FUEL_ENV, 2)
            sub = subst_fv(i)
            ps = cproofS(sub, env, FUEL_ENV, 0)
            return (f'⟨{p2}, fun (v : LTerm) '
                    f'(hv : closed 0 v = true) => {ps}⟩')
        return forall_chain(seg[1], mk)
    raise AssertionError(seg)


def oseg_proof(seg):
    tag = seg[0]
    if tag == 'frag':
        return forall_chain(seg[1], pseg_proof)
    if tag in ('stS', 'bDS'):
        return forall_chain(
            seg[1], lambda i: cproof(i, OUTER + ['t'], ['t'], 0))
    raise AssertionError(seg)


def emit_stuck(e, env, local):
    """the `hsteps`-evaluated body: outer params become stuck
    `subst p i (subst ... (shift i 0 X))` chains — `subst` descends
    until it hits a `shift`-leaf, where the meta-application stays
    stuck.  Each pending wrapper carries the param's own .var-index."""
    if isinstance(e, NAbs):
        inner = emit_stuck(e.body, env + [e.param],
                           local + [e.param])
        return f'(.abs {inner})'
    if isinstance(e, NApp):
        h, args = spine(e)
        return f'(aps {emit_stuck(h, env, local)} [' + \
            ', '.join(emit_stuck(a, env, local) for a in args) + '])'
    if isinstance(e, NVar):
        i = env[::-1].index(e.name)
        if i >= len(local):
            slot = env[len(env) - 1 - i]
            t = f'(shift {i} 0 {REN[slot]})'
            # wrap with the later substs (OUTER order fs..nb; fs is
            # innermost — later params wrap the earlier shift-leaf)
            for p in OUTER[OUTER.index(slot) + 1:]:
                ip = env[::-1].index(p)
                t = f'(subst {REN[p]} {ip} {t})'
            return t
        return f'(.var {i})'
    if isinstance(e, NComb):
        return walkT(e.atom)
    raise TypeError(e)


prog_proof = forall_chain(osegs, oseg_proof)
print('proof-term chars:', len(prog_proof))

with open('_prog_proof.txt', 'w', encoding='utf-8') as f:
    f.write(prog_proof)

with open('_prog_defs.txt', 'w', encoding='utf-8') as f:
    f.write('set_option maxRecDepth 10000 in\n')
    f.write('set_option maxHeartbeats 16000000 in\n')
    f.write('/-- the program body in `.var`-form (the five outer\n'
            '    lambdas of `programT` bind `fs`/`fuel`/`rbb`/`cb`/'
            '`nb`). -/\n')
    f.write('def progBodyVar : LTerm :=\n')
    f.write('  ' + emit_var(E.b, OUTER) + '\n\n')
    f.write('/-- `programOf`\'s routine-list spine: '
            '`λfs λfuel λrbb λcb λnb. progBodyVar`. -/\n')
    f.write('def programT : LTerm :=\n')
    f.write('  .abs (.abs (.abs (.abs (.abs progBodyVar))))\n\n')
    f.write('set_option maxRecDepth 10000 in\n')
    f.write('set_option maxHeartbeats 16000000 in\n')
    f.write('/-- the `hsteps`-evaluated body: `subst`-inserted `shift`\n'
            '    leaves stay stuck (they carry metavariable params), so\n'
            '    each param slot is a nested `subst`/`shift` chain. -/\n')
    f.write('def progBodyStuck\n')
    f.write('    (fsT fuelT rbbT cbT nbT : LTerm) : LTerm :=\n')
    f.write('  ' + emit_stuck(E.b, OUTER, []) + '\n')
print('written _prog_defs.txt')
