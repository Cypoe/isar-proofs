"""Emit asmL (assembleOf) as a Lean LTerm by parsing the seed's own
_assemble_src() with library combinators patched to atomic placeholders."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'host'))
from lambda_dialect import parse, NAbs, NApp, NVar, NComb
from reduce import K, I, KK, S, B, C, D
import spec_term as st

# patch spec_term's combinator templates to atomic placeholders so the
# parsed tree keeps leaf references instead of inlined lambda bodies
st._FOLDL = "FOLDL"
st._CONS_SRC = "CONSS"
st._CONSS = "CONSS"
st._PAIR_SRC = "PAIR"
st._HEAD = "HEAD"
st._REV = "REV"
st._LEN = "LEN"
st._ALOOK = "ALOOK"
st._B4ADD = "B4ADD"
st._B4SUB = "B4SUB"
st._NIB2B4 = "NIB2B4"
st.EQSTR = "EQSTR"
st._JUST_SRC = "JUST"
st._SELS = [f"SEL{i}" for i in range(16)]
st._sel_src = lambda k: f"SEL{k}"
st._prefix_src = lambda pfx, tail: "LBL"          # "label" nibs literal
st._b4_src = lambda v: "B4Z"                      # only called with 0

src = st._assemble_src()
# standalone leaf defs for the literals
LBL_SRC = "CONSS SEL6 (CONSS SEL12 (CONSS SEL6 (CONSS SEL1 (CONSS SEL6 " \
          "(CONSS SEL2 (CONSS SEL6 (CONSS SEL5 (CONSS SEL6 (CONSS SEL12 " \
          "K)))))))))"
B4Z_SRC = "CONSS (PAIR SEL0 SEL0) (CONSS (PAIR SEL0 SEL0) (CONSS " \
          "(PAIR SEL0 SEL0) (CONSS (PAIR SEL0 SEL0) K)))"

COMBS = {K: 'klL', KK: 'klL', I: 'idL', S: 'sCombL', B: 'bCombL',
         C: 'cCombL', D: 'dCombL'}
LEAVES = {'FOLDL': 'foldlL', 'CONSS': 'conssL', 'PAIR': 'pairSrcL',
          'HEAD': 'headL', 'REV': 'revL', 'LEN': 'lenL',
          'ALOOK': 'alookL', 'B4ADD': 'b4addL', 'B4SUB': 'b4subL',
          'NIB2B4': 'nib2b4L', 'EQSTR': 'eqStrL', 'JUST': 'justL',
          'LBL': 'lblL', 'B4Z': 'b4zL'}
LEAVES.update({f'SEL{i}': f'(nibLit {i})' for i in range(16)})


def to_lean(e, env):
    if isinstance(e, NAbs):
        return f'(.abs {to_lean(e.body, env + [e.param])})'
    if isinstance(e, NApp):
        spine = [e]
        while isinstance(spine[0], NApp):
            spine.insert(0, spine[0].left)
            spine[1] = spine[1].right
        head = to_lean(spine[0], env)
        args = ', '.join(to_lean(a, env) for a in spine[1:])
        return f'(aps {head} [{args}])'
    if isinstance(e, NVar):
        if e.name in env:
            i = env[::-1].index(e.name)
            return f'(.var {i})'
        return LEAVES[e.name]
    if isinstance(e, NComb):
        return COMBS[e.atom]
    raise TypeError(e)


def spine(e):
    """flatten NApp spine -> (head, [args])"""
    out = [e]
    while isinstance(out[0], NApp):
        out.insert(0, out[0].left)
        out[1] = out[1].right
    return out[0], out[1:]


# emit a subtree, mapping outer-env slots to Lean param tokens.
# env = names bound since subtree root (plus we count depth); a .var i
# with i >= depth refers to outer slot outer_names[len-1-(i-depth)].
def to_lean_par(e, depth, outer_names, ren):
    if isinstance(e, NAbs):
        return f'(.abs {to_lean_par(e.body, depth + 1, outer_names, ren)})'
    if isinstance(e, NApp):
        h, args = spine(e)
        return f'(aps {to_lean_par(h, depth, outer_names, ren)} [' + \
            ', '.join(to_lean_par(a, depth, outer_names, ren)
                      for a in args) + '])'
    if isinstance(e, NVar):
        # resolve against env names — but here we only have depth.
        # We work on the tree where env-binding was already resolved:
        raise AssertionError('use resolved tree')
    raise TypeError(e)


def resolve(e, env):
    """annotate free-var: return tree with NVar replaced by ('VAR', idx,
    name|'FREE', name) — simpler: emit directly tracking env names."""
    raise AssertionError


def emit(e, env, ren, depth=0):
    """emit; .var i with i >= depth resolves to an outer env slot —
    emit the ren param token for it. Local binders keep .var i."""
    if isinstance(e, NAbs):
        return f'(.abs {emit(e.body, env + [e.param], ren, depth + 1)})'
    if isinstance(e, NApp):
        h, args = spine(e)
        return f'(aps {emit(h, env, ren, depth)} [' + \
            ', '.join(emit(a, env, ren, depth) for a in args) + '])'
    if isinstance(e, NVar):
        if e.name not in env:
            return LEAVES[e.name]
        i = env[::-1].index(e.name)
        if i >= depth:
            slot = env[len(env) - 1 - i]
            assert slot in ren, f'unmapped outer slot {slot}'
            return ren[slot]
        return f'(.var {i})'
    if isinstance(e, NComb):
        return COMBS[e.atom]
    raise TypeError(e)


t = parse(src)

body = t
outer = []
while isinstance(body, NAbs):
    outer.append(body.param)
    body = body.body
assert outer == ['ENC', 'ZRV', 'prog', 'sym', 'base']

lets = []
b = body
while isinstance(b, NApp) and isinstance(b.left, NAbs):
    lets.append((b.left.param, b.right))
    b = b.left.body
assert [n for n, _ in lets] == ['p1', 'loc', 'prep', 'out']
val_of = dict(lets)
# final body: PAIR (REV out) loc
fb_h, fb_args = spine(b)
print('final head is NAbs?', isinstance(fb_h, NAbs))

# --- p1step: inside p1's value = FOLDL fragstep prog init ---------
p1h, p1args = spine(val_of['p1'])
fragstep = p1args[0]                         # λa.λfr. FOLDL p1step fr a
fs_h, fs_args = spine(fragstep.body.body)
p1step = fs_args[0]                          # λacc.λit. ...
p1env = outer + ['a', 'fr']
# --- emitstep: inside out's value = FOLDL emitstep prep K ----------
outh, outargs = spine(val_of['out'])
emitstep = outargs[0]
emenv = outer + ['p1', 'loc', 'prep']

def freevars(e, env, acc):
    if isinstance(e, NAbs):
        freevars(e.body, env + [e.param], acc)
    elif isinstance(e, NApp):
        freevars(e.left, env, acc); freevars(e.right, env, acc)
    elif isinstance(e, NVar):
        if e.name not in env and e.name not in LEAVES \
                and e.name not in acc:
            acc.append(e.name)
    return acc

print('p1step free:', freevars(p1step, p1env, []))
print('emitstep free:', freevars(emitstep, emenv, []))

P1REN = {'ENC': 'encT', 'ZRV': 'zrvT', 'base': 'basT'}
EMREN = {'ENC': 'encT', 'sym': 'symT', 'loc': 'lcT', 'base': 'basT'}

with open('_emit_out.txt', 'w', encoding='utf-8') as f:
    for name, s in [('lblL', LBL_SRC), ('b4zL', B4Z_SRC)]:
        f.write(f'def {name} : LTerm :=\n  {to_lean(parse(s), [])}\n\n')
    f.write('def asmL : LTerm :=\n')
    out = to_lean(t, [])
    f.write('  ' + out + '\n\n')
    f.write('/-- pass-1 per-item step (enc/zrv/base spliced) -/\n')
    f.write('def p1StepT (encT zrvT basT : LTerm) : LTerm :=\n')
    f.write(f'  {emit(p1step, p1env, P1REN)}\n\n')
    f.write('/-- pass-2 emit step (enc/sym/loc/base spliced) -/\n')
    f.write('def emitStepT (encT symT lcT basT : LTerm) : LTerm :=\n')
    f.write(f'  {emit(emitstep, emenv, EMREN)}\n\n')
    # the whole let-chain (body after 5 outer lambdas), outer slots spliced
    ALLREN = {'ENC': 'encT', 'ZRV': 'zrvT', 'prog': 'progT',
              'sym': 'symT', 'base': 'basT'}
    f.write('/-- let-chain body of assemble (all 5 args spliced); the four\n')
    f.write('    let-names stay bound as .var slots. -/\n')
    f.write('def asmLetsT (encT zrvT progT symT basT : LTerm) : LTerm :=\n')
    f.write(f'  {emit(body, outer, ALLREN)}\n')
print(len(out), 'chars')
