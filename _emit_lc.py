"""Emit Lean LTerm source for the assemble-stage combinators by
parsing the Python seed templates with atomic placeholders."""
import sys
sys.path.insert(0, r'C:\Users\fabi0\repos\isar-proofs\host')
from lambda_dialect import parse, NAbs, NApp, NVar, NComb
from reduce import K, I, KK, S, B, C, D

COMBS = {K: 'klL', KK: 'klL', I: 'idL', S: 'sCombL', B: 'bCombL',
         C: 'cCombL', D: 'dCombL'}
LEAVES = {'EQNIB': 'eqnibL', 'STEP_E': 'stepEL', 'FOLDL': 'foldlL',
          'LEN': 'lenL', 'JUST': 'justL', 'EQSTR': 'eqStrL',
          'REV': 'revL', 'APPEND': 'appendL', 'PAIR': 'pairSrcL',
          'B4ADD': 'b4addL', 'B4SUB': 'b4subL', 'NIB2B4': 'nib2b4L',
          'NOTB': 'notbL'}


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


# ---- templates with atoms -------------------------------------

STEP_E = (
    "\\acc. acc (\\la. \\lb. \\o. o "
    "(la "
    "(\\k2. k2 la lb (lb K (\\h. \\t. (K I))))"
    "(\\ha. \\ta. lb "
    "(\\k2. k2 la lb (K I)) "
    "(\\hb. \\tb. EQNIB ha hb "
    "(\\k2. k2 ta tb K) (\\k2. k2 ta tb (K I)))))"
    "(\\k2. k2 la lb (K I)))"
)

EQSTR = ("(\\a. \\b. \\n. (n (STEP_E) "
         "(\\k2. k2 a b K)) "
         "(\\la. \\lb. \\o. o "
         "(la (lb K (\\h. \\t. (K I))) (\\h. \\t. (K I))) (K I)))")

JUST = "(\\v. \\n. \\j. j v)"

ALOOK = ("(\\map. \\key. (FOLDL "
         "(\\acc. \\e. e (\\k2. \\v2. (EQSTR key k2 (LEN key)) "
         "(JUST v2) acc)) map K))")

for name, src in [('stepEL', STEP_E), ('eqStrL', EQSTR),
                  ('justL', JUST), ('alookL', ALOOK)]:
    t = parse(src)
    print(f'def {name} : LTerm :=')
    print(f'  {to_lean(t, [])}')
    print()
