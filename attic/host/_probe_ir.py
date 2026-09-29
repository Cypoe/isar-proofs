import sys
sys.path.insert(0, '.')
sys.path.insert(0, '..\\seed')
import spec_term as st
from reduce import T, K, I, KK, B, S, C, D, app
from lambda_dialect import parse, bracket

lam = "(\\x. x (K I))"
ir_cases = [I, app(S, app(KK, I)),
            st._appn(T(K.VAR, n=0), T(K.VAR, n=1)),
            st.bytelist_term(b'MZ'),
            bracket(parse(lam))]
nfail = 0
for t in ir_cases:
    rt = st.unpack_ir(st.pack_ir(t))
    if not (len(rt) == 1 and rt[0] == t):
        nfail += 1
        print('FAIL roundtrip', repr(t)[:60])
a1 = app(S, I)
two = st.unpack_ir(st.pack_ir(a1, KK))
if not (two[0] == a1 and two[1] == KK
        and st.pack_ir(app(S, I)) == st.pack_ir(a1)):
    nfail += 1
    print('FAIL multi-root/canonical')
bt = bracket(parse(lam))
print(f'ir pack/unpack done nfail={nfail}, '
      f'bracket-term={len(st.pack_ir(bt))}B')
