"""nanopass gates — phi.rel contract: verbatim parse, admissible
construction, relational eval, shape/lowerings, fuel quotient,
meta-level call, basis-term unify witness."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

import phi_rel                                                # noqa: E402
import rel_eval                                               # noqa: E402
import rel_schema                                             # noqa: E402
import rel_witness                                            # noqa: E402

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_REPO = os.path.dirname(_HOST)
_PATENT = os.path.join(_REPO, os.pardir, "isa-physics",
                       "patent", "phi-lang")


def _corpus():
    return phi_rel.parse_rel(open(os.path.join(
        _HOST, "corpus", "stdlib.phi"), encoding="utf-8").read())


def _L(*xs):
    out = rel_eval.NIL
    for x in reversed(xs):
        out = rel_eval.t_pair(x, out)
    return out


def _A(v, bits=8):
    return rel_eval.t_atom(bits, v)


def gate_rel_parse_verbatim() -> bool:
    """the three patent .phi files parse verbatim — 28 rels —
    plus the rel-graph persists through a .plex bundle."""
    n = 0
    for fn in ("phi-lang.phi", "phi-stdlib.phi",
               "phi-runtime.phi"):
        p = os.path.join(_PATENT, fn)
        if os.path.exists(p):
            n += len(phi_rel.parse_rel(
                open(p, encoding="utf-8").read())["rels"])
    if n != 28:
        return False
    # the corpus graph persists through the bundle path
    g = _corpus()
    blob = phi_rel.graph_bundle(g)
    return phi_rel.read_graph_bundle(blob) == g


def gate_rel_schema_admissible() -> bool:
    """stdlib corpus is admissible construction (30 rels, every
    edge bound); the raw patent corpus refuses by name — the
    sketch's nibble_half_add gap is evidence, not a bug."""
    g = _corpus()
    try:
        rel_schema.check(g)
    except rel_schema.SchemaRefusal:
        return False
    if len(g["rels"]) != 30:
        return False
    rels = []
    for fn in ("phi-lang.phi", "phi-stdlib.phi",
               "phi-runtime.phi"):
        p = os.path.join(_PATENT, fn)
        if os.path.exists(p):
            rels += phi_rel.parse_rel(
                open(p, encoding="utf-8").read())["rels"]
    if not rels:
        return True                       # patent absent: skip leg
    try:
        rel_schema.check({"format": "phi.rel/1", "rels": rels})
        return False                      # sketch must refuse
    except rel_schema.SchemaRefusal as e:
        return "nibble_half_add" in str(e)


def gate_rel_shape_lowering() -> bool:
    """lowering contract: self realizes, pairwise unfolds,
    step|reduce refuse naming the unrealized lowering; transitive
    cycles without shape refuse too."""
    rel_eval._reset_fresh()
    g = phi_rel.parse_rel(
        "r : <x> <-> <y> shape step where { r<x> = y }")
    try:
        rel_eval.run_value(g, "r", [rel_eval.t_atom(8, 0)], n=1)
        return False
    except rel_eval.EvalError as e:
        if "lowering not realized" not in str(e):
            return False
    g2 = phi_rel.parse_rel(
        "a : <x> <-> <y> shape self where { b<x> = y }\n"
        "b : <x> <-> <y> where { a<x> = y }")
    try:
        rel_eval.run_value(g2, "a", [rel_eval.t_atom(8, 0)], n=1)
        return False
    except rel_eval.EvalError as e:
        return "declares no shape" in str(e)


def gate_rel_fuel_quotient() -> bool:
    """fuel is declared data: exhaustion is an observable empty
    stream, never a hang and never a silent timeout."""
    rel_eval._reset_fresh()
    g = _corpus()
    assert rel_eval.run_value(g, "fib", [rel_eval.t_atom(8, 5)],
                              n=1, fuel=40) == []
    return rel_eval.run_value(g, "fib", [rel_eval.t_atom(8, 5)],
                              n=1) == [rel_eval.t_atom(8, 5)]


def gate_rel_meta_call() -> bool:
    """env_lookup + MATCH + APPLY dispatch — definitions are data:
    call/map/fold route through the meta-level rel, not an engine
    hook."""
    rel_eval._reset_fresh()
    g = _corpus()
    return (
        rel_eval.run_value(g, "call", [rel_eval.t_sym("succ"),
                                       _A(2)], n=1) == [_A(3)]
        and rel_eval.run_value(g, "map", [rel_eval.t_sym("succ"),
            _L(_A(1), _A(2))], n=1) == [_L(_A(2), _A(3))]
        and rel_eval.run_value(g, "fold", [rel_eval.t_sym("add"),
            _A(0), _L(_A(1), _A(2), _A(3))], n=1) == [_A(6)]
        and rel_eval.run_value(g, "norm",
            [("goalterm", "append", [_L(_A(9)), rel_eval.NIL])],
            n=1) == [_L(_A(9))])


def gate_rel_carry_chain() -> bool:
    """the patent's called-but-undefined edge, closed relationally:
    nibble_half_add<15,2,1> = PAIR(2,1); list carry chain intact."""
    rel_eval._reset_fresh()
    g = _corpus()
    return (
        rel_eval.run_value(g, "nibble_half_add",
            [_A(15, 4), _A(2, 4), _A(1, 4)], n=1) ==
            [rel_eval.t_pair(_A(2, 4), _A(1, 4))]
        and rel_eval.run_value(g, "nibble_add",
            [_L(_A(1, 4), _A(2, 4)), _L(_A(3, 4), _A(0, 4)),
             _A(0, 4)], n=1) == [_L(_A(4, 4), _A(2, 4))])


def gate_rel_boot_congruence() -> bool:
    """phi_boot.appendo vs rel_eval backward append — identical
    splits in identical order (observational equivalence on the
    shared program, not just output equality)."""
    boot_py = os.path.join(_PATENT, "phi_boot.py")
    if not os.path.exists(boot_py):
        return True                          # patent absent: skip
    import importlib.util
    spec = importlib.util.spec_from_file_location("phi_boot",
                                                  boot_py)
    B = importlib.util.module_from_spec(spec)
    sys.modules["phi_boot"] = B
    spec.loader.exec_module(B)

    def appendo(xs, ys, zs):
        def goal(s):
            for s1 in B.conj(B.eq(xs, B.Atom.of(0, bits=0)),
                             B.eq(zs, ys))(s):
                yield s1
            h, t, r = B.fresh(), B.fresh(), B.fresh()
            for s1 in B.conj(B.eq(xs, B.Pair(h, t)),
                             B.conj(appendo(t, ys, r),
                                    B.eq(zs, B.Pair(h, r))))(s):
                yield s1
        return goal

    def bL(*xs):
        out = B.Atom.of(0, bits=0)
        for x in reversed(xs):
            out = B.Pair(x, out)
        return out

    def bt(t):
        if type(t).__name__ == "Atom":
            return rel_eval.t_atom(t.bits, t.value()) \
                if t.bits else rel_eval.NIL
        if type(t).__name__ == "Pair":
            return rel_eval.t_pair(bt(t.car), bt(t.cdr))
        return t

    bxs, bys = B.fresh(), B.fresh()
    bres = B.run(appendo(bxs, bys, bL(B.Atom.of(1), B.Atom.of(2))),
                 n=3)
    rel_eval._reset_fresh()
    g = _corpus()
    qx, qy = rel_eval.fresh(), rel_eval.fresh()
    want = _L(_A(1), _A(2))
    sols = rel_eval.run_solutions(g, "append", [qx, qy], want, n=3)
    ours = [(rel_eval.reify(qx, s), rel_eval.reify(qy, s))
            for s in sols]
    boot = [(bt(B.reify(bxs, s)), bt(B.reify(bys, s))) for s in bres]
    return len(boot) == 3 and boot == ours


def gate_rel_basis_unify() -> bool:
    """the bounded basis slice: atom-vs-atom unify on the graph cd
    fixpoint returns the FAIL marker — same reducer the emitted
    kernel runs, no Python fallback."""
    got, _rounds = rel_witness._run(
        "(" + rel_witness._unify(4) + " " + rel_witness.r_atom(5) +
        " " + rel_witness.r_atom(7) + " " + rel_witness._NIL +
        " (\\s2. s2) " + rel_witness._FAIL + ")")
    return rel_witness._cmp(got, rel_witness._expect(
        rel_witness._FAIL))


def _phi2seed():
    """phi2/seed.py is a corpus engine, not a host dep — load it
    file-scoped so the module table stays clean."""
    import importlib.util
    sp = importlib.util.spec_from_file_location(
        "phi2seed", os.path.join(_REPO, "phi2", "seed.py"))
    m = importlib.util.module_from_spec(sp)
    sys.modules["phi2seed"] = m
    sp.loader.exec_module(m)
    return m


def gate_rel_native_menv_enc2() -> bool:
    """native eval<menv> under gc=sweep emits a real x86 byte: the
    unrolled corpus evaluator (machine_term) interprets the
    generated assemble_x86_win64 map env and computes
    enc2<'op('ret)> = [0xC3] — byte-identical to fasmg's flat-
    binary oracle.  The collapsed cogen leg (frag 0025): the map
    is declared data, the evaluator is the corpus eval — Python
    only packs the term and reifies the subst.  Refusals stay
    loud: missing fasmg names the oracle axis; fuel/OOM exits are
    rc=2/4 — never a silent pass."""
    import subprocess
    sys.path.insert(0, os.path.join(_REPO, "seed"))
    import emit_chain as ec
    import spec_term as st
    import graph_runtime as G
    import reduce as R
    import seed as hseed
    import isa_x86_64 as ix

    ps = _phi2seed()
    ps._init_prelude()
    S, NIL, tp, ta = ps.t_sym, ps.NIL, ps.t_pair, ps.t_atom

    def eT(tag, *xs):
        o = xs[-1] if xs else NIL
        for x in reversed(xs[:-1]):
            o = tp(x, o)
        return tp(S(tag), o)

    def eP(a, b):
        return tp(S("pair"), tp(a, b))

    def _esym(x):
        return tp(S("sym"), S(x))

    def eAtom2(b, v):
        return tp(S("atom"), tp(ta(8, b), ta(8, v)))

    def enc_t(t):
        k = ps._ND[ps._force(t, NIL)]
        if k[0] == "p":
            return eP(enc_t(k[1]), enc_t(k[2]))
        if k[0] == "s":
            return _esym(k[1])
        return eAtom2(k[1], k[2])

    std = os.path.join(_REPO, "phi2", "std")
    mapg = ps.load_corpus(
        [os.path.join(std, f + ".plex") for f in
         ("arith_nibble_carry", "arith_peano_succ",
          "lists_append_mapfold", "lists_member_assoc",
          "unify_terms_core", "meta_call_run")]
        + [os.path.join(_REPO, "phi2", "maps",
                        "assemble_x86_win64.plex")])
    # prune to enc2's call-closure — env_find cost is linear in
    # env size; the rels themselves stay declared data
    byname = {r["name"]: r for r in mapg["rels"]}
    seen, wl = set(), ["enc2"]
    while wl:
        n = wl.pop()
        if n in seen or n not in byname:
            continue
        seen.add(n)
        for cl in byname[n]["clauses"] or []:
            for g in (cl["guard"] or []) + cl["goals"]:
                if isinstance(g, dict) and "call" in g:
                    wl.append(g["call"]["rel"])
    mapg["rels"] = [r for r in mapg["rels"] if r["name"] in seen]
    env = ps.enc_env(mapg)

    zero8 = NIL
    for _ in range(8):
        zero8 = tp(ta(4, 0), zero8)
    ov = tp(S("var"), ta(8, 0))
    nil_e = enc_t(NIL)
    z8e = enc_t(zero8)

    def enc2_goal(opterm):
        at = tp(enc_t(opterm), tp(nil_e, tp(z8e, NIL)))
        return tp(S("call"), tp(_esym("enc2"), tp(at, ov)))

    cases = [(eT("op", S("push_r64"), S("rbp")), "push rbp"),
             (eT("op", S("ret")), "ret")]

    M = ps.machine_term(8192)
    envS = ps.enc_sub(env)
    n1e = ps.enc_sub(ta(8, 1))
    Ts = []
    for opterm, _asm in cases:
        call = ps.mcall(M, "eval", envS, ps.enc_sub(enc2_goal(opterm)),
                        ps._PRE["dnil"], n1e)
        Ts.append(ps._to_host_T(ps.mcall(M, "take", ps._nat(1), call)))

    Rz = hseed.Realization(reclaim="redirect", gc="sweep",
                           io=("stdin", "stdout"),
                           fuel=2_000_000_000,
                           ir_arena_bytes=2 << 30)
    cp = subprocess.run([ec.ir_exe_for(Rz)],
                        input=st.pack_ir(*Ts), capture_output=True,
                        timeout=600)
    if cp.returncode != 0:
        raise RuntimeError(
            f"ir batch rc={cp.returncode} stderr={cp.stderr!r}")
    lines = cp.stdout.decode().splitlines()
    if len(lines) != len(Ts):
        return False
    import tower
    gg = G.Graph()
    nfts = [gg.import_tree(tower.quote_surface(
        hseed._parse_native_out(ln))) for ln in lines]

    marks = (R.I, R.app(R.KK, R.I), R.app(R.KK, R.KK),
             R.app(R.KK, R.I))

    def sol_subst(i):
        """first sol's subst: {var-id: term} off the PAIR spine."""
        dec = ps._dec_stream(gg, i, 8000, marks)
        if not dec or dec[0][0] != "p":
            return None
        subst = {}
        cur = dec[0][1]
        while cur[0] == "p":
            kv = cur[1]
            if kv[0] == "p" and kv[1][0] == "a" and kv[1][1] == 8:
                subst[kv[1][2]] = kv[2]
            cur = cur[2]
        return subst

    def reify(t, subst, d=0):
        if d > 60 or t[0] != "p":
            return t
        if t[1] == ("s", "var"):
            j = t[2][2]
            return reify(subst[j], subst, d + 1) if j in subst else t
        if t[1] == ("s", "pair"):
            return ("p", reify(t[2][1], subst, d + 1),
                    reify(t[2][2], subst, d + 1))
        if t[1] == ("s", "atom"):
            return ("a", t[2][1][2], t[2][2][2])
        return t

    def as_bytes(v, subst):
        out, t = [], reify(v, subst)
        while t[0] == "p":
            h = t[1]
            if h[0] != "a" or h[1] != 8:
                return None
            out.append(h[2])
            t = t[2]
        return out or None

    for i, (_opterm, asm) in zip(nfts, cases):
        subst = sol_subst(i)
        if subst is None:
            return False
        got = None
        for v in subst.values():
            got = as_bytes(v, subst)
            if got:
                break
        if not got:
            return False
        if bytes(got) != ix._fasmg(ix._FASM_HDR + asm + "\n"):
            return False
    return True
