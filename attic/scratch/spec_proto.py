"""Prototype for spec_term: encoding + query, measured on real toolchain.json."""
import json, os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
from reduce import T, K, I, KK, B, S, C, D, app
from lambda_dialect import parse, bracket_abstract0
from graph_runtime import reduce_tree_lo, reduce_tree_cd

sys.setrecursionlimit(10_000_000)


def _appn(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t


_CONS = bracket_abstract0(parse("\\h. \\t. \\n. \\c. c h t"))
_NIL = KK
_SELECTORS = tuple(
    bracket_abstract0(parse("".join(f"\\c{i}. " for i in range(16)) + f"c{k}"))
    for k in range(16))
_PAIR = bracket_abstract0(parse("\\k. \\v. \\f. f k v"))
_CHURCH_A = _appn(S, app(KK, S), _appn(S, app(KK, KK), I))


def church(k):
    t = app(KK, I)
    for _ in range(k):
        t = _appn(S, _CHURCH_A, t)
    return t


def tsize(t, memo=None):
    if memo is None:
        memo = set()
    if id(t) in memo:
        return 0
    memo.add(id(t))
    if t.k == K.APP:
        return 1 + tsize(t.l, memo) + tsize(t.r, memo)
    return 1


def tcount(t):
    if t.k == K.APP:
        return 1 + tcount(t.l) + tcount(t.r)
    return 1


def str_term(s):
    data = s.encode("utf-8")
    t = _NIL
    for byte in reversed(data):
        t = _appn(_CONS, _SELECTORS[byte & 15], t)
        t = _appn(_CONS, _SELECTORS[byte >> 4], t)
    return t


def json_to_term(obj):
    if obj is None:
        return app(C, I)                 # inert tag: C needs 3 args
    if isinstance(obj, bool):
        return KK if obj else app(KK, I)
    if isinstance(obj, int):
        return church(obj)
    if isinstance(obj, str):
        return str_term(obj)
    if isinstance(obj, list):
        t = _NIL
        for x in reversed(obj):
            t = _appn(_CONS, json_to_term(x), t)
        return t
    if isinstance(obj, dict):
        t = _NIL
        for k, v in reversed(list(obj.items())):
            t = _appn(_CONS, _appn(_PAIR, json_to_term(k), json_to_term(v)), t)
        return t
    raise TypeError(f"unsupported JSON value: {obj!r}")


def church_src(k):
    return "(\\f. \\x. " + "f (" * k + "x" + ")" * k + ")"


def b_src(k):
    s = "I"
    for _ in range(k):
        s = f"(B {s})"
    return s


def sel_src(k):
    return "(" + "".join(f"\\c{i}. " for i in range(16)) + f"c{k})"


def str_src(s):
    """λ-source for a nibble-string literal (same shape as str_term)."""
    out = "K"
    for byte in reversed(s.encode("utf-8")):
        out = f"((\\h. \\t. \\n. \\c. c h t) {sel_src(byte & 15)} {out})"
        out = f"((\\h. \\t. \\n. \\c. c h t) {sel_src(byte >> 4)} {out})"
    return out


# --- λ-source pieces -------------------------------------------------------
# eqNib: \a.\b. a (b K F…F)(b F K…F)…(b F…F K)  -> Church bool
EQNIB = ("(\\a. \\b. a " +
         " ".join("(b " +
                  " ".join("K" if j == i else "(K I)" for j in range(16)) +
                  ")" for i in range(16)) + ")")

# eqStr a b n: iterate over `a` (n >= len(a)); flag short-circuits on FALSE.
# acc = \k. k la lb o ; o = Church bool.
_STEP_E = (
    "\\acc. acc (\\la. \\lb. \\o. o "
    "(la "
    "(\\k2. k2 la lb (lb K (\\h. \\t. (K I))))"
    "(\\ha. \\ta. lb "
    "(\\k2. k2 la lb (K I)) "
    "(\\hb. \\tb. " + EQNIB + " ha hb "
    "(\\k2. k2 ta tb K) (\\k2. k2 ta tb (K I)))))"
    "(\\k2. k2 la lb (K I)))"
)

EQSTR = ("(\\a. \\b. \\n. (n (" + _STEP_E + ") "
         "(\\k2. k2 a b K)) "
         "(\\la. \\lb. \\o. o))")

# specGet spec key n nb: assoc lookup; acc = \k. k l o ; o = option.
# nb = eqStr bound (>= 2*len(key)); iterates `key` (first arg).
_STEP_A = (
    "\\acc. acc (\\l. \\o. l "
    "(\\k2. k2 l o) "
    "(\\p. \\t. p (\\k3. \\v3. (" + EQSTR + " key k3 nb) "
    "(\\k2. k2 t (\\n4. \\j4. j4 v3)) "
    "(\\k2. k2 t o))))"
)

SPECGET = ("(\\spec. \\key. \\n. \\nb. (n (" + _STEP_A + ") "
           "(\\k2. k2 spec (\\n4. \\j4. n4))) "
           "(\\l. \\o. o))")

# emit list n -> C (B^k I) … K spine (xdu output-map shape, no rc)
_STEP_M = (
    "\\acc. acc (\\l. \\o. l "
    "(\\k2. k2 l o) "
    "(\\h. \\t. \\k2. k2 t (\\r. o (C (h " +
    " ".join(b_src(i) for i in range(16)) + ") r))))"
)

EMIT = ("(\\list. \\n. ((n (" + _STEP_M + ") "
        "(\\k2. k2 list (\\r. r))) "
        "(\\l. \\o. o)) K)")

_STEP_B = (
    "\\acc. acc (\\l. \\o. l "
    "(\\k2. k2 l o) "
    "(\\entry. \\t. (" + SPECGET + " entry __NAMET__ __NENT__ __NBE__) "
    "(\\k2. k2 t o) "
    "(\\v. " + EQSTR + " name v __NBEQ__ "
    "(\\k2. k2 t (" + SPECGET + " entry __PATHT__ __NENT__ __NBE__)) "
    "(\\k2. k2 t o))))"
)

PATH_OF = (
    "(\\spec. \\name. (" + SPECGET + " spec __TOOLST__ __NTOP__ __NBT__) I "
    "(\\arr. ((__NARR__ (" + _STEP_B + ") "
    "(\\k2. k2 arr (\\n4. \\j4. n4))) "
    "(\\l. \\o. o)) I (\\v. " + EMIT + " v __NEMIT__)))"
)


def query_src(n_top, n_ent, n_arr, n_emit, n_beq, n_bt, n_be):
    src = PATH_OF
    for ph, val in (
        ("__TOOLST__", str_src("toolchains")),
        ("__NAMET__", str_src("name")),
        ("__PATHT__", str_src("path")),
        ("__NTOP__", church_src(n_top)),
        ("__NENT__", church_src(n_ent)),
        ("__NARR__", church_src(n_arr)),
        ("__NEMIT__", church_src(n_emit)),
        ("__NBEQ__", church_src(n_beq)),
        ("__NBT__", church_src(n_bt)),
        ("__NBE__", church_src(n_be)),
    ):
        src = src.replace(ph, val)
    assert "__" not in src
    return src


def main():
    spec = json.load(open(os.path.join("host", "toolchain.json")))
    SPEC = json_to_term(spec)
    print(f"SPEC unique nodes: {tsize(SPEC)}  tree nodes: {tcount(SPEC)}")

    n_top = len(spec)
    n_ent = max(len(e) for e in spec["toolchains"])
    n_arr = len(spec["toolchains"])
    names = [e["name"] for e in spec["toolchains"]]
    maxname = max(2 * len(n.encode()) for n in names)
    # eqStr iterates its FIRST arg:
    #   specGet:      first arg = literal key  -> bound = 2*len(key)+2
    #   name compare: first arg = query name   -> bound = maxname+2
    #   emit:         bound >= path length nibbles
    n_bt = 2 * len("toolchains") + 2       # top assoc key bound
    n_be = 2 * max(len("name"), len("path")) + 2
    n_beq = maxname + 2
    n_emit = 2 * max(len(e["path"]) for e in spec["toolchains"]) + 2
    print(f"bounds: top={n_top} ent={n_ent} arr={n_arr} "
          f"bt={n_bt} be={n_be} beq={n_beq} emit={n_emit}")

    src = query_src(n_top=n_top, n_ent=n_ent, n_arr=n_arr,
                    n_emit=n_emit, n_beq=n_beq, n_bt=n_bt, n_be=n_be)
    print(f"query src: {len(src)} chars")
    t0 = time.time()
    Q = bracket_abstract0(parse(src))
    print(f"QUERY: {tsize(Q)} unique nodes ({time.time()-t0:.1f}s)")

    name = "xdu.x86_64.pe"
    t = _appn(Q, SPEC, str_term(name))
    t0 = time.time()
    nf, steps, alloc = reduce_tree_lo(t, 4_000_000_000)
    print(f"graph.lo {name!r}: {steps} steps alloc={alloc} "
          f"{time.time()-t0:.1f}s")
    print(f"nf: {nf}")


if __name__ == "__main__":
    main()
