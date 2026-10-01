"""
lisp_dialect — TinyLisp surface dialect over the canonical packed-IR path.

Surface (corpus-driven subset of the isa-physics tinylisp suite):
  atoms    : integers >= 0, t, nil, symbols, 'quote (sym / list / num)
  forms    : define (name val | (f a ..) body), lambda, if, cond,
             let / let* / letrec* (Y-combinator recursion),
             and / or / not, assert (e "msg"), dotted apply (f a . l)
  builtins : + - * / mod abs, < <= > >= = eq eq? equal?,
             cons car cdr list null? pair? atom? list? number? symbol?,
             append length map filter reduce seq foldl

Encoding — tagged values, `v = λp. p TAG PAY` (TAG a raw Church numeral):
  nil=0  t=1  num n=2 (Church payload)  sym i=3 (interned index)
  cons=4 (payload λq. q h t).  Tags keep atom?/number?/symbol?/pair?/
  null?/equal? exact — no nil≡false≡0 conflation.  `-` saturates at 0;
  `/` `mod` are repeated subtraction (small numbers); no floats,
  negatives, strings, set!, or varargs — the ported corpus files are
  the compat subset of isa-physics's suite.

Compilation: s-expr -> desugar -> lambda_dialect mixed IR (NExpr) ->
Turner bracket -> closed basis term.  Every `assert` is an independent
root: `let defines.. prelude.. in truthy-check expr` — one .lisp file
IS the multi-root batch the canonical path dispatches (single /
CPU-MT pool via run.batch workers / ir_cuda).  Gate: each root's NF
must be the tagged-true NF.

Modes: default = graph.lo (fast tier); --exe = emitted IR kernel via
run.batch (--workers N); --cuda = ir_cuda.exe under IR_CUDA_PER_ROOT.
"""
from __future__ import annotations

import os
import re
import sys
from typing import Dict, List, Optional, Tuple, Union

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_REPO = os.path.dirname(_HOST)

from reduce import T  # noqa: E402
import lambda_dialect as ld  # noqa: E402
from lambda_dialect import NExpr, NVar, NApp, NAbs, NComb  # noqa: E402
from host_pieces import default_piece, run_piece  # noqa: E402

# ---------------------------------------------------------------------------
# s-expression reader
# ---------------------------------------------------------------------------

SAtom = Union[int, str]            # int literal | symbol | "str" literal
S = Union[SAtom, List["S"]]


def tokenize(src: str) -> List[str]:
    src = re.sub(r";[^\n]*", "", src)
    out: List[str] = []
    i = 0
    while i < len(src):
        c = src[i]
        if c.isspace():
            i += 1
            continue
        if c == '"':                        # string literal -> one tok
            j = src.find('"', i + 1)
            out.append(src[i:j + 1] if j >= 0 else '"')
            i = j + 1 if j >= 0 else len(src)
            continue
        if c in "()":
            out.append(c)
            i += 1
            continue
        if c == "'":
            out.append("'")
            i += 1
            continue
        if c == "`":
            out.append("`")
            i += 1
            continue
        if c == ",":
            out.append(",@" if src[i + 1:i + 2] == "@" else ",")
            i += 2 if src[i + 1:i + 2] == "@" else 1
            continue
        j = i
        while j < len(src) and not src[j].isspace() \
                and src[j] not in "()`,":
            j += 1
        out.append(src[i:j])
        i = j
    return out


def parse_all(src: str) -> List[S]:
    toks = tokenize(src)
    forms: List[S] = []
    i = 0
    while i < len(toks):
        e, i = _sx(toks, i)
        forms.append(e)
    return forms


def _sx(toks: List[str], i: int) -> Tuple[S, int]:
    t = toks[i]
    if t == "(":
        out: List[S] = []
        i += 1
        while i < len(toks) and toks[i] != ")":
            e, i = _sx(toks, i)
            out.append(e)
        if i >= len(toks):
            raise ValueError("unclosed '('")
        return out, i + 1
    if t == ")":
        raise ValueError("unexpected ')'")
    if t == "'":
        e, j = _sx(toks, i + 1)
        return ["quote", e], j
    if t == "`":
        e, j = _sx(toks, i + 1)
        return ["quasiq", e], j
    if t == ",":
        e, j = _sx(toks, i + 1)
        return ["unquote", e], j
    if t == ",@":
        e, j = _sx(toks, i + 1)
        return ["unquote-splice", e], j
    if re.fullmatch(r"-?\d+", t):
        return int(t), i + 1
    if re.fullmatch(r"-?\d+\.\d+", t):
        raise ValueError(f"float literal {t!r}: not realized (no floats)")
    if t.startswith('"'):
        return t, i + 1                    # string literal (assert msg)
    return t, i + 1


# ---------------------------------------------------------------------------
# NExpr helpers
# ---------------------------------------------------------------------------

def L(param: str, body: NExpr) -> NExpr:
    return NAbs(param, body)


def Ap(f: NExpr, *xs: NExpr) -> NExpr:
    t = f
    for x in xs:
        t = NApp(t, x)
    return t


def fvn(e: NExpr, bound=frozenset()) -> frozenset:
    if isinstance(e, NVar):
        return frozenset() if e.name in bound else frozenset({e.name})
    if isinstance(e, NAbs):
        return fvn(e.body, bound | {e.param})
    if isinstance(e, NApp):
        return fvn(e.left, bound) | fvn(e.right, bound)
    return frozenset()


def church(n: int) -> NExpr:
    body: NExpr = NVar("x")
    for _ in range(n):
        body = NApp(NVar("f"), body)
    return L("f", L("x", body))


C0, C1, C2, C3, C4 = (church(i) for i in range(5))

_TAG = {  # tag numerals as NExpr for prelude source holes
    "NIL": C0, "T": C1, "NUM": C2, "SYM": C3, "CONS": C4,
}


def _lam(name: str, src: str) -> Tuple[str, NExpr]:
    return name, ld.parse(src)


# prelude — raw helpers first (Church arith, raw bools, Y), then the
# tagged-value ops.  Raw bool TRUE/FALSE are plain K/KI; every surface
# op that returns a boolean wraps via `<raw> tv nilv`.
_PRELUDE_SRC: List[Tuple[str, Optional[str]]] = [
    ("I_",   "\\x. x"),
    ("TRUE", "\\a. \\b. a"),
    ("FALSE", "\\a. \\b. b"),
    ("Y",    "\\g. (\\x. g (x x)) (\\x. g (x x))"),
    ("succ", "\\n. \\f. \\x. f (n f x)"),
    ("plus", "\\m. \\n. \\f. \\x. m f (n f x)"),
    ("mul",  "\\m. \\n. \\f. m (n f)"),
    ("pred", "\\n. \\f. \\x. n (\\g. \\h. h (g f)) (\\u. x) (\\u. u)"),
    ("sub",  "\\m. \\n. n pred m"),
    ("isz",  "\\n. n (\\x. FALSE) TRUE"),
    ("and2", "\\a. \\b. a b FALSE"),
    ("leq",  "\\m. \\n. isz (sub m n)"),
    # numeral equality by simultaneous pred-descent — never builds a
    # sub numeral; O(n) pred calls instead of two O(n^2) sub traversals
    ("eqn",  "Y (\\s. \\m. \\n. (isz m) (isz n) "
             "((isz n) FALSE (s (pred m) (pred n))))"),
    ("ltn",  "\\m. \\n. leq (succ m) n"),
    ("div",  "Y (\\s. \\m. \\n. leq n m (succ (s (sub m n) n)) "
             "(\\f. \\x. x))"),
    ("modr", "\\n. Y (\\s. \\m. leq n m (s (sub m n)) m)"),
    # tagged constructors: v = λp. p tag pay
    ("mk",   "\\t. \\p. \\s. s t p"),
    ("nilv", None), ("tv", None), ("numv", None),
    ("symv", None), ("consv", None),
    # raw-bool selectors of a tagged value
    ("isnilv", "\\v. v (\\t. \\p. isz t)"),          # tag==0
    ("istv",   "\\v. v (\\t. \\p. isz (sub t "
               "(\\f. \\x. f x)) )"),               # tag==1... see below
    ("tagis",  "\\c. \\v. v (\\t. \\p. eqn c t)"),  # raw bool
    # surface bool ops on tagged values
    ("notv",   "\\v. isnilv v tv nilv"),
    ("carv",   "\\v. v (\\t. \\p. isz t nilv (p (\\h. \\t2. h)))"),
    ("cdrv",   "\\v. v (\\t. \\p. isz t nilv (p (\\h. \\t2. t2)))"),
    ("op2",    "\\op. \\a. \\b. a (\\ta. \\pa. b (\\tb. \\pb. "
               "numv (op pa pb)))"),
    ("cmp2",   "\\op. \\a. \\b. a (\\ta. \\pa. b (\\tb. \\pb. "
               "(op pa pb) tv nilv))"),
    ("istagv", "\\c. \\v. tagis c v tv nilv"),      # tagged bool
    ("equalp",
     "Y (\\self. \\x. \\y. x (\\tx. \\px. y (\\ty. \\py. "
     "(eqn tx ty) "
     "((eqn tx (\\f. \\x. f (f (f (f x))))) "       # tag==CONS?
     "((and2 (istv (self (px (\\h. \\t. h)) (py (\\h. \\t. h)))) "
     "(istv (self (px (\\h. \\t. t)) (py (\\h. \\t. t))))) "
     "tv nilv) "
     "((eqn px py) tv nilv)) "
     "nilv)))"),
    ("appendv",
     "Y (\\s. \\l1. \\l2. l1 (\\t. \\p. isz t l2 "
     "(consv (p (\\h. \\t2. h)) (s (p (\\h. \\t2. t2)) l2))))"),
    ("lengthv",
     "Y (\\s. \\l. l (\\t. \\p. isz t (numv (\\f. \\x. x)) "
     "(s (p (\\h. \\t2. t2)) (\\t3. \\p3. numv (succ p3)))))"),
    ("mapv",
     "\\f. Y (\\s. \\l. l (\\t. \\p. isz t nilv "
     "(consv (f (p (\\h. \\t2. h))) (s (p (\\h. \\t2. t2))))))"),
    ("filterv",
     "\\f. Y (\\s. \\l. l (\\t. \\p. isz t nilv "
     "((\\h. \\t2. (f h) (\\t3. \\p3. isz t3 (s t2) "
     "(consv h (s t2)))) "
     "(p (\\h2. \\t4. h2)) (p (\\h2. \\t4. t4)))))"),
    ("reducev",
     "\\f. Y (\\s. \\a. \\l. l (\\t. \\p. isz t a "
     "(s (f a (p (\\h. \\t2. h))) (p (\\h. \\t2. t2)))))"),
    ("seqv",
     "Y (\\s. \\a. \\b. a (\\ta. \\pa. b (\\tb. \\pb. "
     "ltn pb pa nilv "
     "(consv a (s (numv (succ pa)) b)))))"),
    # apply f to a spread list: (f a . l) desugars to applyv f (a . l)
    ("applyv",
     "Y (\\s. \\f. \\l. l (\\t. \\p. isz t f "
     "(s (f (p (\\h. \\t2. h))) (p (\\h. \\t2. t2)))))"),
]

# constructor bodies that need the tag constants (built after the
# table so church numerals stay NExpr-precise)
_CONSTR = {
    "nilv":  Ap(NVar("mk"), C0, C0),
    "tv":    Ap(NVar("mk"), C1, C0),
    "numv":  L("n", Ap(NVar("mk"), C2, NVar("n"))),
    "symv":  L("i", Ap(NVar("mk"), C3, NVar("i"))),
    "consv": L("h", L("t", Ap(NVar("mk"), C4,
                              L("q", Ap(NVar("q"), NVar("h"),
                                        NVar("t")))))),
}
# istv: tag==1 raw bool — express via eqn (tag is a numeral)
_CONSTR["istv"] = L("v", Ap(NVar("v"),
                            L("t", L("p", Ap(NVar("eqn"), C1,
                                            NVar("t"))))))

_PRELUDE: List[Tuple[str, NExpr]] = []
for _n, _e in _PRELUDE_SRC:
    _PRELUDE.append((_n, _CONSTR[_n] if _n in _CONSTR
                     else ld.parse(_e)))


def _n(name: str) -> str:
    """surface identifier -> λ-var name."""
    return (name.replace("?", "_Q").replace("-", "_")
            .replace("*", "_S").replace("!", "_B"))


class _Env:
    def __init__(self):
        self.syms: Dict[str, int] = {}
        self.defs: List[Tuple[str, NExpr]] = []
        self.checks: List[Tuple[NExpr, str]] = []
        self.values: List[NExpr] = []

    def intern(self, s: str) -> int:
        if s not in self.syms:
            self.syms[s] = len(self.syms) + 1
        return self.syms[s]


def _num(n: int) -> NExpr:
    if n < 0:
        raise ValueError(f"negative literal {n}: not realized "
                         "(Church numerals; '-' saturates at 0)")
    return Ap(NVar("numv"), church(n))


def _quote(e: S, env: _Env) -> NExpr:
    if isinstance(e, int):
        return _num(e)
    if isinstance(e, list):
        out: NExpr = NVar("nilv")
        for x in reversed(e):
            out = Ap(NVar("consv"), _quote(x, env), out)
        return out
    if e == "nil":
        return NVar("nilv")
    return Ap(NVar("symv"), church(env.intern(str(e))))


def _quasiq(e: S, env: _Env) -> NExpr:
    """`(a ,b ,@c) -> append/cons building with unquoted holes."""
    if isinstance(e, list) and e and e[0] == "unquote":
        return _desug(e[1], env)
    if isinstance(e, list):
        out: NExpr = NVar("nilv")
        for x in reversed(e):
            if isinstance(x, list) and x and x[0] == "unquote-splice":
                out = Ap(NVar("appendv"), _desug(x[1], env), out)
            else:
                out = Ap(NVar("consv"), _quasiq(x, env), out)
        return out
    return _quote(e, env)


def _if(c: NExpr, a: NExpr, b: NExpr) -> NExpr:
    """tagged cond: tag 0 (nil) -> b, anything else -> a; lazy under LO."""
    return Ap(c, L("t_", L("p_", Ap(NVar("isz"), NVar("t_"),
                                    b, a))))


def _ywrap(name: str, v: NExpr, rec: bool) -> NExpr:
    if not rec and name not in fvn(v):
        return v
    return Ap(NVar("Y"), L(name, v))


def _lets(defs: List[Tuple[str, NExpr]], body: NExpr) -> NExpr:
    out = body
    for n, v in reversed(defs):
        out = NApp(L(n, out), v)
    return out


_OPS: Dict[str, NExpr] = {}


def _op(h: str) -> Optional[NExpr]:
    """builtin head -> NExpr (prelude-var names or small composites)."""
    if not _OPS:
        _OPS.update({
            "+": ld.parse("op2 plus"), "-": ld.parse("op2 sub"),
            "*": ld.parse("op2 mul"), "/": ld.parse("op2 div"),
            "mod": ld.parse("(\\a. \\b. a (\\ta. \\pa. "
                            "b (\\tb. \\pb. numv (modr pb pa))))"),
            "abs": NVar("I_"),
            "<": ld.parse("cmp2 ltn"), "<=": ld.parse("cmp2 leq"),
            ">": ld.parse("cmp2 (\\m. \\n. ltn n m)"),
            ">=": ld.parse("cmp2 (\\m. \\n. leq n m)"),
            "=": NVar("equalp"), "eq": NVar("equalp"),
            "eq?": NVar("equalp"), "equal?": NVar("equalp"),
            "car": NVar("carv"), "cdr": NVar("cdrv"),
            "cons": NVar("consv"), "null?": NVar("notv"),
            "not": NVar("notv"),
            "pair?": Ap(NVar("istagv"), C4),
            "atom?": L("v", Ap(NVar("notv"),
                              Ap(NVar("istagv"), C4, NVar("v")))),
            "list?": L("v", Ap(Ap(NVar("isnilv"), NVar("v")),
                               NVar("tv"),
                               Ap(NVar("istagv"), C4, NVar("v")))),
            "number?": Ap(NVar("istagv"), C2),
            "symbol?": Ap(NVar("istagv"), C3),
            "length": NVar("lengthv"), "append": NVar("appendv"),
            "map": NVar("mapv"), "filter": NVar("filterv"),
            "reduce": NVar("reducev"), "foldl": NVar("reducev"),
            "seq": NVar("seqv"),
        })
    return _OPS.get(h)


def _desug(e: S, env: _Env) -> NExpr:
    if isinstance(e, int):
        return _num(e)
    if isinstance(e, str):
        if e.startswith('"'):
            return NVar("nilv")              # string literal: opaque nil
        if e in ("t", "#t"):
            return NVar("tv")
        if e in ("nil", "()", "#f"):
            return NVar("nilv")
        f = _op(e)
        if f is not None:              # op name in argument position
            return f
        return NVar(_n(e))
    if not isinstance(e, list) or not e:
        return NVar("nilv")
    h, *args = e
    if "." in args:                    # (f a1 .. an . l)
        i = args.index(".")
        f = _op(h) if isinstance(h, str) else None
        if h in ("+", "-", "*", "/", "append") and f is not None:
            # variadic op under spread: fold, not apply —
            # (op a . l) = reducev op a l; extra args cons onto l
            lst = _desug(args[i + 1], env)
            for a in reversed(args[1:i]):
                lst = Ap(NVar("consv"), _desug(a, env), lst)
            return Ap(NVar("reducev"), f, _desug(args[0], env), lst)
        fterm = _desug(h, env)
        lst = _desug(args[i + 1], env)
        for a in reversed(args[:i]):
            lst = Ap(NVar("consv"), _desug(a, env), lst)
        return Ap(NVar("applyv"), fterm, lst)
    if not isinstance(h, str):
        return Ap(_desug(h, env), *(_desug(a, env) for a in args))
    if h == "quote":
        return _quote(args[0], env)
    if h == "quasiq":
        return _quasiq(args[0], env)
    if h == "lambda":
        params, body = args[0], args[1]
        if not isinstance(params, list):
            params = [params]
        out = _desug(body, env)
        for p in reversed(params):
            out = L(_n(str(p)), out)
        return out
    if h == "if":
        c, a, b = args
        return _if(_desug(c, env), _desug(a, env), _desug(b, env))
    if h == "cond":
        out: NExpr = NVar("nilv")
        for clause in reversed(args):
            out = _if(_desug(clause[0], env), _desug(clause[1], env),
                      out)
        return out
    if h in ("let", "let*", "letrec", "letrec*"):
        binds, body = args[0], args[1]
        # tinylisp shape: binds may be a bare pair (x v) or a list
        # of pairs ((x v) (y w))
        if binds and not isinstance(binds[0], list):
            binds = [binds]
        out = _desug(body, env)
        for b in reversed(binds):
            nm, val = _n(str(b[0])), _desug(b[1], env)
            out = NApp(L(nm, out),
                       _ywrap(nm, val, h.startswith("letrec")))
        return out
    if h == "and":
        out = NVar("tv")
        for a in reversed(args):
            out = _if(_desug(a, env), out, NVar("nilv"))
        return out
    if h == "or":
        out = NVar("nilv")
        for a in reversed(args):
            out = _if(_desug(a, env), NVar("tv"), out)
        return out
    if h == "assert":
        env.checks.append((_desug(args[0], env),
                           str(args[1]) if len(args) > 1 else ""))
        return NVar("tv")
    if h == "define":
        raise ValueError("define only at top level")
    if h == "list":
        out = NVar("nilv")
        for a in reversed(args):
            out = Ap(NVar("consv"), _desug(a, env), out)
        return out
    f = _op(h)
    if f is not None:
        xs = [_desug(a, env) for a in args]
        if h in ("+", "-", "*", "/", "append") and len(xs) > 2:
            acc = Ap(f, xs[0], xs[1])          # n-ary -> left fold
            for x in xs[2:]:
                acc = Ap(f, acc, x)
            return acc
        return Ap(f, *xs)
    return Ap(NVar(_n(h)), *(_desug(a, env) for a in args))


def compile_program(src: str) -> Tuple[List[NExpr], List[str], _Env]:
    """parse file -> (check-roots, labels, env).  Every assert and
    every bare top-level expr is an independent root closed over
    prelude + defines; the gate asserts each NF == tagged-true."""
    env = _Env()
    for form in parse_all(src):
        if isinstance(form, list) and form and form[0] == "define":
            if isinstance(form[1], list):           # (define (f a..) b)
                name = _n(str(form[1][0]))
                body = _desug(form[2], env)
                for p in reversed(form[1][1:]):
                    body = L(_n(str(p)), body)
            else:
                name = _n(str(form[1]))
                body = _desug(form[2], env)
            env.defs.append((name, _ywrap(name, body, False)))
            continue
        if isinstance(form, list) and form and form[0] == "assert":
            _desug(form, env)
        else:
            env.values.append(_desug(form, env))
    defs = _PRELUDE + env.defs
    strict = lambda e: Ap(e, L("t_", L("p_", Ap(NVar("isz"),
                                               NVar("t_"),
                                               NVar("nilv"),
                                               NVar("tv")))))
    roots: List[NExpr] = []
    labels: List[str] = []
    for i, (e, msg) in enumerate(env.checks):
        roots.append(_lets(defs, strict(e)))
        labels.append(msg or f"check {i}")
    for i, e in enumerate(env.values):
        roots.append(_lets(defs, strict(e)))
        labels.append(f"expr {i}")
    return roots, labels, env


def compile_roots(roots: List[NExpr]) -> List[T]:
    """bracket-abstract on a dedicated thread: fv/abs_ recursion depth
    scales with the prelude-embedded term spine, which exceeds both the
    default recursion limit and the main-thread stack on real programs."""
    import threading
    out: List[T] = []
    err: List[BaseException] = []

    def go() -> None:
        sys.setrecursionlimit(200_000)
        try:
            out.extend(ld.bracket(r) for r in roots)
        except BaseException as e:
            err.append(e)

    threading.stack_size(64 << 20)
    t = threading.Thread(target=go)
    t.start()
    t.join()
    threading.stack_size(0)
    if err:
        raise err[0]
    return out


_TRUE_NF_T: Optional[T] = None


def _true_nf() -> T:
    """NF of the tagged-true value: tv = mk C1 C0 reduces to
    λs. s C1 C0 — bracket that directly (already normal)."""
    global _TRUE_NF_T
    if _TRUE_NF_T is None:
        _TRUE_NF_T = ld.bracket(L("s", Ap(NVar("s"), C1, C0)))
    return _TRUE_NF_T


def nf_is_true(t: T) -> bool:
    return ld.show(t) == ld.show(_true_nf())


def run_suite_file(path: str, run) -> Tuple[int, int, List[str]]:
    """returns (passed, total, failure-lines)."""
    src = open(path, encoding="utf-8").read()
    roots, labels, env = compile_program(src)
    terms = compile_roots(roots)
    if not terms:
        return 0, 0, []
    nfs, steps, _ = run.batch(terms)
    fails = []
    for lb, nf in zip(labels, nfs):
        if not nf_is_true(nf):
            fails.append(f"{lb}: nf={ld.show(nf)[:120]}")
    return len(nfs) - len(fails), len(nfs), fails


def _graph_runner():
    """single-threaded graph.lo runner with the batch interface."""
    piece = default_piece()

    class _R:
        @staticmethod
        def batch(qs):
            nfs, steps = [], 0
            for q in qs:
                nf, s, _n = run_piece(piece, q, fuel=5_000_000)
                nfs.append(nf)
                steps += s
            return nfs, steps, -1
    return _R()


def _exe_runner(fuse_s: bool = False, workers: int = 4):
    sd = os.path.join(_REPO, "seed")
    if sd not in sys.path:
        sys.path.insert(0, sd)
    import seed
    import toolchain
    from emit_chain import make_ir_runner
    exe = seed._exe_for(seed.Realization(
        ir_arena_bytes=int(os.environ.get("LISP_ARENA_GB", "16")) << 30,
        fuse_s=fuse_s),
                        tc=toolchain.by_name("native.x86_64.pe.ir"))
    return make_ir_runner(exe, workers=workers)


def _cuda_runner():
    import subprocess as sp
    sd = os.path.join(_REPO, "seed")
    if sd not in sys.path:
        sys.path.insert(0, sd)
    import cuda_gate
    import spec_term as st
    import seed
    exe = os.path.join(cuda_gate.WORK, "ir_cuda.exe")
    if not os.path.exists(exe):
        cuda_gate._build_cuda(exe, fuse_s=False)

    class _R:
        @staticmethod
        def batch(qs):
            blob = st.pack_ir(*qs)
            cp = sp.run([exe], input=blob, capture_output=True,
                        timeout=3600,
                        env={**os.environ, "IR_CUDA_PER_ROOT": "1"})
            if cp.returncode != 0:
                raise RuntimeError(f"ir_cuda rc={cp.returncode} "
                                   f"{cp.stderr[:200]!r}")
            lines = cp.stdout.decode().splitlines()
            return [seed._parse_native_out(ln) for ln in lines], -1, -1
    return _R()


MINI_SUITE = r"""
(define (add2 a b) (+ a b))
(assert (eq t t) "t==t")
(assert (not nil) "not nil")
(assert (= (+ 2 3) 5) "2+3=5")
(assert (= (* 6 7) 42) "6*7=42")
(assert (= (add2 20 22) 42) "user fn")
(assert (= (/ 10 2) 5) "div")
(assert (= (mod 10 3) 1) "mod")
(assert (eq? (car '(a b c)) 'a) "car")
(assert (equal? (cdr '(a b c)) '(b c)) "cdr")
(assert (equal? (cons 'a '(b c)) '(a b c)) "cons")
(assert (equal? (append '(a b) '(c)) '(a b c)) "append")
(assert (= (length '(1 2 3 4)) 4) "length")
(assert (null? '()) "null")
(assert (not (null? '(a))) "not null")
(assert (atom? 'x) "atom sym")
(assert (number? 3) "number?")
(assert (symbol? 'x) "symbol?")
(assert (not (atom? '(a))) "cons not atom")
(assert (pair? '(a)) "pair?")
(assert (list? '(a b)) "list?")
(assert (if nil 0 1) "if nil -> else 1 truthy")
(assert ((lambda (x) (+ x 1)) 41) "lambda call")
(assert (let ((x 3) (y 4)) (= (+ x y) 7)) "let")
(assert (let* ((x 2) (y (+ x 3))) (= y 5)) "let*")
(define (fact n) (if (< n 2) 1 (* n (fact (- n 1)))))
(assert (= (fact 5) 120) "fact5")
(assert (= (reduce + 0 '(1 2 3 4)) 10) "reduce")
(assert (equal? (map (lambda (x) (* x x)) '(1 2 3))
                '(1 4 9)) "map")
(assert (equal? (filter (lambda (x) (< x 3)) '(1 4 2 5))
                '(1 2)) "filter")
(assert (cond ((= 1 2) 9) (t 7)) "cond")
(assert (equal? (seq 2 5) '(2 3 4 5)) "seq")
(assert (= (foldl + 0 '(1 2 3)) 6) "foldl")
"""


def main(argv: List[str]) -> int:
    args = list(argv)
    mode = "graph"
    workers = 4
    suite_dirs: List[str] = []
    i = 0
    while i < len(args):
        if args[i] == "--exe":
            mode = "exe"
        elif args[i] == "--cuda":
            mode = "cuda"
        elif args[i] == "--workers":
            i += 1
            workers = int(args[i])
        elif args[i] == "--suite":
            i += 1
            suite_dirs.append(args[i])
        elif args[i].endswith(".lisp"):
            suite_dirs.append(args[i])
        else:
            raise SystemExit(f"unknown argument {args[i]!r} "
                             "(expected --exe/--cuda/--workers N/"
                             "--suite DIR|FILE.lisp)")
        i += 1

    if mode == "exe":
        run = _exe_runner(workers=workers)
    elif mode == "cuda":
        run = _cuda_runner()
    else:
        run = _graph_runner()

    ok = True
    total_p = total_n = 0

    def check_file(path: str):
        nonlocal ok, total_p, total_n
        p, n, fails = run_suite_file(path, run)
        total_p += p
        total_n += n
        tag = "OK " if not fails else "FAIL"
        print(f"{tag} {os.path.basename(path)}: {p}/{n} checks",
              flush=True)
        for f in fails[:8]:
            print(f"    {f}")
        ok = ok and not fails

    mini = os.path.join(_HOST, "emit_work", "_lisp_mini.lisp")
    os.makedirs(os.path.dirname(mini), exist_ok=True)
    with open(mini, "w") as f:
        f.write(MINI_SUITE)
    check_file(mini)

    for d in suite_dirs:
        files = ([d] if os.path.isfile(d)
                 else sorted(os.path.join(d, x) for x in os.listdir(d)
                             if x.endswith(".lisp")))
        for path in files:
            check_file(path)

    print(f"{'OK' if ok else 'FAIL'} lisp_dialect "
          f"({total_p}/{total_n} checks)", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
