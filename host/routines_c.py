"""
routines_c — the C reducer kernel (hosted, order="lo"): the second host.

Mirrors routines_x86_64_win64's routine-builder decomposition at the
C-ISA level: each builder emits an isa_c Program fragment (functions
via FN/end, statements via I).  The kernel is the same IStepBasis
machine the PE hosts — tagged bump-heap nodes {tag,l,r}, streaming
postfix parse over the read granule, LO step order, NF decompile to
the same token alphabet — with strategy data (chunk_bytes,
read_buf_bytes, node_bytes, fuel, fuse_s) baked as emitted literals,
never as runtime parameters.

Semantic contract mirrored from seed/seed.py + routines:
  tags      APP=0 norm=1 konst=2 s=3 comp=4 dup=5 swap=6 STK=7
  step      normβ konstβ dupβ compβ swapβ (+sβ iff fuse_s), then
            appL then appR — full IStepBasis, not host/reduce.py IStep
  parse     token push; '@' pops x,y pushes app(y,x); underflow pads
            the stack top with I; " \\t\\r\\n," skipped; else exit(3)
  out       NF tokens each followed by ' ', then '\\n' on stdout;
            "steps=N alloc=M\\n" on stderr; rc 0/2/3/4
  alloc     nalloc counts term cells (mkleaf/mkapp); parse-stack
            cons cells (tag=STK=7) are excluded, same as the PE

imports are C headers (stdio/stdlib/stdint), data_slots carry the
read buffer — the same fields the PE record fills with kernel32
imports and .data slots.
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
_SEED_DIR = os.path.normpath(os.path.join(_HOST, "..", "seed"))
for _p in (_HOST, _SEED_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import isa_c as _isa                        # noqa: E402
from isa_c import I, FN, Program            # noqa: E402
from toolchain import NotRealized           # noqa: E402
from seed import Tag, Realization           # noqa: E402

IMPORTS: Tuple[str, ...] = ("stdint.h", "stdio.h", "stdlib.h")
DATA_SLOTS: Tuple[Tuple[str, int], ...] = ()

Ctx = Dict[str, object]

_TAG_NAME = {
    Tag.norm: "T_NORM", Tag.konst: "T_KONST", Tag.s: "T_S",
    Tag.comp: "T_COMP", Tag.dup: "T_DUP", Tag.swap: "T_SWAP",
}


def r_prelude(R: Realization, ctx: Ctx) -> Program:
    """Type model + globals: N{tag,l,r}, tag enum, strategy constants,
    bump-heap state, stats counters, parse stack, derived_s slot."""
    p: Program = [
        ("i", "note", "node model — Realization.node_bytes"),
        ("i", "raw",
         "typedef struct N { uint64_t tag; struct N *l; struct N *r; } N;"),
        ("i", "raw",
         "enum { T_APP = 0, T_NORM = 1, T_KONST = 2, T_S = 3, "
         "T_COMP = 4, T_DUP = 5, T_SWAP = 6, T_STK = 7 };"),
        ("i", "raw",
         f"_Static_assert(sizeof(N) == {R.node_bytes}, "
         "\"node_bytes\");"),
        ("i", "raw", "static const char CHAR_OF[8] = "
         "{'?','I','K','S','B','W','C','?'};"),
        ("i", "raw", "static const int TAG_OF[256] = "
         "{['I']=T_NORM,['K']=T_KONST,['S']=T_S,"
         "['B']=T_COMP,['W']=T_DUP,['C']=T_SWAP};"),
        ("i", "decl", "static const unsigned long long", "CHUNK",
         f"{R.chunk_bytes}ULL"),
        ("i", "decl", "static unsigned char *", "hp", "0"),
        ("i", "decl", "static unsigned char *", "hpend", "0"),
        ("i", "decl", "static unsigned long long", "nalloc", "0"),
        ("i", "decl", "static unsigned long long", "steps", "0"),
        ("i", "decl", "static N *", "stk", "0"),
        # read granule — one streaming buffer, strategy-sized
        ("i", "raw",
         f"static unsigned char rbuf[{R.read_buf_bytes}];"),
        # stdout/stderr are byte channels — win32 text mode would
        # translate \n -> \r\n; the PE WriteFiles raw bytes
        ("i", "raw", "#ifdef _WIN32"),
        ("i", "raw", "#include <io.h>"),
        ("i", "raw", "#include <fcntl.h>"),
        ("i", "raw", "#endif"),
    ]
    if R.fuel is not None:
        p.append(("i", "decl", "static const unsigned long long",
                  "FUEL", f"{R.fuel}ULL"))
    if not R.fuse_s:
        p.append(("i", "decl", "static N *", "ds", "0"))
    return p


def r_alloc(R: Realization, ctx: Ctx) -> Program:
    """grow_heap/mkleaf/mkapp/mkstk — bump arena over malloc chunks;
    mkstk conses the parse stack without touching nalloc."""
    return [
        ("i", "note", "bump arena — chunk_bytes per malloc"),
        FN("static N *", "cell", "void"),
        I("if", "hp >= hpend"),
        I("do", "hp = (unsigned char *) malloc(CHUNK)"),
        I("if", "!hp"),
        I("do", "exit(4)"),
        I("end"),
        I("assign", "hpend", "hp + CHUNK"),
        I("end"),
        I("decl", "N *", "n", "(N *) hp"),
        I("assign", "hp", f"hp + {R.node_bytes}"),
        I("ret", "n"),
        I("end"),
        FN("static N *", "mkleaf", "int tag"),
        I("decl", "N *", "n", "cell()"),
        I("assign", "n->tag", "tag"),
        I("assign", "n->l", "0"),
        I("assign", "n->r", "0"),
        I("do", "nalloc++"),
        I("ret", "n"),
        I("end"),
        FN("static N *", "mkapp", "N *f, N *x"),
        I("decl", "N *", "n", "cell()"),
        I("assign", "n->tag", "T_APP"),
        I("assign", "n->l", "f"),
        I("assign", "n->r", "x"),
        I("do", "nalloc++"),
        I("ret", "n"),
        I("end"),
        FN("static N *", "mkstk", "N *t, N *next"),
        I("decl", "N *", "n", "cell()"),
        I("assign", "n->tag", "T_STK"),
        I("assign", "n->l", "t"),
        I("assign", "n->r", "next"),
        I("ret", "n"),
        I("end"),
    ]


def r_build_ds(R: Realization, ctx: Ctx) -> Program:
    """build_ds (default build only): DERIVED_S =
    (B (B D)) ((C ((B B)((B B) C))) I) instantiated once —
    seed.DERIVED_S = ((comp,(comp,dup)), ((swap,G),norm)) with
    G = (B B)((B B) C)."""
    return [
        ("i", "note", "derived_s — built once (bc_compile S-push)"),
        FN("static void", "build_ds", "void"),
        I("decl", "N *", "a",
          "mkapp(mkleaf(T_COMP), mkapp(mkleaf(T_COMP), mkleaf(T_DUP)))"),
        I("decl", "N *", "bb",
          "mkapp(mkleaf(T_COMP), mkleaf(T_COMP))"),
        # PE instantiates a fresh (B B) here — tree, not DAG:
        # reusing bb would diverge alloc= from the native host
        I("decl", "N *", "bc",
          "mkapp(mkapp(mkleaf(T_COMP), mkleaf(T_COMP)), "
          "mkleaf(T_SWAP))"),
        I("decl", "N *", "g", "mkapp(bb, bc)"),
        I("decl", "N *", "cg", "mkapp(mkleaf(T_SWAP), g)"),
        I("decl", "N *", "cgi", "mkapp(cg, mkleaf(T_NORM))"),
        I("assign", "ds", "mkapp(a, cgi)"),
        I("end"),
    ]


def r_step(R: Realization, ctx: Ctx) -> Program:
    """step: LO single step — IStepBasis rule order (normβ, konstβ,
    dupβ, compβ, swapβ, [sβ iff fuse_s], appL, appR).  Returns 0 on NF."""
    p: Program = [
        ("i", "note", "LO step — IStepBasis, seed.step mirror"),
        FN("static N *", "step", "N *t"),
        I("if", "t->tag != T_APP"),
        I("ret", "0"),
        I("end"),
        I("decl", "N *", "f", "t->l"),
        I("decl", "N *", "x", "t->r"),
        I("if", "f->tag == T_NORM"),
        I("ret", "x"),
        I("end"),
        I("if", "f->tag == T_APP"),
        I("decl", "N *", "fl", "f->l"),
        I("decl", "N *", "fr", "f->r"),
        I("if", "fl->tag == T_KONST"),
        I("ret", "fr"),
        I("end"),
        I("if", "fl->tag == T_DUP"),
        I("ret", "mkapp(mkapp(fr, x), x)"),
        I("end"),
        I("if", "fl->tag == T_APP"),
        I("decl", "N *", "fll", "fl->l"),
        I("decl", "N *", "flr", "fl->r"),
        I("if", "fll->tag == T_COMP"),
        I("ret", "mkapp(flr, mkapp(fr, x))"),
        I("end"),
        I("if", "fll->tag == T_SWAP"),
        I("ret", "mkapp(mkapp(flr, x), fr)"),
        I("end"),
    ]
    if R.fuse_s:
        p += [
            I("if", "fll->tag == T_S"),
            I("ret", "mkapp(mkapp(flr, x), mkapp(fr, x))"),
            I("end"),
        ]
    p += [
        I("end"),
        I("end"),
        I("decl", "N *", "sf", "step(f)"),
        I("if", "sf"),
        I("ret", "mkapp(sf, x)"),
        I("end"),
        I("decl", "N *", "sx", "step(x)"),
        I("if", "sx"),
        I("ret", "mkapp(f, sx)"),
        I("end"),
        I("ret", "0"),
        I("end"),
    ]
    return p


def r_parse(R: Realization, ctx: Ctx) -> Program:
    """parse: stream stdin over rbuf granules — bc_compile mirror.
    Token pushes leaf (S -> ds when !fuse_s); '@' pops x,y pushes
    app(y,x), underflow pads top with I; separators skipped; other
    bytes exit(3)."""
    leaf = "mkleaf(TAG_OF[ch])" if R.fuse_s \
        else "(ch == 'S' ? ds : mkleaf(TAG_OF[ch]))"
    return [
        ("i", "note", "streaming postfix parse — granule, not cap"),
        FN("static void", "parse", "void"),
        I("decl", "size_t", "n", "0"),
        I("while", "(n = fread(rbuf, 1, sizeof rbuf, stdin)) > 0"),
        I("for", "size_t i = 0", "i < n", "i++"),
        I("decl", "unsigned char", "ch", "rbuf[i]"),
        I("if", "ch==' '||ch=='\\t'||ch=='\\r'||ch=='\\n'||ch==','"),
        I("continue"),
        I("end"),
        I("if", "TAG_OF[ch]"),
        I("do", f"stk = mkstk({leaf}, stk)"),
        I("continue"),
        I("end"),
        I("if", "ch == '@'"),
        I("if", "stk && stk->r"),
        I("decl", "N *", "x", "stk->l"),
        I("decl", "N *", "y", "stk->r->l"),
        I("assign", "stk", "stk->r->r"),
        I("do", "stk = mkstk(mkapp(y, x), stk)"),
        I("else"),
        I("do", "stk = mkstk(mkleaf(T_NORM), stk)"),
        I("end"),
        I("continue"),
        I("end"),
        I("do", "exit(3)"),
        I("end"),
        I("end"),
        I("end"),
    ]


def r_emit(R: Realization, ctx: Ctx) -> Program:
    """emit_nf: postfix decompile to stdout — each token followed by
    ' ' (emit_nf mirror); count_nodes not needed at this layer —
    putchar streams the same bytes the PE WriteFiles."""
    return [
        ("i", "note", "NF decompile — same token alphabet"),
        FN("static void", "emit_nf", "N *t"),
        I("if", "t->tag == T_APP"),
        I("do", "emit_nf(t->l)"),
        I("do", "emit_nf(t->r)"),
        I("do", "putchar('@')"),
        I("else"),
        I("do", "putchar(CHAR_OF[t->tag])"),
        I("end"),
        I("do", "putchar(' ')"),
        I("end"),
    ]


def r_main(R: Realization, ctx: Ctx) -> Program:
    """main: heap head + [build_ds] + parse + reduce loop + NF +
    stats — exits: 0 NF, 2 fuel, 3 bad byte, 4 OOM."""
    p: Program = [
        FN("int", "main", "void"),
        ("i", "raw", "#ifdef _WIN32"),
        I("do", "_setmode(_fileno(stdout), _O_BINARY)"),
        I("do", "_setmode(_fileno(stderr), _O_BINARY)"),
        ("i", "raw", "#endif"),
    ]
    if not R.fuse_s:
        p.append(I("do", "build_ds()"))
    p += [
        I("do", "parse()"),
        I("decl", "N *", "t", "stk ? stk->l : mkleaf(T_NORM)"),
        I("decl", "N *", "nxt", "0"),
        I("while", "(nxt = step(t))"),
        I("assign", "t", "nxt"),
        I("do", "steps++"),
    ]
    if R.fuel is not None:
        p += [
            I("if", "steps >= FUEL"),
            I("do", "exit(2)"),
            I("end"),
        ]
    p += [
        I("end"),
        I("do", "emit_nf(t)"),
        I("do", "putchar('\\n')"),
        I("do", 'fprintf(stderr, "steps=%llu alloc=%llu\\n", '
                "steps, nalloc)"),
        I("ret", "0"),
        I("end"),
    ]
    return p


# Ordered routine names = emission order (same convention as
# routines_x86_64_win64).  "build_ds" emits iff not R.fuse_s.
ROUTINES: Tuple[str, ...] = (
    "prelude", "alloc", "build_ds", "step", "parse", "emit", "main",
)

_BUILDERS: Dict[str, Callable[[Realization, Ctx], Program]] = {
    name[2:]: fn for name, fn in list(globals().items())
    if name.startswith("r_")
}


def program(R: Realization) -> Program:
    if R.order != "lo":
        raise NotRealized(f"order={R.order!r} declared but not realized")
    p: Program = []
    for name in ROUTINES:
        if name == "build_ds" and R.fuse_s:
            continue
        p += _BUILDERS[name](R, {})
    return p


@dataclass(frozen=True)
class Routines:
    name: str          # "c.hosted.lo"
    isa: str           # "c"
    abi: str           # "hosted"
    orders: tuple      # ("lo",)
    routines: tuple    # ROUTINES
    program: Callable  # program(R) -> Program
    imports: tuple
    data_slots: tuple


C_HOSTED_LO = Routines(
    name="c.hosted.lo",
    isa="c",
    abi="hosted",
    orders=("lo",),
    routines=ROUTINES,
    program=program,
    imports=IMPORTS,
    data_slots=DATA_SLOTS,
)


def emit_c(R: Realization) -> bytes:
    """Same chain as seed.emit, driven directly: program -> assemble
    -> pack -> complete C translation unit."""
    import target_c
    prog = program(R)
    syms = target_c.symbols(IMPORTS, DATA_SLOTS)
    text, labels = _isa.assemble(prog, syms, base=0)
    return target_c.pack(text, labels, IMPORTS, DATA_SLOTS, R)


C_DEFAULT = Realization(abi="hosted")

_EXE_CACHE: Dict[str, str] = {}


def _exe_for(R: Realization) -> str:
    """Emit + compile the kernel for R once per process (tempdir)."""
    key = f"{R.fuse_s}:{R.fuel}:{R.chunk_bytes}:{R.read_buf_bytes}"
    if key not in _EXE_CACHE:
        import tempfile
        import target_c
        td = os.path.join(tempfile.gettempdir(), "isar_c_kernel")
        os.makedirs(td, exist_ok=True)
        c_path = os.path.join(td, f"reducer_{abs(hash(key)) & 0xFFFF:x}.c")
        exe_path = c_path[:-2] + ".exe"
        with open(c_path, "wb") as f:
            f.write(emit_c(R))
        _EXE_CACHE[key] = target_c.compile_c(c_path, exe_path)
    return _EXE_CACHE[key]


def _reduce_via(t, R: Realization):
    """HostPiece.reduce signature: (T_host, fuel) -> (nf, steps, alloc).
    Mirrors seed._reduce_via's observation discipline: input is
    translate_to_basis'd on the default build, native NF tokens are
    parsed back, quote_surface folds derived_s subtrees to S."""
    import re
    import tempfile  # noqa: F401
    import seed as _seed
    import target_c
    import tower
    if not R.fuse_s:
        t = tower.translate_to_basis(t)
    tokens = " ".join(_seed.bc_decompile(_seed.t_from_host(t)))
    out, err, rc = target_c.run_exe(_exe_for(R), tokens.encode())
    if rc != 0:
        raise RuntimeError(f"c reducer rc={rc} stderr={err!r}")
    nf = _seed._parse_native_out(out.decode())
    if not R.fuse_s:
        nf = tower.quote_surface(nf)
    steps = alloc = 0
    m = re.search(r"(?:steps|rounds)=(\d+)\s+alloc=(\d+)", err.decode())
    if m:
        steps, alloc = int(m.group(1)), int(m.group(2))
    return nf, steps, alloc


def piece(R: Realization = C_DEFAULT):
    """The C kernel as a catalog HostPiece (kind='cpu')."""
    import host_pieces as hp
    return hp.HostPiece(
        name="native.c", kind="cpu",
        reduce=lambda t, fuel=100_000: _reduce_via(t, R))


def main() -> int:
    """Stage-machinery + kernel check: emit the reducer .c for both
    builds, compile, and run goldens through it — the same
    observational contract as run_native (stdout NF + stderr stats +
    rc).  Expected NF text is derived from seed's own term model
    (bc_decompile + trailing space per token + newline), never
    hardcoded."""
    import seed as _seed
    import tempfile
    import target_c
    ok = True

    def nf_text(t) -> str:
        return "".join(c + " " for c in _seed.bc_decompile(t)) + "\n"

    ds_nf = nf_text(_seed.DERIVED_S_T)
    goldens = [
        # label, input, expected stdout, expected rc (None = don't check out)
        ("empty", "", "I \n", 0),
        ("I K -> K", "I K @", "K \n", 0),
        ("S K K I -> I", "S K @ K @ I @", "I \n", 0),
        ("dup W K I -> I", "W K @ I @", "I \n", 0),
        ("swap C B K I -> B I K", "C B @ K @ I @", "B I @ K @ \n", 0),
        ("underflow @", "@", "I \n", 0),
        ("bad byte", "I \x01", "", 3),
        ("K ds I -> ds (default only)", "K S @ I @", None, 0),
    ]
    for fuse_s in (False, True):
        R = Realization(abi="hosted", fuse_s=fuse_s)
        c_src = emit_c(R)
        tag = "fuse_s" if fuse_s else "default"
        with tempfile.TemporaryDirectory() as td:
            c_path = os.path.join(td, "reducer.c")
            exe_path = os.path.join(td, "reducer.exe")
            with open(c_path, "wb") as f:
                f.write(c_src)
            try:
                target_c.compile_c(c_path, exe_path)
            except RuntimeError as e:
                print(f"  FAIL {tag}: cc failed: {e}")
                print(c_src.decode())
                return 1
            for label, inp, want_nf, want_rc in goldens:
                nf_expected = want_nf
                if label == "K ds I -> ds (default only)":
                    if fuse_s:
                        # fuse_s build: S is primitive — K S I -> S,
                        # stdout is the bare S token
                        nf_expected = "S \n"
                    else:
                        nf_expected = ds_nf
                out, err, rc = target_c.run_exe(exe_path, inp.encode())
                nf = out.decode()
                good = (nf == nf_expected) and rc == want_rc
                print(f"  {'ok' if good else 'FAIL'} {tag} {label}: "
                      f"nf={nf!r} rc={rc} err={err.decode().strip()!r}")
                ok = ok and good

    # seed.emit generic path must produce the same translation unit —
    # the toolchain entry drives the identical stage machinery.
    import toolchain
    R = Realization(abi="hosted")
    via_emit = _seed.emit(R, tc=toolchain.by_name("native.c"))
    good = via_emit == emit_c(R)
    print(f"  {'ok' if good else 'FAIL'} seed.emit(native.c) == emit_c")
    ok = ok and good

    # HostPiece roundtrip: S K K I -> I under operEq.
    from reduce import I as HI, KK as HK, S as HS, app as happ
    p = piece(Realization(abi="hosted"))
    nf, steps, alloc = p.reduce(happ(happ(happ(HS, HK), HK), HI))
    good = nf == HI and steps > 0 and alloc > 0
    print(f"  {'ok' if good else 'FAIL'} piece native.c S K K I -> {nf} "
          f"(steps={steps} alloc={alloc})")
    ok = ok and good
    print(f"{'OK' if ok else 'FAIL'} routines_c")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
