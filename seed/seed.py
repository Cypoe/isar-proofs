"""
SEED — native x86-64 realization of Lean `IStepBasis` as a real PE.

Invariant : IStepBasis = IStepCore ∪ IStepKMacro (Kernel.lean §15):
            L0 agents normβ, compβ, dupβ, swapβ (+ appL/appR, leftmost-
            outermost); L1 fused K-macro konstβ.  The Python mirror in §1
            is a reference transcription of `src/ISAR/Kernel.lean` and the
            host basis reducer (host/graph_runtime.py, the `graph.lo`
            piece).  S is a *view-level derived word* by default: the input
            alphabet admits `S`, but the parser instantiates `derived_s`
            (an L0-only tree) per token — no sβ rule is emitted.
            `Realization.fuse_s=True` instead keeps S primitive with sβ.
Basis     : §0 carries the ISARMatrices signature algebra.  The matrix
            signature fixes the tag set — it is NOT the β-semantics
            (β-reduction does not preserve signatures).  `comp` and `var`
            share the zero matrix by Lean convention; tags are keyed on
            the atom name, never on the matrix value.
Strategy  : `Realization` (§2) — a frozen data record: evaluation order,
            node layout, allocation discipline, fuel policy, stack reserve,
            read granule, fuse_s, ABI.  `order="cd"` is a declared
            parameter value but is *refused* (NotRealized) — mine_adopt
            semantics, never a fallback.
Chain     : §3 emit() — the seed = basis + mirror + strategy + chain
            driver; ISA (host/isa_x86_64), reducer routines
            (host/routines_x86_64_win64) and the PE64 target
            (host/target_pe64) are host DATA the cogen lists/chooses/
            refuses via host/toolchain.py's CATALOG.
Mechanism : toolchain.resolve -> isa.assemble -> target.pack
            (build_pe is a compat alias for emit).
Oracles   : fasmg.exe (byte equality, env ISAR_FASMG — via
            isa_x86_64), host graph.lo piece / graph_runtime (basis NF
            equality), host reduce.py (surface NF for the fuse_s
            build) — host modules imported lazily in §7/§8 only, except
            toolchain which is the §3 chain catalog.

Gates: G0 signature algebra + homomorphism | G0b signature-free emission
| G1 encoder vs fasmg | G2 basis mirror vs host graph.lo | G3 native exe
end-to-end (both builds) | G4 strategy variations + cd refusal + fuel |
G5 host registration (cogen.choose -> cpu, native_realize, piece
adoption through both builds).

Hard rules: no fixed heap (chunked VirtualAlloc growth), fuel optional
(default off — run to NF), cd refused, no cross-repo *code* (oracle
binaries and host oracle modules only).  §0–§2 import nothing from
host; §3 imports only host/toolchain (the catalog) and touches ISA/
routines/target solely through resolve(); §7–§8 import host oracle
modules lazily.
"""
from __future__ import annotations

import os
import re
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass, fields
from enum import IntEnum
from typing import Dict, List, Optional, Sequence, Tuple, Union

SEED_DIR = os.path.dirname(os.path.abspath(__file__))
BUILD_DIR = os.path.join(SEED_DIR, "build")

_HOST_DIR = os.path.normpath(os.path.join(SEED_DIR, "..", "host"))
if _HOST_DIR not in sys.path:
    sys.path.insert(0, _HOST_DIR)
import toolchain                      # noqa: E402  host catalog (see §3 CHAIN)

NotRealized = toolchain.NotRealized   # owned by host/toolchain.py, re-exported


# ======================================================================
# §0  BASIS (ISARMatrices signature algebra — data, not semantics)
#
# The 4x4 signature fixes the tag SET (§1 generates Tag from SIGNATURE's
# keys); it is NOT the β-semantics — β does not preserve signatures.
# `comp` and `var` share the zero matrix by Lean convention; SIGNATURE is
# keyed on the atom name, never on the matrix value.
# ======================================================================

Matrix = Tuple[int, ...]          # 16 ints, row-major


def mul(A: Matrix, B: Matrix) -> Matrix:
    out = []
    for i in range(4):
        for j in range(4):
            out.append(sum(A[i * 4 + k] * B[k * 4 + j] for k in range(4)))
    return tuple(out)


zero: Matrix = (0,) * 16
I_id: Matrix = (1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)
# Version-1 carrier basis (Kernel isar_categorical_proof)
I1: Matrix = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)
R1: Matrix = (1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0)
A1: Matrix = (0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
S1: Matrix = (1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)
K1: Matrix = mul(mul(mul(I1, R1), A1), S1)
# Version-2 carrier basis (verify_isar_ZFC)
I2: Matrix = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)
R2: Matrix = (1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0)
A2: Matrix = (0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
S2: Matrix = (1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)
K2: Matrix = mul(mul(mul(I2, R2), A2), S2)
# Gauge equivalence
P: Matrix = (1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)
P_inv: Matrix = (1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)

BASIS: Dict[str, Matrix] = {"I": I1, "R": R1, "A": A1, "S": S1}

# term_signature_val (BasisCompleteness.lean): atom name -> Matrix4.
SIGNATURE: Dict[str, Matrix] = {
    "norm": I1, "konst": K1, "s": S1, "comp": zero,
    "dup": A1, "swap": R1, "var": zero,
}

# Derived words as term data: a pair (f, x) means app(f, x), a string is an
# atom name from SIGNATURE.  (Kernel.lean `derived_s`, `derived_k_signature`.)
DERIVED_S = (
    ("comp", ("comp", "dup")),
    (("swap", (("comp", "comp"), (("comp", "comp"), "swap"))), "norm"),
)
DERIVED_K_SIG = ((("norm", "swap"), "dup"), "s")


# ======================================================================
# §1  KERNEL MIRROR (reference, Python) — self-contained
# ======================================================================

# Tag is GENERATED from SIGNATURE's keys (+ APP).  Numbering preserves the
# previous {APP,I,K,S,B} assignment: norm=1 konst=2 s=3 comp=4 dup=5 swap=6.
_ATOMS = [k for k in SIGNATURE if k != "var"]
Tag = IntEnum("Tag", {"APP": 0, **{a: i + 1 for i, a in enumerate(_ATOMS)}})

# Input/output alphabet generated from Tag: single uppercase letters.
TOKEN: Dict[str, "Tag"] = {
    "I": Tag.norm, "K": Tag.konst, "S": Tag.s,
    "B": Tag.comp, "W": Tag.dup, "C": Tag.swap,
}
CHAR_OF: Dict["Tag", str] = {v: k for k, v in TOKEN.items()}


class T:
    __slots__ = ("tag", "l", "r")

    def __init__(self, tag: int, l: "Optional[T]" = None, r: "Optional[T]" = None):
        self.tag = tag
        self.l = l
        self.r = r

    def __eq__(self, o) -> bool:
        return (isinstance(o, T) and self.tag == o.tag
                and self.l == o.l and self.r == o.r)

    def __repr__(self) -> str:
        if self.tag == Tag.APP:
            return f"({self.l} {self.r})"
        return CHAR_OF[Tag(self.tag)]

    def __hash__(self):
        return hash((self.tag, id(self.l), id(self.r)))


TI = T(Tag.norm)
TK = T(Tag.konst)
TS = T(Tag.s)
TB = T(Tag.comp)
TW = T(Tag.dup)
TC = T(Tag.swap)


def app(f: T, x: T) -> T:
    return T(Tag.APP, f, x)


def _mk(word) -> T:
    """Instantiate a §0 derived word (tuple-of-tuples) as a term."""
    if isinstance(word, str):
        return T(Tag[word])
    return app(_mk(word[0]), _mk(word[1]))


DERIVED_S_T = _mk(DERIVED_S)
DERIVED_K_SIG_T = _mk(DERIVED_K_SIG)


def signature(t: T) -> Matrix:
    """term_signature_val: atom -> SIGNATURE, app -> mul (homomorphism)."""
    if t.tag == Tag.APP:
        return mul(signature(t.l), signature(t.r))
    return SIGNATURE[Tag(t.tag).name]


# Pattern table as documentation-as-data (Lean IStepBasis rule order).
RULES = (
    ("normβ",  "I x        -> x           (L0)"),
    ("konstβ", "K a b      -> a           (L1 fused macro)"),
    ("dupβ",   "W f x      -> f x x       (L0)"),
    ("compβ",  "B f g x    -> f (g x)     (L0)"),
    ("swapβ",  "C f x y    -> f y x       (L0)"),
    ("sβ",     "S f g x    -> (f x)(g x)  (surface, fuse_s only)"),
)


def step(t: T, fuse_s: bool = False) -> Optional[T]:
    """LO single step = Lean `IStepBasis` (L0 β + L1 konst macro + appL/R).

    `fuse_s=True` adds the surface sβ rule (strategy); by default S never
    reaches the reducer — the parser instantiates `derived_s` instead.
    """
    if t.tag != Tag.APP:
        return None
    f, x = t.l, t.r
    if f.tag == Tag.norm:                       # normβ: I x -> x
        return x
    if f.tag == Tag.APP:
        fl, fr = f.l, f.r
        if fl.tag == Tag.konst:                 # konstβ: K a b -> a
            return fr
        if fl.tag == Tag.dup:                   # dupβ: W f x -> f x x
            return app(app(fr, x), x)
        if fl.tag == Tag.APP:
            fll, flr = fl.l, fl.r
            if fll.tag == Tag.comp:             # compβ: B f g x -> f (g x)
                return app(flr, app(fr, x))
            if fll.tag == Tag.swap:             # swapβ: C f x y -> f y x
                return app(app(flr, x), fr)
            if fuse_s and fll.tag == Tag.s:     # sβ: S f g x -> (f x)(g x)
                return app(app(flr, x), app(fr, x))
    sf = step(f, fuse_s)                        # appL
    if sf is not None:
        return app(sf, x)
    sx = step(x, fuse_s)                        # appR
    if sx is not None:
        return app(f, sx)
    return None


def reduce(t: T, fuel: Optional[int] = None,
           fuse_s: bool = False) -> Tuple[T, int]:
    """Iterate LO step until NF (fuel=None) or exhaustion."""
    cur, n = t, 0
    while fuel is None or n < fuel:
        nxt = step(cur, fuse_s)
        if nxt is None:
            break
        cur = nxt
        n += 1
    return cur, n


def bc_compile(tokens: str, fuse_s: bool = False) -> T:
    """Lean BytecodeView.run incl. underflow rules, then head of stack.

    With fuse_s=False the `S` token pushes the derived_s tree (view
    expansion); with fuse_s=True it pushes the primitive s atom.
    """
    st: List[T] = []
    for ch in tokens:
        if ch in TOKEN:
            st.insert(0, DERIVED_S_T if (ch == "S" and not fuse_s) else T(TOKEN[ch]))
        elif ch == "@":
            if len(st) >= 2:
                x, y = st[0], st[1]
                st = [app(y, x)] + st[2:]
            elif len(st) == 1:
                st = [TI, st[0]]
            else:
                st = [TI]
        elif ch in " \t\r\n,":
            continue
        else:
            raise ValueError(f"bad input byte: {ch!r}")
    return st[0] if st else TI


def bc_decompile(t: T) -> str:
    """Postfix single-char tokens over the full alphabet + '@'."""
    if t.tag == Tag.APP:
        return bc_decompile(t.l) + bc_decompile(t.r) + "@"
    return CHAR_OF[Tag(t.tag)]


def t_to_host(t: T, H):
    """Convert seed T -> host reduce.T (H = host reduce module)."""
    if t.tag == Tag.APP:
        return H.app(t_to_host(t.l, H), t_to_host(t.r, H))
    return {
        Tag.norm: H.I, Tag.konst: H.KK, Tag.s: H.S,
        Tag.comp: H.B, Tag.dup: H.D, Tag.swap: H.C,
    }[Tag(t.tag)]


def t_from_host(h) -> T:
    """Convert host reduce.T -> seed T."""
    from_host = {
        "NORM": Tag.norm, "KONST": Tag.konst, "S": Tag.s,
        "COMP": Tag.comp, "DUP": Tag.dup, "SWAP": Tag.swap,
    }
    if h.k.name == "APP":
        return app(t_from_host(h.l), t_from_host(h.r))
    return T(from_host[h.k.name])


# ======================================================================
# §2  REALIZATION (strategy as data)
# ======================================================================

@dataclass(frozen=True)
class Realization:
    order: str = "lo"                 # "lo" realized | "cd" declared, REFUSED
    node_bytes: int = 24              # {tag:u64 @0, l:ptr @8, r:ptr @16}
    alloc: str = "bump-chunked"       # VirtualAlloc(chunk) on exhaustion
    chunk_bytes: int = 1 << 20
    fuel: Optional[int] = None        # None = run to NF; int = exit 2 on exhaustion
    stack_reserve: int = 64 << 20     # PE SizeOfStackReserve
    read_buf_bytes: int = 64 << 10    # read granule, NOT a cap: input streams
                                    # through one buffer of this size, parsed
                                    # chunk-by-chunk; total input is unbounded
    io: tuple = ("stdin", "stdout")
    abi: str = "win64"
    fuse_s: bool = False              # False: `S` token instantiates derived_s
                                      # (IStepBasis only); True: primitive sβ
    reclaim: str = "none"             # GC slot — explicitly none this wave


DEFAULT = Realization()


# ======================================================================
# §3  CHAIN (toolchain.resolve -> isa.assemble -> target.pack)
#
# The seed only seeds: ISA, reducer routines and the PE64 container are
# host data modules (host/isa_x86_64.py, host/routines_x86_64_win64.py,
# host/target_pe64.py) listed in host/toolchain.py's CATALOG.  emit()
# resolves the toolchain, assembles the program, packs the image.
# ======================================================================

def emit(R: Realization = DEFAULT, tc=None) -> bytes:
    """Module-agnostic chain: resolve the toolchain, assemble the routines'
    program against the target's symbol table at its text base, pack."""
    tc = tc or toolchain.by_name("native.x86_64.pe")
    isa, rts, tgt = toolchain.resolve(tc)
    prog = rts.program(R)
    text, labels = isa.assemble(
        prog, tgt.symbols(rts.imports, rts.data_slots), base=tgt.text_base)
    return tgt.pack(text, labels, rts.imports, rts.data_slots, R)


def build_pe(R: Realization = DEFAULT) -> bytes:
    """Compatibility alias: emit the realized toolchain's PE image."""
    return emit(R)


def write_exe(path: str, R: Realization = DEFAULT) -> str:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(build_pe(R))
    return path


# ======================================================================
# §7  HOST-FACING API (lazy host imports via sys.path ../host)
# ======================================================================

def _host():
    hdir = os.path.normpath(os.path.join(SEED_DIR, "..", "host"))
    if hdir not in sys.path:
        sys.path.insert(0, hdir)
    import reduce as hreduce        # noqa: E402
    import bytecode_dialect as bcd  # noqa: E402
    import host_pieces as hp        # noqa: E402
    return hreduce, bcd, hp


def run_native(exe: str, tokens_text: str) -> Tuple[str, str, int]:
    cp = subprocess.run([exe], input=tokens_text.encode(),
                        capture_output=True, timeout=600)
    return cp.stdout.decode("utf-8", "replace"), \
        cp.stderr.decode("utf-8", "replace"), cp.returncode


_EXE_CACHE: Dict[str, str] = {}


def _exe_for(R: Realization = DEFAULT) -> str:
    key = repr(R)
    if key not in _EXE_CACHE:
        tag = "default" if R == DEFAULT else \
            f"v{abs(hash(key)) & 0xFFFF:x}"
        _EXE_CACHE[key] = write_exe(
            os.path.join(BUILD_DIR, f"reducer_{tag}.exe"), R)
    return _EXE_CACHE[key]


def _parse_native_out(text: str):
    """Parse native NF tokens 'I K S B W C @' -> host T."""
    hreduce, bcd, hp = _host()
    leaf = {"I": hreduce.I, "K": hreduce.KK, "S": hreduce.S,
            "B": hreduce.B, "W": hreduce.D, "C": hreduce.C}
    st: list = []
    for tok in text.split():
        if tok in leaf:
            st.insert(0, leaf[tok])
        elif tok == "@":
            if len(st) >= 2:
                x, y = st[0], st[1]
                st = [hreduce.app(y, x)] + st[2:]
            elif len(st) == 1:
                st = [hreduce.I, st[0]]
            else:
                st = [hreduce.I]
        else:
            raise ValueError(f"bad NF token {tok!r}")
    return st[0] if st else hreduce.I


def _tokens_of_term(t) -> str:
    """Host T -> native input token text (postfix, full alphabet)."""
    hreduce, bcd, hp = _host()
    if t.k.name == "APP":
        return _tokens_of_term(t.l) + " " + _tokens_of_term(t.r) + " @"
    return {
        "NORM": "I", "KONST": "K", "S": "S",
        "COMP": "B", "DUP": "W", "SWAP": "C",
    }[t.k.name]


def _reduce_via(t, R: Realization):
    """HostPiece.reduce signature: (T_host, fuel) -> (nf, steps, alloc).

    The `fuel` argument is intentionally ignored: it is a graph-piece
    parameter, while native fuel is governed by Realization.fuel baked
    into the generated executable.

    Observation discipline mirrors host graph.lo: for the default build
    the input term is `translate_to_basis` (S expands to derived_s), the
    native NF tokens are parsed back, and `quote_surface` folds any exact
    derived_s subtree back to S — the same view the graph piece applies.
    """
    hreduce, bcd, hp = _host()
    import tower
    if not R.fuse_s:
        t = tower.translate_to_basis(t)
    out, err, rc = run_native(_exe_for(R), _tokens_of_term(t))
    if rc != 0:
        raise RuntimeError(f"native reducer rc={rc} stderr={err!r}")
    nf = _parse_native_out(out)
    if not R.fuse_s:
        nf = tower.quote_surface(nf)
    steps = alloc = 0
    import re
    m = re.search(r"steps=(\d+)\s+alloc=(\d+)", err)
    if m:
        steps, alloc = int(m.group(1)), int(m.group(2))
    return nf, steps, alloc


def reduce_native(t, fuel: Optional[int] = None):
    return _reduce_via(t, DEFAULT)


def piece(R: Realization = DEFAULT):
    _, _, hp = _host()
    name = "native.x86_64.pe" if R == DEFAULT else \
        f"native.x86_64.pe.fuse_s"
    return hp.HostPiece(
        name=name, kind="cpu",
        reduce=lambda t, fuel=100_000: _reduce_via(t, R))


# ======================================================================
# §8  ORACLES + GATES
# ======================================================================

# The gates reach the realized chain's data modules directly (§8 is
# oracle/gate plumbing; §3 stays module-agnostic).  Lazy access for
# _routines: it imports seed back, so only function bodies may touch it.
import isa_x86_64 as _isa                    # noqa: E402
import routines_x86_64_win64 as _routines    # noqa: E402
import target_pe64 as _target                # noqa: E402

Insn = _isa.Insn
Program = _isa.Program
LBL = _isa.LBL
I = _isa.I
INSN = _isa.INSN
FORMS = _isa.FORMS
encode = _isa.encode
render_fasm = _isa.render_fasm
assemble = _isa.assemble
_fasmg = _isa._fasmg
_FASM_HDR = _isa._FASM_HDR
FASMG = _isa.FASMG
TEXT_RVA = _target.TEXT_RVA


def reducer_program(R: Realization) -> Program:
    return _routines.program(R)


def _lean_matrices(path: str) -> Dict[str, Matrix]:
    """Parse `def NAME : Matrix4 where` blocks from ISARMatrices.lean into
    row-major 16-tuples (read-only file oracle, like fasmg.exe)."""
    out: Dict[str, Matrix] = {}
    name = None
    vals: Dict[str, int] = {}
    for line in open(path, encoding="utf-8"):
        m = re.match(r"def\s+(\w+)\s*:\s*Matrix4\s+where", line)
        if m:
            name = m.group(1)
            vals = {}
            continue
        if name is None:
            continue
        for mm in re.finditer(r"m([0-3])([0-3])\s*:=\s*(-?\d+)", line):
            vals[mm.group(1) + mm.group(2)] = int(mm.group(3))
        if len(vals) == 16:
            if name != "zero":
                out[name] = tuple(
                    vals[f"{i}{j}"] for i in range(4) for j in range(4))
            name = None
    return out


def _lean_signature(path: str, mats: Dict[str, Matrix]) -> Dict[str, Matrix]:
    """Parse `term_signature_val` `| .atom => expr` lines from
    BasisCompleteness.lean; products are evaluated with `mul`."""
    atoms = {"var": "var", "norm": "norm", "sₛ": "s", "konst": "konst",
             "dup": "dup", "swap": "swap", "comp": "comp"}
    sig: Dict[str, Matrix] = {}
    in_fn = False
    for line in open(path, encoding="utf-8"):
        if "term_signature_val" in line and "=>" not in line:
            in_fn = True
            continue
        if not in_fn:
            continue
        m = re.match(r"\s*\|\s*\.(\S+).*?=>\s*(.+)", line)
        if not m:
            if in_fn and sig:
                break
            continue
        atom, expr = m.group(1), m.group(2).strip()
        if atom not in atoms or atom == "app":
            continue
        factors = [f.strip() for f in expr.split("*")]
        acc = I_id
        for f in factors:
            acc = mul(acc, zero if f == "zero" else mats[f])
        sig[atoms[atom]] = acc
    return sig


def _g0() -> bool:
    """Signature algebra: reproduce the rfl theorems + the app↔mul hom."""
    ok = True
    checks = [
        ("I1*I1==I1", mul(I1, I1) == I1),
        ("K1*K1==zero", mul(K1, K1) == zero),
        ("I2*I2==I2", mul(I2, I2) == I2),
        ("K2*K2==zero", mul(K2, K2) == zero),
        ("P_inv*P==I_id", mul(P_inv, P) == I_id),
        ("P*P_inv==I_id", mul(P, P_inv) == I_id),
        ("P*K1*P_inv==K2", mul(mul(P, K1), P_inv) == K2),
        ("sig(derived_k_signature)==K1", signature(DERIVED_K_SIG_T) == K1),
    ]
    for name, good in checks:
        if not good:
            print(f"  FAIL {name}")
            ok = False
    # Literal cross-check against the Lean source (read-only file oracle).
    lean_dir = os.path.normpath(os.path.join(SEED_DIR, "..", "src", "ISAR"))
    mats_path = os.path.join(lean_dir, "ISARMatrices.lean")
    comp_path = os.path.join(lean_dir, "BasisCompleteness.lean")
    try:
        lm = _lean_matrices(mats_path)
        names = ["I1", "R1", "A1", "S1", "I2", "R2", "A2", "S2",
                 "I_id", "P", "P_inv"]
        bad = [n for n in names if lm.get(n) != globals()[n]]
        if bad:
            print(f"  FAIL literals != ISARMatrices.lean: {bad}")
            ok = False
        else:
            print(f"  ok {len(names)} literals == ISARMatrices.lean")
    except (OSError, KeyError) as e:
        print(f"  FAIL ISARMatrices.lean oracle: {e}")
        ok = False
        lm = {}
    try:
        lsig = _lean_signature(comp_path, {**lm, "zero": zero})
        bad = [k for k in SIGNATURE if lsig.get(k) != SIGNATURE[k]]
        if bad or len(lsig) != len(SIGNATURE):
            print(f"  FAIL SIGNATURE != term_signature_val: {bad}")
            ok = False
        else:
            print(f"  ok {len(lsig)} SIGNATURE keys == term_signature_val")
    except (OSError, KeyError) as e:
        print(f"  FAIL BasisCompleteness.lean oracle: {e}")
        ok = False
    # sig(app f x) == mul(sig f, sig x) on random terms (hom property)
    for text in _random_progs(32, alphabet="IKSBWC@"):
        t = bc_compile(text, fuse_s=True)
        if t.tag == Tag.APP:
            good = signature(t) == mul(signature(t.l), signature(t.r))
            if not good:
                print(f"  FAIL sig hom on {text}")
                ok = False
    print(f"  ok signature algebra ({len(checks)} checks + hom on 32 terms)")
    return ok


def _g0b() -> bool:
    """Signature-free emission: no matrix bytes, no sβ in default .text."""
    ok = True
    text = _text_offsets(build_pe(DEFAULT))
    mats = list(BASIS.values()) + [K1]
    for w in (1, 2, 4, 8):
        for mi, m in enumerate(mats):
            pat = b"".join(
                struct.pack("<b" if w == 1 else {2: "<h", 4: "<i", 8: "<q"}[w],
                            v) for v in m)
            if pat in text:
                print(f"  FAIL matrix {mi} pattern at width {w} in .text")
                ok = False
    labels_d = {i[1] for i in reducer_program(DEFAULT) if i[0] == "label"}
    labels_f = {i[1] for i in reducer_program(Realization(fuse_s=True))
                if i[0] == "label"}
    if "st_s" in labels_d:
        print("  FAIL sβ (st_s) emitted in default build")
        ok = False
    if "st_s" not in labels_f or "build_ds" in labels_f:
        print("  FAIL fuse_s build missing st_s / has build_ds")
        ok = False
    if "build_ds" not in labels_d:
        print("  FAIL default build missing build_ds")
        ok = False
    return ok


def _g1() -> bool:
    ok = _isa.check_rows()
    # whole-program: assemble reducer .text, compare with fasmg on the same
    # rendered listing (rel32 via labels, rip via computed displacements).
    prog = reducer_program(DEFAULT)
    idata, iat_syms = _target.build_idata(_routines.IMPORTS)
    data, data_syms = _target.build_data(_routines.DATA_SLOTS)
    all_syms = dict(iat_syms)
    all_syms.update(data_syms)
    local: Dict[str, int] = {}
    pos = 0
    offs = []
    for item in prog:
        if item[0] == "label":
            local[item[1]] = TEXT_RVA + pos
        offs.append(pos)
        if item[0] != "label":
            pos += len(encode(item[1:]))
    src_lines = []
    for item, off in zip(prog, offs):
        if item[0] == "label":
            src_lines.append(f"{item[1]}:")
            continue
        insn = item[1:]
        end = TEXT_RVA + off + len(encode(insn))
        resolver = lambda name, _e=end: (
            all_syms[name] if name in all_syms else local[name]) - _e
        src_lines.append("  " + render_fasm(insn, resolve=resolver))
    try:
        want = _fasmg(_FASM_HDR + "\n".join(src_lines) + "\n")
        got2 = bytearray()
        for item, off in zip(prog, offs):
            if item[0] == "label":
                continue
            insn = item[1:]
            end = TEXT_RVA + off + len(encode(insn))
            resolver = lambda name, _e=end: (
                all_syms[name] if name in all_syms else local[name]) - _e
            got2 += encode(insn, resolve=resolver)
        if bytes(got2) != want:
            for i, (a, b) in enumerate(zip(bytes(got2), want)):
                if a != b:
                    print(f"  FAIL whole-program: first diff at 0x{i:x}: "
                          f"{a:02x} != {b:02x}")
                    break
            else:
                print(f"  FAIL whole-program: len {len(got2)} != {len(want)}")
            ok = False
    except Exception as e:
        print(f"  FAIL whole-program oracle: {e}")
        ok = False
    return ok


def _random_progs(n: int, seed_: int = 83,
                  alphabet: str = "IKS@") -> List[str]:
    import random
    rng = random.Random(seed_)
    out = []
    for _ in range(n):
        k = rng.randint(1, 14)
        out.append(" ".join(rng.choice(alphabet) for _ in range(k)))
    return out


def _deep_terms():
    """≥3 SKI Church-arithmetic terms with >1000 host steps (fuel 1e6)."""
    hreduce, bcd, hp = _host()
    zero = hreduce.app(hreduce.KK, hreduce.I)
    succ = hreduce.app(hreduce.S, hreduce.app(
        hreduce.app(hreduce.S, hreduce.app(hreduce.KK, hreduce.S)), hreduce.KK))

    def num(n):
        t = zero
        for _ in range(n):
            t = hreduce.app(succ, t)
        return t
    return [
        ("church mul 25 10", hreduce.app(
            hreduce.app(num(25), hreduce.app(num(10), succ)), zero)),
        ("church exp 3 5", hreduce.app(hreduce.app(
            hreduce.app(num(5), num(3)), succ), zero)),
        ("church mul 20 15", hreduce.app(
            hreduce.app(num(20), hreduce.app(num(15), succ)), zero)),
    ]


def _tokens_of_prog(prog) -> str:
    _, bcd, _ = _host()
    m = {bcd.Instr.PUSH_I: "I", bcd.Instr.PUSH_K: "K",
         bcd.Instr.PUSH_S: "S", bcd.Instr.APP: "@"}
    return " ".join(m[i] for i in prog)


def _g2() -> bool:
    hreduce, bcd, hp = _host()
    import tower
    ok = True
    # (a) basis mirror (fuse_s=False, S expands via derived_s) vs graph.lo:
    # the host basis reducer — same translate-then-IStepBasis discipline.
    graph = hp.by_name("graph.lo")
    basis_cases: List[Tuple[str, T]] = []
    for text in _random_progs(32, alphabet="IKSBWC@"):
        try:
            basis_cases.append((text, bc_compile(text)))
        except ValueError:
            pass
    for label, prog, _exp in bcd.GOLDENS:
        basis_cases.append(("bc:" + label, bc_compile(_tokens_of_prog(prog))))
    for label, sterm in basis_cases:
        nf_s, st_s = reduce(sterm, fuel=1_000_000)
        nf_h, st_h, _ = graph.reduce(
            tower.translate_to_basis(t_to_host(sterm, hreduce)),
            fuel=1_000_000)
        # NF equality only: graph.lo shares redexes (dag), the mirror walks
        # the tree — step counts legitimately differ on shared subterms.
        good = tower.quote_surface(t_to_host(nf_s, hreduce)) == nf_h
        if not good:
            print(f"  FAIL basis {label}: seed {nf_s}/{st_s} "
                  f"vs graph.lo {nf_h}/{st_h}")
            ok = False
    print(f"  ok basis mirror vs graph.lo: {len(basis_cases)} terms")
    # (b) fused mirror (fuse_s=True, primitive sβ) vs host reduce.py surface.
    surf_cases: List[Tuple[str, T]] = []
    for label, term, _exp in hreduce.GOLDENS:
        surf_cases.append((label, t_from_host(term)))
    for text in _random_progs(24, alphabet="IKS@"):
        try:
            surf_cases.append((text, bc_compile(text, fuse_s=True)))
        except ValueError:
            pass
    for label, sterm in surf_cases:
        nf_s, st_s = reduce(sterm, fuel=1_000_000, fuse_s=True)
        nf_h, st_h = hreduce.reduce(t_to_host(sterm, hreduce), fuel=1_000_000)
        good = (nf_s == t_from_host(nf_h)) and st_s == st_h
        if not good:
            print(f"  FAIL surface {label}: seed {nf_s}/{st_s} "
                  f"vs host {nf_h}/{st_h}")
            ok = False
    print(f"  ok fused mirror vs reduce.py: {len(surf_cases)} terms")
    return ok


def _g3_build(R: Realization, probes, exe_bytes: bytes) -> bool:
    """One build's probes.  Expected values come through the view:
    DEFAULT (fuse_s=False) is observed as translate_to_basis + IStepBasis +
    quote_surface — exactly graph.lo's import/reduce/export discipline;
    fuse_s=True is observed raw against host reduce.py (surface IStep+sβ)."""
    hreduce, bcd, hp = _host()
    import tower
    graph = hp.by_name("graph.lo")
    exe = _exe_for(R)
    ok = True
    for label, text, t in probes:
        try:
            term = t if t is not None else bcd.compile_bytecode(
                bcd.parse_prog(text))
            sterm = bc_compile(text, fuse_s=R.fuse_s)
            nf_seed, steps_seed = reduce(sterm, fuel=1_000_000,
                                         fuse_s=R.fuse_s)
            if R.fuse_s:
                nf_ref, steps_ref = hreduce.reduce(term, fuel=1_000_000)
                expect_nf = nf_ref
            else:
                # NF oracle is graph.lo (same IStepBasis discipline); its
                # step count is dag-shared and lower, so the count oracle
                # is the §1 mirror, which walks the tree like the exe.
                nf_ref, _, _ = graph.reduce(term, fuel=1_000_000)
                steps_ref = steps_seed
                expect_nf = nf_ref
            out, err, rc = run_native(exe, text)
            line = out.strip()
            good = rc == 0
            detail = ""
            if good:
                got = _parse_native_out(line)
                if not R.fuse_s:
                    got = tower.quote_surface(got)
                    seed_nf_h = tower.quote_surface(t_to_host(nf_seed, hreduce))
                else:
                    seed_nf_h = t_to_host(nf_seed, hreduce)
                good = (got == expect_nf) and (seed_nf_h == expect_nf)
                import re
                m = re.search(r"steps=(\d+)", err)
                steps_native = int(m.group(1)) if m else -1
                if steps_native != steps_ref:
                    good = False
                    detail += f" steps {steps_native}!={steps_ref}"
                squashed = text.replace(" ", "")
                if len(squashed) > 4 and squashed.encode() in exe_bytes:
                    good = False
                    detail += " probe-text-in-exe"
            if not good:
                print(f"  FAIL {label}: rc={rc} out={line!r} "
                      f"err={err!r}{detail}")
                ok = False
            else:
                print(f"  ok {label}: nf={line[:120]!r} steps={steps_ref}")
        except Exception as e:
            print(f"  FAIL {label}: {e}")
            ok = False
    return ok


def _g3() -> bool:
    hreduce, bcd, hp = _host()
    ok = True
    probes: List[Tuple[str, str, object]] = []
    for label, prog, _exp in bcd.GOLDENS:
        probes.append((label, _tokens_of_prog(prog), None))
    import mine_adopt as ma
    for i, t in enumerate(ma.default_probes()):
        probes.append((f"probe{i}", _tokens_of_prog(bcd.decompile(t)), t))
    for label, t in _deep_terms():
        probes.append((label, _tokens_of_prog(bcd.decompile(t)), t))
    # streaming-boundary probe: token text > read_buf_bytes (64 KiB granule)
    probes.append(("stream>64KiB", "I K @ " * 20000, None))
    for tag, R in [("default(expanded)", DEFAULT),
                   ("fuse_s", Realization(fuse_s=True))]:
        print(f" build {tag}:")
        exe = _exe_for(R)
        ok = _g3_build(R, probes, open(exe, "rb").read()) and ok
    return ok


def _program_diffs(Ra: Realization, Rb: Realization):
    """Entry-by-entry structural diff: same shape; operands may differ only
    where they equal a Realization field of the respective R."""
    pa, pb = reducer_program(Ra), reducer_program(Rb)
    assert len(pa) == len(pb), (len(pa), len(pb))
    fnames = [f.name for f in fields(Realization)]
    diffs = []

    def walk(x, y, path):
        if x == y:
            return
        if isinstance(x, tuple) and isinstance(y, tuple) and len(x) == len(y):
            for k, (u, v) in enumerate(zip(x, y)):
                walk(u, v, path + (k,))
            return
        hit = [n for n in fnames if getattr(Ra, n) == x and getattr(Rb, n) == y]
        assert hit, f"operand diff not a Realization field: {path} {x!r} {y!r}"
        diffs.append((path, hit[0], x, y))

    for i, (a, b) in enumerate(zip(pa, pb)):
        if a == b:
            continue
        assert a[0] == b[0], (i, a, b)                      # same item kind
        if a[0] == "label":
            assert a[1] == b[1]
            continue
        assert a[1] == b[1], (i, a, b)                    # same insn form
        assert len(a) == len(b)
        for j, (x, y) in enumerate(zip(a[2:], b[2:])):
            walk(x, y, (i, j))
    return diffs


def _text_offsets(pe: bytes) -> bytes:
    """Extract .text section bytes from a built PE image."""
    raw_ptr = struct.unpack_from("<I", pe, 0x40 + 4 + 20 + 0xF0 + 0x10 + 4)[0]
    raw_sz = struct.unpack_from("<I", pe, 0x40 + 4 + 20 + 0xF0 + 0x10)[0]
    return pe[raw_ptr:raw_ptr + raw_sz]


def _variant_exe(tag: str, R: Realization) -> str:
    return write_exe(os.path.join(BUILD_DIR, f"reducer_{tag}.exe"), R)


def _g4() -> bool:
    hreduce, bcd, hp = _host()
    import tower
    graph = hp.by_name("graph.lo")
    ok = True
    # medium-term probe crossing many 4KiB chunks + streaming boundary
    deep_text = _tokens_of_prog(bcd.decompile(_deep_terms()[0][1]))
    probes = ["I K @", "S K @ K @ I @", "K S @ I @",
              deep_text, "I K @ " * 2000]

    variants = [
        ("chunk4k", Realization(chunk_bytes=4096)),
        ("stack8m", Realization(stack_reserve=8 << 20)),
        ("buf16", Realization(read_buf_bytes=16)),
        ("fuse_s", Realization(fuse_s=True)),
    ]
    for tag, Rv in variants:
        exe = _variant_exe(tag, Rv)
        for text in probes:
            term = bcd.compile_bytecode(bcd.parse_prog(text))
            if Rv.fuse_s:
                nf_ref, steps_ref = hreduce.reduce(term, fuel=1_000_000)
            else:
                nf_ref, _, _ = graph.reduce(term, fuel=1_000_000)
                _, steps_ref = reduce(bc_compile(text), fuel=1_000_000)
            out, err, rc = run_native(exe, text)
            good = rc == 0
            if good:
                got = _parse_native_out(out.strip())
                if not Rv.fuse_s:
                    got = tower.quote_surface(got)
                import re
                m = re.search(r"steps=(\d+)", err)
                good = (got == nf_ref
                        and m and int(m.group(1)) == steps_ref)
            if not good:
                print(f"  FAIL {tag} probe: rc={rc} out={out[:60]!r}")
                ok = False
        print(f"  ok {tag}: {len(probes)} probes NF+steps match")

    # structural diffs: operands may differ only in Realization fields
    for tag, Rv in variants:
        if Rv.fuse_s:
            continue  # fuse_s changes program shape (st_s/build_ds), not operands
        diffs = _program_diffs(DEFAULT, Rv)
        if diffs:
            print(f"  diffs {tag}: {[(d[0], d[1]) for d in diffs]}")
    # .text byte offsets that differ (chunk4k)
    ta, tb = _text_offsets(build_pe(DEFAULT)), _text_offsets(
        build_pe(Realization(chunk_bytes=4096)))
    byte_diffs = [hex(i) for i, (a, b) in enumerate(zip(ta, tb)) if a != b]
    print(f"  .text diff offsets chunk4k: {byte_diffs}")

    # cd refusal
    try:
        build_pe(Realization(order="cd"))
        print("  FAIL order='cd' built silently (fallback)")
        ok = False
    except NotRealized as e:
        print(f"  ok cd refused: {e}")

    # fuel variants on church exp 3 5 under fuse_s=True (3148 surface steps;
    # the expanded build needs ~20x more, so fuel is exercised on the fused
    # strategy where the reference count is the host sβ count)
    exp_text = _tokens_of_prog(bcd.decompile(_deep_terms()[1][1]))
    exe_f = _variant_exe("fuel50", Realization(fuel=50, fuse_s=True))
    out, err, rc = run_native(exe_f, exp_text)
    good = rc == 2 and out.strip() == ""
    print(f"  {'ok' if good else 'FAIL'} fuel=50 -> rc={rc} out={out[:40]!r}")
    ok = ok and good
    exe_f2 = _variant_exe("fuel10k", Realization(fuel=10000, fuse_s=True))
    out2, err2, rc2 = run_native(exe_f2, exp_text)
    term = bcd.compile_bytecode(bcd.parse_prog(exp_text))
    nf_host, steps_host = hreduce.reduce(term, fuel=1_000_000)
    good2 = (rc2 == 0 and _parse_native_out(out2.strip()) == nf_host)
    print(f"  {'ok' if good2 else 'FAIL'} fuel=10000 -> rc={rc2}")
    ok = ok and good2
    return ok


def _g5() -> bool:
    hreduce, bcd, hp = _host()
    import cogen
    import mine_adopt as ma
    ok = True
    hp.register_piece(piece())
    c = cogen.MachineContext.detect()
    plan = cogen.choose(hp.catalog(), cogen.Budget.SERIAL, c)
    good = plan.family == "cpu" and plan.source_piece == "native.x86_64.pe"
    print(f"  {'ok' if good else 'FAIL'} choose SERIAL+x86_64 -> "
          f"{plan.family}/{plan.source_piece}")
    ok = ok and good

    spec, nplan, npiece = cogen.native_realize()
    good = cogen.preserves_spec(spec, npiece)
    print(f"  {'ok' if good else 'FAIL'} native_realize preserves_spec "
          f"({len(spec.probes)} probes)")
    ok = ok and good

    progs = [p for _, p, _ in bcd.GOLDENS]
    r = ma.try_adopt(bcd.compile_bytecode, surfaces=progs,
                     known=[bcd.bytecode_map()])
    good = r.accepted and r.matched_map == "bytecode"
    print(f"  {'ok' if good else 'FAIL'} try_adopt compile_bytecode -> {r}")
    ok = ok and good

    rp = ma.try_adopt_piece(
        npiece, probes=[bcd.compile_bytecode(p) for p in progs])
    good = rp.accepted and rp.matched_map == "graph.lo"
    print(f"  {'ok' if good else 'FAIL'} try_adopt_piece native -> {rp}")
    ok = ok and good

    # same probes through the fuse_s=True build: reference is the host
    # surface reducer (reduce.py: primitive sβ), matching its own view
    fpiece = piece(Realization(fuse_s=True))
    surface = hp.HostPiece(
        name="reduce.py.surface", kind="graph",
        reduce=lambda t, fuel=100_000: (
            lambda nf: (nf[0], nf[1], 0))(hreduce.reduce(t, fuel)))
    rf = ma.try_adopt_piece(
        fpiece, probes=[bcd.compile_bytecode(p) for p in progs],
        reference=surface)
    good = rf.accepted and rf.matched_map == "reduce.py.surface"
    print(f"  {'ok' if good else 'FAIL'} try_adopt_piece fuse_s -> {rf}")
    ok = ok and good
    return ok


def main() -> int:
    results = []
    print("G0 signature algebra")
    try:
        g0 = _g0()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g0 = False
    print(f"{'OK' if g0 else 'FAIL'} G0")
    results.append(g0)

    print("G0b signature-free emission")
    try:
        g0b = _g0b()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g0b = False
    print(f"{'OK' if g0b else 'FAIL'} G0b")
    results.append(g0b)

    # smoke exe at the canonical path
    write_exe(os.path.join(BUILD_DIR, "reducer.exe"), DEFAULT)

    print("G1 encoder vs fasmg")
    try:
        g1 = _g1()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g1 = False
    print(f"{'OK' if g1 else 'FAIL'} G1")
    results.append(g1)

    print("G2 kernel mirror vs host reduce")
    try:
        g2 = _g2()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g2 = False
    print(f"{'OK' if g2 else 'FAIL'} G2")
    results.append(g2)

    print("G3 native exe probes")
    try:
        g3 = _g3()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g3 = False
    print(f"{'OK' if g3 else 'FAIL'} G3")
    results.append(g3)

    print("G4 strategy variations")
    try:
        g4 = _g4()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g4 = False
    print(f"{'OK' if g4 else 'FAIL'} G4")
    results.append(g4)

    print("G5 host registration")
    try:
        g5 = _g5()
    except Exception as e:
        print(f"  FAIL gate error: {e}")
        g5 = False
    print(f"{'OK' if g5 else 'FAIL'} G5")
    results.append(g5)
    return 0 if all(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
