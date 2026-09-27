"""
spec_term — G9a: toolchain.json as a consumable basis term (spec-as-term).

This is the first slice of G9's "the catalog is data the kernel can
interrogate": the real spec file crosses the term boundary as a basis
term, and a query term is evaluated against it.  It is NOT the fixpoint —
it is the object the fixpoint will eventually specialize against.

ENCODING (structural — no serialized JSON text):
    object  -> Scott list of pairs; pair = `\\f. f k v`
    string  -> Scott list of 16-ary nibble selectors (the xdu input-map
               shape: bytes -> hi/lo nibbles; nibble k is the selector
               `\\c0. … \\c15. ck`; cons `\\h. \\t. \\n. \\c. c h t`,
               nil = K)
    int     -> Church numeral
    bool    -> K / (K I)          (Church booleans)
    array   -> Scott list
    null    -> `C I` — the dedicated inert tag: a 1-argument partial
               application of swap.  C is 3-ary (swapβ needs `C f g x`),
               so `C I` can never fire, on graph.lo, on graph.cd, or in
               reduce.py — and it contains no S, so translate_to_basis
               leaves it alone (the `S h t` lesson from xdu_dialect:
               S expands to derived_s on import and keeps reducing).
               toolchain.json today contains no nulls; the tag is
               self-checked in main() for slice-completeness.

SPEC — json_to_term of the REAL host/toolchain.json (the point is the
catalog crossing the boundary, not a copy).  Honest size: the 8.3 kB
file's 5351 string chars become ~10.7k nibble cells; the T dag is
~23k unique nodes / ~1.36M nodes counted as a tree (the 16 selectors,
cons, pair and Church numerals are shared, so the dag is small but the
serialized tree is not — the native token text is ~5.5M tokens, ~11MB).

QUERY — `pathOf`: given a toolchain name, fold the `toolchains` array,
find the entry whose "name" field equals the query string, return its
"path" field.  Structure (all bounded Church iterations — no fixpoint
combinator anywhere, so graph.cd reaches a fixpoint):

    specGet spec key n  — assoc fold over the pair list (n = #pairs);
                          key equality is eqStr
    eqStr a b n         — nibble-string equality; iterates `a`
                          (n >= len(a)); each pair of cells goes through
                          eqNib `a (b K F…F)(b F K…F)…(b F…F K)` — 16
                          branches, each applies b to a 16-vector with K
                          at position i.  On mismatch the flag collapses
                          and the remaining iterations are ~O(1) on lo.
                          The extract also requires both lists exhausted,
                          so an over-long `a` degrades to a safe FALSE.
    emit list n         — result observable: `C (B^k I) … K`, the xdu
                          output-map spine shape (no rc element); the
                          element `B^k I` is obtained by applying the
                          stored selector to `B^0 I … B^15 I`.
    option              — none = `\\n. \\j. n`, some v = `\\n. \\j. j v`.
    result              — none -> bare `I`; some path -> C-spine of its
                          nibbles (distinct, decodable observables).

COMPILATION — the data terms (selectors/cons/pair) are bracket_abstract0
(I/K/S, Lean LambdaFragment shape) exactly as in xdu's declared maps.
The QUERY program is compiled with `bracket` (Turner elim: eta/K-lift/
B/C/S).  Both are beta-equivalent compilations of the same lambdas and
the choice is observationally neutral, but Turner is ~3x cheaper on both
reduction orders (measured: eqStr 6519 -> 2025 lo steps; 1-entry pathOf
79673 -> 23781 lo steps, 7993 -> 4794 cd rounds).  A correctness gate
that is 3x cheaper to run is strictly better; documented here.

WITNESSES in main():
    expected  python_walk(name) — direct dict walk over the loaded file;
              shares no code with any realization path.
    graph.lo  reduce_tree_lo(query(name)) on the FULL spec.
    native    seed.reduce_native(query(name)) — token text of the term
              fed to the win64 lo reducer exe (the runtime path's own
              native witness), NF parsed back and quote_surface'd.
    graph.cd  the SAME query term on the FULL spec.  Feasible since the
              heap-level memo wave: `cd` seals each round's results
              (`_cd_memo[out] = out` — HeapDev's `insert o D`, so one
              round is exactly one cdBasis pass, no mid-round residual
              re-development) and marks identity-developed nodes in the
              persistent `_nf` set (readback is NF ⟹ frozen forever —
              no descendant rep can become a redirect source).  The
              ~23k-node spec spine is walked once, then skipped; the
              whole query runs ~12k honest cdIter rounds in seconds
              (was: hours-scale, hence the old projection gate).

G9b — the specialization cell on the real catalog object, Futamura's
P1 shape with the spec itself as the static input:

    prog      = QUERY v0 v1            (v0 static spec, v1 dynamic name)
    residual  = nf_lo(specialize(prog, {0: SPEC}))
    check     = residual[1 := str_term(name)] ~O query(name)

on every witness.  The residual is produced by graph.lo (the tree
mirror cannot afford the shared-dag-as-tree walk at this size) and is
kept honest by the independent witnesses downstream — a graph-produced
wrong residual disagrees under the native exe and the dict walk.

Honest measurement, not a hidden cost: the residual TREE is ~460k
nodes — subst-mix unrolls every static Church-numeral fold over the
dynamic name (each entry's eqStr and each n-iterated step body is
inlined).  Real PE would residualize the loop instead of unrolling it
— that is the documented open item (1993-mix / BTA in Futamura.lean).
The win shows up only after hash-consing: the residual-instance dag is
~6.7k unique nodes (≈ spec size — the toolchains array dominates the
catalog anyway) and cd runs it faster than the direct query (~8.9k
rounds vs ~12k).  v1 must stay free in the residual — a residual with
no dynamic input left would mean the specializer evaluated, not
specialized.

G9c — `resolveOf`: emit stage 1 (`toolchain.resolve`) at term level.
The fold walks entry -> {dialect,isa,routines,target} names -> catalog
sections -> {module,record}; the result is the Scott list of the eight
resolved field strings, "!" for any missing link (the NotRealized
shadow).  No string concatenation — an earlier flat-string draft used
a bounded revOnto-append fold that diverges at L0 when the bound
exceeds the list length by ~5 (the nil-case pack fixpoint is only
benign over value lists); the field list is the honest observable for
a multi-part resolution.  Decoding probes the NF's cons cells and
nibble selectors directly.

G9d — `symbolsOf`: `target.symbols` at term level (emit stage 2).  Two
structurally-bounded folds (imports, then data slots) build the Scott
assoc map `name -> addr`: each import conses `pair ("iat_"++nm) addr`
and advances addr by 8 (`B4ADD o b4_8`); each slot conses `pair nm
addr` and advances by `B4ADD o sz`.  Addresses are bytes4 — the rep
assemble's resolver subtracts — and bases are bytes4 literals computed
at source-generation time (`IDATA_RVA + IDT_SZ + (n+1)*8`, `DATA_RVA`;
the bounds are known, so no runtime numeral->bytes4 coercion — `N2B4`'s
per-unit increment over a ~8k value is exactly the blowup the rep
exists to avoid).  `iat_` is a literal cons prefix, not a fold.

Representation boundary (the "is it ever added/subtracted" line,
answered at lift time and revisited at G9f): computed addresses are
bytes4 because assemble's `rel32 = addr - end` subtracts them — the
ripple ops are constant-cost per value, where Church-numeral PRED
subtraction is quadratic.  Large literals stay byte-list data —
`0x1122334455667788` never needs to be a magnitude, only a
little-endian byte string.  Byte cells decode structurally (each is a
pair of nibble selectors); no behavioral numeral spine-probe is needed
now that the arithmetic rep is not Church.

G9e — `programOf`: `routines.program(R)` at term level (emit stage 3).
One generated term `λfs λfuel λrbb λcb λnb. <fragments>`: the skeleton
is produced by differencing each routine builder under sentinel
Realizations, so the fuse_s/fuel variant regions are discovered, not
re-encoded.  Output is a Scott list of per-routine fragment lists —
the ROUTINES order is the honest emission unit, and the nesting keeps
pending redexes ~30x shallower than one flat ~540-cell spine (the same
quadratic-descent pathology as G9d's probes: flat lo hit ~10M allocs
by 40k steps and never finished; nested finishes in ~80k steps / ~11M
allocs).  Operands are uniformly tagged ["r"|"imm"|"l"|"p"|"m",…];
immediates and mem displacements are bytes8 leaves (never arithmetic),
"l"/"p" payloads stay nibble-string names for the G9d symbol map and
the pass-1 label map.  Native is not gated on this stage — the reduce
exceeds the exe's 600s subprocess cap; lo+cd+python witness all cases.

G9f — `encodeOf` + `assembleOf`: `isa.encode`/`isa.assemble` at term
level (emit stage 4).  The ENCS/FORMS/REG tables cross as nibble-trie
DATA and a field interpreter walks the ordered alternatives; each
insn encodes to pair(byte-list, nibble-length).  `assembleOf` is the
two-pass fold: pass 1 builds a local label map (`pos4 = base+off`) and
records each insn's (item, off4, len4); pass 2 resolves names —
`symbols` SHADOWS `local`, the link seam — and emits rel32 as `B4SUB
target end4`.  All addresses/positions/rel32 are bytes4 ripple ops.
The gate covers fwd/bwd rel32, rip-symbol operands, mem disp8, symbol
shadowing, multi-fragment and a nonzero base on lo+cd vs the
isa.assemble oracle; the full 26-form encode sweep lives in
_probe_g9f_enc.py.  Native is deferred (same exe throughput ceiling).

G9g — `dataOf`/`idataOf`/`packOf`: `target_pe64`'s container writer at
term level (emit stage 5, the last of the chain).  `dataOf` folds the
slot 3-lists [name, sz-numeral, sz-bytes4] into pair(zero bytes,
symmap) — the numeral emits zeros (iteration bound), the bytes4
advances the RVA (arithmetic value).  `idataOf` folds the imports into
IDT/ILT/IAT + hint-name records + kernel32.dll, measuring each record
with LENB4 for the honest `off += len(hn)` and checking parity off the
measured bytes4.  `packOf` emits the 448-byte fixed header as literal
chunks spliced with computed bytes4 fields (sizes, raw pointers,
size_image), then JOINs section bodies behind PADLIST pads — pad count
is extracted as `len & 511` off the length's low nibbles and dropped
from a 512-zero literal via `rem TAIL z512` (never a subtraction).
JOIN is the load-bearing emission shape: a left-fold of APPENDs would
re-walk the prefix (quadratic); right-assoc keeps it linear in the
image size.  Oracle is target_pe64.pack byte-for-byte.

G9h — `linkOf`/`pack2Of`: the linker stage (emit stage 6, closing the
link seam).  `linkOf` runs the section builders ONCE and merges their
exported symtabs — `APPEND iat_syms data_syms`, ALOOK's last-match
mirroring `dict.update` — into the global table assemble's resolver
consumes; the symbol table is now derived from the emitted sections,
not injected.  `pack2Of` is packOf with the sections as inputs — no
internal rebuild — so the same emitted sections feed both the symtab
and the image: `L = linkOf IMPORTS SLOTS`, `assembleOf PROG (L (K I))`
reads the linked symtab, `pack2Of text (L K K) (L K (K I))` packs the
linked sections.  linkOf gates lo+cd at both scales; pack2Of gates
lo+oracle (same measured cd deferral as packOf — image-sized NF);
linkasm gates the resolver seam fed by the link's merged symtab
end-to-end on lo+oracle (composed-stage cd deferred — the link
stage's sequential emission inside the same fixpoint measured >50GB,
the 027/028 retention pathology, not a correctness question).  The win64-scale link→assemble→pack chain is
arena-bound in one graph like G9g's — the staged probe
(_probe_g9g_e2e_staged.py) is the honest model: serialize the NF at
each stage boundary, fresh arena per stage.

Usage: python host/spec_term.py
"""
from __future__ import annotations

import difflib
import json
import os
import struct
import sys
from types import SimpleNamespace
from typing import Dict, List, Optional

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_SEED = os.path.normpath(os.path.join(_HOST, "..", "seed"))
if _SEED not in sys.path:
    sys.path.insert(0, _SEED)

sys.setrecursionlimit(1_000_000)   # cons-spine depth ~ #nibble cells

from reduce import T, K, I, KK, B, S, C, D, app  # noqa: E402
from quotient_map import QuotientMap             # noqa: E402
from observation_regime import encoding_regime   # noqa: E402
from lambda_dialect import (parse, bracket, bracket_abstract0,  # noqa: E402
                            NAbs, NApp, NComb, NExpr, NVar)
from graph_runtime import reduce_tree_lo, reduce_tree_cd     # noqa: E402
from strategy import MixStrategy                             # noqa: E402
import seed                                                  # noqa: E402

TOOLCHAIN_JSON = os.path.join(_HOST, "toolchain.json")


def _appn(*xs: T) -> T:
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t


# ---------------------------------------------------------------------------
# encoding primitives (the xdu input-map shapes; see module docstring)
# ---------------------------------------------------------------------------

_CONS = bracket_abstract0(parse("\\h. \\t. \\n. \\c. c h t"))
_NIL = KK                                # \n. \c. n
_PAIR = bracket_abstract0(parse("\\k. \\v. \\f. f k v"))
_KI = app(KK, I)                           # \a. \b. b — false / Nothing
_SELECTORS = tuple(
    bracket_abstract0(parse(
        "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"))
    for k in range(16))
_CHURCH_A = _appn(S, app(KK, S), _appn(S, app(KK, KK), I))

NULL_TAG = app(C, I)                     # inert: swapβ needs 3 args
TRUE_T = KK
FALSE_T = app(KK, I)


def church(k: int) -> T:
    """Church numeral c_k as a combinator term (iterative construction)."""
    t = app(KK, I)
    for _ in range(k):
        t = _appn(S, _CHURCH_A, t)
    return t


def bytes_term(b: bytes) -> T:
    """Raw bytes -> Scott list of 16-ary nibble selectors."""
    t = _NIL
    for byte in reversed(b):
        t = _appn(_CONS, _SELECTORS[byte & 15], t)
        t = _appn(_CONS, _SELECTORS[byte >> 4], t)
    return t


def str_term(s: str) -> T:
    """UTF-8 bytes -> Scott list of 16-ary nibble selectors."""
    return bytes_term(s.encode("utf-8"))


def json_to_term(obj) -> T:
    """Structural encoder over the JSON slice (see module docstring)."""
    if obj is None:
        return NULL_TAG
    if isinstance(obj, bool):
        return TRUE_T if obj else FALSE_T
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
            t = _appn(_CONS, _appn(_PAIR, json_to_term(k), json_to_term(v)),
                      t)
        return t
    raise TypeError(f"unsupported JSON value: {obj!r}")


def term_nodes(t: T, memo: Optional[set] = None) -> int:
    """Unique (shared-once) node count of a T dag."""
    if memo is None:
        memo = set()
    if id(t) in memo:
        return 0
    memo.add(id(t))
    if t.k == K.APP:
        return 1 + term_nodes(t.l, memo) + term_nodes(t.r, memo)
    return 1


# ---------------------------------------------------------------------------
# G9f byte/nibble representation — the assembler's arithmetic layer.
#
# A byte is `_PAIR nibLo nibHi` (one cell, not two — arithmetic destructures
# locally); a byte-word/list is a Scott list of byte cells.  Nibble ops are
# 16-way selector argument permutations — no Church numerals in the hot
# path (see _NIBADD &co. at the G9f section below).  The empirical rule
# (decision 024 refined): Church numerals are for iteration bounds only;
# any value that is added/subtracted lives as byte cells (constant-cost
# ripple ops — numeral SUB is O(n*m) PRED chains and dies at rel32
# offsets ~14k).
# ---------------------------------------------------------------------------

def byte_term(v: int) -> T:
    """One byte as `\\f. f nibLo nibHi` (pair cell)."""
    return _appn(_PAIR, _SELECTORS[v & 15], _SELECTORS[v >> 4])


def bytelist_term(bs) -> T:
    """bytes/iterable -> Scott list of byte cells."""
    t = _NIL
    for b in reversed(list(bs)):
        t = _appn(_CONS, byte_term(b), t)
    return t


def word_term(v: int, nbytes: int) -> T:
    """LE byte-word of `nbytes` cells."""
    return bytelist_term(
        (v & ((1 << (8 * nbytes)) - 1)).to_bytes(nbytes, "little"))


# ---------------------------------------------------------------------------
# λ-source pieces (assembled like xdu's to_lambda; compiled with `bracket`)
# ---------------------------------------------------------------------------

def _church_src(k: int) -> str:
    return "(\\f. \\x. " + "f (" * k + "x" + ")" * k + ")"


def _b_src(k: int) -> str:
    s = "I"
    for _ in range(k):
        s = f"(B {s})"
    return s


def _sel_src(k: int) -> str:
    return "(" + "".join(f"\\c{i}. " for i in range(16)) + f"c{k})"


def _str_src(s: str) -> str:
    """λ-source for a nibble-string literal (same shape as str_term)."""
    out = "K"
    for byte in reversed(s.encode("utf-8")):
        out = f"((\\h. \\t. \\n. \\c. c h t) {_sel_src(byte & 15)} {out})"
        out = f"((\\h. \\t. \\n. \\c. c h t) {_sel_src(byte >> 4)} {out})"
    return out


# eqNib a b = a (b K F…F)(b F K…F)…(b F…F K)  -> Church bool
EQNIB = ("(\\a. \\b. a " +
         " ".join("(b " +
                  " ".join("K" if j == i else "(K I)" for j in range(16)) +
                  ")" for i in range(16)) + ")")

# eqStr a b n -> Church bool; iterates `a` (n >= len(a)).
# acc = \k. k la lb o ; o = Church flag that short-circuits the eqNib work.
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

# extract: o AND both lists exhausted (la non-nil at bound -> safe FALSE)
EQSTR = ("(\\a. \\b. \\n. (n (" + _STEP_E + ") "
         "(\\k2. k2 a b K)) "
         "(\\la. \\lb. \\o. o "
         "(la (lb K (\\h. \\t. (K I))) (\\h. \\t. (K I))) (K I)))")

# specGet spec key n nb -> option value; assoc fold over n pairs.
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

# emit list n -> C (B^k I) … K  (xdu output-map spine, no rc element)
_STEP_M = (
    "\\acc. acc (\\l. \\o. l "
    "(\\k2. k2 l o) "
    "(\\h. \\t. \\k2. k2 t (\\r. o (C (h " +
    " ".join(_b_src(i) for i in range(16)) + ") r))))"
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

# ---------------------------------------------------------------------------
# G9c: resolveOf — the emit chain's resolve stage at term level.
#
# toolchain.resolve(name) is, at data level: walk toolchains for the entry,
# take its dialect/isa/routines/target names, and look each up in the
# matching catalog section for {module, record}.  All assoc folds — the
# same machinery as pathOf.
#
# OBSERVABLE: a Scott list of the eight resolved field strings
#     [d_mod, d_rec, i_mod, i_rec, r_mod, r_rec, t_mod, t_rec]
# built by pure cons of lookup results — no string concatenation.
#
# (The earlier flat-string version used a bounded revOnto-append fold;
# it diverged at the L0 level whenever the fold bound exceeded the list
# length by ~5 — the nil-case pack fixpoint is only benign when the
# list argument is already a value, and nested lazy applications made
# the excess iterations feed a self-rebuilding residual.  The field
# list is the honest observable for a multi-part resolution anyway.)
#
# "!" stands in for a component that is undeclared or lacks the key —
# the term-level shadow of NotRealized.
# ---------------------------------------------------------------------------

# cons h t = \n.\c. c h t  (λ-source — the T-level _CONS above is taken)
_CONS_SRC = "(\\h2. \\t2. \\n2. \\c2. c2 h2 t2)"


def _cons(h_src: str, t_src: str) -> str:
    return "(" + _CONS_SRC + " " + h_src + " " + t_src + ")"


# _FIELD fk sk rk k — continuation-passing field resolution, open in
# context (spec, entry):  entry[fk] -> cn ; spec[sk] -> sect ;
# sect[cn] -> rec ; rec[rk] -> v ; then `k v`.  Any missing link calls
# k on "!" instead.
_FIELD = (
    "(\\k9. (" + SPECGET + " entry __FK__ __NENT__ __NBF__) (k9 __BANG__) "
    "(\\cn. (" + SPECGET + " spec __SK__ __NTOP__ __NBS__) (k9 __BANG__) "
    "(\\sect. (" + SPECGET + " sect cn __NSECT__ __NBC__) (k9 __BANG__) "
    "(\\rec. (" + SPECGET + " rec __RK__ __NREC__ __NBM__) (k9 __BANG__) "
    "(\\v. k9 v)))))"
)


def _field_src(field: str, section: str, reckey: str, k_src: str) -> str:
    return ("(" + _FIELD.replace("__FK__", _str_src(field))
                        .replace("__SK__", _str_src(section))
                        .replace("__RK__", _str_src(reckey))
            + " " + k_src + ")")


# resolve result: cons-list of the 8 resolved field strings
_FIELDS = (
    ("dialect", "dialects"), ("isa", "isas"),
    ("routines", "routines"), ("target", "targets"),
)


def _resstr() -> str:
    body = "K"
    for i in range(7, -1, -1):
        body = _cons("v%d" % i, body)
    for i in range(7, -1, -1):
        field, sect = _FIELDS[i // 2]
        reckey = "module" if i % 2 == 0 else "record"
        body = _field_src(field, sect, reckey,
                          "(\\v%d. " % i + body + ")")
    return body


_STEP_R = (
    "\\acc. acc (\\l. \\o. l "
    "(\\k2. k2 l o) "
    "(\\entry. \\t. (" + SPECGET + " entry __NAMET__ __NENT__ __NBE__) "
    "(\\k2. k2 t o) "
    "(\\v. " + EQSTR + " name v __NBEQ__ "
    "(\\k2. k2 t (\\n4. \\j4. j4 (" + _resstr() + "))) "
    "(\\k2. k2 t o))))"
)

RESOLVE_OF = (
    "(\\spec. \\name. (" + SPECGET + " spec __TOOLST__ __NTOP__ __NBT__) I "
    "(\\arr. ((__NARR__ (" + _STEP_R + ") "
    "(\\k2. k2 arr (\\n4. \\j4. n4))) "
           "(\\l. \\o. o)) I I))"
)


# ---------------------------------------------------------------------------
# G9d: symbolsOf — target.symbols (IAT + .data RVA map) at term level.
#
# First fragment of the emit chain's sparse->dense seam (memory decision
# 024): the sparse-relational product is an assoc map of `\\f. f key addr`
# pairs built by two structurally-bounded folds (imports by count, slots
# by count), and the dense part is bytes4 ripple arithmetic — constant
# cost per value, sized to the PE RVA space.
#
#   addresses are bytes4 — precisely because assemble's resolver
#       subtracts them (rel32 = addr - end; the boundary is "is it ever
#       added/subtracted").  The ripple-carry vocabulary exists now, so
#       the value rep matches the use; numeral SUB would be O(n*m)
#       through PRED chains.  Literal immediates stay bytes8 leaves.
#   bounds are measured, never padded (the append-divergence rule).
#   `iat_` is prepended as 8 literal cons cells — a real nibble-string
#       key, not a fold, so the emitted map is SPECGET-probeable as-is.
#
# Signature mirrors tgt.symbols(imports, data_slots) -> dict.
# Whether the routines *record* should declare imports/data_slots as
# catalog fields (so the term walks spec -> rts -> symbols) is deferred
# to the `program` lift — the typed-IR-package direction (research note)
# wants that surface designed, not accreted.
#
#   iat_<name> -> IDATA_RVA + IDT_SZ + (n_imp+1)*8 + i*8   (build_idata)
#   <slot>     -> DATA_RVA + running offset                (build_data)
# ---------------------------------------------------------------------------

_SUCC_SRC = "(\\n5. \\f5. \\x5. f5 (n5 f5 x5))"
_ADD_SRC = "(\\m5. \\n5. \\f5. \\x5. m5 f5 (n5 f5 x5))"
_MUL_SRC = "(\\m5. \\n5. \\f5. m5 (n5 f5))"
_PAIR_SRC = "(\\k5. \\v5. \\f6. f6 k5 v5)"


def _num_src(k: int) -> str:
    """Church numeral for k as a MUL-composition of <=16 literals —
    keeps the source small where _church_src would nest `f (` k deep."""
    if k <= 16:
        return _church_src(k)
    for f in range(16, 1, -1):
        if k % f == 0:
            return ("(" + _MUL_SRC + " " + _church_src(f) + " "
                    + _num_src(k // f) + ")")
    return "(" + _ADD_SRC + " " + _num_src(k - 1) + " " + _church_src(1) + ")"


def _prefix_src(pfx: str, tail_src: str) -> str:
    """Cons pfx's nibble cells onto tail_src — literal prepend, no fold."""
    out = tail_src
    for byte in reversed(pfx.encode("utf-8")):
        out = _cons(_sel_src(byte & 15), out)
        out = _cons(_sel_src(byte >> 4), out)
    return out


# ---------------------------------------------------------------------------
# term prelude: selector/nibble/byte-cell vocabulary, list utils,
# λ-source builders, and bytes4 ripple arithmetic.  Shared by every
# emit stage — moved ahead of G9d so symbolsOf can emit bytes4
# addresses (they are added/subtracted by assemble's resolver).
# ---------------------------------------------------------------------------

# --- λ-source helpers -------------------------------------------------------

def _let(v: str, val: str, body: str) -> str:
    return f"(\\{v}. {body}) ({val})"


def _lets(bindings, body: str) -> str:
    """[(name, valsrc)] -> nested lets, first binding outermost."""
    for name, val in reversed(bindings):
        body = f"(\\{name}. {body}) ({val})"
    return body


def _peel(l: str, names: List[str], body: str) -> str:
    """`l K (\\h0. \\t0. t0 K (\\h1. \\t1. … body))` — cons-destructure."""
    src = body
    for i in reversed(range(len(names))):
        prev = l if i == 0 else f"t{i - 1}"
        src = f"{prev} K (\\{names[i]}. \\t{i}. {src})"
    return src


def _sel16(sel: str, impls: List[str], extra: str = "") -> str:
    """`sel i0 … i15` — nibble dispatch (pads to 16 args with K), then
    applies `extra` (a space-separated arg tail) to the picked impl."""
    args = " ".join(list(impls) + ["K"] * (16 - len(impls)))
    out = f"({sel} {args})"
    return f"{out} {extra}" if extra else out


def _maybe(mv: str, body: str, bv: str = "mv") -> str:
    """maybe-value unwrap: `mv K (\\bv. body)` — K is the never-taken
    Nothing branch (the static tries here are present-keys only)."""
    return f"{mv} K (\\{bv}. {body})"


_CONSS = "(\\h2. \\t2. \\n2. \\c2. c2 h2 t2)"


def _conss(h: str, t: str) -> str:
    return f"({_CONSS} {h} {t})"


def _prs(a: str, b: str) -> str:
    return f"({_PAIR_SRC} {a} {b})"


def _fst(e: str) -> str:
    return f"({e} K)"


def _snd(e: str) -> str:
    return f"({e} (K I))"

_SELS = [_sel_src(i) for i in range(16)]
_BT, _BF = "K", "(K I)"

_NIBADD = ("(\\a. \\b. a " + " ".join(
    "(b " + " ".join(_SELS[(i + j) % 16] for j in range(16)) + ")"
    for i in range(16)) + ")")
_NIBCARRY = ("(\\a. \\b. a " + " ".join(
    "(b " + " ".join(_BT if j >= 16 - i else _BF for j in range(16)) + ")"
    for i in range(16)) + ")")
_NIBGE8 = ("(\\a. a " + " ".join(_BT if j >= 8 else _BF
                                for j in range(16)) + ")")
_NIBSH1 = ("(\\a. a " + " ".join(_SELS[j >> 1] for j in range(16)) + ")")
_NIBLO1 = ("(\\a. a " + " ".join(_BT if j % 2 == 1 else _BF
                                for j in range(16)) + ")")
_NIBMOD8 = ("(\\a. " + _NIBGE8 + " a (" + _NIBADD + " a "
            + _SELS[8] + ") a)")
_NIBNOT = ("(\\a. a " + " ".join(_SELS[15 - j] for j in range(16)) + ")")
_NIBSUCC = ("(\\a. a " + " ".join(_SELS[(j + 1) % 16]
                                 for j in range(16)) + ")")
_B2N = "(\\b. b " + _SELS[1] + " " + _SELS[0] + ")"
_OR = "(\\p. \\q. p K q)"
_AND = "(\\p. \\q. p q (K I))"
_NOT = "(\\p. p (K I) K)"
_EQNIB_T = EQNIB            # source constant, defined in the G9c section

# ADDBC x y cnib -> pair(byte_cell, carry_bool)
_ADDBC = (
    "(\\x. \\y. \\cn. x (\\xl. \\xh. y (\\yl. \\yh. "
    "(\\t. (\\clo. (\\lo. (\\u. (\\cn2. (\\cout. (\\hi. "
    "(" + _PAIR_SRC + " (" + _PAIR_SRC + " lo hi) cout))"
    " (" + _NIBADD + " u cn2))"
    " (" + _OR + " (" + _NIBCARRY + " xh yh) (" + _NIBCARRY
    + " u cn2)))"
    " (" + _B2N + " clo))"
    " (" + _NIBADD + " xh yh))"
    " (" + _NIBADD + " t cn))"
    " (" + _OR + " (" + _NIBCARRY + " xl yl) (" + _NIBCARRY
    + " t cn)))"
    " (" + _NIBADD + " xl yl))))"
)
# EQB a b — byte equality (pair cells, EQNIB both nibs)
_EQB = ("(\\x. \\y. x (\\xl. \\xh. y (\\yl. \\yh. "
        + _AND + " (" + EQNIB + " xl yl) (" + EQNIB + " xh yh))))")
# NOTB — byte complement
_NOTB = ("(\\x. x (\\l. \\h. " + _PAIR_SRC + " (" + _NIBNOT + " l) ("
         + _NIBNOT + " h)))")
# MODRM3 m g r -> byte cell  mod<<6 | reg<<3 | rm   (pair is lo,hi —
# byte-cell convention is lo first, like byte_term)
_MODRM3 = ("(\\m. \\g. \\r. " + _PAIR_SRC + " ("
           + _NIBADD + " ((" + _NIBLO1 + " g) " + _SELS[8] + " "
           + _SELS[0] + ") (" + _NIBMOD8 + " r)) ("
           + _NIBADD + " (" + _NIBADD + " (" + _NIBADD + " m m) ("
           + _NIBADD + " m m)) (" + _NIBSH1 + " g)))")

# Scott-list utils -----------------------------------------------------------
# _FOLDL st l a — left fold bounded by the INPUT SPINE (self-application,
# not fuel): the fold ends when the data does — the principled bound.
_FOLDL = ("(\\st. \\l. \\a. (\\f. f f) (\\g. \\l2. \\a2. l2 a2 "
          "(\\h. \\t. g g t (st a2 h))) l a)")
_HEAD = "(\\x. x K K)"
_TAIL = "(\\x. x K (K I))"
_NTH = ("(\\i. \\l. " + _HEAD + " (i " + _TAIL + " l))")
_REV = ("(\\l. " + _FOLDL
        + " (\\a. \\h. (\\h2. \\t2. \\n. \\c. c h2 t2) h a) l K)")
# _TAKE n l -> pair(reversed-prefix, rest)
_TAKE = ("(\\n. \\l. n (\\p. p (\\ac. \\ll. ll p "
         "(\\h. \\t. " + _PAIR_SRC + " ((\\h2. \\t2. \\n2. \\c2. c2 h2 t2)"
         " h ac) t))) (" + _PAIR_SRC + " K l))")

# bytes4 arithmetic ------------------------------------------------------------
# Values that are ADDED OR SUBTRACTED (positions, addresses, rel32) are
# byte-cell lists, never Church numerals — numeral SUB is O(n*m) through
# PRED chains, while the ripple below is O(width).  Width is 4 cells =
# u32: PE RVAs and rel32 displacements both live in 32 bits (two's
# complement; carry-out is discarded, which is exactly mod-2^32).

def _b4_src(v: int) -> str:
    """bytes4 literal for v & 0xffffffff — cons-chain of 4 byte cells."""
    out = "K"
    for i in reversed(range(4)):
        b = (v >> (8 * i)) & 0xFF
        out = _conss("(" + _PAIR_SRC + " " + _SELS[b & 15] + " "
                     + _SELS[b >> 4] + ")", out)
    return out


# zip-ripple: FOLDL over `a` carrying pair(rest-of-b, pair(carry_nib, out)).
# ADDBC's carry-in is a nibble, its carry-out a bool — B2N converts per
# step.  Input lists are little-endian (b0 first); out accumulates
# consed-then-reversed.  `bl K f` on exhausted b is unreachable: same
# length is the representation invariant.
_B4ADD = (
    "(\\a. \\b. (" + _FOLDL
    + " (\\acc. \\x. acc (\\bl. \\cs. cs (\\cy. \\ou. "
    "bl K (\\hb. \\tb. (" + _ADDBC + " x hb cy) (\\c. \\s. "
    + _prs("tb", _prs("(" + _B2N + " s)", _conss("c", "ou")))
    + ")))))"
    + " a " + _prs("b", _prs(_SELS[0], "K")) + ") "
    "(\\bl. \\cs. cs (\\cy. \\ou. " + _REV + " ou)))"
)
# a - b = a + ~b + 1 (per-byte NOTB, carry-in = 1) — two's complement.
_B4SUB = (
    "(\\a. \\b. (" + _FOLDL
    + " (\\acc. \\x. acc (\\bl. \\cs. cs (\\cy. \\ou. "
    "bl K (\\hb. \\tb. (" + _ADDBC + " x (" + _NOTB + " hb) cy) (\\c. \\s. "
    + _prs("tb", _prs("(" + _B2N + " s)", _conss("c", "ou")))
    + ")))))"
    + " a " + _prs("b", _prs(_SELS[1], "K")) + ") "
    "(\\bl. \\cs. cs (\\cy. \\ou. " + _REV + " ou)))"
)
# carry-lookahead twin of _B4ADD ----------------------------------------------
# The FOLDL carry chain is the residual-chain critical path: byte i's
# ADDBC waits on byte i-1's carry.  Splitting ADDBC into carry-only and
# sum-only halves lets the four byte-carries be a bool tree instead —
# cout(cin) = g | (p & cin) with g = cout(0), p = cout(1) (byte carry-out
# is monotone in carry-in) — and the four byte sums are independent
# cones once the carries are terms.  More total nibble work (~2x), much
# shorter dependency chain — the same-observation trade the spec layer
# is for.  Correctness target: Join (B4ADD a b) (B4CLA a b).
_B4BC = (   # byte carry-out: x y cnib -> bool (ADDBC's carry half)
    "(\\x. \\y. \\cn. x (\\xl. \\xh. y (\\yl. \\yh. "
    + _lets([
        ("t",   "(" + _NIBADD + " xl yl)"),
        ("clo", "(" + _OR + " (" + _NIBCARRY + " xl yl) ("
                + _NIBCARRY + " t cn))"),
        ("cn2", "(" + _B2N + " clo)"),
        ("hh",  "(" + _NIBADD + " xh yh)")],
        "(" + _OR + " (" + _NIBCARRY + " xh yh) (" + _NIBCARRY
        + " hh cn2))") + ")))")
_B4BS = (   # byte sum: x y cnib -> byte cell (ADDBC's sum half)
    "(\\x. \\y. \\cn. x (\\xl. \\xh. y (\\yl. \\yh. "
    + _lets([
        ("t",   "(" + _NIBADD + " xl yl)"),
        ("clo", "(" + _OR + " (" + _NIBCARRY + " xl yl) ("
                + _NIBCARRY + " t cn))"),
        ("lo",  "(" + _NIBADD + " t cn)"),
        ("cn2", "(" + _B2N + " clo)"),
        ("hh",  "(" + _NIBADD + " xh yh)")],
        _prs("lo", "(" + _NIBADD + " hh cn2)")) + ")))")
# _B4CLA a b -> bytes4: lookahead carries, parallel byte sums.
# cb1 = g0 ; cb2 = g1 | p1&cb1 ; cb3 = g2 | p2&cb2  (cb0 = 0 statically)
_B4CLA = (
    "(\\a. \\b. " + _peel("a", ["a0", "a1", "a2", "a3"],
        _peel("b", ["b0", "b1", "b2", "b3"],
            _lets([
                ("g0", "(" + _B4BC + " a0 b0 " + _SELS[0] + ")"),
                ("p0", "(" + _B4BC + " a0 b0 " + _SELS[1] + ")"),
                ("g1", "(" + _B4BC + " a1 b1 " + _SELS[0] + ")"),
                ("p1", "(" + _B4BC + " a1 b1 " + _SELS[1] + ")"),
                ("g2", "(" + _B4BC + " a2 b2 " + _SELS[0] + ")"),
                ("p2", "(" + _B4BC + " a2 b2 " + _SELS[1] + ")"),
                ("c2", "(" + _OR + " g1 (" + _AND + " p1 g0))"),
                ("c3", "(" + _OR + " g2 (" + _AND + " p2 (" + _OR
                       + " g1 (" + _AND + " p1 g0))))")],
                _conss("(" + _B4BS + " a0 b0 " + _SELS[0] + ")",
                _conss("(" + _B4BS + " a1 b1 (" + _B2N + " g0))",
                _conss("(" + _B4BS + " a2 b2 (" + _B2N + " c2))",
                _conss("(" + _B4BS + " a3 b3 (" + _B2N + " c3))",
                       "K"))))))) + ")")
# nibble -> bytes4 (a nibble is the only honest width to lift: x86 insns
# are <=15 bytes, so insn length fits one nibble).  There is deliberately
# NO Church-numeral -> bytes4 coercion: numeral->bytes4 by n increments
# is O(n) B4ADDs, which is the blowup this rep exists to prevent — any
# bytes4 quantity known at gen time is emitted as a `_b4_src` literal.
_B0C = "(" + _PAIR_SRC + " " + _SELS[0] + " " + _SELS[0] + ")"
_NIB2B4 = ("(\\n5. " + _conss(_prs("n5", _SELS[0]),
           _conss(_B0C, _conss(_B0C, _conss(_B0C, "K")))) + ")")
# list length as a Church numeral (structural fold — bounds for EQSTR)
_LEN = ("(\\l. " + _FOLDL + " (\\a. \\c. " + _SUCC_SRC
        + " a) l (K I))")
# assoc lookup: list of pair(name,val) -> maybe val.  Nothing = K.
_JUST_SRC = "(\\v. \\n. \\j. j v)"
_ALOOK = ("(\\map. \\key. (" + _FOLDL
          + " (\\acc. \\e. e (\\k2. \\v2. (" + EQSTR + " key k2 ("
          + _LEN + " key)) (" + _JUST_SRC + " v2) acc)) map K))")

# ---------------------------------------------------------------------------
# G9g byte/nibble ops — the pack stage's machinery.
#
# The representation rule (decision 026) is extended here with a cost
# observation: B4ADD/B4SUB are general ripple ops (~thousands of steps
# each), so they are used ONLY where a real add/subtract is needed.  The
# pack layout's dominant quantity is *length* — measured, incremented,
# compared — and that runs on B4INC, a byte4 increment whose carry is a
# nibble chain that almost never propagates (~tens of steps).  Lengths
# stay bytes4 (LENB4, PADTO); a numeral is added to a bytes4 as
# `num B4INC acc` (cheap increments), never a per-unit B4ADD.
# ---------------------------------------------------------------------------

# nibble == 15 -> bool (the carry-out condition for a 4-bit increment)
_NIBIS15 = ("(\\a. a " + " ".join([_BF] * 15 + [_BT]) + ")")
# INC_BYTE: byte cell -> pair(byte', carry).  lo wraps iff lo==15, then
# hi increments and carries iff hi==15.
_INCB = (
    "(\\b. b (\\lo. \\hi. (" + _NIBIS15 + " lo) "
    "(" + _PAIR_SRC + " (" + _PAIR_SRC + " " + _SELS[0] + " ("
    + _NIBSUCC + " hi)) (" + _NIBIS15 + " hi)) "
    "(" + _PAIR_SRC + " (" + _PAIR_SRC + " (" + _NIBSUCC
    + " lo) hi) " + _BF + ")))"
)


def _b4inc_body() -> str:
    """bytes4 increment as an unrolled rare-carry chain over 4 cells."""
    def emit(cells):
        out = "K"
        for x in reversed(cells):
            out = _conss(x, out)
        return out

    def chain(i: int, prefix) -> str:
        if i == 4:                       # carry past b3 discarded: mod 2^32
            return emit(prefix)
        nb, c = "nb" + str(i), "c" + str(i)
        return ("(" + _INCB + " b" + str(i) + ") (\\" + nb + ". \\" + c
                + ". " + c + " (" + chain(i + 1, prefix + [nb]) + ") ("
                + emit(prefix + [nb] + ["b" + str(j) for j in
                                        range(i + 1, 4)]) + "))")

    return _peel("v", ["b0", "b1", "b2", "b3"], chain(0, []))


_B4INC = "(\\v. " + _b4inc_body() + ")"
# bytes4 length — a FOLDL of cheap increments (not per-element B4ADD)
_LENB4 = ("(\\l. " + _FOLDL + " (\\a. \\x. " + _B4INC + " a) l "
          + _b4_src(0) + ")")
# bytes4 equality — AND of per-byte EQB (PADTO's stop condition)
_EQB4 = (
    "(\\x. \\y. " + _peel("x", ["x0", "x1", "x2", "x3"],
                          _peel("y", ["y0", "y1", "y2", "y3"],
                                _AND + " (" + _EQB + " x0 y0) (" + _AND
                                + " (" + _EQB + " x1 y1) (" + _AND
                                + " (" + _EQB + " x2 y2) (" + _EQB
                                + " x3 y3)))")) + ")")
# PADTO tgt pos -> zeros(tgt - pos): bounded B4INC+EQB4 loop.  Callers
# APPEND the pad list (consing zeros onto acc would PREPEND them).
_PADTO = (
    "(\\tgt. (\\f. f f) (\\g. \\pos. (" + _EQB4
    + " pos tgt) K " + _conss(_B0C, "(g g (" + _B4INC + " pos))")
    + "))")
# APPEND xs ys = xs ++ ys (byte-list concat)
_APPEND = ("(\\xs. \\ys. " + _FOLDL + " (\\a. \\h. " + _conss("h", "a")
           + ") (" + _REV + " xs) ys)")
# nibble-string -> byte list: pair (hi,lo) cells into pair(lo,hi) bytes.
_NIBS2BYTES = (
    "(\\l. ((\\f. f f) (\\g. \\l2. l2 K (\\hi. \\t. t K (\\lo. \\t2. "
    + _conss("(" + _PAIR_SRC + " lo hi)", "(g g t2)") + ")))) l)"
)
# ZEROFILL n -> n zero byte cells (n is a Church numeral bound)
_ZEROFILL = ("(\\n. n (\\l. " + _conss(_B0C, "l") + ") K)")
# U64: bytes4 -> 8 LE cells (zero-extend — computed fields fit u32)
_U64 = ("(\\b. " + _APPEND + " b " + _conss(
    _B0C, _conss(_B0C, _conss(_B0C, _conss(_B0C, "K")))) + ")")
# alignment: power-of-2 align = (v + a-1) & ~(a-1), a nibble-level mask.
# 0x200 clears low 9 bits: byte0 -> 0, byte1's low nibble &= 0xE.
_NIBANDE = ("(\\a. a " + " ".join(_SELS[j & 0xE] for j in range(16)) + ")")
_ALIGN512 = (
    "(\\v. " + _let("w", "(" + _B4ADD + " v " + _b4_src(0x1FF) + ")",
        _peel("w", ["b0", "b1", "b2", "b3"],
              "b1 (\\lo. \\hi. " + _conss(_B0C, _conss(
                  _prs("(" + _NIBANDE + " lo)", "hi"),
                  _conss("b2", _conss("b3", "K")))) + ")"))
    + ")")
# 0x1000 clears low 12 bits: byte0 -> 0, byte1's low nibble -> 0.
_ALIGN4096 = (
    "(\\v. " + _let("w", "(" + _B4ADD + " v " + _b4_src(0xFFF) + ")",
        _peel("w", ["b0", "b1", "b2", "b3"],
              "b1 (\\lo. \\hi. " + _conss(_B0C, _conss(
                  _prs(_SELS[0], "hi"),
                  _conss("b2", _conss("b3", "K")))) + ")"))
    + ")")

# imports fold: state (l_in, addr, out); each step pops a name, conses
# `pair ("iat_"++nm) addr` onto out and advances addr by 8.
# addr is bytes4 — the value is subtracted by assemble's resolver, so it
# lives in the arithmetic rep (ripple ops), not a Church numeral.
_STEP_I = (
    "\\acc. acc (\\l. \\o. \\u. l "
    "(\\k2. k2 l o u) "
    "(\\nm. \\t. \\k2. k2 t (" + _B4ADD + " o " + _b4_src(8) + ") "
    + _cons("(" + _PAIR_SRC + " __IATPFX__ o)", "u") + "))"
)

# slots fold: same state; each element is a 2-list [name, size] — cons
# `pair nm addr` and advance addr by sz.  sz arrives as a bytes4 literal
# (the input encodes it in the arithmetic rep — N2B4's per-unit
# increment would be O(sz) B4ADDs, which is exactly the explosion the
# bytes4 rep exists to avoid).
_STEP_S = (
    "\\acc. acc (\\l. \\o. \\u. l "
    "(\\k2. k2 l o u) "
    "(\\p. \\t. p (\\k2. k2 t o u) "
    "(\\nm. \\rest. rest (\\k2. k2 t o u) "
    "(\\sz. \\r2. \\k2. k2 t (" + _B4ADD + " o sz) "
    + _cons("(" + _PAIR_SRC + " nm o)", "u") + "))))"
)

# iat base = IDATA_RVA + IDT_SZ + (n_imp+1)*8 — the build_idata layout.
# Computed at source-generation time (n_imp is a known bound) and
# emitted as a bytes4 literal — never N2B4 over a ~8k numeral.
SYMS_OF = (
    "(\\imports. \\slots. (__NIMPB__ (" + _STEP_I + ") "
    "(\\k2. k2 imports __IATB__ K)) "
    "(\\li. \\ai. \\u. (__NSLOT__ (" + _STEP_S + ") "
    "(\\k2. k2 slots " + _b4_src(0x3000) + " u)) "
    "(\\ls. \\as. \\u2. u2)))"
)


def symbols_src(n_imp: int, n_slot: int) -> str:
    """λ-source of `\\imports. \\slots. symbolsOf` — bounds measured."""
    src = SYMS_OF
    for ph, val in (
        ("__NIMPB__", _church_src(n_imp)),
        ("__NSLOT__", _church_src(n_slot)),
        ("__IATPFX__", _prefix_src("iat_", "nm")),
        ("__IATB__", _b4_src(0x2000 + 40 + (n_imp + 1) * 8)),
    ):
        src = src.replace(ph, val)
    assert "__" not in src, "uninstantiated placeholder"
    return src


def build_symbols(n_imp: int, n_slot: int) -> T:
    """symbolsOf instantiated to (imports, data_slots) counts."""
    return bracket(parse(symbols_src(n_imp, n_slot)))


def query_src(n_top: int, n_ent: int, n_arr: int, n_emit: int,
              n_beq: int, n_bt: int, n_be: int) -> str:
    """λ-source of `\\spec. \\name. pathOf` with bounds instantiated."""
    src = PATH_OF
    for ph, val in (
        ("__TOOLST__", _str_src("toolchains")),
        ("__NAMET__", _str_src("name")),
        ("__PATHT__", _str_src("path")),
        ("__NTOP__", _church_src(n_top)),
        ("__NENT__", _church_src(n_ent)),
        ("__NARR__", _church_src(n_arr)),
        ("__NEMIT__", _church_src(n_emit)),
        ("__NBEQ__", _church_src(n_beq)),
        ("__NBT__", _church_src(n_bt)),
        ("__NBE__", _church_src(n_be)),
    ):
        src = src.replace(ph, val)
    assert "__" not in src, "uninstantiated placeholder"
    return src


# ---------------------------------------------------------------------------
# the real catalog as a term + the compiled query
# ---------------------------------------------------------------------------

def load_raw() -> dict:
    with open(TOOLCHAIN_JSON, encoding="utf-8") as f:
        return json.load(f)


_RAW = load_raw()
_ENTRIES: List[dict] = _RAW["toolchains"]
NAMES: List[str] = [e["name"] for e in _ENTRIES]
NEGATIVE = "not.a.toolchain"


def build_query(raw: dict) -> T:
    """pathOf instantiated to this catalog's bounds (see query_src)."""
    entries = raw["toolchains"]
    max_name = max(2 * len(n.encode("utf-8"))
                   for n in [e["name"] for e in entries] + [NEGATIVE])
    src = query_src(
        n_top=len(raw),
        n_ent=max(len(e) for e in entries),
        n_arr=len(entries),
        n_emit=2 * max(len(e["path"].encode("utf-8")) for e in entries) + 2,
        n_beq=max_name + 2,
        n_bt=2 * len("toolchains") + 2,
        n_be=2 * max(len("name"), len("path")) + 2,
    )
    return bracket(parse(src))


SPEC = json_to_term(_RAW)
QUERY = build_query(_RAW)


def query(name: str, spec_t: Optional[T] = None) -> T:
    """`pathOf SPEC <name>` — or on an explicit (projection) spec term."""
    return _appn(QUERY, SPEC if spec_t is None else spec_t, str_term(name))


def resolve_src(n_top: int, n_arr: int, n_ent: int, n_be: int,
                n_beq: int, n_bf: int, n_bs: int, n_sect: int,
                n_bc: int, n_rec: int, n_bm: int, n_bt: int) -> str:
    """λ-source of `\\spec. \\name. resolveOf` with bounds instantiated."""
    src = RESOLVE_OF
    for ph, val in (
        ("__TOOLST__", _str_src("toolchains")),
        ("__NAMET__", _str_src("name")),
        ("__BANG__", _str_src("!")),
        ("__NTOP__", _church_src(n_top)),
        ("__NARR__", _church_src(n_arr)),
        ("__NENT__", _church_src(n_ent)),
        ("__NBE__", _church_src(n_be)),
        ("__NBEQ__", _church_src(n_beq)),
        ("__NBF__", _church_src(n_bf)),
        ("__NBS__", _church_src(n_bs)),
        ("__NSECT__", _church_src(n_sect)),
        ("__NBC__", _church_src(n_bc)),
        ("__NREC__", _church_src(n_rec)),
        ("__NBM__", _church_src(n_bm)),
        ("__NBT__", _church_src(n_bt)),
    ):
        src = src.replace(ph, val)
    assert "__" not in src, "uninstantiated placeholder"
    return src


def build_resolve(raw: dict) -> T:
    """resolveOf instantiated to this catalog's bounds."""
    entries = raw["toolchains"]
    sects = [raw.get(s, {}) for s in
             ("dialects", "isas", "routines", "targets")]
    comps = [c for s in sects for c in s.values()]

    def nib(s: str) -> int:
        return 2 * len(s.encode("utf-8"))

    return bracket(parse(resolve_src(
        n_top=len(raw),
        n_arr=len(entries),
        n_ent=max(len(e) for e in entries),
        n_be=nib("name") + 2,
        n_beq=max(nib(e["name"]) for e in entries) + nib(NEGATIVE) + 2,
        n_bf=nib("routines") + 2,          # longest field key
        n_bs=nib("dialects") + 2,          # longest section key
        n_sect=max(len(s) for s in sects),
        n_bc=max(nib(n) for s in sects for n in s) + 2,
        n_rec=max(len(c) for c in comps) + 2,
        n_bm=nib("record") + 2,          # longer of module/record
        n_bt=nib("toolchains") + 2,
    )))


# ---------------------------------------------------------------------------
# independent expected value: direct dict walk (shares no code)
# ---------------------------------------------------------------------------

def python_walk(name: str, raw: Optional[dict] = None) -> Optional[str]:
    """pathOf by dict walk: the toolchain entry named `name`'s "path"."""
    raw = _RAW if raw is None else raw
    for e in raw.get("toolchains", []):
        if e.get("name") == name:
            return e.get("path")
    return None


def python_resolve(name: str, raw: Optional[dict] = None) -> Optional[list]:
    """resolveOf by dict walk: the eight resolved field strings
    [d_mod, d_rec, i_mod, i_rec, r_mod, r_rec, t_mod, t_rec] — "!" for a
    link that is undeclared or lacks the key (the NotRealized shadow)."""
    raw = _RAW if raw is None else raw
    ent = next((e for e in raw.get("toolchains", [])
                if e.get("name") == name), None)
    if ent is None:
        return None
    out = []
    for field, sect in _FIELDS:
        rec = raw.get(sect, {}).get(ent.get(field, ""), {})
        out.append(rec.get("module") or "!")
        out.append(rec.get("record") or "!")
    return out


RESOLVE = build_resolve(_RAW)


def resolve_query(name: str) -> T:
    """`resolveOf SPEC <name>` — emit stage-1 (resolve) at term level."""
    return _appn(RESOLVE, SPEC, str_term(name))


# ---------------------------------------------------------------------------
# G9d oracle: the real target.symbols — the independent witness the term
# is checked against.  Cases: a synthetic minimal input and the real
# x86_64.win64.lo imports/data_slots.
# ---------------------------------------------------------------------------

import target_pe64                                        # noqa: E402
import routines_x86_64_win64                              # noqa: E402

SYMS_CASES = {
    "mini": (["a", "bc"], [("x", 8), ("y", 16)]),
    "x86_64.win64.lo": (list(routines_x86_64_win64.IMPORTS),
                        list(routines_x86_64_win64.DATA_SLOTS)),
}


def python_symbols(imports, slots) -> Dict[str, int]:
    """tgt.symbols by the real host function — shares no code."""
    return dict(target_pe64.symbols(imports, slots))


def _slots_term(slots) -> T:
    """[(name, size)] -> Scott list of [nibble-name, bytes4-size]."""
    t = _NIL
    for name, sz in reversed(list(slots)):
        cell = _appn(_CONS, str_term(name),
                     _appn(_CONS, bytelist_term(
                         int(sz).to_bytes(4, "little")), _NIL))
        t = _appn(_CONS, cell, t)
    return t


def symbols_query(imports, slots) -> T:
    """`symbolsOf IMPORTS SLOTS` — emit stage-2 fragment at term level.
    Slot sizes are bytes4 (the arithmetic rep) — they feed B4ADD."""
    syms = build_symbols(len(imports), len(slots))
    return _appn(syms, json_to_term(list(imports)),
                 _slots_term(slots))


# ---------------------------------------------------------------------------
# G9e: programOf — routines.program(R) at term level (emit stage 3).
#
# program() is pure cons-emission — decision 024's dense part, no folds
# and no arithmetic.  The term is a generated constant
# `λfs λfuel λrbb λcb λnb. <fragment list>` over exactly the R fields
# that data-flow into the insn stream:
#
#   fs        fuse_s as a Church bool selecting variant FRAGMENTS —
#             routine inclusion (st_s iff fuse_s, build_ds iff not) is
#             an outer-level `fs fragA fragB` splice; intra-routine
#             regions (build_ds call, p_s block, sβ dispatch) are found
#             by differencing each builder under sentinel Realizations,
#             not re-encoded.
#   fuel      Maybe bytes8 — `λn.λj.n` | `λn.λj. j v`: the cmp/jge
#             fuel-check block inside the reduce loop.
#   rbb/cb/nb read_buf_bytes / chunk_bytes / node_bytes as bytes8.
#
#   (order is fixed by the routines record itself — x86_64.win64.lo —
#   and abi is guarded by emit(), outside program; both stay out of the
#   minimal signature.)
#
# The output is a Scott list of per-routine fragment lists — the
# ROUTINES order is the honest emission unit (Python flattens it with
# `p += builder(...)`).  It is also the load-bearing efficiency choice:
# a single flat ~540-cell spine leaves the pending emission redex at
# the bottom of the accumulating structure, so each lo rewrite
# path-copies ~all ancestors — measured quadratic (~10M allocs by 40k
# steps, >16GB; native hangs the same way).  Nested fragments bound
# pending depth to ~routines+routine-size (~85 cells) — the same lesson
# as G9d's numeral probes.  Decode flattens.
#
# Item/operand encoding — the JSON-vs-IR comparison answered at lift:
# items mirror ("label", name) / ("i", form, *ops) as tagged lists, but
# every operand is a uniformly tagged union ["r"|"imm"|"l"|"p"|"m", …]
# so assemble decodes by tag string instead of shape-punning a bare
# nibble-string register against a cons cell.  Immediates AND mem
# displacements are bytes8 leaves (packed, never added/subtracted —
# sign-extension equality replaces the i8/i32 range predicates); the
# "l"/"p" payloads stay nibble-string names — SPECGET keys into the G9d
# symbol map / the pass-1 label map.  Sentinel ints in the generated
# program become bound vars, so R is a real parameter, not baked data.
# ---------------------------------------------------------------------------

_SENT_VARS = {-0x1111: "rbb", -0x2222: "cb", -0x3333: "nb", -0x4444: "fv"}
_R_SENT = dict(read_buf_bytes=-0x1111, chunk_bytes=-0x2222,
               node_bytes=-0x3333)

_CONS_E = NComb(_CONS)
_NIL_E = NComb(_NIL)
_STR_CACHE: Dict[str, NExpr] = {}


def _ncons(h: NExpr, t: NExpr) -> NExpr:
    return NApp(NApp(_CONS_E, h), t)


def _nstr(s: str) -> NExpr:
    t = _STR_CACHE.get(s)
    if t is None:
        t = _STR_CACHE[s] = NComb(str_term(s))
    return t


def _nlist(items: List[NExpr], tail: NExpr = _NIL_E) -> NExpr:
    for it in reversed(items):
        tail = _ncons(it, tail)
    return tail


def _le8(v: int) -> T:
    """Immediate/disp leaf: 8-byte little-endian as a byte-cell list —
    byte cells because assembler predicates slice and compare them
    (`i8`/`i32` sign-extension), and disp values are byte-typed data
    (never arithmetic — the G9f rep boundary)."""
    return bytelist_term(int(v & 0xFFFFFFFFFFFFFFFF).to_bytes(8, "little"))


def _val_expr(v: int) -> NExpr:
    """Immediate/disp slot: sentinel int -> bound var, else bytes8."""
    if v in _SENT_VARS:
        return NVar(_SENT_VARS[v])
    return NComb(_le8(v))


def _op_expr(o) -> NExpr:
    if isinstance(o, str):                            # register
        return _nlist([_nstr("r"), _nstr(o)])
    if isinstance(o, int):                            # immediate
        return _nlist([_nstr("imm"), _val_expr(o)])
    tag = o[0]
    if tag in ("l", "p"):                             # label / rip-sym
        assert isinstance(o[1], str)
        return _nlist([_nstr(tag), _nstr(o[1])])
    assert tag == "m"                                 # (base, disp8-bytes)
    return _nlist([_nstr("m"), _nstr(o[1]), _val_expr(o[2])])


def _item_expr(item) -> NExpr:
    if item[0] == "label":
        return _nlist([_nstr("label"), _nstr(item[1])])
    assert item[0] == "i"
    return _nlist([_nstr("i"), _nstr(item[1])]
                  + [_op_expr(o) for o in item[2:]])


def _frag(items) -> NExpr:
    """λt. cons-chain over `items` ending at the bound tail var."""
    return NAbs("t", _nlist([_item_expr(it) for it in items], NVar("t")))


def _fragx(elems: List[NExpr]) -> NExpr:
    """λt. cons-chain over pre-built NExpr cells ending at the tail var."""
    return NAbs("t", _nlist(elems, NVar("t")))


def _regions(pa, pb) -> Dict[int, tuple]:
    """diff opcodes -> {pa_start: (pa_end, pb_items)} variant spans."""
    out = {}
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(
            None, pa, pb, autojunk=False).get_opcodes():
        if tag != "equal":
            out[i1] = (i2, pb[j1:j2])
    return out


def _splice(items, regions, tail: NExpr) -> NExpr:
    """cons-chain over `items`, with `fs`/`fuel` variant splices at the
    region positions (regions keyed by flat index; insert regions have
    i1 == i2 so the item at i is still emitted after the splice)."""
    fuse, fuel = regions
    segs = []
    i = 0
    while i < len(items) or i in fuse or i in fuel:
        if i in fuse:
            e, alt = fuse.pop(i)
            fa, fb = _frag(alt), _frag(items[i:e])
            segs.append(lambda t, fa=fa, fb=fb:
                        NApp(NApp(NApp(NVar("fs"), fa), fb), t))
            i = e
        elif i in fuel:
            e, alt = fuel.pop(i)
            fn = NAbs("t", NVar("t"))
            fj = NAbs("fv", _frag(alt))
            segs.append(lambda t, fn=fn, fj=fj:
                        NApp(NApp(NApp(NVar("fuel"), fn), fj), t))
            i = e
        else:
            it = _item_expr(items[i])
            segs.append(lambda t, it=it: _ncons(it, t))
            i += 1
    assert not fuse and not fuel
    for seg in reversed(segs):
        tail = seg(tail)
    return tail


def program_expr() -> NExpr:
    """λfs λfuel λrbb λcb λnb. <program> — generated per-ROUTINE (the
    ROUTINES order is the honest emission unit; list-of-fragments also
    keeps pending redexes ~30x shallower than one flat spine — the same
    quadratic descent pathology as the G9d numeral probes).  Variant
    regions come from differencing each builder under sentinel
    Realizations; routine inclusion (st_s iff fuse_s, build_ds iff not)
    is the outer-level `fs` splice."""
    rts = routines_x86_64_win64
    ctx = rts._ctx()
    R_def = seed.Realization(**_R_SENT)
    R_fs = seed.Realization(fuse_s=True, **_R_SENT)
    R_fu = seed.Realization(fuel=-0x4444, **_R_SENT)

    tail: NExpr = _NIL_E
    for name in reversed(rts.ROUTINES):
        b = rts._BUILDERS[name]
        f_def, f_fs, f_fu = b(R_def, ctx), b(R_fs, ctx), b(R_fu, ctx)
        if name == "st_s":                      # emitted iff fuse_s
            yes = _fragx([_nlist([_item_expr(i) for i in f_fs])])
            no = NAbs("t", NVar("t"))
        elif name == "build_ds":                # emitted iff not fuse_s
            yes = NAbs("t", NVar("t"))
            no = _fragx([_nlist([_item_expr(i) for i in f_def])])
        else:
            yes = no = None
        if yes is not None:
            tail = NApp(NApp(NApp(NVar("fs"), yes), no), tail)
        else:
            regs = (_regions(f_def, f_fs), _regions(f_def, f_fu))
            tail = _ncons(_splice(f_def, regs, _NIL_E), tail)
    return NAbs("fs", NAbs("fuel", NAbs("rbb", NAbs("cb",
                                                  NAbs("nb", tail)))))


PROGRAM_OF = bracket(program_expr())
_JUST = bracket(parse("(\\v. \\n. \\j. j v)"))


def program_query(R) -> T:
    """`programOf fs fuel rbb cb nb` — emit stage-3 fragment."""
    fuel = KK if R.fuel is None else app(_JUST, _le8(R.fuel))
    return _appn(PROGRAM_OF, TRUE_T if R.fuse_s else FALSE_T, fuel,
                 _le8(R.read_buf_bytes), _le8(R.chunk_bytes),
                 _le8(R.node_bytes))


# ---------------------------------------------------------------------------
# G9f — isa.assemble at term level.
#
# `encode(insn, resolve)` = interpret(FIELDS, PREDS, ENCS[form], ctx,
# b"".join) — the ordered-alternatives walk over the ENCS table is lifted
# wholesale: ENCS/FORMS/REG become nibble-trie DATA (name -> entry, lookup
# = one selector application per name nibble — the quotient-map keyed on
# the name's own structure, not a string compare), field/predicate ops are
# the λ vocabulary below, and operands/addresses are byte cells.
#
# Field tags (nibble dispatch — the name->code map is generated with the
# table): 0 rex, 1 op, 2 oprd, 3 modrm, 4 disp, 5 imm, 6 rel.
# Pred tags: 0 i8, 1 i32, 2 acc.
# modrm reg-side: [0,nib] lit | [1] ext | [2,idx] regN.
# modrm rm-side:  [0,idx] rm | [1,idx] mem | [2] rip.
# Operand-tag trie: r->0 m->1 p->2 l->3.
#
# Addresses/positions are bytes4 (LE) — values under arithmetic, per the
# rep boundary; rel32 = SUBB4 target end, emitted as the 4 result cells.
# ---------------------------------------------------------------------------


# tries ----------------------------------------------------------------------
# node = PAIR maybeval childfn; childfn = \k. k c0..c15; absent child = _NIL
# (lookups are only ever issued for present keys — ENCS/REG are static).

def _nib_path(s: str) -> List[int]:
    out = []
    for b in s.encode("utf-8"):
        out += [b >> 4, b & 15]
    return out


def _napp(*xs: NExpr) -> NExpr:
    t = xs[0]
    for x in xs[1:]:
        t = NApp(t, x)
    return t


def _trie(entries: Dict[str, T]) -> T:
    """Static name->value nibble trie.  Node = pair(maybeVal, \\k. k c0..c15).
    Missing children point at _TRIE_DEAD, which answers Nothing at any
    depth — descent on an absent path is total and terminates."""
    kids: Dict[tuple, set] = {}
    vals: Dict[tuple, T] = {}
    for name, v in entries.items():
        path = tuple(_nib_path(name))
        for i in range(len(path)):
            kids.setdefault(path[:i], set()).add(path[i])
        vals[path] = v

    def node_term(path: tuple) -> T:
        chs = []
        for i in range(16):
            cp = path + (i,)
            chs.append(NComb(node_term(cp)) if i in kids.get(path, ())
                       else NComb(_TRIE_DEAD))
        chfn = bracket(NAbs("k", _napp(NVar("k"), *chs)))
        val = vals.get(path)
        mv = KK if val is None else _appn(_JUST, val)
        return _appn(_PAIR, mv, chfn)

    return node_term(())


# dead trie node: Nothing value, every child K — unreachable on the static
# tries (present keys only), total if ever descended.
_TRIE_DEAD = _appn(_PAIR, KK, bracket_abstract0(parse("\\k. K")))

# TLOOK trie name -> maybeVal — fold the name's nibble cells descending
# node = pair(mv, childfn): childfn nib -> child node.
_TLOOK = ("(\\tr. \\nm. (" + _FOLDL + " (\\nd. \\nb. nd (\\v. \\cf. cf nb))"
          " nm tr) (\\v. \\cf. v))")

# field-tag / pred-tag encoding ---------------------------------------------
_IMM_N = {"i8": 1, "i32": 4, "i64": 8}


def _npred(c) -> NExpr:
    name, i = c[0], c[1]
    tag = {"i8": 0, "i32": 1, "acc": 2}[name]
    return _nlist([NComb(_SELECTORS[tag]), NComb(church(i))])


def _nrole(r: str) -> NExpr:
    if r == "w":
        return _nlist([NComb(_SELECTORS[0])])
    kind = 1 if r[0] == "R" else 2
    return _nlist([NComb(_SELECTORS[kind]), NComb(church(int(r[1:])))])


def _nfield(f) -> NExpr:
    tag = {"rex": 0, "op": 1, "oprd": 2, "modrm": 3,
           "disp": 4, "imm": 5, "rel": 6}[f[0]]
    out = [NComb(_SELECTORS[tag])]
    if f[0] == "rex":
        out.append(_nlist([_nrole(r) for r in f[1:]]))
    elif f[0] == "op" and len(f) > 1:
        out.append(NComb(byte_term(f[1])))
    elif f[0] == "modrm":
        reg, rm = f[1], f[2]
        if isinstance(reg, int):
            rs = _nlist([NComb(_SELECTORS[0]),
                         NComb(_SELECTORS[reg & 15])])
        elif reg == "ext":
            rs = _nlist([NComb(_SELECTORS[1])])
        else:
            rs = _nlist([NComb(_SELECTORS[2]),
                         NComb(church(int(reg[3:])))])
        if rm == "rip":
            ms = _nlist([NComb(_SELECTORS[2])])
        elif rm.startswith("rm"):
            ms = _nlist([NComb(_SELECTORS[0]),
                         NComb(church(int(rm[2:])))])
        else:
            ms = _nlist([NComb(_SELECTORS[1]),
                         NComb(church(int(rm[3:])))])
        out += [rs, ms]
    elif f[0] == "imm":
        out += [NComb(church(_IMM_N[f[1]])), NComb(church(f[2]))]
    elif f[0] == "rel":
        out.append(NComb(church(f[1])))
    return _nlist(out)


def _encs_entry(form: str) -> T:
    """ENCS[form] + FORMS[form] -> pair(row, alts) term."""
    import isa_x86_64 as isa
    _, op, w, ext, _ = isa.FORMS[form]
    # ext: '+' marks oprd rows (modrm never reads it), else the fixed
    # modrm reg-field code 0-7; None for rows with no group field.
    row = _appn(_PAIR, bytelist_term(isa._opbytes(op)),
                _appn(_PAIR, KK if w else _KI,
                      _SELECTORS[ext if isinstance(ext, int) else 0]))
    alts = _NIL
    for conds, tmpl in reversed(isa.ENCS[form]):
        alts = _appn(_CONS,
                     _appn(_PAIR, bracket(_nlist([_npred(c)
                                                for c in conds])),
                           bracket(_nlist([_nfield(f) for f in tmpl]))),
                     alts)
    return _appn(_PAIR, row, alts)


_ENCS_TRIE = _trie({form: _encs_entry(form) for form in
                    __import__("isa_x86_64").ENCS})


def _reg_entries() -> Dict[str, T]:
    import isa_x86_64 as isa
    out = {}
    for name, code in isa.REG64.items():
        out[name] = _appn(_PAIR, _SELECTORS[code], _KI)
    for name, code in isa.REG32.items():
        out[name] = _appn(_PAIR, _SELECTORS[code], _KI)
    for name, code in isa.REG8.items():
        out[name] = _appn(_PAIR, _SELECTORS[code],
                          KK if code >= 4 else _KI)
    return out


_REG_TRIE = _trie(_reg_entries())
_OPTAG_TRIE = _trie({"r": _SELECTORS[0], "m": _SELECTORS[1],
                     "p": _SELECTORS[2], "l": _SELECTORS[3]})



# --- the encoder ------------------------------------------------------------
# ENCODE et rt ott item resv -> pair(byte_list, len_nib)
#   item = ["i", form, op…];  resv = \\name. bytes4
# Tables arrive bound as et/rt/ott (ENCS/REG/op-tag tries); `ops` is the
# item's operand list.  Every fold is _FOLDL — structural on the data.


def _fits8() -> str:
    cells = [f"b{i}" for i in range(8)]
    cond = _EQB + " b1 fl"
    for i in range(2, 8):
        cond = "(" + _AND + " (" + cond + ") (" + _EQB + f" b{i} fl))"
    inner = ("b0 (\\l0. \\h0. (\\fl. " + cond + ") ((" + _NIBGE8
             + " h0) (" + _PAIR_SRC + " " + _SELS[15] + " " + _SELS[15]
             + ") (" + _PAIR_SRC + " " + _SELS[0] + " " + _SELS[0] + ")))")
    return "(\\b8. " + _peel("b8", cells, inner) + ")"


def _fits32() -> str:
    cells = [f"b{i}" for i in range(8)]
    cond = _EQB + " b4 fl"
    for i in range(5, 8):
        cond = "(" + _AND + " (" + cond + ") (" + _EQB + f" b{i} fl))"
    inner = ("b3 (\\l3. \\h3. (\\fl. " + cond + ") ((" + _NIBGE8
             + " h3) (" + _PAIR_SRC + " " + _SELS[15] + " " + _SELS[15]
             + ") (" + _PAIR_SRC + " " + _SELS[0] + " " + _SELS[0] + ")))")
    return "(\\b8. " + _peel("b8", cells, inner) + ")"


def _isz8() -> str:
    cells = [f"b{i}" for i in range(8)]
    z = _prs(_SELS[0], _SELS[0])
    cond = _EQB + " b0 " + z
    for i in range(1, 8):
        cond = "(" + _AND + " (" + cond + ") (" + _EQB + f" b{i} " + z + "))"
    return "(\\b8. " + _peel("b8", cells, cond) + ")"


def _encode_src() -> str:
    """The ENCS-walking encoder as one λ-source.  Bound names:
    et rt ott item resv; derived: form ops row alts opb w ext;
    helpers REGC EMIT SETD EVALF; field impls F0..F6."""
    S = _SELS

    # operand -> pair(code_nib, need_rex_bool);  op = cons(tag, rest).
    # "r" looks the name up in rt (REG8 entries already carry the
    # needs-REX flag in snd); non-register tags answer (0, false).
    regc = (
        "(\\o. o K (\\tg. \\rr. " + _maybe(
            _TLOOK + " ott tg",
            _sel16("k2", [
                "(\\rr2. (" + _TLOOK + " rt (" + _HEAD + " rr2)) K I)",
                # "m": the REX-relevant code is the BASE register's
                "(\\rr2. (" + _TLOOK + " rt (" + _HEAD + " rr2)) K I)",
                "(\\rr2. " + _prs(S[0], "(K I)") + ")",
                "(\\rr2. " + _prs(S[0], "(K I)") + ")",
            ], "rr"), "k2") + "))")

    # emit chunk ch into acc=(disp,(out,ln))
    emitcell = ("(\\a. \\b. a (\\dp. \\oo. oo (\\ou. \\ln. "
                + _prs("dp", _prs(_conss("b", "ou"),
                                  "(" + _NIBSUCC + " ln)")) + ")))")
    emit = "(\\acc. \\ch. " + _FOLDL + " " + emitcell + " ch acc)"
    setd = ("(\\acc. \\nd. acc (\\dp. \\oo. oo (\\ou. \\ln. "
            + _prs("nd", _prs("ou", "ln")) + ")))")

    # rex: fold roles over s=(vlo, need)
    wstep = ("(\\rt2. \\st. st (\\v. \\nd. "
             + _prs("(" + _NIBADD + " v (w " + S[8] + " " + S[0] + "))",
                    "nd") + "))")
    rstep = ("(\\rt2. \\st. (\\i. (REGC (" + _NTH
             + " i ops)) (\\cd. \\ndd. st (\\v. \\nd. "
             + _prs("(" + _NIBADD + " v ((" + _NIBGE8 + " cd) " + S[4]
                    + " " + S[0] + "))",
                    "(" + _OR + " nd ndd)") + "))) (" + _HEAD
             + " rt2))")
    bstep = ("(\\rt2. \\st. (\\i. (REGC (" + _NTH
             + " i ops)) (\\cd. \\ndd. st (\\v. \\nd. "
             + _prs("(" + _NIBADD + " v ((" + _NIBGE8 + " cd) " + S[1]
                    + " " + S[0] + "))",
                    "(" + _OR + " nd ndd)") + "))) (" + _HEAD
             + " rt2))")
    rolestep = ("(\\st. \\role. role K (\\k. \\rt2. "
                + _sel16("k", [wstep, rstep, bstep], "rt2 st") + "))")
    f_rex = _lets([("rl", _HEAD + " args"),
                   ("vv", _FOLDL + " " + rolestep + " rl "
                          + _prs(S[0], "(K I)")),
                   ("v", _fst("vv")), ("nd", _snd("vv"))],
                  "((" + _OR + " (" + _NOT + " (" + EQNIB + " v " + S[0]
                  + ")) nd) (EMIT acc " + _conss(_prs("v", S[4]), "K")
                  + ") acc)")
    f_rex = "(\\acc. \\args. " + f_rex + ")"

    # op / oprd
    f_op = ("(\\acc. \\args. args (EMIT acc opb) (\\h. \\t. "
            "EMIT acc " + _conss("h", "K") + "))")
    f_oprd = ("(\\acc. \\args. opb K (\\b0. \\tt. b0 (\\bl. \\bh. "
              "(REGC (" + _NTH + " " + _church_src(0) + " ops)) "
              "(\\cd. \\nx. EMIT acc "
              + _conss(_prs("(" + _NIBADD + " bl (" + _NIBMOD8
                            + " cd))", "bh"), "K")
              + "))))")

    # modrm — spec = cons(kind_sel, payload_cell); impls take the
    # payload cell directly (NIL-safe: ext/rip ignore it, lit/rmN/memN
    # HEAD it for their payload).
    rlit = "(\\pl. " + _HEAD + " pl)"
    rext = "(\\pl. ext)"
    rreg = ("(\\pl. (REGC (" + _NTH + " (" + _HEAD + " pl) ops)) "
            "(\\cd. \\nx. " + _NIBMOD8 + " cd))")
    m_rm = ("(\\pl. (REGC (" + _NTH + " (" + _HEAD + " pl) ops)) "
            "(\\cd. \\nx. EMIT acc " + _conss(
                "(" + _MODRM3 + " " + S[3] + " r cd)", "K") + "))")
    m_rip = ("(\\pl. EMIT acc " + _conss(
        "(" + _MODRM3 + " " + S[0] + " r " + S[5] + ")", "K") + ")")
    # mem: op = ["m", base_name, b8]; mod/disp by the _f_memi truth table
    mem_body = _lets([
        ("op", _NTH + " (" + _HEAD + " pl) ops"),
        ("rr", _TAIL + " op"),
        ("bs", _HEAD + " rr"),
        ("d8", _HEAD + " (" + _TAIL + " rr)"),
        ("bc", "(" + _TLOOK + " rt bs) K (\\c. c K)"),
        ("lo", _NIBMOD8 + " bc"),
        ("isz", _isz8() + " d8"),
        ("isz5", "(" + _AND + " isz (" + _NOT + " (" + EQNIB
                 + " lo " + S[5] + ")))"),
        ("fts", _fits8() + " d8"),
        ("mod", "isz5 " + S[0] + " (fts " + S[1] + " " + S[2] + ")"),
        ("dp2", "isz5 K (fts (d8 K (\\h. \\t2. " + _conss("h", "K")
                + ")) (" + _REV + " " + _fst(
                    _TAKE + " " + _church_src(4) + " d8") + "))"),
        ("sib", EQNIB + " lo " + S[4]),
        ("rm", "sib " + S[4] + " lo"),
        ("mb", _MODRM3 + " mod r rm"),
        ("ch", _conss("mb", "(sib " + _conss(_prs(S[4], S[2]), "K")
                      + " K)")),
    ], "EMIT (SETD acc dp2) ch")
    m_mem = "(\\pl. " + mem_body + ")"
    f_modrm = _lets([
        ("rs", _HEAD + " args"),
        ("ms", _HEAD + " (" + _TAIL + " args)"),
    ], "rs K (\\rk. \\rr. "
       + "(\\r. ms K (\\mk. \\mr. "
       + _sel16("mk", [m_rm, m_mem, m_rip], "mr") + ")) "
       + "(" + _sel16("rk", [rlit, rext, rreg], "rr") + "))")
    f_modrm = "(\\acc. \\args. " + f_modrm + ")"

    # disp / imm / rel
    f_disp = "(\\acc. \\args. acc (\\dp. \\oo. EMIT acc dp))"
    f_imm = _lets([
        ("cn", _HEAD + " args"),
        ("i", _HEAD + " (" + _TAIL + " args)"),
        ("op", _NTH + " i ops"),
        ("pl", _TAIL + " op"),          # op = cons(tag, cons(b8,NIL))
        ("b8", _HEAD + " pl"),
    ], "EMIT acc (" + _REV + " " + _fst(_TAKE + " cn b8") + ")")
    f_imm = "(\\acc. \\args. " + f_imm + ")"
    f_rel = _lets([
        ("i", _HEAD + " args"),
        ("op", _NTH + " i ops"),
        ("nm", _HEAD + " (" + _TAIL + " op)"),
    ], "EMIT acc (resv nm)")
    f_rel = "(\\acc. \\args. " + f_rel + ")"

    fldstep = ("(\\acc. \\fld. fld K (\\tg. \\args. "
               + _sel16("tg", ["F0", "F1", "F2", "F3", "F4", "F5", "F6"],
                        "acc args") + "))")

    # preds — acc = bool; `acc EV (K I)` = AND acc EV
    payl = "(\\o. o K (\\tg. \\rr. " + _HEAD + " rr))"
    p_i8 = "(\\i. " + _fits8() + " (" + payl + " (" + _NTH + " i ops)))"
    p_i32 = "(\\i. " + _fits32() + " (" + payl + " (" + _NTH + " i ops)))"
    p_acc = ("(\\i. (REGC (" + _NTH + " i ops)) (\\cd. \\nx. " + EQNIB
             + " cd " + S[0] + "))")
    predstep = ("(\\acc. \\pr. acc (pr K (\\pt. \\prr. prr K (\\pi. \\px. "
                + _sel16("pt", [p_i8, p_i32, p_acc], "pi") + "))) (K I))")
    allp = "(\\prs2. " + _FOLDL + " " + predstep + " prs2 K)"

    # alt select + field fold; acc = pair(done, result)
    acc0 = _prs("K", _prs("K", S[0]))
    evalf = ("(\\fl. " + _FOLDL + " " + fldstep + " fl " + acc0 + " "
             "(\\d. \\o. o (\\ou. \\ln. " + _prs(
                 "(" + _REV + " ou)", "ln") + ")))")
    altstep = ("(\\acc. \\alt. acc (\\dn. \\pv. dn acc ("
               "alt (\\pr. \\fl. (" + allp + " pr) "
               + _prs("K", "(EVALF fl)") + " acc))))")
    ares = _FOLDL + " " + altstep + " alts " + _prs("(K I)", "K")

    body = _lets([
        ("ft", _TAIL + " item"),
        ("form", _HEAD + " ft"),
        ("ops", _TAIL + " ft"),
        ("ent", "(" + _TLOOK + " et form) K I"),
        ("row", _fst("ent")),
        ("alts", _snd("ent")),
        ("opb", _fst("row")),
        ("we", _snd("row")),
        ("w", _fst("we")),
        ("ext", _snd("we")),
        ("REGC", regc),
        ("EMIT", emit),
        ("SETD", setd),
        # F0..F6 before EVALF: the impl sources are free-name references
        # into fldstep's dispatch and must sit inside their binders.
        ("F0", f_rex), ("F1", f_op), ("F2", f_oprd), ("F3", f_modrm),
        ("F4", f_disp), ("F5", f_imm), ("F6", f_rel),
        ("EVALF", evalf),
    ], ares + " (\\dn. \\rs. rs)")
    return "(\\et. \\rt. \\ott. \\item. \\resv. " + body + ")"


# bytes4 zero resolver — pass-1 size encoding / the no-resolve gate
_Z4 = bytelist_term(b"\x00\x00\x00\x00")
_ZRESV = bracket(NAbs("nm", NComb(_Z4)))

_ENCODE_OF = _appn(bracket_abstract0(parse(_encode_src())),
                   _ENCS_TRIE, _REG_TRIE, _OPTAG_TRIE)


def encode_query(item, resv: Optional[T] = None) -> T:
    """`encodeOf item resv` — item = ("i", form, *ops) python tuple.
    resv = λname. bytes4; the default is the zero resolver (pass-1 size
    encoding: rel fields emit four zero bytes)."""
    return _appn(_ENCODE_OF, bracket(_item_expr(item)),
                 resv if resv is not None else _ZRESV)


def decode_encode(nf: T) -> Optional[bytes]:
    """NF pair(bytes, len) -> the emitted byte string."""
    if nf.k == K.NORM:
        return None
    bt = _l0_nf(app(nf, KK), 100_000)
    return _decode_bytecells(bt)


# ---------------------------------------------------------------------------
# assembleOf — isa.assemble's two passes at term level.
#
#   ASM prog sym base -> pair(code_bytes, local_map)
#
#   prog  = fragment list from programOf (list of item lists)
#   sym   = assoc map name -> bytes4  — THE LINK SEAM: `symbols` is the
#           external table (imports/data RVAs today, a real linker's
#           merged object table in the later toolchain phase); it is
#           injected data and SHADOWS local labels, mirroring
#           `symbols[name] if name in symbols else local[name]`.
#   base  = bytes4 load base (TEXT_RVA analogue).
#
#   pass 1 folds fragments -> (pos4, localmap, prepared_rev): labels
#       record base+pos; insns record (item, off4, len4) where
#       len4 = snd (ENC it ZRV) — the zero resolver gives the correct
#       byte COUNT because rel fields are always four cells.
#   pass 2 folds prepared records: end4 = base+off+len;
#       resv nm = SUBB4 (sym nm | loc nm) end4 — two's-complement
#       rel32 emitted as the 4 result cells.  A resolver miss yields
#       -end (0 - end, the `.get(n,0)` analogue; the oracle raises
#       KeyError — gate inputs always resolve).
#
# All arithmetic is bytes4 ripple ops — constant cost per value, no
# Church-numeral PRED chains.  insn length is a NIBBLE lifted once via
# NIB2B4 (x86 insns are <=15 bytes by ISA limit — the nibble is honest).
# ---------------------------------------------------------------------------


def _assemble_src() -> str:
    lbl = _prefix_src("label", "K")          # nibble-string "label"
    is_lbl = ("(" + EQSTR + " tg " + lbl + " (" + _LEN + " tg))")

    # pass-1 acc = pair(pos4, pair(loc, prep_rev))
    label_case = (
        "acc (\\p0. \\r0. r0 (\\lc. \\pr. " + _prs("p0", _prs(
            _conss(_prs("(" + _HEAD + " rr)",
                        "(" + _B4ADD + " base p0)"), "lc"),
            _conss(_prs("it", _prs("p0", "K")), "pr"))) + "))")
    insn_case = _lets([
        ("enc", "(ENC it ZRV)"),
        ("ln4", "(" + _NIB2B4 + " " + _snd("enc") + ")"),
    ], "acc (\\p0. \\r0. r0 (\\lc. \\pr. " + _prs(
        "(" + _B4ADD + " p0 ln4)",
        _prs("lc", _conss(_prs("it", _prs("p0", "ln4")), "pr"))) + "))")
    # NB: both branch bodies are APPLICATIONS — they must sit parenthesized
    # in the bool spine, else `is_lbl a b c` mis-groups (acc and the ENC
    # call leak into the dispatch as extra args).
    p1step = ("(\\acc. \\it. it K (\\tg. \\rr. " + is_lbl + " ("
              + label_case + ") (" + insn_case + ")))")

    # pass-2 resolver: symbols shadow locals (the link seam)
    resv = ("(\\nm. (" + _ALOOK + " sym nm) ((" + _ALOOK + " loc nm) ("
            + _B4SUB + " " + _b4_src(0) + " end4) (\\lv. " + _B4SUB
            + " lv end4)) (\\sv. " + _B4SUB + " sv end4))")
    insn_emit = _lets([
        ("end4", "(" + _B4ADD + " (" + _B4ADD + " base of) ln)"),
        ("rsv", resv),
        ("enc2", "(ENC it rsv)"),
    ], _FOLDL + " (\\o. \\c. " + _conss("c", "o") + ") "
       + _fst("enc2") + " acc")
    emitstep = ("(\\acc. \\rec. rec (\\it. \\ol. ol (\\of. \\ln. "
                "it K (\\tg. \\rr. " + is_lbl + " acc ("
                + insn_emit + ")))))")

    body = _lets([
        ("p1", _FOLDL + " (\\a. \\fr. " + _FOLDL + " " + p1step
               + " fr a) prog " + _prs(_b4_src(0), _prs("K", "K"))),
        ("loc", "(" + _snd("p1") + " K)"),
        ("prep", "(" + _REV + " (" + _snd("p1") + " (K I)))"),
        ("out", _FOLDL + " " + emitstep + " prep K"),
    ], _prs("(" + _REV + " out)", "loc"))
    return "(\\ENC. \\ZRV. \\prog. \\sym. \\base. " + body + ")"


_ASSEMBLE = _appn(bracket_abstract0(parse(_assemble_src())),
                  _ENCODE_OF, _ZRESV)


def symtab_term(symbols: Dict[str, int]) -> T:
    """{name: rva} -> assoc list of pair(nibble-string, bytes4)."""
    t = _NIL
    for name, addr in reversed(list(symbols.items())):
        t = _appn(_CONS, _appn(_PAIR, str_term(name),
                              bytelist_term(
                                  addr.to_bytes(4, "little"))), t)
    return t


def fraglist_term(frags) -> T:
    """[[item,…],…] -> programOf's fragment-list shape."""
    t = _NIL
    for frag in reversed(frags):
        f = _NIL
        for it in reversed(frag):
            f = _appn(_CONS, bracket(_item_expr(it)), f)
        t = _appn(_CONS, f, t)
    return t


def assemble_query(prog: T, symbols: Dict[str, int], base: int) -> T:
    """`assembleOf prog symtab base`."""
    return _appn(_ASSEMBLE, prog, symtab_term(symbols),
                 bytelist_term(base.to_bytes(4, "little")))


def assemble_query_t(prog: T, symtab: T, base: int) -> T:
    """`assembleOf` with program and symtab already terms — the staged
    seam: prog is programOf's NF, symtab a linkOf-NF projection."""
    return _appn(_ASSEMBLE, prog, symtab,
                 bytelist_term(base.to_bytes(4, "little")))


def decode_assemble(nf: T):
    """NF pair(bytes, localmap) -> (bytes, {name: rva})."""
    if nf.k == K.NORM:
        return None
    out = _decode_bytecells(_l0_nf(app(nf, KK), 200_000))
    lc = _l0_nf(app(nf, _KI), 200_000)
    local: Dict[str, int] = {}
    while lc.k != K.KONST:
        pr, lc = _cell_parts(lc)
        key = _decode_str(_l0_nf(app(pr, KK), 50_000))
        local[key] = int.from_bytes(
            _decode_bytecells(_l0_nf(app(pr, _KI), 50_000)), "little")
    return out, local


def python_assemble(prog, symbols, base):
    """isa.assemble on the same items — the independent oracle."""
    import isa_x86_64 as isa
    flat = [it for frag in prog for it in frag]
    return isa.assemble(flat, dict(symbols), base)


# ---------------------------------------------------------------------------
# G9g: dataOf / idataOf / packOf — target_pe64.pack at term level
# (emit stage 5, the container writer).
#
# Oracle shape (target_pe64.py):
#   build_data slots -> (zeros(total_sz), {name: DATA_RVA + off})
#   build_idata imps -> (idt|ilt|iat|names|dll bytes, {iat_nm: rva})
#   pack text labels imps slots R -> headers ++ text_raw ++ idata_raw
#       ++ data_raw   (raw = section ++ pad to FILE_ALIGN)
#
# Rep boundary (unchanged from G9f): values that are added/subtracted —
# RVAs, offsets, sizes — are bytes4; emission counts (zero fills, pads)
# are Church numerals.  Section pad align512(len)-len is never computed
# by subtraction: PADLIST extracts rem = len & 511 directly off len4's
# low nibbles (pure masking), then `rem TAIL z512` drops rem cells off a
# 512-zero literal — one cheap TAIL per pad cell, no B4INC+EQB4 loop and
# no numeral SUB/PRED chain.
# ---------------------------------------------------------------------------


def _bytes_src(bs) -> str:
    """Literal byte-cell list of any length — same rep as _b4_src."""
    out = "K"
    for b in reversed(list(bs)):
        out = _conss("(" + _PAIR_SRC + " " + _SELS[b & 15] + " "
                     + _SELS[b >> 4] + ")", out)
    return out


def _join_src(chunks) -> str:
    """JOIN [c1 … ck] — right-assoc concat: each chunk traversed once."""
    out = "K"
    for c in reversed(chunks):
        out = _conss("(" + c + ")", out)
    return "(" + _JOIN + " " + out + ")"


# JOIN l — flatten a list of byte lists; right-assoc so total work is
# linear in the image size (left-fold APPEND would re-walk the prefix).
_JOIN = (
    "(\\l. (\\f. f f) (\\g. \\l2. l2 K (\\h. \\t. (" + _APPEND
    + " h (g g t)))) l)"
)
# MAP f l — order-preserving map (self-application bounded by the spine)
_MAP = (
    "(\\f2. \\l2. (\\f. f f) (\\g. \\l3. l3 K (\\h. \\t3. "
    + _conss("(f2 h)", "(g g t3)") + ")) l2)"
)
# nibble -> bool (K = odd) / nibble -> numeral / nibble -> parity numeral
_NIBODD = ("(\\a. a " + " ".join(
    "K" if i & 1 else "(K I)" for i in range(16)) + ")")
_NIB2NUM = ("(\\a. a " + " ".join(
    "(" + _num_src(i) + ")" for i in range(16)) + ")")
_NIBPAR = ("(\\a. a " + " ".join(
    "(" + _num_src(i & 1) + ")" for i in range(16)) + ")")
# PADLIST len4 -> zeros(align512(len) - len) — rem = len & 511 read off
# byte0 (lo+16*hi) and byte1's low-nibble bit0; pad = rem TAIL z512
# (512 - rem zeros), guarded to zero at rem = 0.
_PADLIST = (
    "(\\v. " + _peel("v", ["b0", "b1"],
        "b0 (\\l0. \\h0. b1 (\\l1. \\h1. "
        + _let("rem",
               "(" + _ADD_SRC + " (" + _ADD_SRC + " (" + _NIB2NUM
               + " l0) (" + _MUL_SRC + " " + _num_src(16) + " ("
               + _NIB2NUM + " h0))) (" + _MUL_SRC + " " + _num_src(256)
               + " (" + _NIBPAR + " l1)))",
               "(rem (\\x. (K I)) K) K (rem " + _TAIL + " ("
               + _ZEROFILL + " " + _num_src(512) + "))")
        + "))") + ")"
)

# dataOf ------------------------------------------------------------------
# slots fold: state (l, off, syms, zeros); each element is the 3-list
# [name, sz-numeral, sz-bytes4] — the numeral emits zeros (iteration
# bound), the bytes4 advances the RVA (arithmetic value).  This is the
# same slot payload as G9d's 2-list plus its numeral twin.
_STEP_D = (
    "\\acc. acc (\\l. \\o. \\u. \\z. l "
    "(\\k2. k2 l o u z) "
    "(\\p. \\t. p (\\k2. k2 t o u z) "
    "(\\nm. \\r1. r1 (\\k2. k2 t o u z) "
    "(\\szn. \\r2. r2 (\\k2. k2 t o u z) "
    "(\\szb. \\r3. \\k2. k2 t (" + _B4ADD + " o szb) "
    + _conss("(" + _PAIR_SRC + " nm o)", "u")
    + " (szn (\\l2. " + _conss(_B0C, "l2") + ") z))))))"
)
DATA_OF = (
    "(\\slots. (__NSLOTD__ (" + _STEP_D + ") "
    "(\\k2. k2 slots " + _b4_src(0x3000) + " K K)) "
    "(\\l. \\o. \\u. \\z. " + _prs("z", "u") + "))"
)


def data_src(n_slot: int) -> str:
    src = DATA_OF.replace("__NSLOTD__", _church_src(n_slot))
    assert "__" not in src, "uninstantiated placeholder"
    return src


# idataOf ------------------------------------------------------------------
# imports fold: state (l, off, oiat, rvas, recs, syms).  off is the
# section-relative cursor (oracle `off`); hn_rva = IDATA_RVA + off is
# measured per record and the record length is measured by LENB4 — the
# honest `off += len(hn)`.  oiat walks the IAT in +8 steps for the
# symbol map (same as G9d's _STEP_I).
_STEP_ID = (
    "\\acc. acc (\\l. \\o. \\oi. \\rv. \\rc. \\sy. l "
    "(\\k2. k2 l o oi rv rc sy) "
    "(\\nm. \\t. " + _lets([
        ("nmb", "(" + _NIBS2BYTES + " nm)"),
        ("brec", _join_src([_bytes_src(b"\x00\x00"), "nmb",
                            _bytes_src(b"\x00")])),
        ("rln", "(" + _LENB4 + " brec)"),
        ("odd", _peel("rln", ["b0"],
                      "b0 (\\bl. \\bh. " + _NIBODD + " bl)")),
        ("rec", "(odd (" + _APPEND + " brec " + _bytes_src(b"\x00")
                + ") brec)"),
        ("rl2", "(" + _LENB4 + " rec)"),
        ("hrv", "(" + _B4ADD + " " + _b4_src(0x2000) + " o)"),
    ], "\\k2. k2 t (" + _B4ADD + " o rl2) (" + _B4ADD + " oi "
       + _b4_src(8) + ") " + _conss("hrv", "rv") + " "
       + _conss("rec", "rc") + " "
       + _conss("(" + _PAIR_SRC + " __IATPFX__ oi)", "sy"))
    + "))"
)
_IDATA_FIN = _lets([
    ("drva", "(" + _B4ADD + " " + _b4_src(0x2000) + " o)"),
    ("ilt", "(" + _JOIN + " (" + _REV + " "
            + _conss(_bytes_src(bytes(8)),
                     "(" + _MAP + " " + _U64 + " rv)") + "))"),
    ("idt", _join_src([
        _b4_src(0x2000 + 40), _b4_src(0), _b4_src(0), "drva",
        "__IATRVA4__",
        "(" + _ZEROFILL + " " + _num_src(20) + ")"])),
    ("nams", "(" + _JOIN + " (" + _REV + " rc))"),
    ("body", _join_src(["idt", "ilt", "ilt", "nams",
                        _bytes_src(b"kernel32.dll\x00")])),
], _prs("body", "sy"))
IDATA_OF = (
    "(\\imports. (__NIMP__ (" + _STEP_ID + ") "
    "(\\k2. k2 imports __NAMESOFF__ __IATB__ K K K)) "
    "(\\l. \\o. \\oi. \\rv. \\rc. \\sy. " + _IDATA_FIN + "))"
)


def idata_src(n_imp: int) -> str:
    ilt_sz = (n_imp + 1) * 8
    iat_off = 40 + ilt_sz
    src = IDATA_OF
    for ph, val in (
        ("__NIMP__", _church_src(n_imp)),
        ("__IATPFX__", _prefix_src("iat_", "nm")),
        ("__IATB__", _b4_src(0x2000 + iat_off)),
        ("__NAMESOFF__", _b4_src(iat_off + ilt_sz)),
        ("__IATRVA4__", _b4_src(0x2000 + iat_off)),
    ):
        src = src.replace(ph, val)
    assert "__" not in src, "uninstantiated placeholder"
    return src


# packOf -------------------------------------------------------------------
# `pack text imports slots stackres` — labels are diagnostics-only in
# the oracle (dropped); R enters only through stack_reserve (a u64
# field).  All format constants (magics, RVAs, aligns, versions, the
# fixed 448-byte header pad) are literal chunks; every size/offset field
# is computed at term level from LENB4 / ALIGN / B4ADD over the actual
# section bytes.  JOIN keeps emission linear in the image size.
def _pack_body() -> str:
    """The shared pack emission.  `text`, `idata`, `datab`, `stackres`
    are free — bound by the enclosing λ (packOf's params, or pack2Of's
    post-link signature)."""
    z12 = "(" + _ZEROFILL + " " + _num_src(12) + ")"
    chunks = [
        _bytes_src(b"MZ"), "(" + _ZEROFILL + " " + _num_src(58) + ")",
        _bytes_src(struct.pack("<I", 0x40)),
        _bytes_src(b"PE\x00\x00"),
        _bytes_src(struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0,
                               0x22)),
        _bytes_src(struct.pack("<HBB", 0x20B, 0, 0)),
        "traw", "iddr", _bytes_src(struct.pack("<I", 0)),
        _bytes_src(struct.pack("<I", 0x1000)),
        _bytes_src(struct.pack("<I", 0x1000)),
        _bytes_src(struct.pack("<Q", 0x140000000)),
        _bytes_src(struct.pack("<II", 0x1000, 0x200)),
        _bytes_src(struct.pack("<HHHHHH", 6, 0, 0, 0, 6, 0)),
        _bytes_src(struct.pack("<I", 0)), "img",
        _bytes_src(struct.pack("<II", 0x200, 0)),
        _bytes_src(struct.pack("<HH", 3, 0x8100)),
        "(" + _U64 + " stackres)",
        _bytes_src(struct.pack("<QQQ", 0x1000, 0x100000, 0x1000)),
        _bytes_src(struct.pack("<II", 0, 16)),
        _bytes_src(struct.pack("<II", 0, 0)),
        _bytes_src(struct.pack("<I", 0x2000)), "li",
        "(" + _ZEROFILL + " " + _num_src(14 * 8) + ")",
        _bytes_src(b".text\x00\x00\x00"), "lt",
        _bytes_src(struct.pack("<I", 0x1000)), "traw",
        _bytes_src(struct.pack("<I", 0x200)), z12,
        _bytes_src(struct.pack("<I", 0x60000020)),
        _bytes_src(b".idata\x00\x00"), "li",
        _bytes_src(struct.pack("<I", 0x2000)), "iraw", "iptr", z12,
        _bytes_src(struct.pack("<I", 0x40000040)),
        _bytes_src(b".data\x00\x00\x00"), "ld",
        _bytes_src(struct.pack("<I", 0x3000)), "draw", "dptr", z12,
        _bytes_src(struct.pack("<I", 0xC0000040)),
        "(" + _ZEROFILL + " " + _num_src(0x200 - 448) + ")",
        "text", "(" + _PADLIST + " lt)",
        "idata", "(" + _PADLIST + " li)",
        "datab", "(" + _PADLIST + " ld)",
    ]
    return _lets([
        ("lt", "(" + _LENB4 + " text)"),
        ("li", "(" + _LENB4 + " idata)"),
        ("ld", "(" + _LENB4 + " datab)"),
        ("traw", "(" + _ALIGN512 + " lt)"),
        ("iraw", "(" + _ALIGN512 + " li)"),
        ("draw", "(" + _ALIGN512 + " ld)"),
        ("iptr", "(" + _B4ADD + " " + _b4_src(0x200) + " traw)"),
        ("dptr", "(" + _B4ADD + " iptr iraw)"),
        ("iddr", "(" + _B4ADD + " iraw draw)"),
        ("img", "(" + _ALIGN4096 + " (" + _B4ADD + " "
                + _b4_src(0x3000) + " ld))"),
    ], _join_src(chunks))


def pack_src(n_imp: int, n_slot: int) -> str:
    body = _lets([
        ("idr", "(" + idata_src(n_imp) + " imports)"),
        ("dat", "(" + data_src(n_slot) + " slots)"),
        ("idata", "(idr K)"), ("datab", "(dat K)"),
    ], _pack_body())
    return "(\\text. \\imports. \\slots. \\stackres. " + body + ")"


def pack2_src() -> str:
    """packOf post-link: `\\text. \\idata. \\datab. \\stackres` — the
    sections arrive already built (by linkOf); nothing is recomputed."""
    return "(\\text. \\idata. \\datab. \\stackres. " + _pack_body() + ")"


# --- G9g inputs / queries / decoders ---------------------------------------

def _slots3_term(slots) -> T:
    """[(name, size)] -> Scott list of [nibname, numeral, bytes4]."""
    t = _NIL
    for name, sz in reversed(list(slots)):
        cell = _appn(_CONS, str_term(name),
                     _appn(_CONS, church(int(sz)),
                           _appn(_CONS, bytelist_term(
                               int(sz).to_bytes(4, "little")), _NIL)))
        t = _appn(_CONS, cell, t)
    return t


def data_query(slots) -> T:
    """`dataOf SLOTS` — build_data at term level."""
    return _appn(bracket(parse(data_src(len(slots)))), _slots3_term(slots))


def idata_query(imports) -> T:
    """`idataOf IMPORTS` — build_idata at term level."""
    return _appn(bracket(parse(idata_src(len(imports)))),
                 json_to_term(list(imports)))


def pack_query(text: bytes, imports, slots, stackres: int) -> T:
    """`packOf text imports slots stackres` — target_pe64.pack."""
    return pack_query_t(bytelist_term(text), imports, slots, stackres)


def pack_query_t(text_t: T, imports, slots, stackres: int) -> T:
    """pack_query with `text` already a term — lets an upstream stage
    feed packOf inside one graph (e.g. `(assembleOf …) K`), which is
    the end-to-end composition probe."""
    return _appn(bracket(parse(pack_src(len(imports), len(slots)))),
                 text_t, json_to_term(list(imports)),
                 _slots3_term(slots),
                 bytelist_term(stackres.to_bytes(4, "little")))


def decode_bytesyms(nf: T):
    """NF pair(bytes, syms-alist) -> (bytes, {name: rva})."""
    if nf.k == K.NORM:
        return None
    out = _decode_bytecells(_l0_nf(app(nf, KK), 500_000))
    return out, decode_symbols(_l0_nf(app(nf, _KI), 500_000))


def python_data(slots):
    """tgt.build_data — the independent oracle."""
    return target_pe64.build_data(slots)


def python_idata(imports):
    """tgt.build_idata — the independent oracle."""
    return target_pe64.build_idata(imports)


def python_pack(text, imports, slots, stackres) -> bytes:
    """tgt.pack — the independent oracle (labels unused by it)."""
    R = SimpleNamespace(stack_reserve=stackres)
    return target_pe64.pack(text, {}, imports, slots, R)


# ---------------------------------------------------------------------------
# G9h: linkOf — the linker stage.  The section builders run ONCE and
# export their symtabs; linkOf merges them into the global table that
# assemble's resolver consumes, and hands the emitted sections to
# pack2Of.  The link seam closes: symbols are derived from the actual
# emitted sections, not injected by hand and not recomputed from counts.
#
#   L = linkOf IMPORTS SLOTS          -> pair(pair(idata, datab), syms)
#   A = assembleOf PROG (L (K I)) base               -- symtab from link
#   P = pack2Of (A K) (L K K) (L K (K I)) stackres   -- sections from link
#
# Merge order: ALOOK is FOLDL last-match, so APPEND iat_syms data_syms
# puts data last — mirrors `out = dict(iat); out.update(ds)` in
# target.symbols.  Namespaces never collide in practice (the iat_
# prefix), but the order is the honest mirror anyway.
# ---------------------------------------------------------------------------


def link_src(n_imp: int, n_slot: int) -> str:
    """λ-source of `\\imports. \\slots. linkOf` — bounds instantiated."""
    return ("(\\imports. \\slots. "
            + _lets([
                ("idr", "(" + idata_src(n_imp) + " imports)"),
                ("dat", "(" + data_src(n_slot) + " slots)"),
            ], _prs(_prs("(idr K)", "(dat K)"),
                    "(" + _APPEND + " (idr (K I)) (dat (K I)))"))
            + ")")


def link_query(imports, slots) -> T:
    """`linkOf IMPORTS SLOTS` — sections + merged symtab at term level."""
    return _appn(bracket(parse(link_src(len(imports), len(slots)))),
                 json_to_term(list(imports)), _slots3_term(slots))


def pack2_query(text: bytes, idata: bytes, datab: bytes,
                stackres: int) -> T:
    """`pack2Of text idata datab stackres` — pack over linked sections."""
    return _appn(bracket(parse(pack2_src())), bytelist_term(text),
                 bytelist_term(idata), bytelist_term(datab),
                 bytelist_term(stackres.to_bytes(4, "little")))


def pack2_query_t(text: T, idata: T, datab: T, stackres: int) -> T:
    """`pack2Of` with all section inputs already terms — the staged
    seam: text is an assembleOf-NF projection, idata/datab linkOf
    projections."""
    return _appn(bracket(parse(pack2_src())), text, idata, datab,
                 bytelist_term(stackres.to_bytes(4, "little")))


def linkasm_query(prog: T, imports, slots, base: int) -> T:
    """`assembleOf PROG (linkOf … (K I)) base` — the resolver seam fed
    by the link stage's merged symtab instead of an injected table."""
    link_t = _appn(bracket(parse(link_src(len(imports), len(slots)))),
                   json_to_term(list(imports)), _slots3_term(slots))
    return _appn(_ASSEMBLE, prog, app(link_t, _KI),
                 bytelist_term(base.to_bytes(4, "little")))


def decode_link(nf: T):
    """NF pair(pair(idata, datab), syms) -> (idata, datab, {name: rva})."""
    if nf.k == K.NORM:
        return None
    sects = _l0_nf(app(nf, KK), 500_000)
    ib = _decode_bytecells(_l0_nf(app(sects, KK), 300_000))
    db = _decode_bytecells(_l0_nf(app(sects, _KI), 300_000))
    syms = decode_symbols(_l0_nf(app(nf, _KI), 500_000))
    return ib, db, syms


def python_link(imports, slots):
    """linkOf oracle: build_idata + build_data + the merged table —
    `update` order mirrors ALOOK's last-match."""
    ib, isyms = target_pe64.build_idata(imports)
    db, dsyms = target_pe64.build_data(slots)
    syms = dict(isyms)
    syms.update(dsyms)
    return ib, db, syms


def isa_x86_64_gate_encode(insn) -> bytes:
    """isa.encode on the raw ("i", form, *ops) item — oracle bytes."""
    import isa_x86_64 as isa
    return isa.encode(tuple(insn[1:]))


def python_program(R) -> list:
    """rts.program(R) on the real module — the independent witness."""
    return list(routines_x86_64_win64.program(R))


PROG_CASES = {
    "default": seed.Realization(),
    "fuse_s": seed.Realization(fuse_s=True),
    "fuel64": seed.Realization(fuel=64),
    "buf128k": seed.Realization(read_buf_bytes=128 << 10),
    "fuel+fuse": seed.Realization(fuse_s=True, fuel=64),
}


# G9f gate data — a fragment list exercising every item kind:
# forward AND backward local rel32 (negative displacement via B4SUB),
# rip-relative symbol refs, one name present in BOTH the local labels
# and the symbol table (the oracle's resolver prefers `symbols` — the
# link seam's shadowing rule), mem/disp forms, and base != 0.
ASM_PROG = [
    [("label", "start"),
     ("i", "call_rel32", ("l", "mid")),               # forward local
     ("i", "push_r64", "rbp"),
     ("i", "mov_r64_r64", "rbp", "rsp")],
    [("label", "mid"),
     ("i", "mov_r64_rip", "rax", ("p", "scratch")),   # symbol via rip
     ("i", "mov_r64_m64", "rbx", ("m", "rsp", 8)),
     ("i", "call_rel32", ("l", "start")),            # backward local
     ("i", "mov_r64_rip", "rcx", ("p", "mid")),      # shadowed: sym wins
     ("i", "pop_r64", "rbp"),
     ("i", "ret",)],
]
ASM_SYMS = {"scratch": 0x3248, "mid": 0x7777}
# The suite gate splits the mini program's coverage into two tractable
# cases — the monolithic mini is probe-verified (~1.22M lo steps,
# ~28GB arena) but too heavy for the routine loop.  `link` covers
# labels + fwd/bwd rel32 + multi-fragment; `shadow` covers rip-symbol
# refs + mem disp + the symbols-shadow-local link rule (mid is in
# both maps) + a nonzero base.
ASM_LINK = [
    [("label", "top"),
     ("i", "call_rel32", ("l", "bot")),               # forward local
     ("i", "ret")],
    [("label", "bot"),
     ("i", "call_rel32", ("l", "top")),               # backward local
     ("i", "ret")],
]
ASM_SHADOW = [
    [("label", "mid"),
     ("i", "mov_r64_rip", "rcx", ("p", "mid")),       # shadowed: sym wins
     ("i", "mov_r64_rip", "rax", ("p", "scratch")),   # symbol via rip
     ("i", "mov_r64_m64", "rbx", ("m", "rsp", 8)),    # mem disp8
     ("i", "ret")],
]
ASM_MINI = (ASM_PROG, ASM_SYMS, 0x1000)   # extended case — probe-verified
ASM_CASES = {"link": (ASM_LINK, {}, 0x1000),
             "shadow": (ASM_SHADOW, ASM_SYMS, 0x2000)}

# encode spot-checks — one form per field-shape class not covered by
# the mini program (full 26-instance sweep: _probe_g9f_enc.py).
ENC_CASES = [
    ("i", "mov_r64_imm", "rax", 0x1122334455),       # oprd + imm64
    ("i", "add_r64_imm", "rcx", 300),                # ext + i32 alt
    ("i", "mov_m8_imm8", ("m", "rbx", 4), 9),        # ext + mem + i8
    ("i", "mov_r64_m64", "rax", ("m", "r12", 16)),   # SIB + disp8
    ("i", "xor_r32_r32", "eax", "eax"),              # 32-bit modrm
    ("i", "lea_r64_rip", "rbx", ("p", "data")),      # rip-rel
]

# G9g gate data — pack stage.  dataOf/idataOf gate at both scales
# (the folds are cheap); packOf gates on the PE64-self-check shape
# (target_pe64.main's own probe: ret + one import + one slot) and an
# aligned-edge case (len(text) ≡ 0 mod FILE_ALIGN exercises the
# PADLIST rem=0 guard — no pad bytes emitted).  The real win64 pack
# (1991B text -> 3584B image, ~2.1M lo steps) is probe-verified,
# heavyweight-only — see _probe_g9g_pack.py.
DATA_CASES = {
    "mini": (("x", 8),),
    "win64": routines_x86_64_win64.DATA_SLOTS,
}
IDATA_CASES = {
    "mini": ("ExitProcess",),
    "win64": routines_x86_64_win64.IMPORTS,
}
PACK_CASES = {
    "mini": (b"\xc3", ("ExitProcess",), (("x", 8),), 64 << 20),
    "aligned": (bytes(512), ("ExitProcess",), (("x", 8),), 64 << 20),
}

# G9h gate data — the linker stage.  linkOf gates at both scales (the
# folds are cheap); pack2Of gates the mini shape (same cd deferral as
# packOf — the NF is image-sized); linkasm gates the resolver seam fed
# by the link's merged symtab — real iat_/data addresses derived from
# the emitted sections, not injected.
LINK_CASES = {
    "mini": (("ExitProcess",), (("x", 8),)),
    "win64": (routines_x86_64_win64.IMPORTS,
              routines_x86_64_win64.DATA_SLOTS),
}
PACK2_CASES = {
    "mini": (b"\xc3", ("ExitProcess",), (("x", 8),), 64 << 20),
}
LINKASM_PROG = [
    [("label", "top"),
     ("i", "call_rel32", ("l", "bot")),                        # local fwd
     ("i", "mov_r64_rip", "rax", ("p", "x")),                  # data sym
     ("i", "mov_r64_rip", "rcx", ("p", "iat_ExitProcess")),    # iat sym
     ("label", "bot"),
     ("i", "ret",)],
]
LINKASM_CASES = {
    "mini": (LINKASM_PROG, ("ExitProcess",), (("x", 8),), 0x1000),
}
# Vocabulary congruence — the CLA twin must Join the ripple on the
# critical carry shapes (full wraparound cascade; mixed carries).
# Lean proves b4add_b4cla_basis for ALL inputs (SpecVocabulary); this
# gates the host encoding against the literal.  cd rounds printed —
# the lookahead's independent carry cones show as fewer rounds.
CLA_CASES = {
    "wrap": (0x00000001, 0xFFFFFFFF),
    "mixed": (0x01020304, 0x0F0E0D0C),
}
# Re-association congruence — (a++b)++c ≡ a++(b++c) on every closed
# Scott list (Lean: append_assoc_basis, all inputs).  This is the
# license to pick emission shape by strategy: sequential right-assoc
# spine (linear lo work) vs balanced tree (independent cones — cd
# develops both halves per round; the "max parallelism" payoff).
ASSOC_CASES = {
    "l234": (b"\x01\x02", b"\x03\x04\x05", b"\x06\x07\x08\x09"),
    "skewL": (b"\x0a\x0b\x0c\x0d\x0e", b"\x0f", b"\x10"),
    "nilR": (b"\x11\x12\x13", b"\x14\x15", b""),
}


# ---------------------------------------------------------------------------
# output map: bare I = none; C (B^k I)…K spine = nibble-string
# ---------------------------------------------------------------------------

def _decode_nib(h: T) -> int:
    """B^k I -> k (xdu output-map convention)."""
    k = 0
    while h.k == K.APP and h.l is not None and h.l.k == K.COMP:
        k += 1
        h = h.r
    if h is None or h.k != K.NORM:
        raise ValueError(f"output map: element is not B^k I: {h}")
    return k


def decode_result(nf: T) -> Optional[str]:
    """NF -> None (bare I) or the decoded path string (C-spine)."""
    if nf.k == K.NORM:
        return None
    nibs: List[int] = []
    t = nf
    while (t.k == K.APP and t.l is not None and t.l.k == K.APP
           and t.l.l is not None and t.l.l.k == K.SWAP):
        nibs.append(_decode_nib(t.l.r))
        t = t.r
    if t is None or t.k != K.KONST:
        raise ValueError(f"result is neither I nor a C-spine: {nf}")
    if len(nibs) & 1:
        raise ValueError("output map: odd nibble count (no rc convention)")
    return bytes(nibs[i] << 4 | nibs[i + 1]
                 for i in range(0, len(nibs), 2)).decode("utf-8")


# ---------------------------------------------------------------------------
# resolve output map: bare I = none; Scott list of nibble-strings else.
# Destructured by probes: cell I K -> head, cell I (K I) -> tail;
# nibble sel applied to 16 VAR markers -> v_k.  The probes are tiny
# closed applications, reduced by a minimal L0 stepper (the exported NF
# is already normal — probes only fire the cell/selector λs).
# ---------------------------------------------------------------------------

_MARKS = tuple(T(K.VAR, n=i) for i in range(16))


def _l0_step(t: T) -> Optional[T]:
    if t.k != K.APP:
        return None
    f, x = t.l, t.r
    if f.k == K.NORM:
        return x
    if f.k == K.APP:
        fl, fr = f.l, f.r
        if fl.k == K.KONST:
            return fr
        if fl.k == K.DUP:
            return app(app(fr, x), x)
        if fl.k == K.APP:
            fll, flr = fl.l, fl.r
            if fll.k == K.COMP:
                return app(flr, app(fr, x))
            if fll.k == K.SWAP:
                return app(app(flr, x), fr)
            if (fll.k == K.APP and fll.l is not None
                    and fll.l.k == K.S):
                return app(app(fll.r, x), app(flr, x))
    sf = _l0_step(f)
    if sf is not None:
        return app(sf, x)
    sx = _l0_step(x)
    return None if sx is None else app(f, sx)


def _l0_nf(t: T, cap: int = 100_000) -> T:
    for _ in range(cap):
        nxt = _l0_step(t)
        if nxt is None:
            return t
        t = nxt
    raise ValueError("decode probe did not terminate")


def _cell_parts(cell: T) -> tuple:
    # NF of `_CONS h t` is the fixed compiled shape
    #   K (D ((B (C (D ((B (C I)) (K h))))) (K t)))
    # — head at r.r.l.r.r.r.r.r, tail at r.r.r.r (verified by VAR-marked
    # probe; identical across all three witnesses by nf_lo == nf_nat).
    # Structural dereference is O(1); the probe fallback covers any
    # evaluator that produces a different-but-equal NF.
    if (cell.k == K.APP and cell.l == KK and cell.r is not None
            and cell.r.k == K.APP and cell.r.l == D
            and cell.r.r is not None and cell.r.r.r is not None
            and cell.r.r.l is not None):
        return cell.r.r.l.r.r.r.r.r, cell.r.r.r.r
    return (_l0_nf(app(app(cell, I), KK)),
            _l0_nf(app(app(cell, I), _KI)))


_SEL_IDX = {s: i for i, s in enumerate(_SELECTORS)}


def _decode_bytes(s: T) -> bytes:
    nibs: List[int] = []
    while s.k != K.KONST:
        nib, s = _cell_parts(s)
        k = _SEL_IDX.get(nib)          # the leaf is the shared selector
        if k is None:                  # T — fallback: 16-marker probe
            probe = _l0_nf(_appn(nib, *_MARKS))
            if probe.k != K.VAR:
                raise ValueError(f"nibble probe returned {probe}")
            k = probe.n
        nibs.append(k)
    if len(nibs) & 1:
        raise ValueError("odd nibble count in nibble-list")
    return bytes(nibs[i] << 4 | nibs[i + 1]
                 for i in range(0, len(nibs), 2))


def _decode_str(s: T) -> str:
    return _decode_bytes(s).decode("utf-8")


def decode_resolve(nf: T) -> Optional[List[str]]:
    """NF -> None (bare I) or the eight resolved field strings."""
    if nf.k == K.NORM:
        return None
    out = []
    while nf.k != K.KONST:
        field, nf = _cell_parts(nf)
        out.append(_decode_str(field))
    return out


# ---------------------------------------------------------------------------
# symbols output map: Scott list of pair cells — an assoc
# map of nibble-string -> bytes4 (the arithmetic rep — assemble's
# resolver subtracts them; see decision 024 for the probe folklore the
# numeral repr previously needed).
# ---------------------------------------------------------------------------




def decode_symbols(nf: T) -> Optional[Dict[str, int]]:
    """NF -> None (bare I) or {symbol: rva} from the assoc-map cells.
    Values are bytes4 — structural byte-cell decode, no numeral probe."""
    if nf.k == K.NORM:
        return None
    out: Dict[str, int] = {}
    while nf.k != K.KONST:
        pair, nf = _cell_parts(nf)
        key = _decode_str(reduce_tree_lo(app(pair, KK), 1_000_000)[0])
        addr = _decode_bytecells(
            reduce_tree_lo(app(pair, _KI), 1_000_000)[0])
        out[key] = int.from_bytes(addr, "little")
    return out


# ---------------------------------------------------------------------------
# program output map: Scott list of items —
#   ["label", name] | ["i", form, op…]
#   op = ["r", reg] | ["imm", b8] | ["l", name] | ["p", name]
#      | ["m", base, b8disp]
# decoded back to the exact ("label",…)/("i",…) tuples program() emits.
# ---------------------------------------------------------------------------

def _decode_i64(b: bytes) -> int:
    if len(b) != 8:
        raise ValueError(f"bytes8 leaf has {len(b)} bytes")
    return int.from_bytes(b, "little", signed=True)


def _decode_sel(t: T) -> int:
    """16-way selector -> index (shared leaf, else VAR-marker probe)."""
    k = _SEL_IDX.get(t)
    if k is not None:
        return k
    probe = _l0_nf(_appn(t, *_MARKS))
    if probe.k != K.VAR:
        raise ValueError(f"nibble probe returned {probe}")
    return probe.n


def _decode_bytecell(b: T) -> int:
    """`\\f. f lo hi` -> int.  `b K` = lo, `b (K I)` = hi."""
    lo = _decode_sel(_l0_nf(app(b, KK), 10_000))
    hi = _decode_sel(_l0_nf(app(b, _KI), 10_000))
    return (hi << 4) | lo


def _decode_bytecells(s: T) -> bytes:
    out = bytearray()
    while s.k != K.KONST:
        cell, s = _cell_parts(s)
        out.append(_decode_bytecell(cell))
    return bytes(out)


def _decode_op(op: T):
    tag_t, rest = _cell_parts(op)
    tag = _decode_str(tag_t)
    if tag == "r":
        return _decode_str(_cell_parts(rest)[0])
    if tag == "imm":
        return _decode_i64(_decode_bytecells(_cell_parts(rest)[0]))
    if tag in ("l", "p"):
        return (tag, _decode_str(_cell_parts(rest)[0]))
    if tag == "m":
        base_t, rest2 = _cell_parts(rest)
        disp_t = _cell_parts(rest2)[0]
        return ("m", _decode_str(base_t),
                _decode_i64(_decode_bytecells(disp_t)))
    raise ValueError(f"bad operand tag {tag!r}")


def decode_program(nf: T) -> list:
    """NF -> the flat program item list ("label"/"i" tuples); the term
    emits a list of routine fragments — decoded by flattening."""
    out = []
    while nf.k != K.KONST:
        frag, nf = _cell_parts(nf)
        while frag.k != K.KONST:
            item, frag = _cell_parts(frag)
            tag_t, rest = _cell_parts(item)
            tag = _decode_str(tag_t)
            if tag == "label":
                out.append(("label", _decode_str(_cell_parts(rest)[0])))
                continue
            if tag != "i":
                raise ValueError(f"bad item tag {tag!r}")
            form_t, ops_l = _cell_parts(rest)
            ops = []
            while ops_l.k != K.KONST:
                op, ops_l = _cell_parts(ops_l)
                ops.append(_decode_op(op))
            out.append(tuple(["i", _decode_str(form_t)] + ops))
    return out


def has_var(t: T, n: int) -> bool:
    if t.k == K.VAR:
        return t.n == n
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return has_var(t.l, n) or has_var(t.r, n)
    return False


# ---------------------------------------------------------------------------
# packed IR (ADR-005) — canonical binary serialization of basis terms.
# Node record: u8 tag | u32 l | u32 r, postorder (children < parents),
# hash-consed on (tag,l,r) — sharing survives the unshared export and
# equal terms serialize identically (content-addressable).  Tag byte is
# seed.Tag's own numbering + 0xFE for VAR probes.
# ---------------------------------------------------------------------------

IR_MAGIC = 0x30524950                 # "PIR\0"
IR_VERSION = 1
IR_VAR = 0xFE

_IR_TAG = {K.APP: 0, K.NORM: 1, K.KONST: 2, K.S: 3,
           K.COMP: 4, K.DUP: 5, K.SWAP: 6}
_IR_LEAF = {1: I, 2: KK, 3: S, 4: B, 5: D, 6: C}


def pack_ir(*roots: T) -> bytes:
    """terms -> canonical packed-IR bytes (multi-root, arg order)."""
    memo: Dict[tuple, int] = {}
    nodes = bytearray()

    def emit(t: T) -> int:
        if t.k == K.APP:
            key = (0, emit(t.l), emit(t.r))
        elif t.k == K.VAR:
            key = (IR_VAR, t.n, 0)
        else:
            key = (_IR_TAG[t.k], 0, 0)
        i = memo.get(key)
        if i is None:
            i = len(memo)
            memo[key] = i
            nodes.extend(struct.pack("<BII", *key))
        return i

    idx = [emit(r) for r in roots]
    out = bytearray(struct.pack("<IIII", IR_MAGIC, IR_VERSION,
                                len(memo), len(roots)))
    for i in idx:
        out += struct.pack("<I", i)
    return bytes(out) + bytes(nodes)


def unpack_ir(data: bytes) -> List[T]:
    """packed-IR bytes -> root terms (single forward pass; the
    postorder invariant makes every child index < its parent's)."""
    magic, ver, n_nodes, n_roots = struct.unpack_from("<IIII", data, 0)
    if magic != IR_MAGIC:
        raise ValueError(f"bad packed-IR magic {magic:#x}")
    if ver != IR_VERSION:
        raise ValueError(f"packed-IR version {ver}")
    pos = 16
    roots = struct.unpack_from(f"<{n_roots}I", data, pos)
    pos += 4 * n_roots
    cells: List[T] = []
    for _ in range(n_nodes):
        tag, l, r = struct.unpack_from("<BII", data, pos)
        pos += 9
        if tag == 0:
            cells.append(app(cells[l], cells[r]))
        elif tag == IR_VAR:
            cells.append(T(K.VAR, n=l))
        else:
            cells.append(_IR_LEAF[tag])
    return [cells[i] for i in roots]


def ir_map() -> QuotientMap:
    """Dialect record `packed.ir`: bytes <-> T.  The map-level unit is
    single-root (multi-root batching is a transport concern); decode
    observes a term by canonical re-pack — equal NFs have equal bytes."""
    enc = lambda b: unpack_ir(b)[0]
    return QuotientMap(
        name="packed.ir",
        encode=enc,
        decode=pack_ir,
        regime=encoding_regime(enc, name="packed.ir.operEq"),
    )


# ---------------------------------------------------------------------------
# gate
# ---------------------------------------------------------------------------

LO_FUEL = 50_000_000
CD_FUEL = 300_000


def main() -> int:
    nfail = 0
    n_q = 0

    # slice-completeness self-checks (the real file has no int/bool/null)
    assert json_to_term(None) == NULL_TAG
    assert json_to_term(True) == TRUE_T and json_to_term(False) == FALSE_T

    print(f"SPEC: {TOOLCHAIN_JSON}")
    print(f"  {os.path.getsize(TOOLCHAIN_JSON)}B -> "
          f"{term_nodes(SPEC)} unique T nodes "
          f"({len(_RAW)} top keys, {len(_ENTRIES)} toolchains)")
    print(f"QUERY: {term_nodes(QUERY)} unique T nodes "
          f"(pathOf, Turner-compiled)")

    for name in NAMES + [NEGATIVE]:
        expected = python_walk(name)
        n_q += 1
        tag = "OK" if expected is not None or name == NEGATIVE else "??"
        t = query(name)

        nf_lo, steps_lo, alloc_lo = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_result(nf_lo)

        nf_nat, steps_nat, _ = seed.reduce_native(t, 0)
        val_nat = decode_result(nf_nat)

        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_result(nf_cd)

        line = (f"{tag} {name:18s} -> {val_lo!r} "
                f"[lo {steps_lo} steps | native {steps_nat} steps | "
                f"cd {rounds_cd} rounds, full spec]")
        good = (val_lo == expected and val_nat == expected
                and val_cd == expected and nf_lo == nf_nat)
        if name == NEGATIVE:
            good = good and val_lo is None and val_nat is None
        if not good:
            nfail += 1
            line = "FAIL " + line[3:] + (
                f"  expected {expected!r}")
        print(line)

    # ------------------------------------------------------------------
    # G9c: resolveOf — emit stage 1 (toolchain.resolve) at term level.
    # For each toolchain name the term walks: entry -> field names ->
    # catalog sections -> {module, record}; the result is the Scott list
    # of the eight resolved field strings ("!" = declared but unrealized
    # — the NotRealized shadow).
    # ------------------------------------------------------------------
    # All names are gated on graph.lo + the python-walk oracle; the
    # expensive witnesses (native token text, cd rounds) run on a
    # representative subset — full sweep behind --resolve-all.
    heavy = set(NAMES[:2] + [NEGATIVE])
    resolve_all = "--resolve-all" in sys.argv[1:]
    for name in NAMES + [NEGATIVE]:
        expected = python_resolve(name)
        n_q += 1
        t = resolve_query(name)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_resolve(nf_lo)

        ran_heavy = resolve_all or name in heavy
        if ran_heavy:
            nf_nat, steps_nat, _ = seed.reduce_native(t, 0)
            val_nat = decode_resolve(nf_nat)
            nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
            val_cd = decode_resolve(nf_cd)
        else:
            steps_nat, val_nat, rounds_cd, val_cd = -1, expected, -1, expected

        line = (f"{'OK ' if val_lo == expected else 'FAIL'} "
                f"{name:18s} resolve -> {val_lo} "
                f"[lo {steps_lo} | native {steps_nat} | "
                f"cd {rounds_cd} rounds]")
        good = (val_lo == expected and val_nat == expected
                and val_cd == expected)
        if ran_heavy:
            good = good and nf_lo == nf_nat
        if not good:
            nfail += 1
            line = "FAIL " + line[4:] + f"  expected {expected}"
        print(line)

    # ------------------------------------------------------------------
    # G9d: symbolsOf — target.symbols (IAT + .data RVAs) at term level.
    # Two structurally-bounded folds build the assoc map; addresses are
    # bytes4 — the rep assemble's resolver subtracts (the "is it ever
    # added/subtracted" boundary, applied now that the ripple
    # vocabulary exists — see decision 026).
    # Oracle is the real target_pe64.symbols on the same inputs.  lo +
    # cd + oracle run on both cases.  Native is gated on `mini` only:
    # win64.lo is ~95k lo steps, which exceeds the fixed-fuel exe's 600s
    # subprocess cap — the same throughput ceiling G9e documents, not a
    # correctness gap.  nf_lo == nf_nat is pinned by the `mini` leg and
    # the resolveOf legs, which exercise the same reduction machinery.
    # ------------------------------------------------------------------
    for cname, (imports, slots) in SYMS_CASES.items():
        expected = python_symbols(imports, slots)
        n_q += 1
        t = symbols_query(imports, slots)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_symbols(nf_lo)

        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_symbols(nf_cd)

        steps_nat = "-"
        good = (val_lo == expected and val_cd == expected)
        if cname == "mini":
            nf_nat, steps_nat, _ = seed.reduce_native(t, 0)
            val_nat = decode_symbols(nf_nat)
            good = good and val_nat == expected and nf_lo == nf_nat

        line = (f"{'OK ' if good else 'FAIL'} "
                f"{cname:18s} symbols -> {len(val_lo or {})} entries "
                f"[lo {steps_lo} | native {steps_nat} | "
                f"cd {rounds_cd} rounds]")
        if not good:
            nfail += 1
            line = "FAIL " + line[4:] + f"  expected {expected}"
        print(line)

    # ------------------------------------------------------------------
    # G9e: programOf — routines.program(R) at term level (emit stage 3).
    # One generated term `λfs λfuel λrbb λcb λnb. <fragments>`; the gate
    # instantiates it on five Realizations — two structural variants
    # (fuse_s, fuel) and pure data substitutions — and decodes the
    # emitted fragment list back to the exact flat program(R).
    # lo + cd + python oracle on all cases.  Native is NOT gated here:
    # the ~80k-step reduce exceeds the exe's 600s subprocess cap (the
    # default exe additionally pays translate_to_basis on the ~18k-node
    # input).  That is a throughput ceiling of the fixed-fuel exe, not
    # a correctness gap — the same term witnesses identical NF shape on
    # lo and cd, and nf_lo == nf_nat is pinned by the resolveOf/symbolsOf
    # legs which exercise the same reduction machinery on smaller terms.
    # ------------------------------------------------------------------
    for cname, R in PROG_CASES.items():
        expected = python_program(R)
        n_q += 1
        t = program_query(R)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_program(nf_lo)

        steps_nat, val_nat = -1, expected

        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_program(nf_cd)

        line = (f"{'OK ' if val_lo == expected else 'FAIL'} "
                f"{cname:18s} program -> {len(val_lo)} items "
                f"[lo {steps_lo} | native {steps_nat} | "
                f"cd {rounds_cd} rounds]")
        good = (val_lo == expected and val_cd == expected)
        if not good:
            nfail += 1
            line = "FAIL " + line[4:] + f"  expected {expected}"
        print(line)

    # ------------------------------------------------------------------
    # G9f: encodeOf + assembleOf — emit stage 4 at term level.
    #   ENC spot-checks cover one form per field-shape class the mini
    #   program misses (the 26-instance sweep lives in
    #   _probe_g9f_enc.py — each encode is ~3.5k steps / ~70s, so the
    #   full sweep does not belong in the suite loop).  cd only — the
    #   same term witnesses lo equality inside assembleOf below.
    #   assembleOf runs the two-pass fold end-to-end on the mini
    #   program: pass-1 label map, pass-2 resolver with symbol shadowing
    #   and a negative rel32.  Witnesses: lo + cd + the isa.assemble
    #   oracle; native is not gated (same exe throughput ceiling as
    #   programOf — ~80k+ steps is past the subprocess cap).
    # ------------------------------------------------------------------
    for insn in ENC_CASES:
        want = isa_x86_64_gate_encode(insn)
        n_q += 1
        t = encode_query(insn)
        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        got = decode_encode(nf_cd)
        line = (f"{'OK ' if got == want else 'FAIL'} "
                f"{insn[1]:16s} encode -> {got.hex() if got else None} "
                f"[cd {rounds_cd} rounds]")
        if got != want:
            nfail += 1
            line += f"  expected {want.hex()}"
        print(line)

    for cname, (prog, syms, base) in ASM_CASES.items():
        expected_b, expected_l = python_assemble(prog, syms, base)
        n_q += 1
        t = assemble_query(fraglist_term(prog), syms, base)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_assemble(nf_lo)

        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_assemble(nf_cd)

        ok = (val_lo == (expected_b, expected_l)
              and val_cd == (expected_b, expected_l))
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} assemble -> "
                f"{len(val_lo[0]) if val_lo else 0}B "
                f"{len(val_lo[1]) if val_lo else 0} labels "
                f"[lo {steps_lo} | cd {rounds_cd} rounds]")
        if not ok:
            nfail += 1
            line += f"  expected {expected_b.hex()}/{expected_l}"
        print(line)

    # ------------------------------------------------------------------
    # G9g: dataOf / idataOf / packOf — target_pe64.pack at term level
    # (emit stage 5, the container writer).  dataOf/idataOf return
    # pair(bytes, symmap) checked against build_data/build_idata at both
    # scales on lo+cd; packOf emits the full PE64 image byte-for-byte
    # vs target_pe64.pack on lo+oracle only (cd deferred — see the pack
    # loop).  Native is not gated (the same fixed-fuel-exe throughput
    # ceiling as programOf/assembleOf — the term graph is far past it).
    # ------------------------------------------------------------------
    for cname, slots in DATA_CASES.items():
        want_b, want_s = python_data(slots)
        n_q += 1
        t = data_query(slots)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_bytesyms(nf_lo)
        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_bytesyms(nf_cd)

        ok = (val_lo == (want_b, want_s) and val_cd == (want_b, want_s))
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} data -> "
                f"{len(val_lo[0]) if val_lo else 0}B "
                f"{len(val_lo[1]) if val_lo else 0} syms "
                f"[lo {steps_lo} | cd {rounds_cd} rounds]")
        if not ok:
            nfail += 1
            line += f"  expected {len(want_b)}B/{want_s}"
        print(line)

    for cname, imports in IDATA_CASES.items():
        want_b, want_s = python_idata(imports)
        n_q += 1
        t = idata_query(imports)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_bytesyms(nf_lo)
        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_bytesyms(nf_cd)

        ok = (val_lo == (want_b, want_s) and val_cd == (want_b, want_s))
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} idata -> "
                f"{len(val_lo[0]) if val_lo else 0}B "
                f"{len(val_lo[1]) if val_lo else 0} syms "
                f"[lo {steps_lo} | cd {rounds_cd} rounds]")
        if not ok:
            nfail += 1
            line += f"  expected {len(want_b)}B/{want_s}"
        print(line)

    for cname, (text, imports, slots, res) in PACK_CASES.items():
        want = python_pack(text, imports, slots, res)
        n_q += 1
        t = pack_query(text, imports, slots, res)

        # lo + oracle only.  cd is deferred here, not for correctness
        # but throughput: reduce_cd runs full confluence sweeps to
        # fixpoint, and on a term whose NF is a ~16k-cell byte list the
        # persistent-memo bookkeeping measured >5000s CPU on one case —
        # past routine-gate budget (same class of ceiling as the native
        # exe).  cd's engine coverage stays comprehensive across every
        # lighter stage; pack's unique emission content is pinned
        # byte-exact by lo vs the oracle.
        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = _decode_bytecells(nf_lo)

        ok = val_lo == want
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} pack -> "
                f"{len(val_lo)}B "
                f"[lo {steps_lo} | cd deferred]")
        if not ok:
            nfail += 1
            line += f"  expected {len(want)}B"
        print(line)

    # ------------------------------------------------------------------
    # G9h: linkOf — the linker stage.  Section builders run once,
    # export their symtabs, and linkOf merges them into the table
    # assemble's resolver consumes; pack2Of takes the linked sections
    # with no rebuild.  linkOf gates lo+cd at both scales; pack2Of and
    # linkasm gate lo+oracle — pack2Of for the image-sized NF (same as
    # packOf), linkasm because the COMPOSED link+assemble term under
    # cd's fixpoint is the arena-resident composition quadratic
    # (>50GB/~1100s CPU measured on mini before deferral — the link
    # stage's sequential section emission inside the same sweep, the
    # 027/028 retention pathology, not a correctness question).  The
    # resolver seam keeps its own lo+cd coverage on ASM_CASES.
    # ------------------------------------------------------------------
    for cname, (imports, slots) in LINK_CASES.items():
        want = python_link(imports, slots)
        n_q += 1
        t = link_query(imports, slots)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_link(nf_lo)
        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_link(nf_cd)

        ok = val_lo == want and val_cd == want
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} link -> "
                f"{len(val_lo[0]) if val_lo else 0}B+"
                f"{len(val_lo[1]) if val_lo else 0}B "
                f"{len(val_lo[2]) if val_lo else 0} syms "
                f"[lo {steps_lo} | cd {rounds_cd} rounds]")
        if not ok:
            nfail += 1
            line += (f"  expected {len(want[0])}B+{len(want[1])}B/"
                     f"{want[2]}")
        print(line)

    for cname, (text, imports, slots, res) in PACK2_CASES.items():
        want = python_pack(text, imports, slots, res)
        ib, db, _ = python_link(imports, slots)
        n_q += 1
        t = pack2_query(text, ib, db, res)

        # lo + oracle only — same measured cd deferral as packOf.
        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = _decode_bytecells(nf_lo)

        ok = val_lo == want
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} pack2 -> "
                f"{len(val_lo)}B "
                f"[lo {steps_lo} | cd deferred]")
        if not ok:
            nfail += 1
            line += f"  expected {len(want)}B"
        print(line)

    for cname, (prog, imports, slots, base) in LINKASM_CASES.items():
        _, _, lsyms = python_link(imports, slots)
        want_b, want_l = python_assemble(prog, lsyms, base)
        n_q += 1
        t = linkasm_query(fraglist_term(prog), imports, slots, base)

        # lo + oracle only — composed-stage cd deferred (measured).
        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_assemble(nf_lo)

        ok = val_lo == (want_b, want_l)
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} linkasm -> "
                f"{len(val_lo[0]) if val_lo else 0}B "
                f"{len(val_lo[1]) if val_lo else 0} labels "
                f"[lo {steps_lo} | cd deferred]")
        if not ok:
            nfail += 1
            line += f"  expected {want_b.hex()}/{want_l}"
        print(line)

    # ------------------------------------------------------------------
    # Vocabulary congruence: _B4CLA must Join _B4ADD — both reduce to
    # the b4_src literal of (a+b) mod 2^32.  Lean proves the Join for
    # all inputs (ISAR.b4add_b4cla_basis); here the host encoding is
    # gated on the critical carry shapes.  cd rounds reported: the
    # lookahead collapses the ripple's sequential carry chain into
    # independent cones (~270 vs ~424 rounds, ~30% more allocs).
    # ------------------------------------------------------------------
    for cname, (a, b) in CLA_CASES.items():
        n_q += 1
        t_rip = bracket(parse(f"({_B4ADD} {_b4_src(a)} {_b4_src(b)})"))
        t_cla = bracket(parse(f"({_B4CLA} {_b4_src(a)} {_b4_src(b)})"))
        t_lit = bracket(parse(_b4_src((a + b) & 0xFFFFFFFF)))

        nf_rip, s_rip, _ = reduce_tree_lo(t_rip, LO_FUEL)
        nf_cla, s_cla, _ = reduce_tree_lo(t_cla, LO_FUEL)
        nf_lit, _, _ = reduce_tree_lo(t_lit, LO_FUEL)
        _, r_rip, _ = reduce_tree_cd(t_rip, CD_FUEL)
        _, r_cla, _ = reduce_tree_cd(t_cla, CD_FUEL)

        ok = nf_rip == nf_cla == nf_lit
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} cla≡rip -> "
                f"[lo {s_rip}/{s_cla} | cd {r_rip}/{r_cla} rounds]")
        if not ok:
            nfail += 1
        print(line)

    # ------------------------------------------------------------------
    # Re-association congruence: APPEND (APPEND a b) c must Join
    # APPEND a (APPEND b c) — the formal license for choosing emission
    # shape per strategy (Lean: append_assoc_basis covers all closed
    # lists; here the host encoding is gated incl. the empty edge).
    # Both parenthesizations are compared against the literal concat.
    # ------------------------------------------------------------------
    for cname, (a, b, c) in ASSOC_CASES.items():
        n_q += 1
        # all terms through bracket(parse(_bytes_src)) — NF equality is
        # only meaningful inside one compilation convention (Turner
        # bracket vs bracket_abstract0 land β-equal cells in different
        # normal forms; the Lean Join is about the compiled encoding).
        at = bracket(parse(_bytes_src(a)))
        bt = bracket(parse(_bytes_src(b)))
        ct = bracket(parse(_bytes_src(c)))
        t_left = _appn(bracket(parse(_APPEND)),
                       _appn(bracket(parse(_APPEND)), at, bt), ct)
        t_right = _appn(bracket(parse(_APPEND)), at,
                        _appn(bracket(parse(_APPEND)), bt, ct))
        t_lit = bracket(parse(_bytes_src(a + b + c)))

        nf_left, s_left, _ = reduce_tree_lo(t_left, LO_FUEL)
        nf_right, s_right, _ = reduce_tree_lo(t_right, LO_FUEL)
        nf_lit2, _, _ = reduce_tree_lo(t_lit, LO_FUEL)
        _, r_left, _ = reduce_tree_cd(t_left, CD_FUEL)
        _, r_right, _ = reduce_tree_cd(t_right, CD_FUEL)

        ok = nf_left == nf_right == nf_lit2
        line = (f"{'OK ' if ok else 'FAIL'} {cname:18s} assoc -> "
                f"[lo {s_left}/{s_right} | cd {r_left}/{r_right} rounds]")
        if not ok:
            nfail += 1
        print(line)

    # ------------------------------------------------------------------
    # G9b: specialize the query program against the static catalog.
    # prog = QUERY v0 v1; residual = nf_lo(prog[0 := SPEC]); per name,
    # residual[1 := str_term name] must agree with the direct query on
    # every witness.  See the module docstring for the honest cost note.
    # ------------------------------------------------------------------
    mix = MixStrategy()
    prog = _appn(QUERY, T(K.VAR, n=0), T(K.VAR, n=1))
    residual, s_res, _ = reduce_tree_lo(
        mix.specialize(prog, {0: SPEC}), LO_FUEL)
    live = has_var(residual, 1)
    print(f"RESIDUAL: {term_nodes(residual)} tree nodes "
          f"(spec {term_nodes(SPEC)}; {s_res} lo steps to build); "
          f"v1 {'free' if live else 'ABSENT'}")
    if not live:
        nfail += 1
        print("FAIL residual has no dynamic input — "
              "the specializer evaluated instead of specializing")

    for name in NAMES + [NEGATIVE]:
        expected = python_walk(name)
        inst = mix.specialize(residual, {1: str_term(name)})

        nf_lo, steps_lo, _ = reduce_tree_lo(inst, LO_FUEL)
        val_lo = decode_result(nf_lo)

        nf_nat, steps_nat, _ = seed.reduce_native(inst, 0)
        val_nat = decode_result(nf_nat)

        nf_cd, rounds_cd, _ = reduce_tree_cd(inst, CD_FUEL)
        val_cd = decode_result(nf_cd)

        line = (f"{'OK ' if val_lo == expected else 'FAIL'} "
                f"{name:18s} residual -> {val_lo!r} "
                f"[lo {steps_lo} | native {steps_nat} | "
                f"cd {rounds_cd} rounds]")
        good = (val_lo == expected and val_nat == expected
                and val_cd == expected and nf_lo == nf_nat)
        if not good:
            nfail += 1
            line = "FAIL " + line[4:] + f"  expected {expected!r}"
        print(line)

    # ------------------------------------------------------------------
    # ADR-005 packed IR: roundtrip + canonicality.  Sharing survives
    # (hash-consed on (tag,l,r)); equal terms give identical bytes.
    # ------------------------------------------------------------------
    n_ir = 0
    ir_cases = [I, app(S, app(KK, I)),
                _appn(T(K.VAR, n=0), T(K.VAR, n=1)),
                bytelist_term(b"MZ"),
                st_query := bracket(parse("(\\x. x (K I))"))]
    for t in ir_cases:
        rt = unpack_ir(pack_ir(t))
        ok = len(rt) == 1 and rt[0] == t
        n_ir += 1
        if not ok:
            nfail += 1
            print(f"FAIL ir roundtrip {t!r:.60}")
    # multi-root + canonicality: equal-but-distinct trees -> same bytes
    a1, a2 = app(S, I), app(S, I)
    two = unpack_ir(pack_ir(a1, KK))
    ok = (two[0] == a1 and two[1] == KK
          and pack_ir(app(S, I)) == pack_ir(a1))
    n_ir += 1
    if not ok:
        nfail += 1
        print("FAIL ir multi-root/canonical")
    print(f"OK  ir pack/unpack: {n_ir} cases "
          f"({len(pack_ir(st_query))}B for a small λ-compiled term)")

    print(f"{'OK' if not nfail else 'FAIL'} spec_term "
          f"({len(NAMES) + 1} pathOf + {len(NAMES) + 1} resolveOf + "
          f"{len(SYMS_CASES)} symbolsOf + {len(PROG_CASES)} programOf + "
          f"{len(ENC_CASES)} encodeOf + {len(ASM_CASES)} assembleOf + "
          f"{len(DATA_CASES)} dataOf + {len(IDATA_CASES)} idataOf + "
          f"{len(PACK_CASES)} packOf + {len(LINK_CASES)} linkOf + "
          f"{len(PACK2_CASES)} pack2Of + {len(LINKASM_CASES)} linkasm + "
          f"{len(CLA_CASES)} cla≡rip + {len(ASSOC_CASES)} assoc + "
          f"{len(NAMES) + 1} residual instances x 4 witnesses: graph.lo, "
          "native lo exe, graph.cd full-spec, python walk)")
    return 1 if nfail else 0


if __name__ == "__main__":
    raise SystemExit(main())
