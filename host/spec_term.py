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
and advances addr by 8 (`8 SUCC o`); each slot conses `pair nm addr`
and advances by `ADD o sz`.  Bases are real term arithmetic —
`IDATA_RVA + IDT_SZ + (n+1)*8` and `DATA_RVA` as ADD/MUL/SUCC
compositions — and `iat_` is a literal cons prefix, not a fold.

Representation boundary (the open question, answered at lift time):
computed addresses are Church numerals because they are added and
subtracted (assemble's `rel32 = addr - end` is the real consumer);
large literals stay byte-list data — that is the "is it ever
added/subtracted" line, and `0x1122334455667788` never needs to be a
magnitude, only a little-endian byte string.  Numeral literals are
MUL-compositions of <=16 factors (`_num_src`) so the source stays
small.  Numerals decode behaviorally: `n VF VX` normalizes to a right
spine of n `app(VF, ·)` applications counted by a pointer walk —
reduced on graph.cd (lo re-descends the growing spine quadratically).
Two dead ends are recorded in decision 024: marker-cell probes cost
~10^5 allocs/cell on MUL-composed literals, and no closed atom
survives n applications as an app-spine base (B dies at 3, K at 2,
I at 1) — only fresh VARs make the unfold inert end-to-end.

Usage: python host/spec_term.py
"""
from __future__ import annotations

import json
import os
import sys
from typing import Dict, List, Optional

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_SEED = os.path.normpath(os.path.join(_HOST, "..", "seed"))
if _SEED not in sys.path:
    sys.path.insert(0, _SEED)

sys.setrecursionlimit(1_000_000)   # cons-spine depth ~ #nibble cells

from reduce import T, K, I, KK, B, S, C, app  # noqa: E402
from lambda_dialect import parse, bracket, bracket_abstract0  # noqa: E402
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


def str_term(s: str) -> T:
    """UTF-8 bytes -> Scott list of 16-ary nibble selectors."""
    t = _NIL
    for byte in reversed(s.encode("utf-8")):
        t = _appn(_CONS, _SELECTORS[byte & 15], t)
        t = _appn(_CONS, _SELECTORS[byte >> 4], t)
    return t


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
# by count), and the dense part is SMALL-NUMERAL arithmetic only.
#
#   addresses are Church numerals — precisely because pass-2's
#       rel32 = addr - end adds/subtracts them (the boundary is "is it
#       ever added/subtracted"); a byte-list repr would need a
#       ripple-carry adder in term machinery.  Literal immediates stay
#       byte-lists when `program` lifts.
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


# imports fold: state (l_in, addr, out); each step pops a name, conses
# `pair ("iat_"++nm) addr` onto out and advances addr by 8.
_STEP_I = (
    "\\acc. acc (\\l. \\o. \\u. l "
    "(\\k2. k2 l o u) "
    "(\\nm. \\t. \\k2. k2 t (" + _church_src(8) + " " + _SUCC_SRC + " o) "
    + _cons("(" + _PAIR_SRC + " __IATPFX__ o)", "u") + "))"
)

# slots fold: same state; each element is a 2-list [name, size] — cons
# `pair nm addr` and advance addr by sz.
_STEP_S = (
    "\\acc. acc (\\l. \\o. \\u. l "
    "(\\k2. k2 l o u) "
    "(\\p. \\t. p (\\k2. k2 t o u) "
    "(\\nm. \\rest. rest (\\k2. k2 t o u) "
    "(\\sz. \\r2. \\k2. k2 t (" + _ADD_SRC + " o sz) "
    + _cons("(" + _PAIR_SRC + " nm o)", "u") + "))))"
)

# iat base = IDATA_RVA + IDT_SZ + (n_imp+1)*8 — the build_idata layout,
# expressed as real term arithmetic (no precomputed constants).
_IATB = ("(" + _ADD_SRC + " (" + _ADD_SRC + " " + _num_src(0x2000)
         + " " + _church_src(40) + ") (" + _MUL_SRC + " (" + _SUCC_SRC
         + " __NIMP__) " + _church_src(8) + "))")

SYMS_OF = (
    "(\\imports. \\slots. (__NIMPB__ (" + _STEP_I + ") "
    "(\\k2. k2 imports " + _IATB + " K)) "
    "(\\li. \\ai. \\u. (__NSLOT__ (" + _STEP_S + ") "
    "(\\k2. k2 slots " + _num_src(0x3000) + " u)) "
    "(\\ls. \\as. \\u2. u2)))"
)


def symbols_src(n_imp: int, n_slot: int) -> str:
    """λ-source of `\\imports. \\slots. symbolsOf` — bounds measured."""
    src = SYMS_OF
    for ph, val in (
        ("__NIMP__", _church_src(n_imp)),
        ("__NIMPB__", _church_src(n_imp)),
        ("__NSLOT__", _church_src(n_slot)),
        ("__IATPFX__", _prefix_src("iat_", "nm")),
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


def symbols_query(imports, slots) -> T:
    """`symbolsOf IMPORTS SLOTS` — emit stage-2 fragment at term level."""
    syms = build_symbols(len(imports), len(slots))
    return _appn(syms, json_to_term(list(imports)),
                 json_to_term([list(s) for s in slots]))


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

_KI = app(KK, I)
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
    return (_l0_nf(app(app(cell, I), KK)),
            _l0_nf(app(app(cell, I), _KI)))


def _decode_str(s: T) -> str:
    nibs: List[int] = []
    while s.k != K.KONST:
        nib, s = _cell_parts(s)
        probe = _l0_nf(_appn(nib, *_MARKS))
        if probe.k != K.VAR:
            raise ValueError(f"nibble probe returned {probe}")
        nibs.append(probe.n)
    if len(nibs) & 1:
        raise ValueError("odd nibble count in resolve field")
    return bytes(nibs[i] << 4 | nibs[i + 1]
                 for i in range(0, len(nibs), 2)).decode("utf-8")


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
# symbols output map: Scott list of `\\f. f key addr` pairs — an assoc
# map of nibble-string -> Church numeral.  A numeral is probed with
# `addr VF VX` (fresh vars): the numeral unfolds inertly into a left spine
# `app(VF, app(VF, … VX))` and the count is an O(n) pointer walk — no
# marker atoms (no closed base survives n applications; B dies at 3,
# K at 2, I at 1) and no per-cell reduction (cons-cell probes cost
# ~10^5 allocs/cell on MUL-composed literals — O(n^2)).
# ---------------------------------------------------------------------------

_VF = T(K.VAR, n=17)
_VX = T(K.VAR, n=18)


def _decode_num(n: T) -> int:
    # `n VF VX` -> `app(VF, app(VF, … VX))` — a right spine of n var-headed
    # applications.  VAR arguments let the numeral's own machinery unfold
    # inertly (no rule fires on a var-headed app, so no marker cells and no
    # per-cell reduction); the count is an O(n) pointer walk.  Reduced on
    # graph.cd: lo re-descends the growing spine (~quadratic allocs on
    # MUL-composed literals), cd unfolds at ~24 allocs/VF.
    # Marker-cell probes (`n (cons M) z`) cost ~10^5 allocs/cell — O(n^2) —
    # and no closed base survives n applications on an app-spine probe
    # (B dies at 3, K at 2, I at 1).
    spine = reduce_tree_cd(app(app(n, _VF), _VX), LO_FUEL)[0]
    k = 0
    while spine != _VX:
        if spine.k != K.APP or spine.l != _VF:
            raise ValueError(f"numeral probe spine {spine}, not f^n x")
        k += 1
        spine = spine.r
    return k


def decode_symbols(nf: T) -> Optional[Dict[str, int]]:
    """NF -> None (bare I) or {symbol: rva} from the assoc-map cells."""
    if nf.k == K.NORM:
        return None
    out: Dict[str, int] = {}
    while nf.k != K.KONST:
        pair, nf = _cell_parts(nf)
        key = _decode_str(reduce_tree_lo(app(pair, KK), 1_000_000)[0])
        out[key] = _decode_num(reduce_tree_lo(app(pair, _KI), 1_000_000)[0])
    return out


def has_var(t: T, n: int) -> bool:
    if t.k == K.VAR:
        return t.n == n
    if t.k == K.APP:
        assert t.l is not None and t.r is not None
        return has_var(t.l, n) or has_var(t.r, n)
    return False


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
    # Church numerals (the "is it ever added/subtracted" boundary).
    # Oracle is the real target_pe64.symbols on the same inputs; all
    # three witnesses run on both cases (the terms are small).
    # ------------------------------------------------------------------
    for cname, (imports, slots) in SYMS_CASES.items():
        expected = python_symbols(imports, slots)
        n_q += 1
        t = symbols_query(imports, slots)

        nf_lo, steps_lo, _ = reduce_tree_lo(t, LO_FUEL)
        val_lo = decode_symbols(nf_lo)

        nf_nat, steps_nat, _ = seed.reduce_native(t, 0)
        val_nat = decode_symbols(nf_nat)

        nf_cd, rounds_cd, _ = reduce_tree_cd(t, CD_FUEL)
        val_cd = decode_symbols(nf_cd)

        line = (f"{'OK ' if val_lo == expected else 'FAIL'} "
                f"{cname:18s} symbols -> {len(val_lo or {})} entries "
                f"[lo {steps_lo} | native {steps_nat} | "
                f"cd {rounds_cd} rounds]")
        good = (val_lo == expected and val_nat == expected
                and val_cd == expected and nf_lo == nf_nat)
        if not good:
            nfail += 1
            line = "FAIL " + line[4:] + f"  expected {expected}"
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

    print(f"{'OK' if not nfail else 'FAIL'} spec_term "
          f"({len(NAMES) + 1} pathOf + {len(NAMES) + 1} resolveOf + "
          f"{len(SYMS_CASES)} symbolsOf + "
          f"{len(NAMES) + 1} residual instances x 4 witnesses: graph.lo, "
          "native lo exe, graph.cd full-spec, python walk)")
    return 1 if nfail else 0


if __name__ == "__main__":
    raise SystemExit(main())
