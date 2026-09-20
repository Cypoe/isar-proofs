"""
Futamura cube — direct vs synthesized, across strategies and witnesses.

Lean `Futamura.lean` proves the square for a `PESetup`:
  P0 direct      eval int (pair src d)
  P1 target      eval (spec int src) d                 -- mix
  P2 compiler    eval (spec specTerm int) src           -- futamura_second
  P3 cogen       eval (spec specTerm specTerm) int      -- futamura_third
and `futamura_first` at the subst layer:
  subst (specialize t static) dynamic = subst t (static ∪ dynamic).

What this host harness CHECKS (rows marked CHECK):
  Pathway axis, P0 vs P1, with `eval` = β-normal form on a real host piece:
    P0  nf_piece( p[static ∪ dynamic] )
    P1  residual := nf_tree( specialize(p, static) )   -- static redexes fire,
                                                       -- dynamic vars stay free
        nf_piece( residual[dynamic] )
  This is not the syntactic identity of `futamura_first` (that would be
  vacuous): P1 reduces the residual BEFORE dynamic data exists, so agreement
  rests on confluence + `subst_env_preserves_red`, and it is observed on the
  emitted machine code, not on the Lean term model.
  Strategy axis: S expanded (IStepBasis, default) vs fuse_s.
  Witness axis:  tree mirror (host/reduce.py, IStep surface: I/K/B/S — so
                 probes are bracketed abstract0-style, I/K/S only; the
                 native pieces' swap/dup β are covered by seed G2/G3)
                 | graph.lo | native default PE | native fuse_s PE.  Every cell also agrees with an
                 independently constructed expected NF (B^k I), so the check
                 is not merely "the witnesses agree with each other".
  Cross-witness comparison uses only probes whose NF is S-free: a partial
  application of S is one NF in the fused class and a different (further
  reducible) term in the basis class — same OperEq class, different spelling.

What it does NOT check (rows marked DECLARED), stated so nobody reads it in:
  P2/P3 need an object-level `specTerm` whose β-behaviour on `pair p s` IS
  the specializer.  Lean's `TrivialPE`/`OptimizingPE`/`JGS_PE` prove the
  square for toy `eval`s (custom `run` functions), not for β-NF; `specTerm`
  is the atom `swap` overloaded by that toy eval.  On this host the
  specializer is meta-level Python (`strategy.MixStrategy` = Lean
  `specialize`), and the seed's cogen chain `emit(R)` is a HAND-WRITTEN
  generating extension: it is what P2 would *produce* (reducer specialized to
  a Realization), not the product of self-application.  Closing P2/P3 on β
  is the open 1993-mix item in Futamura.lean and the G7 self-description
  gate in HANDOFF — not claimed here.
"""
from __future__ import annotations

import os
import sys
from typing import Callable, Dict, List, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, K, I, KK, B, S, app, reduce as tree_reduce  # noqa: E402
from strategy import MixStrategy  # noqa: E402
from host_pieces import GRAPH_PIECE, GRAPH_CD_PIECE, HostPiece  # noqa: E402
from lambda_dialect import bracket_abstract0 as bracket  # noqa: E402  (I/K/S only: host/reduce.py has no swap/dup β)
from lambda_bench import church, MULT, PLUS, EXP  # noqa: E402
from lambda_eval import LSTEP_PIECE, t_to_nexpr  # noqa: E402
import lean_eval  # noqa: E402

FUEL = 2_000_000


def v(n: int) -> T:
    return T(K.VAR, n=n)


def appn(*xs: T) -> T:
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t


def subst(t: T, env: Dict[int, T]) -> T:
    """Lean `subst_env` restricted to the vars in env (others stay free)."""
    return MixStrategy().specialize(t, env)


def b_pow_i(k: int) -> T:
    """Expected NF of `c_k B I` = B (B (... I)) with k B's — S-free, k-distinct."""
    t = I
    for _ in range(k):
        t = app(B, t)
    return t


def has_free_var(t: T) -> bool:
    if t.k == K.VAR:
        return True
    if t.k == K.APP:
        return has_free_var(t.l) or has_free_var(t.r)  # type: ignore[arg-type]
    return False


# ---------------------------------------------------------------------------
# probes: (label, program with holes, static env, dynamic env, expected NF)
# ---------------------------------------------------------------------------

def _c(n: int) -> T:
    return bracket(church(n))


MULT_T, PLUS_T, EXP_T = bracket(MULT), bracket(PLUS), bracket(EXP)

PROBES: Tuple[Tuple[str, T, Dict[int, T], Dict[int, T], T], ...] = (
    ("K v0 v1        [v0:=I | v1:=K]",
     appn(KK, v(0), v(1)), {0: I}, {1: KK}, I),
    ("S v0 v1 v2     [v0:=K v1:=I | v2:=B]",
     appn(S, v(0), v(1), v(2)), {0: KK, 1: I}, {2: B}, B),
    ("MULT v0 v1 B I [v0:=c3 | v1:=c4]",
     appn(MULT_T, v(0), v(1), B, I), {0: _c(3)}, {1: _c(4)}, b_pow_i(12)),
    ("MULT v1 v0 B I [v0:=c3 | v1:=c4]  (static in 2nd position)",
     appn(MULT_T, v(1), v(0), B, I), {0: _c(3)}, {1: _c(4)}, b_pow_i(12)),
    ("PLUS v0 v1 B I [v0:=c5 | v1:=c7]",
     appn(PLUS_T, v(0), v(1), B, I), {0: _c(5)}, {1: _c(7)}, b_pow_i(12)),
    ("EXP v0 v1 B I  [v0:=c2 | v1:=c3]  (2^3)",
     appn(EXP_T, v(0), v(1), B, I), {0: _c(2)}, {1: _c(3)}, b_pow_i(8)),
    ("EXP v0 v1 B I  [v0:=c3 | v1:=c2]  (3^2)",
     appn(EXP_T, v(0), v(1), B, I), {0: _c(3)}, {1: _c(2)}, b_pow_i(9)),
)


# ---------------------------------------------------------------------------
# witnesses
# ---------------------------------------------------------------------------

def _tree_piece() -> HostPiece:
    def _r(t: T, fuel: int = FUEL) -> Tuple[T, int, int]:
        nf, n = tree_reduce(t, fuel=fuel)
        return nf, n, 0
    return HostPiece(name="tree.surface", kind="tree", reduce=_r)


def witnesses() -> List[Tuple[str, str, HostPiece]]:
    """(label, strategy class, piece). Native pieces only if the seed imports."""
    out: List[Tuple[str, str, HostPiece]] = [
        ("tree.surface", "fused", _tree_piece()),
        ("graph.lo", "basis", GRAPH_PIECE),
        ("graph.cd", "basis", GRAPH_CD_PIECE),
        ("lambda.lstep", "lstep", LSTEP_PIECE),
    ]
    seed_dir = os.path.join(os.path.dirname(_HOST), "seed")
    if seed_dir not in sys.path:
        sys.path.insert(0, seed_dir)
    try:
        import seed  # noqa: E402
        out.append(("native.default", "basis", seed.piece()))
        out.append(("native.fuse_s", "fused",
                    seed.piece(seed.Realization(fuse_s=True))))
    except ImportError as e:  # pragma: no cover
        print(f"SKIP native witnesses ({e})")
    return out


def run(piece: HostPiece, t: T) -> T:
    nf, _, _ = piece.reduce(t, FUEL)
    return nf


def check_cell(piece: HostPiece, prog: T, static: Dict[int, T],
               dynamic: Dict[int, T], expected: T) -> Tuple[bool, str]:
    full = dict(static)
    full.update(dynamic)
    p0 = run(piece, subst(prog, full))
    residual, _ = tree_reduce(subst(prog, static), fuel=FUEL)
    staged = "residual_size=%d" % _size(residual) if has_free_var(residual)         else "dynamic var eliminated at spec time (dead under K)"
    p1 = run(piece, subst(residual, dynamic))
    if str(p0) != str(p1):
        return False, f"P0 {p0} != P1 {p1}"
    if str(p0) != str(expected):
        return False, f"nf {p0} != expected {expected}"
    return True, staged


def _size(t: T) -> int:
    return 1 if t.k != K.APP else 1 + _size(t.l) + _size(t.r)  # type: ignore[arg-type]


def main() -> int:
    ok = True
    ws = witnesses()
    print(f"witnesses: {[w[0] + '/' + w[1] for w in ws]}")
    print("CHECK P0 (direct) vs P1 (specialize -> reduce residual -> supply dynamic)")
    for label, prog, static, dynamic, expected in PROBES:
        for wname, cls, piece in ws:
            good, note = check_cell(piece, prog, static, dynamic, expected)
            ok = ok and good
            print(f"  {'OK ' if good else 'FAIL'} {wname:15s} {cls:6s} {label}  {note}")
    # cogen-level first projection: the emitted PE is `emit(R)` = reducer
    # specialized to R; its agreement with graph.lo on the same inputs is
    # the P1 check at the toolchain level (already gated by seed G3/G5).
    print("CHECK cogen-level P1: native.default ~O graph.lo, native.fuse_s ~O tree.surface "
          "on all probes (covered by the cells above)")
    # lean.eval spot oracle: the P0 (fully-supplied) probe terms batched
    # through ONE `lake env lean` call; NF compared against the probe's
    # expected value routed through the same lambda-expansion path.
    if "--with-lean" in sys.argv[1:]:
        if not lean_eval.available():
            print("SKIP lean.eval (lake not found)")
        else:
            batch = []
            pairs = []
            for i, (label, prog, static, dynamic, expected) in \
                    enumerate(PROBES):
                full = dict(static)
                full.update(dynamic)
                batch.append((f"p{i}", t_to_nexpr(subst(prog, full))))
                batch.append((f"p{i} [expected]", t_to_nexpr(expected)))
                pairs.append((f"p{i}", expected))
            got = lean_eval.run_batch(batch)
            for key, expected in pairs:
                good = got[key] == got[key + " [expected]"]
                ok = ok and good
                print(f"  {'OK ' if good else 'FAIL'} lean.eval      oracle "
                      f"{key}: {got[key]} ~ {got[key + ' [expected]']}")
    else:
        print("SKIP lean.eval (--with-lean not passed)")
    print("DECLARED P2 (compiler = spec specTerm int): no beta-level specTerm; seed emit() is a "
          "hand-written generating extension")
    print("DECLARED P3 (cogen = spec specTerm specTerm): open — Futamura.lean 1993-mix item; "
          "HANDOFF G7")
    print(f"{'OK' if ok else 'FAIL'} futamura_cube")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
