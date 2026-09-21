"""
Phase 2.5 proper-toy: principled basis graph (pure tower, rewrite dispatch).

L0 atoms: norm, comp, dup, swap  (+ app edges, var)
L1: S expands to derived_s; K is a macro tag with fused β (sig IRAS in tower.py)
L2: QuotientMap dialects (encode/decode) — observe via this Graph

Share + forward kürzen. App/mul backend (GPU, …) = Phase 4 dispatch.
"""
from __future__ import annotations

import os
import sys
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import K, T, I, KK, B, S, D, C, app as tree_app  # noqa: E402
from tower import translate_to_basis, quote_surface  # noqa: E402


class Graph:
    __slots__ = (
        "kind", "varn", "left", "right", "fwd",
        "_atom", "_var_intern", "_app_intern",
        "_step_memo", "_cd_memo", "_nf",
        "_macro_k",
    )

    def __init__(self) -> None:
        self.kind: List[K] = []
        self.varn: List[int] = []
        self.left: List[int] = []
        self.right: List[int] = []
        self.fwd: List[int] = []
        self._atom: Dict[K, int] = {}
        self._var_intern: Dict[int, int] = {}
        self._app_intern: Dict[Tuple[int, int], int] = {}
        self._step_memo: Dict[int, Optional[int]] = {}
        self._cd_memo: Dict[int, int] = {}
        self._nf: Dict[int, bool] = {}
        # L0 only
        for kind in (K.NORM, K.COMP, K.DUP, K.SWAP):
            self._atom[kind] = self._alloc(kind)
        # L1 macro K (fused β) — not an L0 substrate op
        self._macro_k = self._alloc(K.KONST)
        self._nf[self._macro_k] = True

    def _alloc(self, kind: K, n: int = 0, left: int = -1, right: int = -1) -> int:
        i = len(self.kind)
        self.kind.append(kind)
        self.varn.append(n)
        self.left.append(left)
        self.right.append(right)
        self.fwd.append(-1)
        return i

    def repr(self, i: int) -> int:
        if self.fwd[i] < 0:
            return i
        seen: List[int] = []
        while self.fwd[i] >= 0:
            seen.append(i)
            i = self.fwd[i]
        for s in seen:
            self.fwd[s] = i
        return i

    def redirect(self, src: int, dst: int) -> int:
        src = self.repr(src)
        dst = self.repr(dst)
        if src == dst:
            return src
        self.fwd[src] = dst
        self._step_memo[src] = dst
        self._cd_memo[src] = dst
        self._nf.pop(src, None)
        return dst

    def atom(self, kind: K) -> int:
        if kind == K.S:
            raise ValueError("S is L1 expand — use translate_to_basis / import_tree")
        if kind == K.KONST:
            return self._macro_k
        return self._atom[kind]

    def var(self, n: int) -> int:
        got = self._var_intern.get(n)
        if got is not None:
            return got
        i = self._alloc(K.VAR, n=n)
        self._var_intern[n] = i
        self._nf[i] = True
        return i

    def mk_app(self, left: int, right: int) -> int:
        left, right = self.repr(left), self.repr(right)
        key = (left, right)
        got = self._app_intern.get(key)
        if got is not None:
            return self.repr(got)
        i = self._alloc(K.APP, left=left, right=right)
        self._app_intern[key] = i
        return i

    def alloc_count(self) -> int:
        return len(self.kind)

    @property
    def unique_count(self) -> int:
        return sum(1 for f in self.fwd if f < 0)

    def import_tree(self, t: T, *, expand_s: bool = True) -> int:
        if expand_s:
            t = translate_to_basis(t)
        return self._import(t)

    def _import(self, t: T) -> int:
        if t.k == K.S:
            raise ValueError("unexpected S after translate_to_basis")
        if t.k == K.APP:
            assert t.l is not None and t.r is not None
            return self.mk_app(self._import(t.l), self._import(t.r))
        if t.k == K.VAR:
            return self.var(t.n)
        if t.k == K.KONST:
            return self._macro_k
        return self.atom(t.k)

    def export_tree(self, i: int, *, quote: bool = True) -> T:
        t = self._export_raw(i)
        return quote_surface(t) if quote else t

    def _export_raw(self, i: int) -> T:
        i = self.repr(i)
        k = self.kind[i]
        if k == K.APP:
            return tree_app(self._export_raw(self.left[i]), self._export_raw(self.right[i]))
        if k == K.VAR:
            return T(K.VAR, n=self.varn[i])
        return {
            K.NORM: I, K.KONST: KK, K.DUP: D, K.SWAP: C, K.COMP: B,
        }[k]

    def show(self, i: int) -> str:
        return str(self.export_tree(i))

    def _fun_arg(self, i: int) -> Tuple[int, int]:
        i = self.repr(i)
        assert self.kind[i] == K.APP
        return self.repr(self.left[i]), self.repr(self.right[i])

    def step(self, i: int) -> Optional[int]:
        """LO step: L0 β (I/B/D/C) + L1 macro Kβ."""
        i = self.repr(i)
        if i in self._step_memo:
            return self._step_memo[i]
        if self._nf.get(i):
            self._step_memo[i] = None
            return None
        if self.kind[i] != K.APP:
            self._nf[i] = True
            self._step_memo[i] = None
            return None

        f, x = self._fun_arg(i)
        fk = self.kind[f]

        if fk == K.NORM:
            out = self.redirect(i, x)
            self._step_memo[i] = out
            return out

        if fk == K.APP:
            fl, fr = self._fun_arg(f)
            flk = self.kind[fl]
            # L1 macro K: K x y → x
            if flk == K.KONST:
                out = self.redirect(i, fr)
                self._step_memo[i] = out
                return out
            if flk == K.DUP:
                out = self.redirect(i, self.mk_app(self.mk_app(fr, x), x))
                self._step_memo[i] = out
                return out
            if flk == K.APP:
                fll, flr = self._fun_arg(fl)
                fllk = self.kind[fll]
                if fllk == K.COMP:
                    out = self.redirect(i, self.mk_app(flr, self.mk_app(fr, x)))
                    self._step_memo[i] = out
                    return out
                if fllk == K.SWAP:
                    out = self.redirect(i, self.mk_app(self.mk_app(flr, x), fr))
                    self._step_memo[i] = out
                    return out

        sf = self.step(f)
        if sf is not None:
            out = self.redirect(i, self.mk_app(sf, x))
            self._step_memo[i] = out
            return out
        sx = self.step(x)
        if sx is not None:
            out = self.redirect(i, self.mk_app(f, sx))
            self._step_memo[i] = out
            return out

        self._nf[i] = True
        self._step_memo[i] = None
        return None

    def step_lo(self, i: int) -> Optional[int]:
        return self.step(i)

    def step_basis(self, i: int) -> Optional[int]:
        return self.step(i)

    def reduce(self, i: int, fuel: int = 100_000) -> Tuple[int, int]:
        cur, steps = self.repr(i), 0
        while steps < fuel:
            nxt = self.step(cur)
            if nxt is None:
                break
            cur = self.repr(nxt)
            steps += 1
        return cur, steps

    def reduce_lo(self, i: int, fuel: int = 100_000) -> Tuple[int, int]:
        return self.reduce(i, fuel=fuel)

    def reduce_pipeline(self, i: int, fuel: int = 100_000) -> Tuple[int, int, int]:
        nf, n = self.reduce(i, fuel=fuel)
        return nf, n, 0

    def _is_redex_r(self, i: int) -> bool:
        """resolved-head redex test (HeapDev.isRedexNodeR) on a rep app-node."""
        f = self.repr(self.left[i])
        fk = self.kind[f]
        if fk == K.NORM:
            return True
        if fk != K.APP:
            return False
        fl = self.repr(self.left[f])
        flk = self.kind[fl]
        if flk == K.KONST or flk == K.DUP:
            return True
        if flk != K.APP:
            return False
        return self.kind[self.repr(self.left[fl])] in (K.COMP, K.SWAP)

    def _cd_app(self, i: int, f: int, x: int) -> int:
        cf, cx = self.cd(f), self.cd(x)
        out = self.redirect(i, self.mk_app(cf, cx))
        if self._nf.get(cf) and self._nf.get(cx) and not self._is_redex_r(out):
            # hereditary NF: proven-normal children + non-redex root.
            # (cf == f alone is NOT proof — a memo seal can return an
            #  unchanged node whose readback still has residuals.)
            self._nf[out] = True
        return out

    def cd(self, i: int) -> int:
        i = self.repr(i)
        hit = self._cd_memo.get(i)
        if hit is not None:
            return self.repr(hit)
        if self._nf.get(i) or self.kind[i] != K.APP:
            self._nf[i] = True
            self._cd_memo[i] = i
            return i

        f, x = self._fun_arg(i)
        fk = self.kind[f]

        if fk == K.NORM:
            out = self.redirect(i, self.cd(x))
        elif fk == K.APP:
            fl, fr = self._fun_arg(f)
            flk = self.kind[fl]
            if flk == K.KONST:
                out = self.redirect(i, self.cd(fr))
            elif flk == K.DUP:
                zx = self.cd(x)
                out = self.redirect(i, self.mk_app(self.mk_app(self.cd(fr), zx), zx))
            elif flk == K.APP:
                fll, flr = self._fun_arg(fl)
                fllk = self.kind[fll]
                if fllk == K.COMP:
                    out = self.redirect(
                        i, self.mk_app(self.cd(flr), self.mk_app(self.cd(fr), self.cd(x)))
                    )
                elif fllk == K.SWAP:
                    out = self.redirect(
                        i, self.mk_app(self.mk_app(self.cd(flr), self.cd(x)), self.cd(fr))
                    )
                else:
                    out = self._cd_app(i, f, x)
            else:
                out = self._cd_app(i, f, x)
        else:
            out = self._cd_app(i, f, x)

        self._cd_memo[i] = out
        # seal the result (HDev's `insert o D`): residual redexes in `out`
        # are contractum-born — re-entering them this round would compute
        # cd(cd t), over-developing past a single cdBasis pass.
        self._cd_memo[out] = out
        return out

    def par_step(self, i: int) -> int:
        return self.cd(i)

    def reduce_cd(self, i: int, fuel: int = 1000) -> Tuple[int, int]:
        cur, rounds = self.repr(i), 0
        while rounds < fuel:
            self._cd_memo.clear()
            nxt = self.repr(self.cd(cur))
            rounds += 1
            if nxt == cur:
                break
            cur = nxt
        return cur, rounds


def reduce_tree_lo(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    g = Graph()
    root = g.import_tree(t)
    nf, steps = g.reduce(root, fuel=fuel)
    return g.export_tree(nf), steps, g.alloc_count()


def reduce_tree_cd(t: T, fuel: int = 1000) -> Tuple[T, int, int]:
    g = Graph()
    root = g.import_tree(t)
    nf, rounds = g.reduce_cd(root, fuel=fuel)
    return g.export_tree(nf), rounds, g.alloc_count()


def reduce_tree_pipeline(t: T, fuel: int = 100_000) -> Tuple[T, int, int, int]:
    g = Graph()
    root = g.import_tree(t)
    nf, b_n, i_n = g.reduce_pipeline(root, fuel=fuel)
    return g.export_tree(nf), b_n, i_n, g.alloc_count()


GOLDENS = [
    ("I K -> K", tree_app(I, KK), KK),
    ("K S I -> S", tree_app(tree_app(KK, S), I), S),
    ("S K K I -> I", tree_app(tree_app(tree_app(S, KK), KK), I), I),
]


def main() -> int:
    ok = True
    for label, term, expected in GOLDENS:
        nf_lo, steps, n_lo = reduce_tree_lo(term)
        nf_cd, rounds, n_cd = reduce_tree_cd(term)
        match = nf_lo == expected and nf_cd == expected
        tag = "OK" if match else "FAIL"
        print(f"{tag} {label}  lo={nf_lo} ({steps} steps, alloc={n_lo})  "
              f"cd={nf_cd} ({rounds} rounds, alloc={n_cd})")
        if not match:
            print(f"  EXPECTED: {expected}")
            ok = False

    g = Graph()
    assert g.kind[g._macro_k] == K.KONST
    assert K.S not in g._atom
    assert K.NORM in g._atom and K.COMP in g._atom
    print(f"OK L0 atoms={{norm,comp,dup,swap}} macro_k={g._macro_k}")

    g2 = Graph()
    redex = g2.import_tree(tree_app(I, KK))
    p1 = g2.mk_app(g2.atom(K.NORM), redex)
    p2 = g2.mk_app(g2._macro_k, redex)
    g2.step(redex)
    assert g2.export_tree(g2.repr(g2.right[p1])) == KK
    assert g2.export_tree(g2.repr(g2.right[p2])) == KK
    print("OK shared-parent kurzen via forward")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
