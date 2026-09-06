"""
Phase 2 proper-toy: structural composition-graph.

Heap semantics (graph reduction, not tree copy):
  - Interned App cells: equal (left,right) → one id (maximal structural share).
  - Cells are not mutated in place. A rewrite `redirect(src, dst)` installs a
    forward so every parent that already held `src` observes `dst` on `repr`
    (kürzen). That is the tensor-graph update, not “dict as the ontology.”
  - Sβ / Wβ build both uses with the same arg id before intern.
  - `_step_memo` / `_cd_memo` avoid re-walking reduced cells.

Lean = NF gold. Atoms unique. Not plex-core ports/lowerings.
"""
from __future__ import annotations

import os
import sys
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import K, T, I, KK, B, S, D, C, app as tree_app  # noqa: E402


class Graph:
    __slots__ = (
        "kind", "varn", "left", "right", "fwd",
        "_atom", "_var_intern", "_app_intern",
        "_step_memo", "_basis_memo", "_cd_memo", "_nf",
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
        self._basis_memo: Dict[int, Optional[int]] = {}
        self._cd_memo: Dict[int, int] = {}
        self._nf: Dict[int, bool] = {}
        for kind in (K.NORM, K.KONST, K.DUP, K.SWAP, K.COMP, K.S):
            self._atom[kind] = self._alloc(kind)

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
        """Kürzen: all holders of src observe dst."""
        src = self.repr(src)
        dst = self.repr(dst)
        if src == dst:
            return src
        self.fwd[src] = dst
        self._step_memo[src] = dst
        self._basis_memo.pop(src, None)
        self._cd_memo[src] = dst
        self._nf.pop(src, None)
        return dst

    def atom(self, kind: K) -> int:
        return self._atom[kind]

    def var(self, n: int) -> int:
        got = self._var_intern.get(n)
        if got is not None:
            return got
        i = self._alloc(K.VAR, n=n)
        self._var_intern[n] = i
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

    def import_tree(self, t: T) -> int:
        if t.k == K.APP:
            assert t.l is not None and t.r is not None
            return self.mk_app(self.import_tree(t.l), self.import_tree(t.r))
        if t.k == K.VAR:
            return self.var(t.n)
        return self.atom(t.k)

    def export_tree(self, i: int) -> T:
        i = self.repr(i)
        k = self.kind[i]
        if k == K.APP:
            return tree_app(self.export_tree(self.left[i]), self.export_tree(self.right[i]))
        if k == K.VAR:
            return T(K.VAR, n=self.varn[i])
        return {
            K.NORM: I, K.KONST: KK, K.DUP: D, K.SWAP: C, K.COMP: B, K.S: S,
        }[k]

    def show(self, i: int) -> str:
        i = self.repr(i)
        k = self.kind[i]
        if k == K.APP:
            return f"({self.show(self.left[i])} {self.show(self.right[i])})"
        if k == K.VAR:
            return f"v{self.varn[i]}"
        return {
            K.NORM: "I", K.KONST: "K", K.DUP: "D", K.SWAP: "C",
            K.COMP: "B", K.S: "S",
        }[k]

    def _fun_arg(self, i: int) -> Tuple[int, int]:
        i = self.repr(i)
        assert self.kind[i] == K.APP
        return self.repr(self.left[i]), self.repr(self.right[i])

    def step_lo(self, i: int) -> Optional[int]:
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
            if flk == K.KONST:
                out = self.redirect(i, fr)
                self._step_memo[i] = out
                return out
            if flk == K.APP:
                fll, flr = self._fun_arg(fl)
                fllk = self.kind[fll]
                if fllk == K.COMP:
                    out = self.mk_app(flr, self.mk_app(fr, x))
                    out = self.redirect(i, out)
                    self._step_memo[i] = out
                    return out
                if fllk == K.S:
                    out = self.mk_app(self.mk_app(flr, x), self.mk_app(fr, x))
                    out = self.redirect(i, out)
                    self._step_memo[i] = out
                    return out

        sf = self.step_lo(f)
        if sf is not None:
            out = self.redirect(i, self.mk_app(sf, x))
            self._step_memo[i] = out
            return out
        sx = self.step_lo(x)
        if sx is not None:
            out = self.redirect(i, self.mk_app(f, sx))
            self._step_memo[i] = out
            return out

        self._nf[i] = True
        self._step_memo[i] = None
        return None

    def reduce_lo(self, i: int, fuel: int = 100_000) -> Tuple[int, int]:
        cur, steps = self.repr(i), 0
        while steps < fuel:
            nxt = self.step_lo(cur)
            if nxt is None:
                break
            cur = self.repr(nxt)
            steps += 1
        return cur, steps

    def step_basis(self, i: int) -> Optional[int]:
        i = self.repr(i)
        if i in self._basis_memo:
            return self._basis_memo[i]
        if self.kind[i] != K.APP:
            self._basis_memo[i] = None
            return None
        f, x = self._fun_arg(i)
        if self.kind[f] == K.APP:
            fl, fr = self._fun_arg(f)
            if self.kind[fl] == K.DUP:
                out = self.redirect(i, self.mk_app(self.mk_app(fr, x), x))
                self._basis_memo[i] = out
                return out
            if self.kind[fl] == K.APP:
                fll, flr = self._fun_arg(fl)
                if self.kind[fll] == K.SWAP:
                    out = self.redirect(i, self.mk_app(self.mk_app(flr, x), fr))
                    self._basis_memo[i] = out
                    return out
        sf = self.step_basis(f)
        if sf is not None:
            out = self.redirect(i, self.mk_app(sf, x))
            self._basis_memo[i] = out
            return out
        sx = self.step_basis(x)
        if sx is not None:
            out = self.redirect(i, self.mk_app(f, sx))
            self._basis_memo[i] = out
            return out
        self._basis_memo[i] = None
        return None

    def reduce_pipeline(self, i: int, fuel: int = 100_000) -> Tuple[int, int, int]:
        cur = self.repr(i)
        b_n = i_n = 0
        while b_n + i_n < fuel:
            nxt = self.step_basis(cur)
            if nxt is not None:
                cur = self.repr(nxt)
                b_n += 1
                continue
            nxt = self.step_lo(cur)
            if nxt is not None:
                cur = self.repr(nxt)
                i_n += 1
                continue
            break
        return cur, b_n, i_n

    def cd(self, i: int) -> int:
        i = self.repr(i)
        hit = self._cd_memo.get(i)
        if hit is not None:
            return self.repr(hit)
        if self._nf.get(i):
            self._cd_memo[i] = i
            return i
        if self.kind[i] != K.APP:
            self._cd_memo[i] = i
            return i

        f, x = self._fun_arg(i)
        fk = self.kind[f]

        if fk == K.NORM:
            out = self.redirect(i, self.cd(x))
        elif fk == K.APP:
            fl, fr = self._fun_arg(f)
            if self.kind[fl] == K.KONST:
                out = self.redirect(i, self.cd(fr))
            elif self.kind[fl] == K.APP:
                fll, flr = self._fun_arg(fl)
                fllk = self.kind[fll]
                if fllk == K.COMP:
                    out = self.redirect(
                        i, self.mk_app(self.cd(flr), self.mk_app(self.cd(fr), self.cd(x)))
                    )
                elif fllk == K.S:
                    zx = self.cd(x)
                    out = self.redirect(
                        i,
                        self.mk_app(
                            self.mk_app(self.cd(flr), zx),
                            self.mk_app(self.cd(fr), zx),
                        ),
                    )
                else:
                    out = self.redirect(i, self.mk_app(self.cd(f), self.cd(x)))
            else:
                out = self.redirect(i, self.mk_app(self.cd(f), self.cd(x)))
        else:
            out = self.redirect(i, self.mk_app(self.cd(f), self.cd(x)))

        self._cd_memo[i] = out
        return out

    def par_step(self, i: int) -> int:
        return self.cd(i)

    def reduce_cd(self, i: int, fuel: int = 1000) -> Tuple[int, int]:
        cur, rounds = self.repr(i), 0
        while rounds < fuel:
            self._cd_memo.clear()
            nxt = self.cd(cur)
            nxt = self.repr(nxt)
            rounds += 1
            if nxt == cur:
                break
            cur = nxt
        return cur, rounds


def reduce_tree_lo(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
    g = Graph()
    root = g.import_tree(t)
    nf, steps = g.reduce_lo(root, fuel=fuel)
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
    root = g.import_tree(tree_app(tree_app(tree_app(S, KK), KK), I))
    after = g.step_lo(root)
    assert after is not None
    r = g.repr(after)
    la, ra = g.repr(g.left[r]), g.repr(g.right[r])
    assert la == ra
    print(f"OK S-beta shares spine  (alloc={g.alloc_count()})")

    g2 = Graph()
    redex = g2.import_tree(tree_app(I, KK))
    p1 = g2.mk_app(g2.atom(K.NORM), redex)
    p2 = g2.mk_app(g2.atom(K.KONST), redex)
    g2.step_lo(redex)
    assert g2.export_tree(g2.repr(g2.right[p1])) == KK
    assert g2.export_tree(g2.repr(g2.right[p2])) == KK
    print("OK shared-parent kurzen via forward")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
