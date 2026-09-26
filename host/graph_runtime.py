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
from collections import Counter
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
        "_pending", "_pnd_dup",
        "_macro_k", "stats", "_memo_step",
        "_collect_frontier", "_frontier_next", "_last_remap",
        "_eager_tail", "_tail_queue", "_tail_budget",
    )

    def __init__(self) -> None:
        self.kind: List[K] = []
        self.varn: List[int] = []
        self.left: List[int] = []
        self.right: List[int] = []
        self.fwd: List[int] = []
        self._atom: Dict[K, int] = {}
        self._var_intern: Dict[int, int] = {}
        self._app_intern: Dict[int, int] = {}
        self._step_memo: Dict[int, Optional[int]] = {}
        self._cd_memo: Dict[int, int] = {}
        self._nf: Dict[int, bool] = {}
        # pending = nodes inside an in-flight step()/cd() call (the spine
        # ancestors of the current focus).  A redirect target whose
        # effective subtree contains a pending node fabricates a cyclic
        # graph once that pending node forwards — HeapDev.Acyc — and
        # step()'s spine descent diverges on it.
        #
        # The only way a pending node can enter a result is an interned
        # hit in mk_app: the interned node's raw children may have
        # redirected since interning, so its *effective* term is no
        # longer the requested one and can reach a live spine node.
        # All mk_app arguments are pending-free by induction (they are
        # descendants of the focus or prior results — pending nodes are
        # strictly ancestors; a descendant containing an ancestor would
        # already be a cycle), so an interned hit is verified by
        # comparing its repr-resolved children against the request —
        # a drifted hit is abandoned and the literal term gets a fresh
        # node.  _pnd_dup backs _freeze for the residual direct case.
        self._pending: set = set()
        self._pnd_dup: Dict[int, int] = {}
        # memory/alloc accounting — always-on Counter, ~free relative to
        # the dict lookups already on these paths.  Sites:
        #   mk_app.hit / .miss / .drifted / .pending — intern outcomes
        #   alloc.mk_app / .freeze / .var / .atom / .import-ish
        #   redirect.ok / .noop / .freeze_dst
        #   cd.memo_hit / .nf_hit / .recurse   step.memo_hit / .nf_hit
        self.stats: Counter = Counter()
        # step_memo seeding is engine-conditional: redirect() seeds
        # "step(src)=dst" knowledge for the lo path; cd never calls
        # step(), so seeding there is write-only residency (decision
        # 030: ~13M dead entries on sequential runs).  reduce_cd sets
        # this False for the duration.
        self._memo_step: bool = True
        # frontier collection: when _collect_frontier is set, every
        # redex-shaped node produced by mk_app/_freeze lands in
        # _frontier_next — the wavefront the next cd round develops
        # (see reduce_cd(frontier=True); decision 030).
        self._collect_frontier: bool = False
        self._frontier_next: set = set()
        self._last_remap: Dict[int, int] = {}
        # eager tail-calls: self-application-headed redexes (`app` spine
        # containing an `app(g,g)` link) are fold continuations — the
        # FOLDL/JOIN encodings bound recursion by the input spine, so
        # developing them eagerly within a round unfolds the whole
        # spine in one pass while payloads stay round-sealed.  Legal
        # because combinators are an orthogonal TRS: every complete
        # development converges to the same NF (parallel moves), so
        # the seal is a strategy parameter, not correctness.  The
        # budget is a divergence guard for ill-founded self-apps —
        # on exhaustion the node just waits for a normal round.
        self._eager_tail: bool = False
        self._tail_queue: List[int] = []
        self._tail_budget: int = 0
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

    def _push_pending(self, i: int) -> None:
        if not self._pending:
            self._pnd_dup.clear()
        self._pending.add(i)

    def redirect(self, src: int, dst: int) -> int:
        fwd = self.fwd
        if fwd[src] >= 0:
            src = self.repr(src)
        if fwd[dst] >= 0:
            dst = self.repr(dst)
        if src == dst:
            self.stats["redirect.noop"] += 1
            return src
        # Acyc (HeapDev): a redirect target must be pending-free — a dst
        # containing a pending node gains a back-edge once that node
        # forwards.  Contracta are pending-free by construction (mk_app
        # verifies interned hits); a still-pending dst is the residual
        # case — the occurrence keeps its finite-term semantics as a
        # frozen duplicate.
        if dst in self._pending:
            self.stats["redirect.freeze_dst"] += 1
            dst = self._freeze(dst)
            if dst == src:
                return src
        self.stats["redirect.ok"] += 1
        self.fwd[src] = dst
        if self._memo_step:
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
        self.stats["alloc.var"] += 1
        i = self._alloc(K.VAR, n=n)
        self._var_intern[n] = i
        self._nf[i] = True
        return i

    def _freeze(self, i: int) -> int:
        """Frozen copy of a pending node: fresh non-interned APP nodes
        along pending paths, shared elsewhere.  The copy keeps the
        pre-reduction occurrence as an independent node so it reduces in
        its own context instead of back-edging into the live spine."""
        if self.fwd[i] >= 0:
            i = self.repr(i)
        if i not in self._pending:
            return i
        got = self._pnd_dup.get(i)
        if got is not None:
            return got
        self.stats["alloc.freeze"] += 1
        n = self._alloc(K.APP, n=0, left=self._freeze(self.left[i]),
                        right=self._freeze(self.right[i]))
        if self._collect_frontier and self._is_redex_r(n):
            self._frontier_next.add(n)
        if self._eager_tail and self._is_tail_call(n):
            self._tail_queue.append(n)
        self._pnd_dup[i] = n
        return n

    def mk_app(self, left: int, right: int) -> int:
        fwd = self.fwd
        if fwd[left] >= 0:
            left = self.repr(left)
        if fwd[right] >= 0:
            right = self.repr(right)
        key = left << 32 | right
        got = self._app_intern.get(key)
        if got is not None:
            if fwd[got] >= 0:
                got = self.repr(got)
            # The interned node's raw children may have redirected since
            # interning — then its effective term is no longer `left
            # right` (and can reach a live spine node → fabricated cycle,
            # HeapDev.Acyc).  A hit is only honoured if its repr-resolved
            # children are exactly the request — then it denotes the same
            # term and is pending-free because the arguments are (pending
            # nodes are strictly ancestors of the focus; an argument
            # containing one would already be a cycle).  A pending `got`
            # likewise cannot be returned — fresh node = the literal term.
            gl, gr = self.left[got], self.right[got]
            if fwd[gl] >= 0:
                gl = self.repr(gl)
            if fwd[gr] >= 0:
                gr = self.repr(gr)
            if got not in self._pending \
                    and gl == left \
                    and gr == right:
                self.stats["mk_app.hit"] += 1
                if self._collect_frontier and self._is_redex_r(got):
                    self._frontier_next.add(got)
                if self._eager_tail and self._is_tail_call(got):
                    self._tail_queue.append(got)
                return got
            if got in self._pending:
                self.stats["mk_app.pending"] += 1
            else:
                self.stats["mk_app.drifted"] += 1
            self.stats["alloc.mk_app"] += 1
            i = self._alloc(K.APP, left=left, right=right)
            self._app_intern[key] = i
            if self._collect_frontier and self._is_redex_r(i):
                self._frontier_next.add(i)
            if self._eager_tail and self._is_tail_call(i):
                self._tail_queue.append(i)
            return i
        self.stats["mk_app.miss"] += 1
        self.stats["alloc.mk_app"] += 1
        i = self._alloc(K.APP, left=left, right=right)
        self._app_intern[key] = i
        if self._collect_frontier and self._is_redex_r(i):
            self._frontier_next.add(i)
        if self._eager_tail and self._is_tail_call(i):
            self._tail_queue.append(i)
        return i

    def alloc_count(self) -> int:
        return len(self.kind)

    @property
    def unique_count(self) -> int:
        return sum(1 for f in self.fwd if f < 0)

    def census(self) -> Dict[str, int]:
        """Where the memory is.  Nodes live in 5 parallel lists
        (kind/varn/left/right/fwd); the rest lives in dicts.  The
        byte estimates use sys.getsizeof on the containers — list
        over-allocation and dict tables are counted; the ~28B/int
        object cost for non-interned ints is folded into `est_bytes`
        as a per-entry allowance (honest order-of-magnitude, not
        accounting-exact)."""
        n = len(self.kind)
        dead = sum(1 for f in self.fwd if f >= 0)
        lists_b = sum(sys.getsizeof(x)
                      for x in (self.kind, self.varn, self.left,
                                self.right, self.fwd))
        dicts = {
            "app_intern": len(self._app_intern),
            "var_intern": len(self._var_intern),
            "step_memo": len(self._step_memo),
            "cd_memo": len(self._cd_memo),
            "nf": len(self._nf),
            "pending": len(self._pending),
            "pnd_dup": len(self._pnd_dup),
        }
        dicts_b = (
            sys.getsizeof(self._app_intern) + 100 * len(self._app_intern)
            + sys.getsizeof(self._var_intern) + 70 * len(self._var_intern)
            + sys.getsizeof(self._step_memo) + 70 * len(self._step_memo)
            + sys.getsizeof(self._cd_memo) + 70 * len(self._cd_memo)
            + sys.getsizeof(self._nf) + 70 * len(self._nf)
            + sys.getsizeof(self._pending) + 40 * len(self._pending)
            + sys.getsizeof(self._pnd_dup) + 70 * len(self._pnd_dup))
        return {
            "nodes": n,
            "forwarded": dead,
            "live_reps": n - dead,
            "app_nodes": sum(1 for k in self.kind if k == K.APP),
            **dicts,
            "lists_bytes": lists_b,
            "dicts_bytes": dicts_b,
            "est_bytes": lists_b + dicts_b,
        }

    def live_reachable(self, root: int) -> int:
        """Nodes still reachable from `root` through resolved children —
        the semantically live set.  Everything else is retained residue:
        consumed spines, drifted duplicates, contractum scaffolding."""
        fwd = self.fwd
        if fwd[root] >= 0:
            root = self.repr(root)
        seen = set()
        stack = [root]
        while stack:
            i = stack.pop()
            if i in seen:
                continue
            seen.add(i)
            if self.kind[i] == K.APP:
                l, r = self.left[i], self.right[i]
                if fwd[l] >= 0:
                    l = self.repr(l)
                if fwd[r] >= 0:
                    r = self.repr(r)
                stack.append(l)
                stack.append(r)
        return len(seen)

    def compact(self, root: int, keep=None) -> int:
        """Rebuild the arena keeping only nodes reachable from `root`
        plus the permanent atoms — the retention fix measured in
        decision 030 (forwarded scaffolding is never freed otherwise).

        Re-indexes every surviving node, rebuilds `_app_intern` /
        `_var_intern` / `_atom` / `_macro_k` on the new indices (which
        also re-keys intern entries whose children redirected since
        interning — the drifted-hit population disappears), carries
        `_nf` marks, and drops the memos: `_cd_memo` is round-scoped
        anyway and `_step_memo`/`_pnd_dup`/`_pending` key old indices.

        Only safe at a reduce boundary: `_pending` must be empty (no
        in-flight step/cd call may hold an index across a re-index).
        `keep` lists extra old node ids to preserve as seeds (the
        frontier set); `_last_remap` exposes the old→new map for them.
        Returns the new index of `root`."""
        assert not self._pending
        if self.fwd[root] >= 0:
            root = self.repr(root)
        # permanent roots: atoms + macro K are named by _atom/_macro_k
        # and must survive even when unreachable from `root`.
        seeds = [root, *(keep or ()), *self._atom.values(), self._macro_k]
        remap: Dict[int, int] = {}
        order: List[int] = []
        stack = list(seeds)
        fwd = self.fwd
        while stack:
            i = stack.pop()
            if i in remap:
                continue
            if fwd[i] >= 0:
                i = self.repr(i)
                if i in remap:
                    continue
            remap[i] = len(order)
            order.append(i)
            if self.kind[i] == K.APP:
                l, r = self.left[i], self.right[i]
                if fwd[l] >= 0:
                    l = self.repr(l)
                if fwd[r] >= 0:
                    r = self.repr(r)
                stack.append(l)
                stack.append(r)
        okind, ovarn = self.kind, self.varn
        oleft, oright, onf = self.left, self.right, self._nf
        self.kind = [okind[i] for i in order]
        self.varn = [ovarn[i] for i in order]
        self.left = [remap[self.repr(oleft[i])]
                     if okind[i] == K.APP else -1
                     for i in order]
        self.right = [remap[self.repr(oright[i])]
                      if okind[i] == K.APP else -1
                      for i in order]
        self.fwd = [-1] * len(order)
        self._app_intern = {}
        for j, i in enumerate(order):
            if okind[i] == K.APP:
                self._app_intern[self.left[j] << 32 | self.right[j]] = j
        self._atom = {k: remap[i] for k, i in self._atom.items()}
        self._macro_k = remap[self._macro_k]
        self._var_intern = {ovarn[i]: remap[i] for i in order
                            if okind[i] == K.VAR}
        self._nf = {remap[i]: True for i in order if onf.get(i)}
        self._step_memo = {}
        self._cd_memo = {}
        self._pnd_dup = {}
        self.stats["compact.runs"] += 1
        self.stats["compact.kept"] += len(order)
        self._last_remap = remap
        return remap[root]

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
        fwd = self.fwd
        if fwd[i] >= 0:
            i = self.repr(i)
        assert self.kind[i] == K.APP
        l, r = self.left[i], self.right[i]
        if fwd[l] >= 0:
            l = self.repr(l)
        if fwd[r] >= 0:
            r = self.repr(r)
        return l, r

    def step(self, i: int) -> Optional[int]:
        """LO step: L0 β (I/B/D/C) + L1 macro Kβ."""
        if self.fwd[i] >= 0:
            i = self.repr(i)
        if i in self._step_memo:
            self.stats["step.memo_hit"] += 1
            return self._step_memo[i]
        if self._nf.get(i):
            self.stats["step.nf_hit"] += 1
            self._step_memo[i] = None
            return None
        if self.kind[i] != K.APP:
            self._nf[i] = True
            self._step_memo[i] = None
            return None

        self._push_pending(i)
        try:
            return self._step_body(i)
        finally:
            self._pending.discard(i)

    def _step_body(self, i: int) -> Optional[int]:
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

    def reduce(self, i: int, fuel: int = 100_000,
               compact_every: int = 0) -> Tuple[int, int]:
        fwd = self.fwd
        cur = self.repr(i) if fwd[i] >= 0 else i
        steps = 0
        while steps < fuel:
            nxt = self.step(cur)
            if nxt is None:
                break
            if fwd[nxt] >= 0:
                nxt = self.repr(nxt)
            cur = nxt
            steps += 1
            if compact_every and steps % compact_every == 0:
                # between steps _pending is empty — the compact safety
                # precondition.  Drops _step_memo: cached redirects are
                # recomputed, semantically transparent (decision 030).
                cur = self.compact(cur)
                fwd = self.fwd
        return cur, steps

    def reduce_lo(self, i: int, fuel: int = 100_000) -> Tuple[int, int]:
        return self.reduce(i, fuel=fuel)

    def reduce_pipeline(self, i: int, fuel: int = 100_000) -> Tuple[int, int, int]:
        nf, n = self.reduce(i, fuel=fuel)
        return nf, n, 0

    def _is_redex_r(self, i: int) -> bool:
        """resolved-head redex test (HeapDev.isRedexNodeR) on a rep app-node."""
        fwd = self.fwd
        f = self.left[i]
        if fwd[f] >= 0:
            f = self.repr(f)
        fk = self.kind[f]
        if fk == K.NORM:
            return True
        if fk != K.APP:
            return False
        fl = self.left[f]
        if fwd[fl] >= 0:
            fl = self.repr(fl)
        flk = self.kind[fl]
        if flk == K.KONST or flk == K.DUP:
            return True
        if flk != K.APP:
            return False
        fll = self.left[fl]
        if fwd[fll] >= 0:
            fll = self.repr(fll)
        return self.kind[fll] in (K.COMP, K.SWAP)

    def _is_tail_call(self, i: int) -> bool:
        """self-application tail call: an app spine whose left chain
        contains an `app(g,g)` link (repr-equal children — hash-consed
        self-application).  This is the continuation signature of the
        spec's self-application folds (FOLDL/JOIN/MAP): recursion is
        bounded by the input spine, so eager development terminates
        on real folds and the budget bounds it elsewhere."""
        fwd = self.fwd
        if fwd[i] >= 0:
            i = self.repr(i)
        f = i
        for _ in range(8):
            if self.kind[f] != K.APP:
                return False
            l, r = self.left[f], self.right[f]
            if fwd[l] >= 0:
                l = self.repr(l)
            if fwd[r] >= 0:
                r = self.repr(r)
            if l == r:
                return True
            f = l
        return False

    def _drain_tails(self) -> None:
        """Develop queued tail-call redexes within the current round —
        the eager spine unfold.  Each drained cd may queue more; the
        loop drains them iteratively so depth never exceeds budget."""
        fwd = self.fwd
        while self._tail_queue and self._tail_budget > 0:
            self._tail_budget -= 1
            t = self._tail_queue.pop()
            if fwd[t] >= 0 or self._nf.get(t):
                continue
            self.stats["tail.dev"] += 1
            self.cd(t)

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
        fwd = self.fwd
        if fwd[i] >= 0:
            i = self.repr(i)
        hit = self._cd_memo.get(i)
        if hit is not None:
            self.stats["cd.memo_hit"] += 1
            if fwd[hit] >= 0:
                hit = self.repr(hit)
            return hit
        if self._nf.get(i) or self.kind[i] != K.APP:
            self.stats["cd.nf_hit"] += 1
            self._nf[i] = True
            self._cd_memo[i] = i
            return i

        self._push_pending(i)
        try:
            return self._cd_body(i)
        finally:
            self._pending.discard(i)

    def _cd_body(self, i: int) -> int:
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

    def reduce_cd(self, i: int, fuel: int = 1000,
                  compact: bool = False, frontier: bool = False,
                  eager_tail: bool = False) -> Tuple[int, int]:
        if frontier:
            return self._reduce_cd_frontier(i, fuel, compact,
                                            eager_tail)
        fwd = self.fwd
        cur = self.repr(i) if fwd[i] >= 0 else i
        rounds = 0
        # cd never calls step() — the per-redirect step_memo seed is
        # write-only waste on this engine (decision 030).
        prev = self._memo_step
        prev_t = self._eager_tail
        self._memo_step = False
        self._eager_tail = eager_tail
        try:
            while rounds < fuel:
                if compact:
                    cur = self.compact(cur)
                    fwd = self.fwd
                self._cd_memo.clear()
                self._tail_budget = 1_000_000
                nxt = self.cd(cur)
                if fwd[nxt] >= 0:
                    nxt = self.repr(nxt)
                if eager_tail:
                    self._drain_tails()
                    if fwd[cur] >= 0:
                        nxt = self.repr(cur)
                    else:
                        nxt = cur
                rounds += 1
                if nxt == cur:
                    break
                cur = nxt
            return cur, rounds
        finally:
            self._memo_step = prev
            self._eager_tail = prev_t

    def _reduce_cd_frontier(self, i: int, fuel: int,
                            compact: bool,
                            eager_tail: bool = False) -> Tuple[int, int]:
        """Wavefront cd: each round develops only the residual redexes
        born during the previous round — collected at mk_app/_freeze
        construction time — instead of re-walking the whole live cone
        from the root (decision 030; the re-walk was ~1k calls/round
        of pure traversal vs ~500 allocs of real work).

        Frontier = redex-shaped mk_app/_freeze results collected
        during the round.  That misses ONE birth path: a live rep
        `app(a,b)` built while `a` is undeveloped goes redex-shaped
        when `a` later redirects to a redex-headed form (shared
        children — a developed through a different parent).  So the
        frontier alone is incomplete; the hybrid: frontier rounds
        while nonempty, and a full cd(cur) walk as the convergence
        check whenever the frontier empties — a redirect-birth is
        caught at the next full walk.  Termination is the original
        criterion: a full pass that develops nothing.
        Dead frontier entries are skipped by repr(f) != f;
        dead-but-still-rep entries waste one cd call — bounded.
        """
        prev = self._memo_step
        prev_c = self._collect_frontier
        prev_t = self._eager_tail
        self._memo_step = False
        self._collect_frontier = True
        self._eager_tail = eager_tail
        fwd = self.fwd
        cur = self.repr(i) if fwd[i] >= 0 else i
        rounds = 0
        frontier = {cur}
        try:
            while rounds < fuel:
                if compact:
                    cur = self.compact(cur, keep=frontier)
                    fwd = self.fwd
                    frontier = {self._last_remap[f] for f in frontier
                                if f in self._last_remap}
                self._cd_memo.clear()
                self._frontier_next = set()
                self._tail_budget = 1_000_000
                if frontier:
                    for f in frontier:
                        if fwd[f] >= 0 or self._nf.get(f):
                            self.stats["frontier.dead"] += 1
                            continue
                        self.stats["frontier.dev"] += 1
                        self.cd(f)
                    did_full = False
                else:
                    self.stats["frontier.fullwalk"] += 1
                    self.cd(cur)
                    did_full = True
                if eager_tail:
                    self._drain_tails()
                if fwd[cur] >= 0:
                    cur = self.repr(cur)
                frontier = self._frontier_next
                rounds += 1
                if did_full and not frontier:
                    break
            return cur, rounds
        finally:
            self._memo_step = prev
            self._collect_frontier = prev_c
            self._eager_tail = prev_t
            self._frontier_next = set()
            self._tail_queue = []


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
