# diag.py — diagnostics across every registered reduction engine.
#
# The engines (the evaluator strategies, distinct from strategy.py's
# specialize slot):
#
#   tree.lo           reduce.reduce        pure-T LO step (Lean IStep
#                                         reference — no arena)
#   tree.cd           reduce.reduce_cd     pure-T complete development
#   graph.lo          Graph.reduce         arena LO step + step_memo
#   graph.cd          Graph.reduce_cd      arena cd fixpoint
#   graph.cd+compact  Graph.reduce_cd(compact=True)
#                                         + per-round arena rebuild
#   native            seed.reduce_native   compiled exe subprocess
#                     (peak RSS via psutil; its alloc comes from the
#                     exe's own stderr report)
#
# Metrics per (term, engine): wall ms, peak bytes (tracemalloc for
# in-process; child RSS for native), cycles (steps or rounds), node
# allocs, NF hash — NF equality across engines is the congruence gate.
#
#   python diag.py            # small corpus
#   python diag.py --full     # + the JOIN retention case
import os
import sys
import threading
import time
from typing import Callable, Dict, List, Optional, Tuple

import psutil

_HOST = os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))
_ROOT = os.path.dirname(_HOST)
for p in (_HOST, _ROOT, os.path.join(_ROOT, "seed")):
    if p not in sys.path:
        sys.path.insert(0, p)

from reduce import T, reduce as tree_lo, reduce_cd as tree_cd  # noqa: E402
from graph_runtime import Graph                               # noqa: E402


# ---------------------------------------------------------------------
# engine registry
# ---------------------------------------------------------------------

def _e_tree_lo(t: T, fuel: int) -> Tuple[T, int]:
    return tree_lo(t, fuel=fuel)


def _e_tree_cd(t: T, fuel: int) -> Tuple[T, int]:
    return tree_cd(t, fuel=fuel)


class _GraphRun:
    """graph engines return the Graph too — census/stats live on it."""
    __slots__ = ("nf", "cycles", "g")

    def __init__(self, nf: int, cycles: int, g: Graph):
        self.nf, self.cycles, self.g = nf, cycles, g


def _e_graph_lo(t: T, fuel: int) -> _GraphRun:
    g = Graph()
    r = g.import_tree(t)
    nf, steps = g.reduce(r, fuel=fuel)
    return _GraphRun(nf, steps, g)


def _e_graph_cd(t: T, fuel: int) -> _GraphRun:
    g = Graph()
    r = g.import_tree(t)
    nf, rounds = g.reduce_cd(r, fuel=fuel)
    return _GraphRun(nf, rounds, g)


def _e_graph_cd_compact(t: T, fuel: int) -> _GraphRun:
    g = Graph()
    r = g.import_tree(t)
    nf, rounds = g.reduce_cd(r, fuel=fuel, compact=True)
    return _GraphRun(nf, rounds, g)


def _e_graph_cd_frontier(t: T, fuel: int) -> _GraphRun:
    g = Graph()
    r = g.import_tree(t)
    nf, rounds = g.reduce_cd(r, fuel=fuel, frontier=True)
    return _GraphRun(nf, rounds, g)


def _e_graph_cd_fc(t: T, fuel: int) -> _GraphRun:
    g = Graph()
    r = g.import_tree(t)
    nf, rounds = g.reduce_cd(r, fuel=fuel, frontier=True, compact=True)
    return _GraphRun(nf, rounds, g)


def _e_native(t: T, fuel: int):
    import seed  # subprocess witness — may need the exe built
    nf, steps, alloc = seed.reduce_native(t, 0)
    return (nf, steps, alloc)


# (name, runner, kind) — kind: "tree" (T nf), "graph" (index + Graph),
# "native" (nf text + steps + alloc, out of process)
ENGINES: List[Tuple[str, Callable, str]] = [
    ("tree.lo", _e_tree_lo, "tree"),
    ("tree.cd", _e_tree_cd, "tree"),
    ("graph.lo", _e_graph_lo, "graph"),
    ("graph.cd", _e_graph_cd, "graph"),
    ("graph.cd+compact", _e_graph_cd_compact, "graph"),
    ("graph.cd+frontier", _e_graph_cd_frontier, "graph"),
    ("graph.cd+f+c", _e_graph_cd_fc, "graph"),
    ("native", _e_native, "native"),
]


def nf_key(res, kind: str, g: Optional[Graph]) -> str:
    """Canonical NF string for the congruence check — everything is
    compared in surface form (quote_surface folds derived_s → S;
    export_tree already applies it on the graph side)."""
    from tower import quote_surface
    if kind == "tree":
        return repr(quote_surface(res[0]))
    if kind == "graph":
        return repr(g.export_tree(res.nf)) if g is not None else "?"
    return repr(quote_surface(res[0]))


def run_one(name: str, runner: Callable, kind: str,
            t: T, fuel: int) -> Dict:
    """Wall time + peak process RSS (self + children — the native exe
    subprocess counts).  RSS is sampled, not instrumented: no per-alloc
    overhead, so wall stays honest."""
    proc = psutil.Process()
    base = proc.memory_info().rss
    peak = [base]
    stop = threading.Event()

    def sampler():
        while not stop.is_set():
            try:
                rss = proc.memory_info().rss
                for ch in proc.children(recursive=True):
                    try:
                        rss += ch.memory_info().rss
                    except psutil.Error:
                        pass
                if rss > peak[0]:
                    peak[0] = rss
            except psutil.Error:
                pass
            stop.wait(0.02)

    th = threading.Thread(target=sampler, daemon=True)
    th.start()
    t0 = time.perf_counter()
    try:
        res = runner(t, fuel)
        ok, err = True, ""
    except Exception as e:  # native missing exe, fuel exhaust, …
        res, ok, err = None, False, f"{type(e).__name__}: {e}"
    wall_ms = (time.perf_counter() - t0) * 1000
    stop.set()
    th.join()
    row = {"engine": name, "ok": ok, "wall_ms": wall_ms,
           "peak_mb": max(peak[0] - base, 0) / 1e6}
    if not ok:
        row["err"] = err
        return row
    if kind == "tree":
        row["cycles"], row["allocs"] = res[1], None
        row["nf"] = nf_key(res, kind, None)
    elif kind == "graph":
        g = res.g
        c = g.census()
        row["cycles"] = res.cycles
        # total allocations = work done; nodes = final residency
        row["allocs"] = sum(v for k, v in g.stats.items()
                          if k.startswith("alloc."))
        row["nf"] = nf_key(res, kind, g)
        row["nodes"] = c["nodes"]
        row["reachable"] = g.live_reachable(res.nf)
    else:  # native
        row["cycles"], row["allocs"] = res[1], res[2]
        row["nf"] = nf_key(res, kind, None)
    return row


# ---------------------------------------------------------------------
# corpus
# ---------------------------------------------------------------------

def corpus(full: bool) -> List[Tuple[str, Callable[[], T], set]]:
    """(label, builder, engine-kinds).  Spec-term cases use L0 atoms
    (norm/comp/dup/swap) that the tree reducer doesn't know — those
    are graph+native only."""
    import math
    from lambda_dialect import bracket, parse, reduce_basis
    from lambda_bench import church, apply_id_k, fact_product, appn, EXP
    import spec_term as st

    def lam(e):
        # same prep as compare_lo_cd: bracket + basis reduce, so all
        # engines see the same basis-level input
        return lambda: reduce_basis(bracket(e), fuel=200_000)[0]

    def zf(n):
        return bracket(parse(f"({st._ZEROFILL} {st._num_src(n)})"))

    allk = {"tree", "graph", "native"}
    gnk = {"graph", "native"}
    cases: List[Tuple[str, Callable[[], T], set]] = [
        ("c50 I K", lam(apply_id_k(church(50))), allk),
        ("fact5", lam(apply_id_k(fact_product(5))), allk),
        ("2^6", lam(apply_id_k(appn(EXP, church(2), church(6)))), allk),
        ("linkOf-mini", lambda: st.link_query(("ExitProcess",),
                                             (("x", 8),)), gnk),
    ]
    if full:
        z1, z2 = zf(64), zf(128)
        join = st._appn(term_of(st._JOIN),
                        st._appn(st._CONS, z1,
                                 st._appn(st._CONS, z2, st._NIL)))
        cases.append(("JOIN zf64 zf128", lambda: join, gnk))
    return cases


def term_of(src):
    from lambda_dialect import bracket, parse
    return bracket(parse(src))


# ---------------------------------------------------------------------
# table
# ---------------------------------------------------------------------

def main() -> int:
    full = "--full" in sys.argv[1:]
    engines = ENGINES
    if "--no-native" in sys.argv[1:]:
        engines = [e for e in engines if e[2] != "native"]
    sys.setrecursionlimit(20000)
    n_bad = 0
    for label, mk, kinds in corpus(full):
        t = mk()
        print(f"\n== {label} ==", flush=True)
        nfs: Dict[str, str] = {}
        for name, runner, kind in engines:
            if kind not in kinds:
                continue
            row = run_one(name, runner, kind, t, 10_000_000)
            if not row["ok"]:
                print(f"  {name:18s} SKIP/FAIL {row['err']}", flush=True)
                continue
            nfs[name] = row["nf"]
            extra = (f"  nodes={row['nodes']:,} reach={row['reachable']:,}"
                     if kind == "graph" else "")
            alloc = (f"alloc={row['allocs']:,}"
                     if row["allocs"] is not None else "")
            print(f"  {name:18s} {row['wall_ms']:9.1f}ms "
                  f"peak={row['peak_mb']:8.1f}MB "
                  f"cyc={row['cycles']:<10,} {alloc}{extra}", flush=True)
        if len(set(nfs.values())) > 1:
            n_bad += 1
            print("  CONGRUENCE FAIL — engines disagree:", flush=True)
            for k, v in nfs.items():
                print(f"    {k:18s} {v[:90]}", flush=True)
        else:
            print(f"  congruence OK ({len(nfs)} engines)", flush=True)
    print(f"\n{'FAIL' if n_bad else 'OK'} diag: "
          f"{len(corpus(full))} terms x {len(engines)} engines")
    return 1 if n_bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
