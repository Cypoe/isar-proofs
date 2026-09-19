"""
Phase 4: Principled CoGen / Realize under ObservationRegime O + MachineContext c.

choose → LoaderPlan → emit → HostPiece (catalog).
IdentityRealize (graph) and FasmRealize (family=fasm, qm=fasm_map) — reduce still graph.lo.

Bootstrap = truthful representation for this machine, never InvariantLayer "IT".
A native PE loader (seed/seed.py) is the first family=cpu backend; fasmg is
used by the seed only as a byte oracle, never to assemble/link the product.
"""
from __future__ import annotations

import os
import platform
import sys
from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, List, Optional, Sequence, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, I, KK, S, app  # noqa: E402
from observation_regime import ObservationRegime, oper_eq_regime  # noqa: E402
from host_pieces import (  # noqa: E402
    HostPiece,
    catalog as base_catalog,
    run_piece,
    register_piece,
)
from strategy import Strategy, IdentityStrategy  # noqa: E402
from quotient_map import QuotientMap, identity_map  # noqa: E402
from fasm_dialect import fasm_map, GOLDENS as FASM_GOLDENS, show_fasm  # noqa: E402
from bytecode_dialect import bytecode_map  # noqa: E402
import toolchain  # noqa: E402
from toolchain import NotRealized  # noqa: E402


class Budget(Enum):
    """Loader family hint — stubs until SIMD/GPU product."""

    SERIAL = "serial"  # → graph / fasm / cpu
    PARALLEL_PARTIAL = "parallel_partial"  # → graph.cd (cd rounds, serial executor)
    FULL_TILE = "full_tile"  # → GPU family (stub → graph)


@dataclass(frozen=True)
class MachineContext:
    """Enough arch to choose a loader family — not a full OS model."""

    arch: str
    machine: str
    bits: int
    features: Tuple[str, ...] = ()

    @staticmethod
    def detect() -> "MachineContext":
        mach = platform.machine() or "unknown"
        bits = 64 if sys.maxsize > 2**32 else 32
        feats: List[str] = []
        if mach.lower() in ("amd64", "x86_64", "x64"):
            feats.append("x86_64")
        elif mach.lower() in ("aarch64", "arm64"):
            feats.append("aarch64")
        return MachineContext(
            arch=platform.system().lower() or "unknown",
            machine=mach,
            bits=bits,
            features=tuple(feats),
        )


@dataclass(frozen=True)
class LoaderPlan:
    """Pure selection result — no asm / dialect text."""

    name: str
    family: str  # "graph" | "fasm" | "cpu" | "simd" | "gpu"
    source_piece: str  # catalog name to wrap / reuse
    budget: Budget
    context: MachineContext
    note: str = ""
    toolchain: Optional[str] = None  # toolchain.CATALOG name for cpu plans


@dataclass(frozen=True)
class RealizeSpec:
    """
    Obligation: emitted piece preserves O on the probe suite.
    qm = how presentations reach substrate; regime defaults to OperEq.
    """

    name: str
    regime: ObservationRegime
    strategy: Strategy
    context: MachineContext
    budget: Budget
    qm: QuotientMap
    probes: Tuple[Any, ...] = ()


def choose(
    catalog: Sequence[HostPiece],
    budget: Budget,
    context: MachineContext,
    *,
    prefer: Optional[str] = None,
    prefer_family: Optional[str] = None,
) -> LoaderPlan:
    """
    Pure selection: budget + c → loader family plan. No emit side effects.
    SERIAL + x86_64 defaults to family=fasm unless prefer_family forces otherwise.
    SIMD/GPU families still wrap graph.lo until native loaders exist.
    """
    names = {p.name for p in catalog}
    src = prefer if prefer in names else (
        "graph.lo" if "graph.lo" in names else (catalog[0].name if catalog else "graph.lo")
    )
    note = "reduce via source piece; simd/gpu stub to graph"

    # A realized toolchain whose ISA matches this machine and whose target
    # OS is windows, with its piece registered, beats the fasm default.
    native_tc = None
    for tc in toolchain.realized():
        if tc.isa in context.features and tc.name in names:
            _isa, _rts, tgt = toolchain.resolve(tc)
            if tgt.os == context.arch:
                native_tc = tc
                break

    if (
        prefer_family is None
        and budget is Budget.SERIAL
        and "x86_64" in context.features
        and native_tc is not None
    ):
        family = "cpu"
        src = native_tc.name
        note = "native PE loader (seed/seed.py)"
    elif prefer_family == "fasm" or (
        prefer_family is None
        and budget is Budget.SERIAL
        and "x86_64" in context.features
    ):
        family = "fasm"
        note = "FASM(g) presentation backend; reduce via graph.lo (no external fasmg)"
    elif prefer_family == "graph" or (
        budget is Budget.SERIAL and prefer_family is None and "x86_64" not in context.features
    ):
        family = "graph" if src.startswith("graph") else "cpu"
    elif prefer_family is not None:
        family = prefer_family
    elif budget is Budget.PARALLEL_PARTIAL:
        # runtime path (toolchain.paths()["runtime"]): cd rounds are the
        # parallel semantics, executed serially
        family = "graph"
        runtime_pieces = set(
            toolchain.paths().get("runtime", {}).get("pieces", ()))
        if "graph.cd" in names and "graph.cd" in runtime_pieces:
            src = "graph.cd"
            note = "cd rounds — parallel semantics, serial executor"
    elif budget is Budget.FULL_TILE:
        family = "gpu"
        note = "stub: no GPU executor — wraps the graph source piece"
    else:
        family = "graph" if src.startswith("graph") else "cpu"

    # Explicit prefer_family=graph wins over x86_64 fasm default
    if prefer_family == "graph":
        family = "graph" if src.startswith("graph") else "cpu"
        note = "IdentityRealize / graph family"

    return LoaderPlan(
        name=f"plan.{family}.{budget.value}",
        family=family,
        source_piece=src,
        budget=budget,
        context=context,
        note=note,
        toolchain=native_tc.name if family == "cpu" and native_tc else None,
    )


# Mutable registry of CoGen-emitted pieces (alongside base catalog).
_EMITTED: Dict[str, HostPiece] = {}


def emitted_catalog() -> List[HostPiece]:
    return list(_EMITTED.values())


def full_catalog() -> List[HostPiece]:
    seen = {p.name: p for p in base_catalog()}
    seen.update(_EMITTED)
    return list(seen.values())


def emit(plan: LoaderPlan, *, catalog: Optional[Sequence[HostPiece]] = None) -> HostPiece:
    """
    Materialize a HostPiece from a plan and register it.
    FASM family: kind=fasm, still wraps graph reduce (truthful under O).
    """
    cat = list(catalog) if catalog is not None else full_catalog()
    by = {p.name: p for p in cat}
    if plan.source_piece not in by:
        raise KeyError(f"unknown source piece {plan.source_piece!r}")
    src = by[plan.source_piece]
    out_name = f"cogen.{plan.family}.{src.name}"

    def _reduce(t: T, fuel: int = 100_000) -> Tuple[T, int, int]:
        return src.reduce(t, fuel)

    if plan.family == "fasm":
        kind = "fasm"
    elif plan.family == "graph":
        kind = src.kind
    else:
        kind = plan.family

    piece = HostPiece(name=out_name, kind=kind, reduce=_reduce)
    _EMITTED[out_name] = piece
    register_piece(piece)
    return piece


def identity_realize(
    *,
    budget: Budget = Budget.SERIAL,
    context: Optional[MachineContext] = None,
    strategy: Optional[Strategy] = None,
) -> Tuple[RealizeSpec, LoaderPlan, HostPiece]:
    """
    Graph CoGen instance: specialize (identity) → graph.lo → operEqRegime.
    Forces prefer_family=graph so x86_64 machines still get IdentityRealize.
    """
    c = context if context is not None else MachineContext.detect()
    strat = strategy if strategy is not None else IdentityStrategy()
    R = oper_eq_regime()
    qm = identity_map(regime=R)
    probes = (app(I, KK), KK, I)
    spec = RealizeSpec(
        name="IdentityRealize",
        regime=R,
        strategy=strat,
        context=c,
        budget=budget,
        qm=qm,
        probes=probes,
    )
    plan = choose(full_catalog(), budget, c, prefer="graph.lo", prefer_family="graph")
    piece = emit(plan)
    return spec, plan, piece


def fasm_realize(
    *,
    budget: Budget = Budget.SERIAL,
    context: Optional[MachineContext] = None,
    strategy: Optional[Strategy] = None,
) -> Tuple[RealizeSpec, LoaderPlan, HostPiece]:
    """
    First non-identity emit backend: fasm_map + family=fasm piece (reduce=graph.lo).
    """
    c = context if context is not None else MachineContext.detect()
    strat = strategy if strategy is not None else IdentityStrategy()
    qm = fasm_map()
    probes = tuple(prog for _, prog, _ in FASM_GOLDENS)
    spec = RealizeSpec(
        name="FasmRealize",
        regime=qm.regime,
        strategy=strat,
        context=c,
        budget=budget,
        qm=qm,
        probes=probes,
    )
    plan = choose(full_catalog(), budget, c, prefer="graph.lo", prefer_family="fasm")
    piece = emit(plan)
    return spec, plan, piece


def native_realize(
    *,
    budget: Budget = Budget.SERIAL,
    context: Optional[MachineContext] = None,
    strategy: Optional[Strategy] = None,
    toolchain_name: str = "native.x86_64.pe",
) -> Tuple[RealizeSpec, LoaderPlan, HostPiece]:
    """
    Native CoGen instance: bytecode_map → native.x86_64.pe → family=cpu.
    Requires seed/seed.py's piece registered; KeyError otherwise.
    Declared (unrealized) toolchains raise NotRealized — never a fallback.
    """
    tc = toolchain.by_name(toolchain_name)          # KeyError if unlisted
    if tc.status != "realized":
        raise NotRealized(f"{tc.name}: {tc.status}")
    c = context if context is not None else MachineContext.detect()
    strat = strategy if strategy is not None else IdentityStrategy()
    qm = bytecode_map()
    probes = tuple(prog for _, prog, _ in FASM_GOLDENS)
    spec = RealizeSpec(
        name="NativeRealize",
        regime=qm.regime,
        strategy=strat,
        context=c,
        budget=budget,
        qm=qm,
        probes=probes,
    )
    names = {p.name for p in full_catalog()}
    if tc.name not in names:
        raise KeyError(
            f"native piece {tc.name!r} not registered "
            "(import seed.seed and register_piece(seed.piece()))"
        )
    plan = choose(
        full_catalog(), budget, c,
        prefer=tc.name, prefer_family="cpu",
    )
    piece = emit(plan)
    return spec, plan, piece


def preserves_spec(spec: RealizeSpec, piece: HostPiece, *, fuel: int = 100_000) -> bool:
    """Emitted piece agrees with regime observe on probes (and qm.preserves)."""
    for p in spec.probes:
        term = spec.qm.encode(p)
        specialized = spec.strategy.specialize(term, {})
        nf, _, _ = run_piece(piece, specialized, fuel=fuel)
        expected = spec.regime.observe(p)
        if not spec.regime.obs_eq(spec.qm.decode(nf), spec.qm.decode(expected)):
            return False
        if not spec.qm.preserves(p, piece=piece, fuel=fuel):
            return False
    return True


def main() -> int:
    ok = True
    c = MachineContext.detect()
    print(f"MachineContext: arch={c.arch} machine={c.machine} bits={c.bits} features={c.features}")

    # Register the native PE piece if seed/seed.py is importable.
    _seed_dir = os.path.join(os.path.dirname(_HOST), "seed")
    have_native = False
    if _seed_dir not in sys.path:
        sys.path.insert(0, _seed_dir)
    try:
        from seed import piece as _native_piece
        register_piece(_native_piece())
        have_native = True
        print("OK native piece registered (seed/seed.py)")
    except ImportError:
        print("SKIP native (seed not importable)")

    for b in Budget:
        plan = choose(full_catalog(), b, c)
        print(f"OK choose {b.value} -> family={plan.family} source={plan.source_piece}")

    for pname, p in toolchain.paths().items():
        print(f"OK path {pname}: {p.get('meaning', '')}")

    # PARALLEL_PARTIAL plan reduces S K K I -> I via graph.cd (cd rounds,
    # never compared to steps)
    pcd = choose(full_catalog(), Budget.PARALLEL_PARTIAL, c)
    if pcd.source_piece != "graph.cd":
        print(f"FAIL PARALLEL_PARTIAL source {pcd.source_piece} != graph.cd")
        ok = False
    else:
        nf, rounds, _ = run_piece(emit(pcd), app(app(app(S, KK), KK), I))
        good = str(nf) == "I"
        print(f"{'OK' if good else 'FAIL'} graph.cd S K K I -> {nf} "
              f"({rounds} rounds)")
        ok = ok and good

    # On x86_64, default SERIAL choose prefers the native PE piece when the
    # seed is importable, else fasm.
    if "x86_64" in c.features:
        p0 = choose(full_catalog(), Budget.SERIAL, c)
        expected = "cpu" if have_native else "fasm"
        if p0.family != expected:
            print(f"FAIL default SERIAL choose expected {expected} got {p0.family}")
            ok = False
        else:
            print(f"OK default SERIAL+x86_64 -> {p0.family} ({p0.source_piece})")

    spec, plan, piece = identity_realize()
    print(f"OK IdentityRealize plan={plan.name} piece={piece.name} kind={piece.kind}")
    if plan.family != "graph" or not preserves_spec(spec, piece):
        print("FAIL IdentityRealize")
        ok = False
    else:
        print(f"OK IdentityRealize preserves {spec.regime.name} on probes")

    nf, steps, n = run_piece(piece, app(I, KK))
    if str(nf) != "K":
        print(f"FAIL emit reduce I K => {nf}")
        ok = False
    else:
        print(f"OK emit reduce I K => K (steps={steps} alloc={n})")

    if have_native:
        nspec, nplan, npiece = native_realize()
        print(f"OK NativeRealize plan={nplan.name} piece={npiece.name} kind={npiece.kind} toolchain={nplan.toolchain}")
        if npiece.kind != "cpu" or nplan.family != "cpu":
            print("FAIL NativeRealize family/kind")
            ok = False
        if not preserves_spec(nspec, npiece):
            print("FAIL NativeRealize does not preserve O")
            ok = False
        else:
            print(f"OK NativeRealize preserves {nspec.regime.name} on {len(nspec.probes)} probes")

    print("toolchain catalog:")
    for t in toolchain.realized() + toolchain.declared():
        print(f"  {t.status:9s} {t.name}")
    try:
        native_realize(toolchain_name="x86_64.win64.cd")
        print("FAIL declared toolchain x86_64.win64.cd realized silently")
        ok = False
    except NotRealized as e:
        print(f"OK declared toolchain refused: {e}")

    fspec, fplan, fpiece = fasm_realize()
    print(f"OK FasmRealize plan={fplan.name} piece={fpiece.name} kind={fpiece.kind}")
    if fpiece.kind != "fasm" or fplan.family != "fasm":
        print("FAIL FasmRealize family/kind")
        ok = False
    if not preserves_spec(fspec, fpiece):
        print("FAIL FasmRealize does not preserve O")
        ok = False
    else:
        print(f"OK FasmRealize preserves {fspec.regime.name} on {len(fspec.probes)} probes")
        sample = show_fasm(fspec.probes[3]).splitlines()[1:]
        print(f"  sample probe lines: {sample}")

    print(f"full_catalog: {[p.name for p in full_catalog()]}")
    print("Phase 4b: FasmRealize + NativeRealize emit backends")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
