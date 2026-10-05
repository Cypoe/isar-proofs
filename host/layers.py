"""layers — kernel composition as declared data.

A kernel image is an ordered sequence of LEGS, not a hand-enumerated
routine tuple.  Each leg is a named slot in the emission order gated
by ONE realization axis: the record's value for that axis selects the
leg's contribution — routines, .data slots, or nothing.  An axis
value with no row REFUSES (NotRealized naming the axis), never
silently defaults: the legs table is the complete declaration of
what this kernel family realizes.

Two halves, deliberately kept apart:

- specs/*.json — the CONTRACT: tiny per-dialect spec files declaring
  layer, in/out shapes, status, refusal cases.  Target-agnostic;
  bundled into archives only later.
- LEGS_* tables (in each routines_<target>.py) — the REALIZATION:
  which routines on this target implement each leg, and where they
  sit in the emission order.  A spec with no leg row is declared-
  not-realized; a leg row with no spec is undocumented.

compose() resolves the record against the legs table — what used to
be `routine_names_ir`'s if-chain plus `names[:1]+("plex_read",)+...`
string surgery is now table lookup and ordered assembly.  The emitted
routine LIST is the same bytes either way; what changed is that the
composition is declared.

This is build-time composition: the kernel is still a compiled
routine list.  A kernel that reads a chain spec at runtime and
assembles itself is the interpreted contract — separate, later (G9).
"""
from __future__ import annotations

import json
import os
import sys
from dataclasses import dataclass
from typing import Callable, Dict, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402  refusal type parity


RoutineNames = Tuple[str, ...]
Slots = Tuple[Tuple[str, int], ...]


@dataclass(frozen=True)
class Impl:
    """One leg's contribution for a selected axis value.
    slots: a static slot tuple, or a callable R -> slots when the
    contribution is parameter-shaped (e.g. MT ctx blocks sized by
    R.threads).  slot_rank orders .data layout independent of the
    leg's emission position — .data layout is image-contract, so it
    is declared, never derived from leg order."""
    names: RoutineNames = ()
    slots: object = ()
    slot_rank: int = 0


@dataclass(frozen=True)
class Leg:
    """A named slot in the emission order.  axis=None: the leg emits
    `names` unconditionally.  Otherwise `table[axis_value]` selects
    the Impl — a missing key refuses."""
    name: str
    axis: Optional[str]
    table: object          # RoutineNames | Dict[object, Impl]


# Axis selectors — each leg names exactly one; adding an axis here is
# adding a declared composition dimension, not an ad-hoc if-branch.
AXES: Dict[str, Callable] = {
    "dialect": lambda R: R.dialect,
    "io":      lambda R: R.io,
    "threads": lambda R: "mt" if R.threads > 1 else "st",
    "fuse_s":  lambda R: R.fuse_s,
    "reclaim": lambda R: R.reclaim,
    "gc":      lambda R: R.gc,
}


def _impl(leg: Leg, key: object) -> Impl:
    if isinstance(leg.table, tuple):
        return Impl(names=leg.table)
    try:
        return leg.table[key]
    except KeyError:
        raise NotRealized(
            f"{leg.axis}={key!r} not realized by layer {leg.name!r}")


def compose(R, legs: Tuple[Leg, ...]) -> RoutineNames:
    """The record's routine list, resolved leg by leg in declared
    order.  This replaces tuple enumeration + string insertion — the
    routine list is fully derived from the axis values."""
    out = []
    for leg in legs:
        key = None if leg.axis is None else AXES[leg.axis](R)
        out += _impl(leg, key).names
    return tuple(out)


def compose_slots(R, legs: Tuple[Leg, ...], base: Slots) -> Slots:
    """Base slots + every selected leg's slot contribution, ordered by
    declared slot_rank (not leg position) so the .data layout is an
    explicit part of the image contract."""
    adds = []
    for leg in legs:
        key = None if leg.axis is None else AXES[leg.axis](R)
        impl = _impl(leg, key)
        s = impl.slots(R) if callable(impl.slots) else impl.slots
        if s:
            adds.append((impl.slot_rank, s))
    out = base
    for _, s in sorted(adds, key=lambda t: t[0]):
        out = out + s
    return out


# ----------------------------------------------------------------------
# specs/ — the contract side.  One small JSON file per dialect value;
# load_specs() is the catalog, check_specs() the conformance rules a
# gate enforces (files land in bundles only later — natural resolution).

SPEC_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "specs")

SPEC_LAYERS = ("container", "encoding", "surface", "egress", "target")
SPEC_STATUS = ("realized", "realized-seed", "declared")
SPEC_REQUIRED = ("name", "layer", "in", "out", "status", "impl", "doc")


def load_specs(spec_dir: str = SPEC_DIR) -> Dict[str, dict]:
    """specs/*.json -> {name: spec}.  Malformed files refuse loudly."""
    out = {}
    for fn in sorted(os.listdir(spec_dir)):
        if not fn.endswith(".json"):
            continue
        with open(os.path.join(spec_dir, fn), encoding="utf-8") as f:
            spec = json.load(f)
        miss = [k for k in SPEC_REQUIRED if k not in spec]
        if miss:
            raise NotRealized(f"spec {fn}: missing fields {miss}")
        if spec["layer"] not in SPEC_LAYERS:
            raise NotRealized(
                f"spec {fn}: layer {spec['layer']!r} not in "
                f"{SPEC_LAYERS}")
        if spec["status"] not in SPEC_STATUS:
            raise NotRealized(
                f"spec {fn}: status {spec['status']!r} not in "
                f"{SPEC_STATUS}")
        if spec["name"] in out:
            raise NotRealized(f"spec {fn}: duplicate name "
                              f"{spec['name']!r}")
        out[spec["name"]] = spec
    return out


def leg_values(legs: Tuple[Leg, ...], axis: str) -> frozenset:
    """The axis values a leg family declares — conformance compares
    these against the specs and the toolchain axis catalog."""
    out = set()
    for leg in legs:
        if leg.axis == axis:
            out |= set(leg.table)
    return frozenset(out)
