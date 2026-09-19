"""
toolchain — loader for the declarations-only spec `host/toolchain.json`.

The cogen reads declarations, not Python literals: dialects, ISAs,
routine sets, targets, pieces, realization paths, strategy axes,
observation regimes, obligations (gates), witnesses.  Status is never
stored: a component or toolchain is realized iff its `module` imports
and has `record` — the loader tries it, the spec cannot lie.

Owns `NotRealized` (seed/seed.py re-exports it).
"""
from __future__ import annotations

import importlib
import json
import os
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

SPEC_PATH = os.path.join(_HOST, "toolchain.json")


class NotRealized(Exception):
    """Declared-but-unrealized component/toolchain (refusal, never fallback)."""


@dataclass(frozen=True)
class Component:
    """One declared dialect/isa/routines/target/piece/regime entry."""
    name: str
    module: Optional[str] = None
    record: Optional[str] = None
    note: str = ""
    data: Tuple[Tuple[str, object], ...] = ()   # extra JSON keys, frozen view

    def resolve(self):
        """The record object; NotRealized if module/record absent or
        the import/lookup fails."""
        if not self.module or not self.record:
            raise NotRealized(f"{self.name}: no module/record declared")
        try:
            mod = importlib.import_module(self.module)
            return getattr(mod, self.record)
        except (ImportError, AttributeError) as e:
            raise NotRealized(f"{self.name}: {e}")

    @property
    def realized(self) -> bool:
        try:
            self.resolve()
            return True
        except NotRealized:
            return False


@dataclass(frozen=True)
class Toolchain:
    name: str
    dialect: str       # "bytecode.postfix"
    isa: str           # "x86_64"
    routines: str      # "x86_64.win64.lo"
    target: str        # "pe64"
    path: str = ""     # "runtime" | "native"
    note: str = ""

    @property
    def status(self) -> str:        # "realized" | "declared" — derived
        try:
            resolve(self)
            return "realized"
        except NotRealized:
            return "declared"


@dataclass(frozen=True)
class Obligation:
    id: str
    suite: str
    what: str
    witnesses: Tuple[str, ...] = ()


_SPEC = None


def load() -> dict:
    """Read toolchain.json once into frozen records; returns the spec dict
    {dialects, isas, routines, targets, pieces, paths, toolchains,
     strategy_axes, regimes, obligations, witnesses}."""
    global _SPEC
    if _SPEC is not None:
        return _SPEC
    with open(SPEC_PATH, encoding="utf-8") as f:
        raw = json.load(f)

    def comps(section: str) -> Dict[str, Component]:
        out = {}
        for name, d in raw.get(section, {}).items():
            extra = tuple((k, v) for k, v in d.items()
                          if k not in ("module", "record", "note"))
            out[name] = Component(
                name=name, module=d.get("module"), record=d.get("record"),
                note=d.get("note", ""), data=extra)
        return out

    _SPEC = {
        "dialects": comps("dialects"),
        "isas": comps("isas"),
        "routines": comps("routines"),
        "targets": comps("targets"),
        "pieces": comps("pieces"),
        "paths": raw.get("paths", {}),
        "toolchains": tuple(
            Toolchain(
                name=t["name"], dialect=t["dialect"], isa=t["isa"],
                routines=t["routines"], target=t["target"],
                path=t.get("path", ""), note=t.get("note", ""))
            for t in raw.get("toolchains", [])),
        "strategy_axes": raw.get("strategy_axes", {}),
        "regimes": comps("regimes"),
        "obligations": tuple(
            Obligation(id=o["id"], suite=o["suite"], what=o["what"],
                       witnesses=tuple(o.get("witnesses", ())))
            for o in raw.get("obligations", [])),
        "witnesses": tuple(raw.get("witnesses", ())),
    }
    return _SPEC


def components() -> Dict[str, Dict[str, Component]]:
    s = load()
    return {"dialect": s["dialects"], "isa": s["isas"],
            "routines": s["routines"], "target": s["targets"]}


def realized() -> List[Toolchain]:
    return [t for t in load()["toolchains"] if t.status == "realized"]


def declared() -> List[Toolchain]:
    return [t for t in load()["toolchains"] if t.status == "declared"]


def by_name(name: str) -> Toolchain:
    for t in load()["toolchains"]:
        if t.name == name:
            return t
    raise KeyError(f"unknown toolchain {name!r}")


def paths() -> Dict[str, dict]:
    return load()["paths"]


def obligations() -> Tuple[Obligation, ...]:
    return load()["obligations"]


def regimes() -> Dict[str, Component]:
    return load()["regimes"]


def pieces() -> Dict[str, Component]:
    return load()["pieces"]


def strategy_axes() -> Dict[str, object]:
    return load()["strategy_axes"]


def witnesses() -> Tuple[str, ...]:
    return load()["witnesses"]


def resolve(tc: Toolchain):
    """(ISA, Routines, Target) records for a realized toolchain.
    Each named component is resolved through the spec; a failure raises
    NotRealized naming the missing component — never a fallback."""
    comps = components()
    vals = {"dialect": tc.dialect, "isa": tc.isa,
            "routines": tc.routines, "target": tc.target}
    recs = {}
    for comp, value in vals.items():
        ent = comps[comp].get(value)
        try:
            if ent is None:
                raise NotRealized(f"undeclared {comp}")
            recs[comp] = ent.resolve()
        except NotRealized as e:
            raise NotRealized(
                f"{tc.name}: {comp} {value!r} not realized ({e})")
    return recs["isa"], recs["routines"], recs["target"]


def main() -> int:
    load()
    print(f"toolchain spec: {SPEC_PATH}")
    for t in load()["toolchains"]:
        print(f"  {t.status:9s} {t.name:22s} {t.dialect} | {t.isa} | "
              f"{t.routines} | {t.target} | {t.path}  {t.note}")
    ok = True
    for t in realized():
        isa, rts, tgt = resolve(t)
        good = (isa.name == t.isa and rts.name == t.routines
                and tgt.name == t.target)
        print(f"  {'ok' if good else 'FAIL'} resolve {t.name}")
        ok = ok and good
    for t in declared():
        try:
            resolve(t)
            print(f"  FAIL {t.name} resolved silently")
            ok = False
        except NotRealized as e:
            print(f"  ok refused: {e}")
    print(f"{'OK' if ok else 'FAIL'} toolchain")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
