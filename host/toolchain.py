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
    family: str = ""
    evidence: str = ""
    regime: Optional[str] = None
    tier: str = "fast"
    requires: Tuple[str, ...] = ()
    args: Tuple[str, ...] = ()
    cost_model: Optional[Tuple[Tuple[str, str], ...]] = None
    lean_decls: Tuple[str, ...] = ()
    label: str = ""
    timeout_s: Optional[int] = None
    release: bool = False


@dataclass(frozen=True)
class Selftest:
    module: str
    tier: str = "fast"
    requires: Tuple[str, ...] = ()
    args: Tuple[str, ...] = ()
    timeout_s: Optional[int] = None


@dataclass(frozen=True)
class Bench:
    name: str
    module: str
    measures: Tuple[str, ...] = ()
    claim: str = ""


@dataclass(frozen=True)
class Demo:
    name: str
    entry: str
    what: str = ""


FAMILIES = {"quotient", "staging", "cost", "selection"}
EVIDENCE = {"congruence", "seam", "cost", "selection", "lean", "structural"}
TIERS = {"fast", "full", "env"}
_REPO = os.path.dirname(_HOST)


def _suite_file(suite: str) -> Optional[str]:
    """Repo-relative file for a suite name; None for the special 'lake'."""
    if suite == "seed":
        return os.path.join(_REPO, "seed", "seed.py")
    if suite == "lake":
        return None
    return os.path.join(_HOST, suite + ".py")


def validate(raw: dict) -> List[str]:
    """Pure schema/honesty check on the raw spec dict -> error strings."""
    errs: List[str] = []

    def _tags(item, kind, name):
        fam, ev, tier = item.get("family"), item.get("evidence"), item.get("tier", "fast")
        if kind == "obligation":
            if fam not in FAMILIES:
                errs.append(f"{name}: bad family {fam!r}")
            if ev not in EVIDENCE:
                errs.append(f"{name}: bad evidence {ev!r}")
        if tier not in TIERS:
            errs.append(f"{name}: bad tier {tier!r}")
        req = item.get("requires", ())
        if (tier == "env") != bool(req):
            errs.append(f"{name}: tier env <=> requires non-empty violated")
        ts = item.get("timeout_s")
        if ts is not None and not (isinstance(ts, int) and ts > 0):
            errs.append(f"{name}: timeout_s must be a positive int")
        rel = item.get("release")
        if rel is not None and not isinstance(rel, bool):
            errs.append(f"{name}: release must be a boolean")
        return req

    seen = set()
    for o in raw.get("obligations", []):
        oid = o.get("id", "?")
        if oid in seen:
            errs.append(f"{oid}: duplicate obligation id")
        seen.add(oid)
        _tags(o, "obligation", oid)
        ev = o.get("evidence")
        fam = o.get("family")
        reg = o.get("regime")
        if ev not in ("structural", "lean"):
            if not reg or reg not in raw.get("regimes", {}):
                errs.append(f"{oid}: regime {reg!r} missing or undeclared")
        need_cost = fam == "cost" or ev == "cost"
        cm = o.get("cost_model")
        if need_cost != bool(cm):
            errs.append(f"{oid}: cost_model required iff family/evidence is cost")
        if cm:
            for k in ("work", "C", "baseline", "scope"):
                if k not in cm:
                    errs.append(f"{oid}: cost_model missing key {k!r}")
            for k in ("work", "C", "baseline"):
                v = str(cm.get(k, "")).lower()
                if "wall" in v or "qemu" in v:
                    errs.append(
                        f"{oid}: cost_model.{k}={cm.get(k)!r} — wall-clock/"
                        "QEMU time is never a Jones/cost measure")
        if bool(o.get("lean_decls")) != (ev == "lean"):
            errs.append(f"{oid}: lean_decls non-empty iff evidence==lean")
        sf = _suite_file(o.get("suite", ""))
        if sf is not None and not os.path.exists(sf):
            errs.append(f"{oid}: suite file missing: {sf}")
    for st in raw.get("selftests", []):
        nm = st.get("module", "?")
        _tags(st, "selftest", nm)
        if not os.path.exists(os.path.join(_HOST, nm + ".py")):
            errs.append(f"selftest {nm}: host/{nm}.py missing")
    for b in raw.get("benches", []):
        nm = b.get("name", "?")
        if not str(b.get("claim", "")).startswith("none"):
            errs.append(f"bench {nm}: claim must start with 'none'")
        if not b.get("measures"):
            errs.append(f"bench {nm}: measures must be non-empty")
        if not os.path.exists(
                os.path.join(_HOST, b.get("module", "") + ".py")):
            errs.append(f"bench {nm}: host/{b.get('module')}.py missing")
    for d in raw.get("demos", []):
        if not os.path.exists(os.path.join(_REPO, d.get("entry", ""))):
            errs.append(f"demo {d.get('name')}: entry {d.get('entry')!r} missing")
    return errs


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
            Obligation(
                id=o["id"], suite=o["suite"], what=o["what"],
                witnesses=tuple(o.get("witnesses", ())),
                family=o.get("family", ""), evidence=o.get("evidence", ""),
                regime=o.get("regime"), tier=o.get("tier", "fast"),
                requires=tuple(o.get("requires", ())),
                args=tuple(o.get("args", ())),
                cost_model=(tuple(sorted(o["cost_model"].items()))
                            if o.get("cost_model") else None),
                lean_decls=tuple(o.get("lean_decls", ())),
                label=o.get("label", ""),
                timeout_s=o.get("timeout_s"),
                release=bool(o.get("release", False)))
            for o in raw.get("obligations", [])),
        "selftests": tuple(
            Selftest(module=s["module"], tier=s.get("tier", "fast"),
                     requires=tuple(s.get("requires", ())),
                     args=tuple(s.get("args", ())),
                     timeout_s=s.get("timeout_s"))
            for s in raw.get("selftests", [])),
        "benches": tuple(
            Bench(name=b["name"], module=b["module"],
                  measures=tuple(b.get("measures", ())),
                  claim=b.get("claim", ""))
            for b in raw.get("benches", [])),
        "demos": tuple(
            Demo(name=d["name"], entry=d["entry"], what=d.get("what", ""))
            for d in raw.get("demos", [])),
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


def selftests() -> Tuple[Selftest, ...]:
    return load()["selftests"]


def benches() -> Tuple[Bench, ...]:
    return load()["benches"]


def demos() -> Tuple[Demo, ...]:
    return load()["demos"]


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


def _negative_cases() -> List[Tuple[str, dict]]:
    """Deep-copied mutations of the real spec that MUST each be rejected."""
    import copy
    base = copy.deepcopy(json.load(open(SPEC_PATH, encoding="utf-8")))
    cases = []

    def mut(fn):
        r = copy.deepcopy(base)
        fn(r)
        return r

    cases.append(("obligation missing family",
                  mut(lambda r: r["obligations"][0].pop("family", None))))
    cases.append(("family cost without cost_model",
                  mut(lambda r: r["obligations"][0].update(
                      family="cost", evidence="congruence",
                      regime="operEq"))))
    cases.append(("cost_model work=wall_ms",
                  mut(lambda r: r["obligations"][0].update(
                      family="cost", evidence="congruence", regime="operEq",
                      cost_model={"work": "wall_ms", "C": "pe_cost",
                                  "baseline": "src", "scope": "x"}))))
    cases.append(("cost_model C=qemu time",
                  mut(lambda r: r["obligations"][0].update(
                      family="cost", evidence="congruence", regime="operEq",
                      cost_model={"work": "steps", "C": "qemu time",
                                  "baseline": "src", "scope": "x"}))))
    cases.append(("bench claim 'faster than graph'",
                  mut(lambda r: r.setdefault("benches", []).append(
                      {"name": "bad", "module": "reduce",
                       "measures": ["ms"], "claim": "faster than graph"}))))
    cases.append(("tier env with empty requires",
                  mut(lambda r: r["obligations"][0].update(
                      tier="env", requires=[]))))
    cases.append(("evidence congruence with regime 'nonexistent'",
                  mut(lambda r: r["obligations"][0].update(
                      family="quotient", evidence="congruence",
                      regime="nonexistent"))))
    cases.append(("release not a bool",
                  mut(lambda r: r["obligations"][0].update(
                      release="yes"))))
    return cases


def main() -> int:
    load()
    print(f"toolchain spec: {SPEC_PATH}")
    ok = True
    verrs = validate(json.load(open(SPEC_PATH, encoding="utf-8")))
    for e in verrs:
        print(f"  FAIL validate: {e}")
        ok = False
    if not verrs:
        print("  ok validate: spec is well-formed")
    for desc, raw in _negative_cases():
        errs = validate(raw)
        if errs:
            print(f"  ok rejected ({desc}): {errs[0]}")
        else:
            print(f"  FAIL negative case accepted: {desc}")
            ok = False
    for t in load()["toolchains"]:
        print(f"  {t.status:9s} {t.name:22s} {t.dialect} | {t.isa} | "
              f"{t.routines} | {t.target} | {t.path}  {t.note}")
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
