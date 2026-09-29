"""
spec_project — generated projections of host/toolchain.json.

Reads the spec + the last battery result (seed/build/battery_last.json;
missing => every live cell is `·`) and produces:

  docs/GATES.md    obligations table (id | suite | what | witnesses | live)
  docs/CATALOG.md  components + toolchains x derived status, strategy axes,
                   paths

main() regenerates into memory and compares with the files on disk:
drift exits 1 with a hint to run `python host/spec_project.py --write`;
`--write` updates the files in place.
"""
from __future__ import annotations

import json
import os
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

import toolchain  # noqa: E402

_REPO = os.path.dirname(_HOST)
DOCS = os.path.join(_REPO, "docs")
BATTERY_JSON = os.path.join(_REPO, "seed", "build", "battery_last.json")

GEN_HDR = "<!-- Generated from host/toolchain.json — do not edit. -->"


def _battery() -> dict:
    try:
        with open(BATTERY_JSON, encoding="utf-8") as f:
            d = json.load(f)
        return {"suites": d.get("suites", {}),
                "obligations": d.get("obligations", {})}
    except OSError:
        return {"suites": {}, "obligations": {}}


def _live_cell(cell) -> str:
    if cell is None:
        return "·"
    st = cell.get("status")
    if st is None:  # pre-protocol JSON: ok flag only
        return "✓" if cell.get("ok") else "✗"
    return {"pass": "✓", "pass*": "✓*", "fail": "✗",
            "skip": "skip"}.get(st, "·")


def _live(suite: str, bat: dict) -> str:
    return _live_cell(bat["suites"].get(suite))


def _ob_cell(o: "toolchain.Obligation", bat: dict):
    # per-obligation record first; the whole-suite record only stands in
    # for obligations that run AS the whole suite (no args) — an
    # obligation with its own args (selector, --cold) that never ran
    # must render `·`, not inherit another unit's result
    cell = bat["obligations"].get(o.id)
    if cell is None and not o.args:
        cell = bat["suites"].get(o.suite)
    return cell


def _live_ob(o: "toolchain.Obligation", bat: dict) -> str:
    return _live_cell(_ob_cell(o, bat))


def _run(suite: str, bat: dict) -> str:
    cell = bat["suites"].get(suite) or {}
    return cell.get("commit") or "·"


def _run_ob(o: "toolchain.Obligation", bat: dict) -> str:
    return (_ob_cell(o, bat) or {}).get("commit") or "·"


def render_gates() -> str:
    bat = _battery()
    suites = bat["suites"]
    lines = [
        GEN_HDR,
        "",
        "# Obligations (gates)",
        "",
        "| id | family | evidence | regime | tier | suite | what "
        "| witnesses | live | run |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for o in toolchain.obligations():
        w = ", ".join(o.witnesses) if o.witnesses else "—"
        what = f"[{o.label}] {o.what}" if o.label else o.what
        lines.append(f"| {o.id} | {o.family} | {o.evidence} | "
                     f"{o.regime or '—'} | {o.tier} | {o.suite} | {what} "
                     f"| {w} | {_live_ob(o, bat)} "
                     f"| {_run_ob(o, bat)} |")
    lines += [
        "",
        "## Selftests",
        "",
        "| module | tier | requires | args | live |",
        "| --- | --- | --- | --- | --- |",
    ]
    for s in toolchain.selftests():
        lines.append(f"| {s.module} | {s.tier} | "
                     f"{', '.join(s.requires) or '—'} | "
                     f"{' '.join(s.args) or '—'} | "
                     f"{_live(s.module, bat)} |")
    lines += ["", "## Benches", "",
              "| name | module | measures | claim |", "| --- | --- | --- | --- |"]
    for b in toolchain.benches():
        lines.append(f"| {b.name} | {b.module} | "
                     f"{', '.join(b.measures)} | {b.claim} |")
    lines += ["", "## Demos", "",
              "| name | entry | what |", "| --- | --- | --- |"]
    for d in toolchain.demos():
        lines.append(f"| {d.name} | {d.entry} | {d.what} |")
    lines += [
        "",
        "live column: `✓` pass, `✓*` pass with skipped legs, `✗` fail, "
        "`skip` whole-suite skip (env missing / exit 77), "
        "`·` not run in last battery; "
        "`run` = commit the suite record was produced on "
        "(`+dirty` = uncommitted host/seed changes, `·` = no record)",
        f"(battery_last.json: {os.path.basename(BATTERY_JSON)})",
        "",
    ]
    return "\n".join(lines)


def _comp_status(c: toolchain.Component) -> str:
    return "realized" if c.realized else "declared"


def render_catalog() -> str:
    s = toolchain.load()
    lines = [
        GEN_HDR,
        "",
        "# Catalog (derived status — never asserted)",
        "",
        "## Components",
        "",
        "| component | name | module.record | status | note |",
        "| --- | --- | --- | --- | --- |",
    ]
    for section, comps in (("dialect", s["dialects"]), ("isa", s["isas"]),
                           ("routines", s["routines"]),
                           ("target", s["targets"]), ("piece", s["pieces"]),
                           ("regime", s["regimes"])):
        for name, c in comps.items():
            mr = f"{c.module}.{c.record}" if c.module else "—"
            lines.append(f"| {section} | {name} | {mr} | "
                         f"{_comp_status(c)} | {c.note} |")
    lines += [
        "",
        "## Toolchains",
        "",
        "| name | dialect | isa | routines | target | path | status |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for t in s["toolchains"]:
        lines.append(f"| {t.name} | {t.dialect} | {t.isa} | {t.routines} | "
                     f"{t.target} | {t.path} | {t.status} |")
    lines += ["", "## Strategy axes", ""]
    for axis, vals in s["strategy_axes"].items():
        if isinstance(vals, dict):
            body = ", ".join(f"{k}={v}" for k, v in vals.items())
        else:
            body = ", ".join(vals)
        lines.append(f"- **{axis}**: {body}")
    lines += ["", "## Paths", ""]
    for pname, p in s["paths"].items():
        lines.append(f"### {pname}")
        for k, v in p.items():
            lines.append(f"- {k}: "
                         f"{', '.join(v) if isinstance(v, list) else v}")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    want_write = "--write" in sys.argv[1:]
    outs = {os.path.join(DOCS, "GATES.md"): render_gates(),
            os.path.join(DOCS, "CATALOG.md"): render_catalog()}
    drift = []
    for path, text in outs.items():
        try:
            cur = open(path, encoding="utf-8").read()
        except OSError:
            cur = None
        if cur != text:
            drift.append(path)
            if want_write:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "w", encoding="utf-8", newline="\n") as f:
                    f.write(text)
                print(f"wrote {path}")
    if drift and not want_write:
        for p in drift:
            print(f"FAIL drift: {p}")
        print("run `python host/spec_project.py --write`")
        return 1
    if not drift:
        print("OK spec_project (projections in sync)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
