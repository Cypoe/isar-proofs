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
            return json.load(f).get("suites", {})
    except OSError:
        return {}


def _live(suite: str, suites: dict) -> str:
    cell = suites.get(suite)
    if cell is None:
        return "·"
    return "✓" if cell.get("ok") else "✗"


def render_gates() -> str:
    suites = _battery()
    lines = [
        GEN_HDR,
        "",
        "# Obligations (gates)",
        "",
        "| id | suite | what | witnesses | live |",
        "| --- | --- | --- | --- | --- |",
    ]
    for o in toolchain.obligations():
        w = ", ".join(o.witnesses) if o.witnesses else "—"
        lines.append(f"| {o.id} | {o.suite} | {o.what} | {w} | "
                     f"{_live(o.suite, suites)} |")
    lines += [
        "",
        f"live column: `✓` suite ok, `✗` suite failed, `·` no battery record",
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
