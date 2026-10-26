#!/usr/bin/env python3
"""host2.spec — the host2 registry record.

Own registry, not a host/toolchain.json module row: host/ resolves
modules by importlib on its own sys.path; host2 is a separate root
(the second pipeline).  The koru.flow toolchain note names this tree.
"""
from __future__ import annotations

HOST2 = {
    "pipeline": "koru.host2",
    "substrate": "python3 stdlib-only witness twin of ISAR.FlowDialect.runK",
    "wire": ".kv (kv-json v1) — canonical writer: "
            "tools/DumpKoruFixtures.lean; reader+validator: kwire",
    "components": {
        "run": {
            "status": "realized",
            "impl": "run.py — runK/evalKE/evalKBin/evalKUn/"
                    "evalKBuiltin twin, all refusal shapes",
        },
        "quote": {
            "status": "realized",
            "impl": "quote.py — quoteProg twin (KProg -> KVal)",
        },
        "emission": {
            "status": "data",
            "impl": "specs/koru-fixtures.json programs.kemit — the "
                    "compiler program is data evaluated by run, "
                    "never reimplemented in python",
        },
        "gate": {
            "status": "realized",
            "impl": "fixtures.py — quote/eval/kemit/cc legs vs the "
                    "generated fixture file",
        },
    },
    "witness_contract": "data crosses (fixture json), logic never "
                        "does — host2 reproduces Lean decisions "
                        "independently, byte-for-byte where strings",
    "deferred": {
        "surface": ".k parse — declared only, refuses everywhere",
        "full_fixpoint": "SelfHostingC99 at forall-src strength is "
                         "the Lean obligation; host2 witnesses the "
                         "same corpus the Lean theorem checks",
    },
}


def describe() -> str:
    lines = [f"{HOST2['pipeline']} — {HOST2['substrate']}",
             f"wire: {HOST2['wire']}", "components:"]
    for name, row in HOST2["components"].items():
        lines.append(f"  {name:<9} {row['status']:<9} {row['impl']}")
    for name, row in HOST2["deferred"].items():
        lines.append(f"  deferred:{name} — {row}")
    return "\n".join(lines)


if __name__ == "__main__":
    print(describe())
