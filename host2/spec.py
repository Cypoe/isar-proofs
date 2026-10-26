#!/usr/bin/env python3
"""host2.spec — the host2 registry record.

Own registry, not a host/toolchain.json module row: host/ resolves
modules by importlib on its own sys.path; host2 is a separate root
(the second pipeline).  The koru.flow toolchain note names this tree.
"""
from __future__ import annotations

HOST2 = {
    "pipeline": "koru.host2",
    "substrate": "C99 (clang -std=c99 -Werror) — src/krun.c, the "
                 "witness twin of ISAR.FlowDialect.runK; CompCert-"
                 "subset discipline (no VLA/_Complex/nested fns)",
    "wire": "[flow-eval] .k claims — same format FlowCheck.lean "
            "decides and golden.txt lists; generator: "
            "tools/DumpKoruFixtures.lean",
    "components": {
        "checker": {
            "status": "realized",
            "impl": "src/krun.c — s-expr reader, total decoders, "
                    "runK/evalKE twin, quoteProg twin; claim mode "
                    "re-decides, emit mode quotes SRC and invokes "
                    "the compiler program's entry",
        },
        "emission": {
            "status": "data",
            "impl": "specs/corpus/kemit.k — the compiler is a claim "
                    "file evaluated by the C witness, never "
                    "reimplemented in C",
        },
        "gate": {
            "status": "realized",
            "impl": "check.py — build/claim/forged/emit/cc legs "
                    "over the generated .k corpus (21 legs)",
        },
    },
    "witness_contract": "data crosses (.k claim files), logic never "
                        "does — the C checker re-decides every claim "
                        "independently; forged claims drift-fail",
    "deferred": {
        "full_fixpoint": "SelfHostingC99 at forall-src strength is "
                         "the Lean obligation; host2 witnesses the "
                         "same corpus the Lean theorem checks",
        "krun_as_target": "krun.c itself is the handwritten "
                          "bootstrap — it dies when a machine-"
                          "checked evaluator (CompCert leg) replaces "
                          "it; until then it is the one piece of "
                          "host logic",
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
