#!/usr/bin/env python3
"""koru.spec -- the dialect record for the toolchain registry.

`KORU_FLOW` is the row toolchain.json points at: what layers exist,
which are realized (and where the proof lives), which refuse.  The
record is data; the semantics is `src/ISAR/`.
"""
from __future__ import annotations

import os
import sys

_HOST = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized  # noqa: E402


KORU_FLOW = {
    "dialect": "koru.flow",
    "object": "KProg (graph x entry x args) -- the wire-expressible "
              "subset of the Koru flow-walker's program shape",
    "layers": {
        "encoding": {
            "status": "realized",
            "impl": "ISAR.FlowView (encProg/decProg + decProg_encProg)",
            "table": "koru.encoding.TAG",
        },
        "grammar": {
            "status": "realized",
            "impl": "ISAR.KoruDialect wfProg (decidable static walls)",
            "walls": "koru.grammar.WALLS",
        },
        "semantics": {
            "status": "realized",
            "impl": "ISAR.FlowDialect (runK/evalKProg, runK_mono; "
                    "port of w:/src/koru/verify/semantics/FlowKernel.lean)",
        },
        "syntax": {
            "status": "realized elsewhere",
            "impl": "no parser in this mirror; the realized .k "
                    "surface is host2/src/korufe.c (C99, declared "
                    "subset: .k -> program.ast.json -> claim); "
                    "koruSurface.parse = fun _ => none in Lean",
            "refuses": "every parse host-side",
        },
        "emission": {
            "status": "realized (subset)",
            "impl": "ISAR.KoruDialect emitC99 + ISAR.KoruEmit kEmit "
                    "(koru_emit_fixpoint) -- declared subset: single "
                    "main = bare int literal, CompCert-accepted C",
            "refuses": "every program outside the declared subset",
        },
    },
    "deferred": {
        "eval_congruence": "FlowEvalCongruent -- a TTerm-resident "
                           "evaluator agreeing with runK on encProg; "
                           "flowEvalDialect is the discharge shape",
        "self_host": "SelfHostingC99 -- full-strength fixpoint "
                     "stated; koru_emit_fixpoint witnesses it on "
                     "koruEmitCorpus (1 accept + 7 refuse)",
    },
}


def describe() -> str:
    lines = [f"{KORU_FLOW['dialect']} -- {KORU_FLOW['object']}", "layers:"]
    for name, row in KORU_FLOW["layers"].items():
        lines.append(f"  {name:<9} {row['status']:<9} {row['impl']}")
    for name, row in KORU_FLOW["deferred"].items():
        lines.append(f"  deferred:{name} -- {row}")
    return "\n".join(lines)


if __name__ == "__main__":
    print(describe())
