#!/usr/bin/env python3
"""koru — the Koru dialect leg (declared-not-realized host layer).

The dialect's ground truth is Lean-side:

  src/ISAR/FlowView.lean    — grammar (KVal..KProg) + proved TTerm codec
  src/ISAR/FlowDialect.lean — runK/evalKProg semantics, runK_mono,
                              FlowEvalCongruent, flowEvalDialect
  src/ISAR/KoruDialect.lean — KEncoding/KGrammar/KSurface/KBackend
                              layer registry + wfProg + SelfHosting

This package is the host-side mirror: the tag table, the layer
registry, and honest refusals for every leg that has no
implementation (`.k` surface, AST objects, C99 emission). It is NOT
a second evaluator — witnesses stay independent; the Lean module is
the semantics.

Layers (each declared data, each refuses by name where unrealized):

  encoding  — the tagged-tree codec table (mirrors encProg tags)
  grammar   — wfProg static walls (entry/invoke/jump resolution)
  syntax    — the `.k` surface (refuses host-side; the realized leg
              is host2/src/korufe.c — C99, declared subset)
  targets   — registered backend rows (c99 declared; emits nothing)
"""
