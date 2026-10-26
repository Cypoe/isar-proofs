"""host2 — the koru-side host pipeline.

Separate root from host/ on purpose: host/ is the plex/ISAR pipeline;
host2 is koru's own substrate.  It owns exactly ONE piece of logic —
run.py, the Python witness twin of ISAR.FlowDialect.runK — plus:

  kwire.py     the .kv wire reader/validator (writer lives in Lean:
               tools/DumpKoruFixtures.lean — generated, never edited)
  quote.py     the quoteProg twin (KProg -> KVal calling convention)
  fixtures.py  the witness gate vs generated expectations
  specs/       generated fixture data + declared spec rows
  spec.py      the host2 registry record (HOST2)

Everything else — emission today, the compiler tomorrow — is koru
programs run AS DATA inside the evaluator, not Python.  The evaluator
is the handwritten bootstrap that dies when a machine-checked-compiled
evaluator replaces it.

Data crosses boundaries (the fixture file), logic never does.
"""
