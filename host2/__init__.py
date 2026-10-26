"""host2 — the koru-side host pipeline.

Separate root from host/ on purpose: host/ is the plex/ISAR pipeline;
host2 is koru's own substrate.  It owns exactly ONE piece of logic —
src/krun.c, the C99 witness twin of ISAR.FlowDialect.runK — plus:

  src/krun.c      the C witness: s-expr reader, total decoders,
                  runK/evalKE twin, quoteProg twin; claim mode
                  re-decides, --emit mode feeds a quoted program to
                  a compiler claim's entry
  specs/corpus/   generated .k [flow-eval] claims (writer lives in
                  Lean: tools/DumpKoruFixtures.lean — never edited)
  check.py        the witness gate: build/claim/forged/emit/cc legs
  spec.py         the host2 registry record (HOST2)

Everything else — emission today, the compiler tomorrow — is koru
programs run AS DATA inside the evaluator, not C.  krun.c is the
handwritten bootstrap that dies when a machine-checked-compiled
evaluator replaces it.

Data crosses boundaries (the .k claim files), logic never does.
"""
