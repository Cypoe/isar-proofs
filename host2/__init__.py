"""host2 — the koru-side host pipeline.

Separate root from host/ on purpose: host/ is the plex/ISAR pipeline;
host2 is koru's own substrate.  Its logic is exactly two C99 tools —
the rest is koru programs run AS DATA:

  src/korufe.c    the surface frontend: real koru syntax (.k,
                  tor/->/=/| arms, guards, labels) -> program.ast.json
                  (canonical shape, koruc --ast-json's layout) ->
                  --lower -> [flow-eval] claim; refuse-by-default
  src/krun.c      the claim witness: s-expr reader, total decoders,
                  runK/evalKE twin, quoteProg twin; claim mode
                  re-decides, --emit mode feeds a quoted program to
                  a compiler claim's entry
  specs/          the declared rows: cases.json (generated),
                  quotient-maps.json, realizations.json,
                  assembly.json — pipeline maps, realization
                  interface/row/arm catalog, target toolchain rows
  specs/corpus/   generated .k files in REAL koru syntax (writer
                  lives in Lean: tools/DumpKoruFixtures.lean)
  check.py        the witness gate: parse/lower/claim/emit/cc legs +
                  refusal probes; orchestration only
  spec.py         the host2 registry record (HOST2)

Everything else — emission today, the compiler tomorrow — is koru
programs run as data inside the evaluator, not C.  korufe+krun are
the handwritten bootstrap that die when koru-spelled and machine-
checked-compiled legs replace them.

Data crosses boundaries (.k source, ast.json, claims, spec rows),
logic never does.
"""
