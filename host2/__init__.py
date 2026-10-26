"""host2 — the koru-side host pipeline.

Separate root from host/ on purpose: host/ is the plex/ISAR pipeline;
host2 is koru's own substrate.  Its logic is exactly two C99 tools —
the rest is koru programs run AS DATA:

  src/korufe/     the surface frontend TUs: real koru syntax (.k,
                  tor/->/=/| arms, guards, labels) -> program.ast.json
                  (canonical shape, koruc --ast-json's layout) ->
                  --lower -> [flow-eval] claim; refuse-by-default.
                  lex/parse/astio/lower/main + korufe.h, each .c with
                  a compilable .lean companion (Host2 lib)
  src/krun/       the claim witness TUs: s-expr reader (sx), total
                  decoders (wire), runK/evalKE twin (eval), quoteProg
                  twin (quote); claim mode re-decides, --emit mode
                  feeds a quoted program to a compiler claim's entry
  specs/tests/    the generated suite — <GGG>_<group>/<NNN>_<leaf>/
                  folders, each input.k + cases.json; groups
                  100_flow/200_emit/800_forged/900_wire (writer
                  lives in Lean: tools/DumpKoruFixtures.lean)
  specs/benches/  authored numbered bench folders, same leaf shape
  specs/ported/   authored real-koru programs (named folders)
  specs/*.json    the declared rows: quotient-maps.json,
                  realizations.json, assembly.json — pipeline maps,
                  realization interface/row/arm catalog, target
                  toolchain rows
  check.py        the witness gate: layout convention + koruc
                  authority + parse/lower/claim + FlowCheck witness
                  + emit/cc legs + refusal probes; orchestration only
  spec.py         the host2 registry record (HOST2)

Everything else — emission today, the compiler tomorrow — is koru
programs run as data inside the evaluator, not C.  korufe+krun are
the handwritten bootstrap that die when koru-spelled and machine-
checked-compiled legs replace them.

Data crosses boundaries (.k source, ast.json, claims, spec rows),
logic never does.
"""
