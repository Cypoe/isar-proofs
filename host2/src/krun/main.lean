/-! # krun/main.c — the claim-check + emit-host contract, pinned

Four legs, all pure interpretation over wire data:

    krun CLAIM                 parse claim -> re-decide -> compare
    krun EMITTER --emit SRC    SRC's program, quoted, fed to
                               EMITTER's `emit` entry as `src`
    krun --quote CLAIM         print `(cell (src <quote>))` — the
                               stdin wire a compiled-program
                               binary consumes when its entry
                               takes the program as `src`
    krun --args CLAIM          print `(cell (name val)…)` — the
                               claim's own entry args replayed as
                               the stdin cell (data-arg entries
                               like klex's `main {chars}`)

## Exit codes (the gate reads these, keep them stable)

- 0: decided and matched (`ok ...`), or refused where the claim
  expected refuse (`ok refuse`)
- 2: malformed claim / unreadable file / misuse
- 3: emit leg refused (no `emit` entry decide, or payload not str)
- 4: DRIFT — decided≠expected, refused≠expected, or an
  expectation-forged claim caught by re-decision.  Forging is
  louder than refusing: a claim that disagrees with the witness
  can never print `ok`.

## Honest position

main.c is the smallest piece of host-side logic: it composes
sx/wire/eval/quote and prints.  The `--emit` convention (quote the
source program, invoke `emit`) is what lets kemit.k run AS DATA —
nothing about C emission is special-cased here or anywhere else. -/
