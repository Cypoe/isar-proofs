/-! # krun/sx.c — the [flow-eval] wire reader, pinned

The wire grammar korufe emits and FlowCheck decides.  The C reader
is a tokenizer + recursive-descent over this grammar; refusal =
malformed input, never a guess.

## Token grammar (as data)

- whitespace: space, tab, `\r`, `\n`
- comments: `#` to end of line (the generated corpus carries none;
  hand-written claims may)
- atoms: maximal runs of non-space, non-paren characters; a `"`-led
  atom runs to its closing `"` and keeps the quotes on the token —
  quote-stripping is a DECODER concern (sx.c only reads)
- parens: `(`, `)` — lists nest

## Claim shape

    [flow-eval] ( (entry NAME (ARG EXPR)*) (fuel INT)
                  (result EXPECTED) (graph (def NAME CALLABLE)*)
                  (oracle (leaf NAME ((A V)*) RESULT)*) )

`[flow-eval]` is a literal marker line-prefix, not a token — the
reader refuses anything else (including `[flow-eval-skip]`).

## Refusal discipline (twin: FlowCheck's sx* total decoders)

- unbalanced parens, stray `)`, empty claim → refuse
- the s-expr layer knows NOTHING about koru — a claim-shaped
  mistake passes sx and dies in wire.c's decoders; that boundary
  is deliberate (sx is grammar, wire is contract) -/
