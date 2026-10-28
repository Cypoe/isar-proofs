/-! # korufe/parse.c — surface → C-AST, pinned

Recursive descent over the real koru surface subset.  Every
construct the parser builds must survive astio's canon-shape JSON
round trip and lower's contract checks; every refusal names the
axis koruc names (or "out of subset" when it doesn't exist there).

Unary `-`/`!` bind at POSTFIX precedence — koru's parsePrimary
takes the operand at primary level, so `-(7) / 2` is
`(negate 7) / 2`, never `negate (7 / 2)`.  An earlier version
parsed the operand as a full expression and silently produced a
different program; the 011-013 emit corpus rows caught it.
Unary results take no postfix (koru refuses `-(a).b` the same way).

Field types accept `[]const T` — koru's slice spelling — alongside
bare identifiers; the bracket pair + `const` + element ident is
consumed and stored as the composite name (types are documentary
here: the wire is untyped and lower reads only field names).

## Item kinds (Item.kind)

| kind | source shape                    | ast.json item     |
|------|---------------------------------|-------------------|
| 0    | `import a/b`                    | `import_decl`     |
| 1    | `tor n {p: T} \| b T -> R`      | `event_decl`      |
| 2    | `n -> expr`                     | `immediate_impl`  |
| 3    | `n = head(args) \| arms`        | `flow` + `impl_of`|
| 4    | `head(args) \| arms` (toplevel) | `flow`, no impl   |

## Arm / node grammar

- `| tag bind when guard -> produce` | `=> ctor [payload]` |
  `|> inv` | terminal (line ends)
- `|>` chains: `|> a(): d |> b(d) |> c()` — `inv: name`
  (`return_binding`) binds into the NEXT step's arm; a trailing
  retbind with no continuation refuses
- `|>` after `|` rows at one level refuses — koru itself gives it
  no source spelling; `|` under a `|>` step needs indentation
  scoping, a named gap
- jump `@label(args)`; arm `kind` 0 terminal / 1 produce /
  2 ctor / 3 invoke / 4 jump

## Parity refusals (checked at parse, not lower)

`| *` retired deref (position-adjacency), `|* ->` bare residual
produce (metatype axis), `x: x` redundant pun + duplicate labels
(PARSE005), `when(` call-shaped guard, single-variant unions
(PARSE003), `{{` interpolation, calls in expressions (KORU104 —
builtins spell `@name(...)`, admitted). -/
