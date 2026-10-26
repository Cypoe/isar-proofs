/-! # korufe/lex.c — real koru tokens, pinned

The lexer produces a token stream the parser walks; koru is
line-oriented, so newline is a real token (`nl`) — arm payloads
and item boundaries are line-scoped.

## Token kinds (C enum order)

| kind | meaning              | notes                              |
|------|----------------------|------------------------------------|
| 0    | ident / keyword      | `a-zA-Z0-9_-`; `-` continues an    |
|      |                      | ident (koru word separation) only  |
|      |                      | when an ident char follows —       |
|      |                      | `a - b` keeps `-` a punct          |
| 1    | int literal          | digits                             |
| 2    | float literal        | `d.d` — parses as exact rational,  |
|      |                      | never f64                          |
| 3    | string literal       | `"..."` — `{{` interpolation       |
|      |                      | refuses at lex                     |
| 4    | punct                | see table below                    |
| 5    | eof                  |                                    |
| 6    | nl                   | newline, position-bearing          |

## Punct tables (as data)

- two-char: `->` `=>` `|>` `==` `!=` `<=` `>=` `&&` `||` `++` `..`
- one-char: `(){}[],:|+-*/%<>=!#.@&`

## Koru parity pins

- `|*` is `|` + `*` tokens; the glued/retired distinction is the
  token POSITION adjacency check in parse.c, not the lexer
- `#` starts punct (labels `#loop`); `//` to EOL is comment —
  `#[` doc-comments are out of subset upstream anyway
- quoted-`@`: `@name` builtins lex as `@` + ident, `@label` jumps
  the same — the parser separates them by context -/
