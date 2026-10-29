---
type: frag
id: 0053
provenance: ISAR.KoruEmit kChain + KoruProgEmit reachables + 905_kchain leaf
ts: 2025-10-29
tags: [kchain, composition, declared-data, emitProgC, reachability, stubs, gate]
---

# kchain: the composed lane as a declared shape

`905_kchain` is the full reifier→emitter chain spelled as one
koru program — not yet *running* end to end, but the whole shape
is declared data now:

- `prefixGraph` renames invoke/head targets (`jump` stays
  `#label`-local) so `kAst` and `kLow` ride along as `a-*` / `l-*`
  subgraphs — `main`/`peek` collisions resolved by data, not by
  hand-editing 171 decls.
- `chain` is the wiring spine: `a-main(chars:src)` rows flow into
  three document legs — `low-txt` (row-text→ast.json, the
  authority-mirror artifact), `wir` (rows+src→claim sexp, the
  `lower.c` mirror — ast.json is *not* on the emit path), and
  `emt-txt` (claim text→C).
- The three legs stand as **arm-less subflows** whose heads
  resolve to `unrealized` — dispatch finds no arm, the refusal
  names the leg by position.  Refuse by default; the tor name IS
  the axis.

The surface file carries the entire union, so `kw`/`kwj`/`kwc`
race the *composition itself* against koruc: 5462 rows agree,
ast-json and ast-canon both identical.  `chain` with args walks
`a-main` for real and refuses inside `low-txt` — claimed and
observed.

## emitProgC learned two honest things

- **Reachability pruning** (`armRefs`/`callableRefs`/`reachables`):
  the generated C is the reachable subgraph from `entry`.  The
  unwired `l-*` graph stays in the declaration but doesn't
  materialize as dead functions — it appears automatically when
  `low-txt` invokes `l-main`.  Closure needs `g.length` steps at
  most; each pass either fixes or grows.
- **`(void)ce` for closed stubs**: an arm-less + arg-less subflow
  never evaluates head args or dispatches, so `ce` is unused —
  the uniform `E *` ABI stays, the body says so explicitly.

Both were forced by `-Werror` under clang *and* ccomp — the
gate's strictness caught real properties of the emitted
program, not lint noise.

## Text-mediated composition is the honest shape

Every boundary in the realized subset is a document: composite
values can't be constructed inside eval (wire `(cell …)` is
literal-only, `++` is string-only).  So the chain passes
text — source → row-text → ast.json/claim → C — which is not a
workaround but the literal reading of "data crosses boundaries".
The value-mediated alternative (rows→cells→emit in-language) is
the same bucket-3 territory as `!`-resume: declared, refused by
name, not smuggled.

## Trade-offs stated

- `905_kchain` exercises `a-*` only; `l-*` parses and typechecks
  in the union but is dead in `kchain.c` until `wir`/`low-txt`
  land.  That is the point of the scaffold: the seam is visible
  in ISAR before the pieces exist.
- `unrealized` returns the string `"unrealized"` (authority
  typechecks `chain`'s string return) — the stub's output is a
  marker value, never consumed downstream in the realized path.
- `kli` skips 905 on the same named trampoline axis (0047) as
  the other self-parse-size files.
