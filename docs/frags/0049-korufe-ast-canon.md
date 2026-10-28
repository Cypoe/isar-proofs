---
type: frag
id: 0049
provenance: korufe --ast-canon + check.py kwc legs
ts: 2025-06-09
tags: [korufe, ast-canon, lossless, mirror, authority, gate]
---

# korufe --ast-canon: the C lane emits the full-shape AST

`korufe` gains `--ast-canon FILE.k` — the *canonical* authority
schema (`{items, main_module_name, module_annotations, parts}`,
zig's reflective `ast_json.serializeCanon` dump: tagged-union nodes,
every struct field, trivia-stripped). The `kwc` gate legs race it
against `koruc --ast-canon` on every corpus `input.k`: **44 files,
deep-equal JSON with zero normalization** — canon carries no
locations, so there is nothing path-dependent to erase.

## Why canon is the right verification boundary

The readable view (frag 0048) is a designed interop projection —
and lossy: retbind names drop (`binding: null`), label-jump args
drop, produce `if` flattens to text. Canon is the COMPLETE post-
parse tree and keeps all three:

- `invocation.return_binding: "c"` — the `f(): c` chain name;
- `label_jump` args survive (e.g. `loop: i` keeps `i` in
  `args[].value`);
- `args[].parsed_expression` / `condition_expr` carry the real
  expression tree (`{node:{binary:{op:"less",...}}}`), which kills
  the last conformance axis: no pretty-printer is involved anywhere
  in canon.

That makes canon the document the *typed-koru* lane should target:
rows → trees is a data transform — the future reifier emits canon
and gets three-way agreement (zig authority ↔ C korufe ↔ koru-spelled
parser) on the full shape, not a projection of it.

## What the mirror actually surfaced

- **Text fields are raw source spans, not a printer.** `value` for
  `1+2*3` is `'1+2*3'`; `condition` preserves `v>0 && v  <  9`
  whitespace verbatim. The whole `zexpr` paren-dialect only agreed
  because corpus sources are generator-normalized. korufe now
  carries `KExpr.lo/hi` byte spans (trailing `snl` walk-back so the
  high endpoint is the last non-newline token) and emits slices —
  matching upstream's actual semantics, which is stricter than the
  old printer: it now agrees on *any* source, not just normalized
  ones. The `grouped` node is real too: source parens parse to a
  `grouped` wrapper (tag 14, transparent to `lower.c`, visible to
  canon).

- **Trees live at exactly two sites.** `parsed_expression` (invocation
  args) and `condition_expr` (when-guards). Produce values, ctor
  fields, and `immediate_impl` values stay raw text — `ExprNode`
  has no array/cell-literal variants, so `[10, 20][0]`-shaped args
  get `parsed_expression: null` and `korufe` refuses to emit a tree
  it can't (cell/array/anon-call → `null`, matching upstream).

- **The `["if"]` invocation needs no synthesis.** `-> if(((d==0)
  &&(s==1)))` parses the cond to a `grouped` node from source parens;
  the arg is just a normal arg — raw span + natural tree. An earlier
  guess (synthesized grouped wrapper) over-wrapped and produced
  `(((…)))`; the probe on `902_ksexp` caught it.

- **Analysis fields are corpus constants.** `is_pure`/`is_transitively
  _pure` are `true,false` on every flow, `false,false` on every
  event decl, absent on impls; `impl_of` is the flow's own declared
  `tor` path (even top-level flows name `main`). We emit the
  constants — if upstream ever *computes* a different value the race
  flags the file, which is the correct escalation: analysis output
  becoming non-constant is a named axis, not silent data.

- **Reflected fields emit their corpus defaults** —
  `binding_annotations`, `binding_marks`, `destructure`,
  `catchall_metatype`, `is_transformed_subtree`, `phantom_type`,
  `source_value`, `expression_value`, `had_explicit_label`,
  `inserted_by_tap`, `from_opaque_tap`, `site_of`, `super_shape`,
  `preamble_code`, `inline_body`, `return_destructure` — all
  null/false/[] across the corpus. Emitting the default is cheap;
  the falsifiable contract is that any real occurrence diffs.

## What stays unexercised (named axes)

- `import_decl`/`module_annotations`/`parts` — no corpus file
  carries real imports; the writers emit the empty shapes and the
  race can't yet reach the populated path.
- `function_call` expression nodes, `bool` literals, bare ctor
  `=> name` (`fields:[]`), `resume_arms` non-null, qualified
  invocation paths (`module_qualifier`), `had_explicit_label` —
  vocabulary confirmed from `ast.zig`, shapes emitted on a
  best-effort basis until a corpus file exercises them.
- Multi-line-expression spans: `lo/hi` walk back over trailing
  newlines only; an arg span *starting* mid-line is correct, but
  exotic trivia inside is whatever the tokens say.

## The lane picture now

```
Z authority   koruc --ast-json ─→ kwj ─┐        koruc --ast-canon ─→ kwc ─┐
C lane        korufe --ast-json ───────┘        korufe --ast-canon ───────┘
              korufe → canon → --lower → claim → krun
koru-typed    kast → row wire ─→ kw (row-identical)
Lean          ISAR spec → emitProgC → the C binaries themselves
```

Three independent evidence boundaries, one corpus: rows prove the
koru-spelled parser's structure, readable JSON proves the interop
document, canon proves the **full** parse — bindings, trees, jump
args — with no projection and no normalization.

## Honest scope

Canon is a reflective dump of zig's internal structs, built for
upstream's printer-roundtrip harness — its schema is zig's, and
mirroring it is conformance to *that* contract. The race is the
whole argument: 44/44 deep-equal means the C lane now re-derives
the complete tree the authority produces, and any field the corpus
hasn't yet made non-default is a flag the race will raise the
moment it does.
