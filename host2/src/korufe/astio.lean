/-! # korufe/astio.c — the ast.json boundary, pinned

Two directions over ONE shape — the canonical `program.ast.json`
layout koruc's `--ast-canon` emits (keyed-dict, `plain_value`
strings).  korufe writes parse output and reads it back for
`--lower`; the round trip is the fidelity check, since koruc's
writer and korufe's agree on the shape but not the bytes.

## Writer (surface AST → canon JSON)

- `module_annotations:[]`, injected `import std/compiler` first
  (the real frontend does this), `items:[...]`,
  `main_module_name`, `parts:[]`
- `event_decl`: `input.fields[{name,type,...}]`, `branches[{name,
  kind,payload:{fields:[]}}]`, `return_type`
- `immediate_impl.value.plain_value` = the expr re-rendered as
  source text (canon stores source strings, not expression trees)
- `flow.invocation.{event,args[{name,value}],variant,
  return_binding}`; `continuations[]` per arm, nested `|>`
  chains recurse
- `location` lines approximate — fidelity is structural

## Reader (canon JSON → C-AST for --lower)

- `jparse`: minimal total JSON reader (escapes: `\"` `\\` `\n`
  `\t` only — the subset never spells more)
- `expr_from_src`: `plain_value`/`value`/arg strings re-parse
  through the SAME korufe expr parser — round-trip fidelity is
  structural, not string equality
- `arm_from_ast`: `branch` `""` = chain arm; `binding` =
  retbind/threaded bind; `continuations` recurse -/
