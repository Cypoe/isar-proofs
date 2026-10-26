---
type: frag
id: 0036
provenance: devin-cli
ts: 2026-10-28
tags: [koru, host2, frontend, ast-json, spec-rows, quotient-maps, realizations, assembly]
---

# 0036 — host2 correction: real koru syntax, real AST, declared spec rows

## What was wrong

Frag 0035's `.k` files carried `[flow-eval]` s-expression claims —
the *verification wire*, not koru source. The corpus conflated
authored syntax, the AST boundary, and the spec layers: no
`program.ast.json`, no quotient-map rows, no realization catalog, no
target/assembly rows. `kemit.k` was an s-expr program, not a koru
program.

## What changed

**`.k` files are real koru.** `tools/DumpKoruFixtures.lean` gained a
surface printer (`KProg` → `tor NAME { a: T } -> T` decls + `name ->
expr` bare impls + `name = #label? head(args)` + `| tag bind when(c)
step` arm rows + `tor` decl-only for thunks). `kemit.k` is the
compiler spec spelled in koru:

```koru
tor emit { src: program } -> string
emit -> if((src.tag == 30) && (len(src.kids) == 3) && ...)
    ("int main(void) { return " ++ intToString(...) ++ "; }")
    else (0).x
```

**`host2/src/korufe.c`** (new, ~1800 lines, C99 `-Werror` clean) —
the surface frontend, two modes:

- `korufe FILE.k` → `program.ast.json` in the canonical shape
  (`--ast-canon`'s keyed-dict layout: `event_decl` / `immediate_impl`
  / `flow` / `import_decl`, `plain_value` source strings) — the
  honest AST boundary.
- `korufe --lower ast.json cases.json KEY` → the `[flow-eval]`
  claim. The s-expr wire is now the *lower layer* only, produced by
  lowering, never authored.

Subset is declared and refuse-first: `=>` impls, `! as` bare
dispatch, `inv : bind`, top-level flows, nested continuation arms,
proc bodies, `{{}}` interpolation all refuse *naming the axis*.
Divergences declared: `=> b` lowers to `(ctor b (lit (cell)))` —
koru's `payload:{fields:[]}` is the empty cell; `0.5` parses to
exact `(float 1 2)`; `lit[T]` annotations (`0[i64]`) stripped.

**`host2/specs/` rows** — the missing layers as data:

- `cases.json` (generated) — per-case entry/fuel/expect/emit/oracle
  rows; the claim's metadata lives here, not in file comments.
- `quotient-maps.json` — the six pipeline maps
  (surface→ast→claim→result→quot/c99→image), each naming mechanism
  and authority.
- `realizations.json` — interface→row→arm→mechanism catalog in the
  `std/realize` vocabulary, including the declared provider gap
  (no Lean-side surface parser).
- `assembly.json` — target rows: `c99` (toolchain the cc leg reads —
  CompCert-subset constraints), `x86_64-pe` and `compcert` deferred.

**`check.py`** — pure orchestration over the four legs:
parse → lower → claim → emit → cc+run, plus refusal probes. The cc
leg reads cc/flags/run semantics from `assembly.json`'s c99 row.

## Verified

`python host2/check.py` — **46 pass, 0 fail, 0 skip**: 2 build legs,
10 parse+lower+claim per file, forged drifts (exit 4), 8 emit legs
(kemit-as-data through real koru), cc+run legs exit `5` and
`4294967293`, 4 refusal probes.

## Trade-offs (stated, not absorbed)

- **Two pieces of host logic now**: `korufe.c` joins `krun.c` as
  handwritten bootstrap — same contract: it dies when a
  koru-spelled frontend self-parses. Its subset is declared in the
  file header and refuses everything else by name.
- **The canon AST shape is followed, not shared**: korufe emits the
  same item structure `koruc --ast-json` produces for the subset,
  but it is a second implementation — field-level fidelity is
  checked by the round trip (parse → print → parse → same claim),
  not by a shared schema. Full-language authority stays `koruc`.
- **`residue`-style gaps remain**: `when` spelling, `!`/`as`
  markers, `inv : bind`, and nested continuation arms are koru
  surface the subset doesn't yet spell — refused, not approximated.
- **`=> b` → `(ctor b (lit (cell)))`**: koru's tag-only produce
  carries an empty-cell payload in this lowering — matches
  `payload:{fields:[]}`; differs from wire-`none` only for
  bind-on-payload consumers. Named axis.

## The rung after this

Subset growth along two axes — grammar arms (nested `|>` conts,
`: bind`, `!`) and the emit subset (more `emitC99` match arms ↔
`shapeOk` conjuncts ↔ corpus rows) — plus `cases.json`-driven
oracle leaves already exercised in probes. `FlowEvalCongruent` and
the `compcert` assembly row remain the heavy rungs.
