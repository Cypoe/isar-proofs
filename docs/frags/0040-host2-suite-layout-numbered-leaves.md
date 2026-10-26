---
type: frag
id: 0040
provenance: devin-cli
ts: 2026-10-26
tags: [koru, host2, suite-layout, convention, bend-style, cleanup]
---

# 0040 — the suite layout: numbered leaves, convention enforced

## What changed

`host2/specs/` is now a real suite, not a flat pile. Every case is a
leaf folder (`input.k` + `cases.json`), numbered like koru's own
regression tests and bend-style self-contained:

```
specs/
  tests/<GGG>_<group>/<NNN>_<leaf>/   generated (DumpKoruFixtures)
    100_flow/    000_subflow … 008_index
    200_emit/    000_accept_int … 007_refuse_thunk, 100_kemit
    800_forged/  000_wrong_expect
    900_wire/    000_catchall_tag, 001_catchall_bare  (cases.json only)
  benches/001_fib_walk/                was ported/bench — fuel-heavy
  ported/{lantern,greet}/              authored programs, named like
                                       koru's own examples/
```

`tests/` groupings are honest: the former `case-0..7` were never
kernel tests — they are `koruEmitCorpus`'s emission-fixpoint shapes
(accepts + every `kEmit` refusal), so they live in `200_emit` with
names that say what they prove (`refuse_entry`, `refuse_graph`,
`refuse_thunk`). `case-forged` → `800_forged/000_wrong_expect`.
Wire rows → `900_wire` — the group number itself says "no surface".

## The convention leg

`check.py` walks `tests/ + benches/ + ported/` uniformly — any dir
holding `cases.json` is a case dir — and enforces:

- `tests/`+`benches/` dirs match `NNN_name` (3-digit + snake)
- surface rows carry `"file":"input.k"` that exists in the leaf
- wire rows carry `"claim"` and **must not** name a file
- leaf `cases.json` rows key by leaf name

A convention violation is a `layout` FAIL, same class as a semantic
one — ordering is part of the spec, not decoration.

## What got deleted

`specs/corpus/` (18 flat `.k` files, mixed `case-N`/`flow-*`/`kemit`
naming), the flat `specs/cases.json`, `ported/bench` (moved). The
generator now emits per-leaf folders; `korufe --lower` resolves
rows against the leaf's own `cases.json`.

## Also renamed

`koruEmitCorpus` leaves renamed by *what they prove*, not position
(`case-4` told you nothing; `004_refuse_graph` does). `kemit.k` →
`tests/200_emit/100_kemit/input.k` — the compiler program sits
inside the suite it emits claims for.

## Verify

`python host2/check.py` → **148 pass, 0 fail, 0 skip**
(was 121: +layout leg, +22 koruc-authority legs now that *every*
surface file is blasted, wire/emit/refusal legs renumbered).
Battery 31/31, spec_project in sync.
