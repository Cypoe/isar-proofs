# 032 — programOf evaluated: PSeg/OSeg segment model, generated proof
terms, stuck-form outer-lambda bridge

Status: landed green (`bea1a4a`, SpecVocabulary +862 lines). Completes
the emit-stage evaluation chain `resolve → symbols → program →
assemble → pack` at the `program` vertex: `programT` is proven to
reduce to the *semantic* fragment list, not just to a term.

## What was proven

```
program_eval :
  LRed (aps programT [boolLit fuse, optionLit fuel, rbbT, cbT, nbT])
       (scottList (progSem fuse fuel (progSegs rbbT cbT nbT)))
```

`programT` is the generated literal `λfs λfuel λrbb λcb λnb. <21-seg
spine>` (outer `OSeg` list: 19 `frag` cells + `stS`/`bDS` fs-selects;
inner `PSeg` lists: `cell` items + `fuse a b` branches + `fuelR`
maybe-branches). `progSem` selects per segment: fuse picks a/b items
by the Church bool, fuelR picks `[]`/`items.map (subst v 1)` by the
Maybe term. `progBody_eq : progBodyOpen = osegChain segs nilL` is
`rfl` — the segment decomposition is verified structural identity of
the emitter output (Python round-trips `rebuild segs == program_expr`
before emitting).

Axiom footprints: `program_open` `[propext]`; `osegChain_eval`,
`closed_progSegs`, `program_eval` `[propext, Quot.sound]`.

## The two load-bearing tricks

**1. Generated proof terms, never simp on the literal.** A `simp`-based
`closed_progSegs` over the ~850KB body was killed at ~93 GB — simp
builds per-node proof terms for every subterm it touches. The
closedness proof is instead *emitted* by `_emit_prog2.py` walking the
same AST that emits the term: `List.forall_mem_cons.mpr` membership
chains × `closed_appD` and-trees × `closed_*_any` leaf lemmas ×
`decide` `.var` leaves × `closed_mono hyp` for runtime params ×
`closed_subst` for fuelR's `subst v 1` clause — ~2MB of proof text,
52k `closed_appD` nodes, constant working set. Same trick applies to
any future generated-literal lemma: **prove with structure, not
search** — the emitter knows the shape, so it emits the proof.

Empty-forall tails: `List.forall_mem_nil` takes `p` explicitly and
anonymous-constructor fields don't propagate it — the robust tail is
`fun x hx => False.elim (List.not_mem_nil hx)`.

**2. Stuck-form bridging for outer beta-substitution.** `hsteps 5`
over `programT · fs · fuel · rbb · cb · nb` does NOT reach
`progBodyOpen`: `subst s c` inserts `shift c 0 s`, and an outer
`subst` application whose scrutinee is a `shift`-applied *variable*
stays a stuck meta-application. The bridge is a third generated term,
`progBodyStuck` — the literal `subst`/`shift` residue — proven by
`rfl` (`hu`), then collapsed to `progBodyOpen` by `simp only` with
`shift_of_closed0`/`subst_of_closed0` instances (`hu2`). Any binder
body containing runtime params needs this three-step
(`rfl`-evaluate → name the residue → collapse) instead of hoping one
`rfl` reaches the clean form.

## Cost note

Full-module build took ~68 min (4082s) — dominated by kernel
whnf-evaluation of `subst`-chains on 850KB terms in `hu`'s `rfl` and
the `progBody_eq` structural check. Compile time, not proof size, is
the binding constraint for generated-literal work at this scale.

## What's next

Host classification (term-level host predicates + structural
imports; fuel fail-safe), then the C-target dialect — a second
target *record* reusing the same stage machinery, not a second
compiler.
