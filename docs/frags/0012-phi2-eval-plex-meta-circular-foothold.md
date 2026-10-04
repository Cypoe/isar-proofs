---
type: decision
id: 0012
provenance: megaplan (~/.devin/plans/plan-83fea387acdafe69.md);
  frag 0011; host/rel_eval.py (oracle); phi2/eval.phi
ts: 2026-10-13
tags: [phi2, eval-plex, meta-circular, enc-terms, reify,
  observational-equivalence, S1]
---
# phi2/eval.plex — the evaluator as corpus data; meta-circular
# foothold: same splits, same order, from a program not the host

S1 of the megaplan: the stepper no longer interprets `eval` — it
*runs* it.  `phi2/eval.plex` is a 20-relation corpus program that
re-implements the relational evaluator over encoded terms, and
`seed.py`'s selftest proves it reproduces the native stepper's
backward-append splits in the same order.  Observational equivalence
on the running program, not just the output bytes.

## What eval.plex is

`phi2/eval.phi` is the authored surface (the encoding contract is
written at its head); `eval.plex` is the canonical bundle.  Terms
are data: `('atom,⟨ATOM(8,b),ATOM(8,v)⟩)`, `('var,id)`, `('pair,a b)`,
plus surface-level tags `('nvar,x)`/`('sym,x)` for the AST layer the
evaluator destructures.  Substitutions, environments, and the
alpha-renaming map are all PAIR-spines of `PAIR(key,val)` — newest
first, walked relationally.

Relations, in layers:

- **subst machine**: `subst_lookup`, `walk`, `walk_res`, `unify_enc`,
  `unify_w` — unification as a tag-cased clause matrix so each
  (u,v) pair hits exactly one clause (disjunction explores every
  matching clause; exclusivity is declared, not emergent).
- **instantiation**: `ren_find`/`ren_fc` — a lazy name→fresh-id map
  with a threaded counter, mirroring rel_eval's ren dict; `inst`
  alpha-renames clause patterns per trial.
- **evaluator**: `env_find`, `eval_call`, `eval_clauses`,
  `eval_clause`, `eval_body`, `eval` — sequential clause traversal
  preserves stream order (the congruence observable).
- **answers**: `reify`/`reify_w` — deep walk producing a
  subst-closed enc term.

Every recursive relation declares `shape self` — the schema contract
holds inside the corpus too (`eval → eval_call → eval_clauses →
eval_clause → eval_body → eval` is an explicit cycle, not smuggled
recursion).

## The check that matters

The selftest builds an encoded `append` def (two clauses, named
vars), an env spine, and an encoded goal `call(append,[var90,var91],
enc<[1,2]>)`, then runs `eval` as a corpus relation.  It yields
three solutions; each solution's meta-subst `s2` is reified through
the corpus `reify` — the evaluator reifying its own answers — and
decoded.  Result: `([], [1,2]), ([1], [2]), ([1,2], [])` — the
native stepper's splits, same order.  That is the S1 bar.

## Two bugs worth recording

- **Encoding discipline is the whole game.**  The selftest's first
  `want` wrapped *raw* `ATOM(8,1)` in `ePair` instead of `eAtom` —
  unification bound it anyway (no type checker), forward decode
  masked it by luck, and `reify_w` correctly had no clause for a
  raw-atom car → empty stream → `IndexError`.  The failure was the
  encoding leaking, and the corpus refused it honestly.  Fixed by
  encoding atoms fully; this is exactly why the encoding contract
  is written at the head of eval.phi.
- **Fuel is semantic; Python's stack is incidental.**  The
  meta-circular search stacks ~10 C-frames per unify step and hit
  the default 1000-frame limit mid-search.  `sys.setrecursionlimit`
  is raised at entry — the honest divergence bound stays fuel
  (empty stream), the C limit is only an implementation parameter.

## What this buys

`eval` is now data the corpus can carry, specialize, and emit.  The
S2 path — `specialize.plex` as a term-level rel, then
`realize`/`cogen` folding maps — consumes `eval.plex` as input, the
same way it consumes `std/append`.  The stepper remains the only
semantics-bearing host code; everything above it is corpus.
