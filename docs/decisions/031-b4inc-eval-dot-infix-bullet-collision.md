# 031 — b4inc_eval proven; `·`-infix/bullet collision is a project trap

## What landed (scratch `_spec_fixr_work.lean`, all green)

- `nibsucc_eval` / `nibis15_eval` — `decide`-table nibble ops
- `incb_eval` — `INCB·(byteLit lo hi) →* pairLit (byteLit nb) (boolLit carry)`
  via inside-out normalization (normalize `nibsucc`/`nibis15`-apps in
  argument position *before* enclosing `pairSrc` heads collapse — there is
  no under-binder congruence)
- `pairLit_apply`, `boolLit_sel`, `b4incK2_apply`, `shift_zero`,
  `subst_shift_succ` — small de Bruijn/selection lemmas
- `emitCells_nf` — emit list → `scottList`
- `b4inc_peel` — the four-cell peel (17 hsteps)
- `b4inc_level_run` — one carry level: `INCB·B·K2 next emit`
  reduces to `aps (boolLit carry) [next', emit']` with concrete substs
- `incBytes` — semantic carry chain on `List (Fin 16 × Fin 16)`
- **`b4inc_eval`** — `LRed (aps b4incL [b4Lit [x0..x3]])
  (scottList ((incBytes [x0,x1,x2,x3] true).map (uncurry byteLit)))`.
  Axioms `[propext, Quot.sound]` only.
- `#eval` witnesses: `0+1` lo-increment and `0xFF+1` carry propagation both
  read back `nibLit 1` in the right cells.

## THE TRAP: `·` is both bullet and SK.app/ITerm.app infix

`Kernel.lean` defines `infixl:70 " · " => SK.app` and `=> ITerm.app`.
A tactic that *ends in a bare term* (`exact hnf3`, `refine f a`) followed
by a `·`-bullet on the next line gets the `·` eaten by the term-parser as
`hnf3 · X` — producing "overloaded `SK.app`/`ITerm.app`" errors, spurious
`⊢ SK`-typed metavariable goals, and downstream "unexpected identifier;
expected command" parse cascades.

**Rule:** before a `·`-bullet, end the preceding tactic on a keyword or
`]`/`}` — never a bare identifier. `assumption` in place of `exact hnfN`
fixes it (the goal is already the `have`d term). This cost ~10 compile
rounds of increasingly bizarre `SK`-typed-goal errors; the actual goals
were always well-formed `LRed`.

## What this unblocks / next

`b4inc_eval` is the deepest leaf of `LENB4 = FOLDL (λa e. B4INC a)`.
`foldl_red`'s `hstep` is `∀ acc e` unrestricted — `B4INC·acc` only
normalizes on `b4Lit`-shaped accumulators, so `lenb4_eval` needs an
**invariant-parameterized** variant (`Inv acc → LRed (st·acc·e) (σ acc e)
∧ Inv (σ acc e)`), the same induction with `Inv` threaded instead of bare
`closed`. That is the next extension; then `lenb4_eval` is one line.

After that: `PADLIST`/`U64` leaves → `pack2Of`-stage assembly → the other
stages share the same leaf inventory.
