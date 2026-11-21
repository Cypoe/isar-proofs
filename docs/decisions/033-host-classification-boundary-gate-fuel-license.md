# 033 — host boundary classification: dialect-parametric WF gate,
fuel as fail-safe not proof

Status: scratch validated green; spliced into `SpecVocabulary.lean`
after `program_eval` (pending full rebuild + commit).

## The three classes

`HostClass = proven | budgeted | rejected` — the boundary split from
the roadmap note:

- **proven** — witness-carrying: `Proven t := ∃ nf, LRed t nf`.
  `program_proven` closes `program_eval` into exactly this shape.
  Fuel never appears in the statement — on the proven path fuel is
  a bug fail-safe, not the termination argument.
- **budgeted** — external input that passes the dialect's import WF
  (closed + self-application-free). The fuel bound is the contract.
- **rejected** — fails import WF: refused structurally at load time,
  not saved by runtime fuel.

## The gate is dialect data

```lean
structure BoundaryGate (T : Type) where wf : T → Bool
def classifyExt (g : BoundaryGate T) t := if g.wf t then .budgeted else .rejected
```

`lambdaGate`/`isarGate` instantiate it: `wfImportL t = closed 0 t &&
!hasSelfApp t`, `wfImportI t = !hasVarI t && !hasSelfAppI t`. The WF
predicate is a per-dialect parameter — no lambda-specific
assumption is baked into the boundary.

## `hasSelfApp` is the divergence detector

`hasSelfApp (.app f x) := decide (f = x) || hasSelfApp f ||
hasSelfApp x` — the `t·t` pattern is the vocabulary's only
divergence-capable shape; the proven fold heads bound their
self-applications inside Scott-list spines, so on the *external*
boundary bare `t·t` is the degenerate shape refused at import.

Supporting lemmas proved shift-invariance rather than restricting
the predicate to the un-shifted surface (Scott cells wrap arguments
in `shift 2 0`):

- `shift_inj` — `shift d c` injective: `shift` of differing terms
  can't collide (needed so `decide (shift f = shift x)` reduces to
  `f = x` inside `hasSelfApp_shift`).
- `hasSelfApp_shift` — `hasSelfApp (shift d c t) = hasSelfApp t`.
- `hasSelfApp_scottList` — a Scott list of selfApp-free cells is
  selfApp-free; the spine's own `t·t` checks compare `.var 0` against
  `shift 2 0`-headed terms, which can never coincide.
- `wfImportL_scottList` — emitted data passes the import gate.
- `classifyExt_wf`/`classifyExt_notwf` — the decidable split.

## Proof notes (for future selfApp work)

- `shift_inj` needs `induction t generalizing c` (binder cases shift
  the cutoff to `c+1`); `split_ifs at h` closes all impossible
  branches itself — trailing `cases h`/`simp` is dead code the
  linter flags.
- `decide`'s `Decidable` instance arg blocks `congrArg decide`;
  rewrite inside `decide` via a local `↔` + `simp only [hiff]`.
- `show` can't unfold `def`s' `Bool`-combinator spelling
  (`!x` vs `decide`) reliably — prefer `simp only [def]` then
  `rw` + `rfl`.

## What's next

C-target dialect — a second target *record* reusing the same stage
machinery (`wf`/`classifyExt` are the instantiation points), then
the C reducer kernel as second host and Python-vs-clang behavioral
cross-verification.
