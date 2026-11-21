# emit() → term chain: scope

`seed.emit()` is Python orchestration over resolved catalog records:

```python
isa, rts, tgt = toolchain.resolve(tc)
prog = rts.program(program, R)  if tc.path == "native" else rts.program(R)
text, labels = isa.assemble(prog, tgt.symbols(rts.imports, rts.data_slots),
                            base=tgt.text_base)
return tgt.pack(text, labels, rts.imports, rts.data_slots, R)
```

Every stage already exists at term level and is gated:

| emit() step            | term stage                          | gate |
|------------------------|-------------------------------------|------|
| toolchain.resolve      | resolveOf SPEC name                 | G9c  |
| rts.program(R)         | programOf FS FUEL RBB CB NB         | G9e  |
| tgt.symbols + sections | linkOf IMPORTS SLOTS                | G9h  |
| isa.assemble           | assembleOf PROG (L (K I)) BASE      | G9f  |
| tgt.pack               | pack2Of (A K) (L K K) (L (K (K I))) | G9g/h|

So `emitOf` is a small let-chain over existing stage terms — the
composition is mechanical. The real scope is everything *around* it:

## Decisions that are actually open

1. **Per-toolchain vs toolchain-parametric.** All stage terms are
   generated per-toolchain (programOf is baked from the
   x86_64.win64.lo routines record). A per-toolchain `emitOf` is
   honest now: generate `emitOf_native_x86_64_pe` the same way.
   A parametric `emitOf TC` requires the catalog to carry the stage
   *terms* as data — resolveOf currently returns field-name strings,
   not λ-closures. That is the Futamura-P1 move (catalog-as-data →
   residual emit chain) and is the real target, but it is a separate
   lift: SPEC entries would need to embed or name stage terms, and
   specialization produces the per-toolchain chain.

2. **Honest refusal at term level.** `emit()` refuses when
   `rts.abi ≠ R.abi` or the catalog entry is unrealized — it must
   never silently fall back. Term-level: `EQSTR abi_rts abi_R` →
   `(TAG_OK image) | (TAG_UNREALIZED name)`. Needs a refusal
   convention the decode layer understands.

3. **The `path` split.** runtime path: `programOf` takes only R
   fields (done). native path (xdu.x86_64.pe): `program` — the
   loaded program record — is an additional input, so `programOf`
   needs a variant taking the program as term data (program records
   are already encodable: they are the same shape resolveOf walks).

4. **Staged execution is not optional.** The single-arena composition
   of link+assemble+pack is measured infeasible (>50GB, the 027/028
   retention pathology — arena pinning, not correctness). `emitOf`
   evaluated in one fixpoint is the *specification*; execution is
   staged: each stage boundary serializes the NF (the .lo seam,
   `_probe_g9g_e2e_staged.py` is the template) and re-imports into a
   fresh arena. The emit driver is the staged pipeline; the term is
   the composition statement.

5. **Labels.** assemble produces `(text, labels)`; pack ignores
   labels (kept for diagnostics). pack2Of already drops them — no
   term work, but decode/oracle must match.

## What emit() adds that is not yet a term

- toolchain resolution + realized-guard + path dispatch (1–3 above)
- the abi check
- nothing else — assemble/pack inputs all derive from the resolved
  triple and R

## Verification plan

- lo+oracle at mini scale: `emitOf` NF decodes to bytes identical to
  `emit()` output.
- win64 scale via staged arenas (assemble→pack2 e2e staged probe is
  the template; add programOf and linkOf as prior stages).
- Byte-identity against known-good PE shas (default
  b9d0ba34…, fuse_s a021f254…).

## Non-goals

- `host.cogen.emit()` (LoaderPlan → HostPiece wrapper) is a different
  seam — unchanged.
- A single-arena monolithic `emitOf` run is explicitly out; the
  measured arena pathology stands until the sharing/persistent-NF
  work lands.

## Vocabulary normalization — the fuel license (next formal target)

Goal: a theorem that licenses dropping the fuel *bound* on the
vocabulary slice.  Architecture per discussion: fuel stays as
fail-safe on the open boundary (arbitrary λ-source, malformed terms —
the Lafont/HVM degenerate-shape case: rejected at import or bounded
at run), while vocabulary-generated terms carry a termination
witness.

Key structural fact: the vocabulary's ENTIRE divergence-capable
surface is one pattern — `(\f. f f)` self-application bounded by a
Scott-list spine (_FOLDL, _JOIN, _MAP, _NIBS2BYTES).  Everything else
is structural (selectors, nibble tables, pair ops) — bounded unfold
by construction.

Proof shape options:

- **A. Grammar + measure (global WN/SN).**  Define WF over emitted
  terms, show WF closed under LRed, measure decreases.  Hard part is
  closure: intermediate states of a partially-run fold aren't in the
  naive source grammar (instantiated bodies, half-applied steps).
- **B. Per-head eval lemmas (existing pattern).**  `∀ well-formed
  args, LRed (V args) (spec NF)` — termination + correctness in one.
  b4add_eval / append_eval / revL_eval are already instances; each
  emit-stage head gets one.  This IS the verified emit chain.
- **C. Core recursion-scheme theorem + leaves.**  One FixSpine
  theorem for the `(\f.f f)`-over-Scott-spine pattern (measure =
  remaining spine), leaf lemmas for structural heads, composition via
  strictness.  Most of the vocabulary inherits termination from the
  scheme.

**C is landed** (SpecVocabulary.lean, axioms `[propext]` only — fully
constructive, no Classical.choice):

- `fold_run` — `ggbA st (scottList cs) a →* cs.foldl (λacc e =>
  st·acc·e) a`.  The `(\f.f f)` spine unfold, generic in `st`/`cs`/`a`;
  recursion depth = `cs.length` by list induction.
- `foldl_red` — the unreduced-application chain reduces to the
  semantic foldl `cs.foldl σ a`, given a per-step lemma
  `LRed (st·acc·e) (σ acc e)` + closedness preservation.  The
  induction is generalized over a syntactic/semantic accumulator pair
  `X`/`a` with `LRed X a` — that invariant is what makes the cons
  case go through (the LHS accumulator stays a frozen `st·a·c`
  application while σ advances).
- `spine_eval` — composed: `ggbA st (scottList cs) a →* cs.foldl σ a`.
- `fold_eval` — the full head shape: `foldlL·st·l·a →* cs.foldl σ a`
  whenever `l →* scottList cs`.  This is the recipe every fold-family
  head plugs into.

Proof that the abstraction pays: `fold_read` (the stepConsL fold
readback) collapsed from a 28-line hand induction to a one-line
`spine_eval` application + `List.foldr_reverse`.  Per-head cost is
now exactly `hstep` — a bounded `LRed_of_hsteps` unfold — plus
`closed 0 st`.  That is the answer to "07 separate heads is
tail-chasing": the heads don't carry termination proofs at all, they
carry per-step lemmas.

**Right-spine mirror landed** (commit 8cbda6f): `_JOIN`/`_MAP`/
`_PADTO` use `l2 z (λh.λt. st·h·(g·g·t))` — recursion on the tail
INSIDE the step, sitting in argument position where `hstep` never
descends.  `rcell_unfold` therefore carries the raw `gsRA`
double-application and closes it via one `LRed_app_right` congruence.
The rest is symmetric: `fixrG`/`RGR`/`gsRA`/`rgrA`/`fixrA`,
`spine_run_r`/`closed_foldr`/`foldr_red`/`spine_eval_r`/`fixr_eval`.
`foldr_red` is simpler than `foldl_red` — no accumulator-pair
invariant needed.

`join_eval` is the first head discharged purely by `fixr_eval`:
`JOIN (scottList (map scottList bss)) →* scottList bss.flatten` —
the chunk concat every emit stage is built on.  Per-head obligation:
the 2-step `appendL→appendT` β-unfold.  The semantic-side lemma is
`appendT_foldr_scott` (foldr of appendT flattens) — per-head because
σ's semantics need element-shape hypotheses a pure-LTerm σ can't
express.

Simp-list gotcha worth remembering: keep applied heads (`appendL`)
FOLDED inside milestone simps — `shift_of_closed0` rewrites
`shift k 0 head` atomically; unfolding first scatters the shift into
`shift k 2 body` under binders where no lemma matches.

B and C compose: stage eval lemmas (programOf/assembleOf/packOf/
linkOf) still state `LRed (V args) NF` per head (option B shape), but
their fold cores instantiate `fold_eval` — the induction is shared,
only `hstep` + the σ-readback identity is per-head.

WF as data is the dialect-general point: each dialect carries its
own well-formedness predicate (degenerate-shape detection is an
import-time structural check — closedness, arity, spine-boundedness),
not a λ-specific assumption.

Boundary classification per discussion: proven spine-bounded terms
run proof-backed (fuel = bug fail-safe only); queries, residuals,
loader input are external effects/events and stay budgeted;
malformed/degenerate shapes are rejected structurally at import.
Fuel on the proven path is never the termination argument.

Remaining: `b4fold_run` still carries its own interleaved induction
(its σ isn't a plain foldl — the state is `pairLit (b4Lit drop)·carry·acc`,
a candidate refactor but it works as-is); stage eval lemmas for
programOf/assembleOf/packOf/linkOf are the work list — each now
plugs `fold_eval` rather than re-running the spine induction.
