# What Koru actually is — a basis inventory

**Tree pinned:** `w:/src/koru-orchestrate` @ `9f8576850`
(`Cypoe/challenges-orchestrate`); semantic receipts cross-checked
against `w:/src/koru` @ `ea981b295`
(`verify/semantics/FlowKernel.lean`, `verify/holds/HoldsCheck.lean`,
`src/ast.zig`, `src/*_checker.zig`, `docs/CHANNEL.md`,
`docs/koru-verification-path.md`, `tests/regression/`).

This is a survey for talking about Koru with people who will ask "what
kind of system is this" — stated against the checked-out tree. Where a
label from the literature doesn't fit, the misfit is the finding and
it's named.

---

## 0. One paragraph

Koru is a **call-by-value, first-order functional core inside a
branch-dispatch flow layer**: functions (`tor`s) return a three-case
result — a *tagged* outcome (declared branch name + payload), a *bare*
value, or void — and every call site carries the dispatch structure
(arms, guards, continuation chains) that decides what happens next.
On top of that sit: resumable call-site-bound effects (`!` arms),
affine handle obligations (checked statically, re-decided at runtime),
a comptime transform/staging layer, and a cooperative scheduler
composition (`std/pump`). Backends emit Zig and JavaScript; a C99
oracle lane is designed.

## 1. The kernel, precisely

`FlowKernel.lean` mechanizes the flow walker as a faithful subset:

- `Val` = int | float | bool | str | arr | cell(record). First-order
  values; cells immutable; the kernel's value domain has no closure
  case — tors are invoked by name, not passed as values.
- `Result` = `{branch? , payload?}`: exactly three cases. Void results
  cannot dispatch at all; tagged results dispatch by name against
  ordered guarded arms; bare results ignore arm names and guard-select
  in order (catchall under bare dispatch *refuses*).
- Arm nodes: terminal | `@label` jump | invoke-with-nested-arms |
  `=> branch` (tagged constructor) | `-> expr` (bare produce).
- `#label`/`@label` re-enters the flow head — that is the loop
  primitive, so the runtime language is **Turing-complete**; the
  kernel bounds every evaluation with fuel and *proves* `run_mono`
  (more fuel never flips a decided result). Fuel is a resource cap,
  not a semantics change — that theorem is the honest shape of
  "totality" here.
- Serialization **refuses** what the walker doesn't model:
  `!`-handlers, stores, residual catchall metatypes, destructured
  arms, function calls in expression position, nested labels.

## 2. What kind of system — the academic map

### 2a. Branch dispatch — named-sum returns + ordered guards

A `tor` declaring `| ok v | err e | retry` is a **sum type whose
injectors are named, user-owned vocabulary**. The caller's arms are
ordered, guarded (`when`) patterns over the tag — pattern matching,
except the "match" is structure at the call site, not a syntactic
block. `=> branch` re-injects. This is closest to *checked exceptions
as data*: every call's outcome space is declared, and dispatch is
exhaustive-or-refuse at the arm set, not catch-and-pray.

The inversion that makes it unusual: **branch names carry no
semantics in the compiler.** `return`/`break`/`continue` are inert
identifiers; a *subflow* gives them meaning by mapping one tor's
outcome vocabulary into another's (test 240 pins this). A subflow is
therefore a **handler** in the algebraic-effects sense — a
translation between two declared effect/outcome signatures — but
it's spelled as ordinary flow composition, not a `handle` keyword.

### 2b. `!` arms — resumable effects, inverted arrow

`pub tor ping { x: i64 } ! pong i64` declares an effect arm; the impl
*fires* it (`ping = pong(x)`); the caller binds the handler inline:
`ping(x: 41) ! pong reply |> ...`. The handler's value is the resume
value delivered back to the firing site.

The honest classification:

- **Algebraic effects and handlers** is the right family (Koka,
  Effekt, OCaml-5 `perform`/`continue`): declared effect signatures,
  resumable, handler replies feed back.
- **The arrow is inverted** (CHANNEL.md's own words): the producer
  calls the consumer's bound code; the consumer never holds a
  resumption object. Koru has no first-class `Resume` — "languages
  that pass computations around as values" is explicitly what it
  declines. So: *shallow, call-site-bound handlers*, not
  deep/multi-shot delimited control. No `shift/reset`, no captured
  continuations as values.
- **Handler sets are comptime-known per call site** — the consumer
  set is statically enumerable (that's what makes `std/channel`'s
  `!`-arm join site compile to fan-out dispatch rather than dynamic
  routing). Dynamically *bound*, statically *enumerable* — closer to
  Effekt's capability-passing discipline than to Koka's effect rows.

### 2c. Obligations — affine, not linear

`app/fs:open` returns a handle carrying a **cleanup obligation**: the
phantom checker (a static pass, ~5.7K LOC) requires the handle to be
*consumed by disposal* — `open |> close`. Concept frags put the
principle plainly: an obligation is a liveness interval; a terminal
disposer settles a debt by use.

This is **affine resource discipline in the Rust sense**, not linear
logic in the Girard sense:

- Ordinary values (ints, strs, cells, arrs) contract and weaken
  freely — copy semantics, no linear context split.
- *Tracked* handles must be used-then-discharged — the protocol is
  per-resource, enforced statically (checker) *and* re-decided
  dynamically: `bridge.custody.kz` logs every mint/use/release, and
  `HoldsCheck.lean` re-decides the ledger as a lawful custody record
  (double-mint refuses, use-after-release refuses).
- So the linearity is a **checked protocol layer**, not the type
  system's connective structure. Where a linear λ-calculus would
  give you `A ⊸ B` as the function type, koru gives you a
  first-order function layer plus an obligation overlay with two
  independent enforcers. Weaker as a theory; stronger as an
  instrument — the runtime ledger catches what the static pass
  can't see.

### 2d. Metatypes — a closed residual vocabulary

`|*` catchall arms can bind a metatype — and the vocabulary is
*closed*: `"Transition"`, `"Profile"`, `"Audit"` (`ast.zig`,
`catchall_metatype`/`metatype_binding`). The residual case — "all
outcomes I didn't name" — arrives as a typed record with transition
metadata. This is exhaustiveness-by-accounting rather than by
wildcard: the leftover is a value you can inspect, and its kind is
declared.

### 2e. Staging — comptime evaluation as the genericity mechanism

- `[comptime|abstract]` tors and `~`-annotations mark compile-time
  execution; transforms rewrite call sites, with **per-site budgeted
  fixpoints** (a transform re-fires until stable or budget-out —
  refusal, not divergence).
- Proto-definition bodies `{ value: u64 }` pass *type names as
  comptime data* — Zig-style generics-by-elaboration, not System F
  quantification. There is no `∀α.`; polymorphism is staging.
- The stage split is a namespace fact: `std/io` (user-stage) vs
  `std/compiler` (transform-stage). Two-level discipline à la
  MetaOCaml, enforced by facet rather than by type quotation.

### 2f. Effects boundary — `proc`, purity, hosts

`proc f|zig { ... }` is the honest FFI boundary: host code lives
behind `proc`, everything else is Koru. A purity checker propagates
a call-graph fixpoint so "does this flow reach host code" is a
*computed verdict*, not a comment. `|zig`/`|js`/`|cs` variants on one
tor are the realization rows — one spec, several bodies, and the
compiler's own long-term ambition (AMBITIONS A2) is deleting the
unearned ones.

## 3. So — what logic does Koru implement?

**None, and that's the precise answer.** Koru is a programming
language, not a logic; it makes no consistency claim and therefore
owes no paradox defense in the proof-theoretic sense. What it has
instead of a logic is a *decision discipline*:

- a mechanized kernel (`FlowKernel.lean`) that is a total evaluator
  on a bounded subset, proved monotone in fuel;
- refusal-by-default everywhere else — the refusal matrix is the
  semantic boundary, not an error path;
- independent re-decision (FlowCheck re-decides claims; HoldsCheck
  re-decides custody) — evidence is recomputed, never trusted.

If you *insist* on a Curry-Howard reading (a `tor` decl ≈ a judgment,
an impl ≈ a proof), the reading fails at exactly two doors, and both
doors are named below — which is why the next section exists.

## 4. The classic self-reference paradoxes

### Curry's paradox (unrestricted self-application → explosion)

The computational version — a looping self-application — is live in
Koru: `@label` jumps give general recursion, transforms rewrite
transforms. Koru's answer is **budgets, not types**:

- kernel evaluation: fuel + `run_mono`;
- transform fixpoints: per-site budgets → refusal;
- comptime walker: `WALK_ITERATION_WALL`.

A Curry-style "type" of explosive self-reference cannot be *stated*
in koru because there is no implication/proof layer to inhabit; the
nearest analog (a transform that loops) hits a resource wall and
refuses — observably, not axiomatically.

### Girard's paradox (Type : Type)

No surface for it. Koru's type layer is first-order and *closed*:
atomic types, cells, protos, and the 3-member metatype vocabulary —
there is no type-of-types, no universe, and `∀` doesn't exist in the
term language at all. Type-names-as-values in proto bodies are
comptime data elaborated away before runtime — the stratification is
*staging* (what's comptime vs what's runtime), not a universe
hierarchy. Girard needs `Type : Type` in one self-contained layer;
koru's two layers refuse to be one layer by construction.

### The honest summary

Where a proof language avoids these paradoxes with stratification
theorems, koru avoids them with **refusal + budgets + staging**:
self-application costs fuel, type-valued data lives one stage up,
and anything outside the kernel subset is a named refusal rather
than a silent inhabitant. The paradoxes aren't *proved* absent —
they're *unspellable* in the checked fragment and *resource-bounded*
in the executable one.

## 5. What it isn't (the negative space that defines it)

- **Not a λ-calculus dialect**: no first-class functions, no
  closures in the kernel value domain; control structure is
  declared dispatch data, not λ-terms.
- **Not a linear/affine λ-calculus**: affine at the obligation
  overlay only; the core type discipline is first-order.
- **Not a dependent type system**: no terms in types, no Π/Σ; the
  metatype vocabulary is a closed enum, not a universe.
- **Not standard exceptions**: outcomes are named sums with
  declared vocabularies and ordered guard dispatch — resumable on
  the `!` axis, non-resumable on the `|` axis, both statically
  enumerable.
- **Not actor/message-passing at the core**: channels and pump are
  *compositions* of four existing mechanisms (ring, `!`-arms,
  threads, poll) — concurrency is a library shape, not a primitive.
- **Not a proof assistant**: nothing in the tree asserts totality
  of user programs; fuel is a resource bound and `run_mono` is the
  boundary of the formal claim.

## 6. Where it differs — the short table for outsiders

| Surface | Closest neighbor | The actual difference |
|---|---|---|
| tagged/bare/void results | checked exceptions, `Either` | 3 cases, not 2; named user vocabularies; dispatch lives at call sites as data |
| subflows | effect handlers | translation between declared vocabularies, spelled as composition not `handle` |
| `!` arms | Koka/Effekt effects | inverted: callee calls bound handler; handler sets comptime-enumerable; no resumption values |
| obligations | Rust affine, session types | overlay + double enforcement (static checker + runtime ledger re-decided in Lean) |
| metatypes | catchall patterns | closed 3-member typed residual vocabulary, not a wildcard |
| comptime | Zig comptime, MetaOCaml | transforms rewrite call sites; per-site budgeted fixpoint refuses instead of diverging |
| pump/channels | Go select, libuv | no `block` primitive; backpressure = arms; scheduler is a composition |

## 7. Could it use a basis?

A formal basis is not load-bearing for what Koru does today — its
epistemics are the corpus, the refusal matrix, and mechanized
re-decision. But the pieces are *closer to a basis than they look*:

- The flow layer has a natural denotation: first-order terms over a
  named-sum return monad with ordered-guard handlers — a small
  algebraic-effects calculus, minus resumption-as-value. Writing
  `handle`-as-subflow as an explicit translation would make the
  `!`/`|` split a theorem-shaped statement instead of a runtime fact.
- The obligation layer *is* an affine system waiting for its typing
  rules: mint/use/discharge as a resource protocol is textbook
  (Rust's borrow discipline, session-type duality on
  acquire/release). `HoldsCheck.lean` already is the model — the
  missing artifact is the static-side judgment the phantom checker
  approximates.
- Staging has a basis in two-level type systems / binding-time
  analysis; the facet split (`std/io` vs `std/compiler`) is already
  the annotation discipline one would write down.

What a basis would *buy*: the `∀ src` theorem — semantic
preservation of codegen, not corpus-bounded equivalence. What it
wouldn't: the parts the project actually depends on (refusal
coverage, witness independence, attestation) are operational
disciplines a type theory doesn't reach. The right read: **the
kernel is already the basis; the calculus exists but is unnamed** —
naming it is a paper, not a refactor.
