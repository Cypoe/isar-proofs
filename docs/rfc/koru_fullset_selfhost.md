# RFC — Option 1: own the whole span (koru → our target semantics)

**Status:** draft, for review. Measured against `w:/src/koru` @
`ea981b295` and `isar-proofs` @ `e0f43a6` (H2 landed, gate 402/0/0).

## 0. The question this answers

`docs/koru-logical-basis.md` §7 ended at: the kernel is already the
basis; the calculus exists but is unnamed. The follow-up: the
CertiCoq-style theorem — `∀ src, emit preserves semantics` — cannot
be proved *into* C in Lean, because CompCert's C semantics lives in
Coq. Prove into our own C model and the correspondence between our
model and Clight becomes the new unverified gap, one level up.

**Option 1 is the alternative: own the whole span.** `KProg` →
quotient maps → a target semantics we formalize in Lean. Then
semantic preservation is a theorem inside one prover about
structures we own end-to-end — the ladder becomes a theorem, not a
witness protocol.

## 1. What Option 1 actually costs (the user's objection, measured)

Owning the span means owning *all three* handwritten components —
not just codegen:

| component | today | LOC (upstream ref) | status |
|---|---|---|---|
| frontend (korufe) | 4 handwritten C TUs (lex/parse/astio/lower) | parser 12,935 + flow_parser 1,512 + expr_parser 951 + lexer 998 + annotation_parser 668 ≈ **17.1K** | parses subset, refuses by axis |
| evaluator (krun) | handwritten C `runK`/`evalKE` twin | comptime_eval **2,375** | twin on subset; FlowKernel models the same subset — `!`, stores, metatypes refused there too |
| codegen (emitProgC) | Lean → freestanding C99 (verified span ends at ccomp) | c_emitter **3,414** | subset; CompCert is witness, not basis |

The "full emit" the option prices in is not upstream's Zig pipeline —
it's our own realization maps: `emitProgC` and whatever succeeds it.
Host code (`proc` bodies, the Zig/JS/CS emitters) stays outside the
theorem *by construction* — `proc` is the declared host boundary;
the theorem quantifies over Koru-realized maps, not host realization.

**So the scope is bounded twice:** by the authority's own kernel
(`!`-arms/stores/metatypes are refused by FlowKernel itself — fullset
means fullset-*for-what-is-modeled*), and by the proc boundary (host
is a declared vertex, not an obligation). What remains — surface
parse, claim lower, kernel-modeled eval, emission — is ownable.

**Two ladders, same shape — do not conflate.** The witness chain
`frontend-as-data → emitProgC → ccomp → self-parse` certifies the
*artifact*: CompCert's theorem covers C→i386, and emitProgC's
correctness stays corpus-observed — a verified-compiled binary of
an observed-correct compiler. Option 1 certifies the *map*:
`∀ src, runK(src) ≡ targetSem(emit(src))` removes the corpus bound
on the correctness axis entirely. The ccomp chain is the witness
ladder's ceiling — useful, deployable, and worth walking (it is
the korufe-as-data path regardless); it is not the rung G, which
is a different claim proved in a different place.

## 2. Construct census — semantics → owning file → host2 status

Grammar authority is `ast.zig` (`Item`/`Node`/`ExprNode`/`Continuation`);
semantics authority is `comptime_eval.zig` (the walker FlowKernel
mirrors); checker owners named per row. Status: **✓** implemented /
**∂** partial / **✗** named refusal / **—** not surface (IR-only).

### 2a. Top-level items (`ast.zig Item`)

| construct | semantics | owner | host2 | fullset work |
|---|---|---|---|---|
| `tor n {params} \| branches -> R` | event signature: input shape + named outcome union + bare return | `parser.zig` (event_decl), `EventDecl` | ✓ | return-phantom `*R<active!>`, `pub`, implicit-flow param, `[annotations]` |
| `n -> expr` | bare-return impl | `parser.zig` (immediate_impl) | ✓ | — |
| `n = head(args) \| arms` | subflow: vocabulary translation | `flow_parser.zig`, `Flow.is_impl` | ✓ | — |
| toplevel flow | program body / entry | `flow_parser.zig` | ✓ | — |
| `import a/b` | module resolution, AST merge | `import_pipeline.zig` (1,547) | ∂ records path, single-file | real transitive resolution (KORU002 parity) |
| `proc f\|zig {\|js\|cs` | host impl boundary | `parser.zig` (proc_decl) | ✗ | **admit as declaration row** — declared, never evaluated; the honesty vertex |
| host line (raw Zig) | verbatim splice | `parser.zig` (host_line) | ✗ | **stay refused** — host surface, not koru |
| `host type` decl | host type import | `parser.zig` (host_type_decl) | ✗ | stay refused — host surface |
| event tap `std/x(n) ! arm` | `!`-arm join site / watch | `parser.zig` EventTap, `tap_transformer.zig` | ✗ | the `!` family — see 2b |
| `#label` anchor | jump target | `flow_parser.zig`, LabelDecl | ✓ | — |
| IR: native_loop / fused_event / inlined_event / inline_code / facet_decl | optimizer & transform rewrites | `ast_transform.zig`, `transforms/` | — | backend IR, never parsed; out of frontend scope |

### 2b. Flow nodes (`ast.zig Node`) — the dispatch layer

| construct | semantics | owner | host2 | fullset work |
|---|---|---|---|---|
| invocation `f(a: x)` | call → 3-case result → arm dispatch | `flow_parser.zig`, `comptime_eval` | ✓ named args only (KORU104 parity) | positional? upstream refuses too |
| `#label` / `@label(args)` | anchor + jump re-entering flow head (the loop primitive) | `flow_parser.zig` | ✓ | nested-label jump (upstream refuses in walker) |
| `_` terminal | flow end | `flow_parser.zig` | ✓ | — |
| `=> branch [payload]` | tagged re-injection | `flow_parser.zig` | ✓ | — |
| `-> expr` produce | bare result | `flow_parser.zig` | ✓ | — |
| `when expr` guard | ordered arm gate; payload bound before guard | `flow_parser.zig` | ✓ | — |
| `\|* Meta b` / `!*` catchall | residual arm binds closed metatype record (Transition/Profile/Audit) | `flow_parser.zig`, `catchall_metatype` | ✗ metatype axis | admit `\|* Meta b` — closed 3-member vocab, kernel refuses it too (kernel-extension axis) |
| `\| b {f, g}` destructure | payload field projection at bind | `flow_parser.zig` | ✗ | parse → lower to field-access chain |
| `\| b { produce }` + post-`when` | element-scope rewrite stage | `flow_parser.zig` | ✗ | stage list `(when E \| { F })*` |
| `! arm` effect handler | **resumable effect** — callee calls bound handler, reply is resume | `flow_parser.zig`, `comptime_eval` (refused in kernel) | ✗ | **the big one** — resume semantics; FlowKernel serializes it as refusal; fullset here = extending the kernel, upstream territory |
| `cond`/conditional node | value-dispatch branches | `flow_parser.zig` | ✗ (expr-level cond parses) | node-level cond |
| `switch_result` | union dispatch on inline result | `flow_parser.zig` | ✗ | — |
| `foreach` | iteration | `flow_parser.zig` (desugars/`~for`) | ✗ | surface spelling is a transform — decide parse-vs-desugar with upstream |
| `assignment` | capture-binding field update (`[mutable]`) | `flow_parser.zig` | ✗ | mutable cell axis — kernel has immutable cells; extension |
| `expression` node | bare expr as flow step | `flow_parser.zig` | ✗ | semantics = eval-and-discard? decide with upstream |
| `conditional_block` | legacy tap-when | (legacy) | ✗ | stay refused — retired shape |

### 2c. Expressions (`ast.zig ExprNode`)

| construct | semantics | owner | host2 | fullset work |
|---|---|---|---|---|
| literal (int/float/str/bool) | values; no negative-literal spelling (unary-neg) | `expression_parser.zig` | ✓ | — |
| identifier | env lookup | `expression_parser.zig` | ✓ | — |
| binary arith/cmp/`++`/logic | `ktdiv`/`ktmod` truncate-toward-zero = C | `expression_parser.zig`, `comptime_eval` | ✓ | — |
| unary `-`/`!` | **postfix-level operand** (H2 fix) | `expression_parser.zig` | ✓ | — |
| `.f` field / `[i]` index | cell/arr navigation | `expression_parser.zig` | ✓ | — |
| `cond(a, t, e)` | expression conditional | `expression_parser.zig` | ✓ | — |
| `@builtin(args)` | builtin table (`as`, `len`, `intToString`, `divTrunc`…) | `expression_parser.zig`, `comptime_eval` | ✓ (table partial) | complete the shared-vocabulary table; extension builtins are a declared axis |
| `f(x)` call in expr | **refused by the upstream walker** (needs source-time bridge) | `expression_parser.zig` | ✗ KORU104 parity | parity refusal is *correct* — keep |
| `{{ }}` interpolation | liquid templates | `liquid.zig` (1,042) | ✗ | template leg — string interpolation axis |
| grouped `()` | vanishes at parse | `expression_parser.zig` | ✓ | — |

### 2d. Shapes & types

| construct | semantics | owner | host2 | fullset work |
|---|---|---|---|---|
| `{f: T}` input shape | param record, named args | `parser.zig`, `shape_checker` (2,743) | ✓ parse; no static check | shape checking is a checker, not parser — separate leg |
| `\| b T` branch payloads | variant types | `parser.zig`, `branch_checker` (691) | ✓ + PARSE003/021 parity | — |
| `-> T` / `*R<active!>` return phantom | obligation on the return | `parser.zig`, `phantom_semantic_checker` (5,710) | ∂ parses, skips | obligation checker — the largest single checker; affine protocol leg |
| proto `{ v: u64 }` bodies | comptime type-values | `parser.zig` proto grammar | ✗ | comptime-elaboration axis |
| `[pure|fusible|abstract|mutable]`/`~` annotations | effect/stage marks | `annotation_parser.zig` (668) | ✗ | annotation grammar → checker semantics |

### 2e. Checkers — the verification surface (each is its own leg)

| checker | verdict | LOC | host2 analog |
|---|---|---|---|
| flow_checker | arm/dispatch legality, exhaustiveness | 3,377 | parity refusals only (KORU021/104/SHAPE002) |
| shape_checker | shape/type conformance | 2,743 | none — korufe lowers untyped |
| branch_checker | union/branch rules | 691 | PARSE003 parity |
| phantom_semantic_checker | obligation liveness | 5,710 | none — the affine layer is unchecked in host2 |
| auto_discharge_inserter | implicit disposal insertion | 5,644 | none |
| purity / threaded / host_type_scope | purity, threading, host scope | 335+353+557 | none |
| **comptime_eval** | **the reference semantics** | 2,375 | krun = twin on subset |

## 3. The distance, honestly totaled

- **Surface grammar to mirror:** ~17.1K LOC of parser — but most of
  `parser.zig`'s mass is diagnostics, host lines, and item plumbing;
  the grammar decisions are what korufe already mirrors.
- **Semantics:** `comptime_eval` is only 2,375 — *small*. The
  semantic core (parse+AST+eval+checkers) ≈ 47K; emit/backends ≈ 31K;
  the other ~60K of `src/` is LSP, packaging, coordination, three
  backends, tests — **none of it inside the span**.
- **korufe today covers** the `Item`/`Node`/`ExprNode` core of the
  *evaluated* fragment (the subset both koruc's walker and
  FlowKernel model) — by design. The uncovered constructs split
  into three honest buckets:
  1. **parsetime work** (destructure, produce-stage, `|* Meta`,
     annotations, proto bodies, switch/foreach/cond-nodes) —
     grammar + lower, no new semantics;
  2. **checker legs** (shape, phantom, purity, auto-discharge) —
     static analyses, each a separate obligation row;
  3. **kernel extensions** (`!`-arms resume, stores/watch, mutable
     cells) — FlowKernel itself refuses these; fullset here means
     extending the *authority's* kernel, which is Lars's territory
     and can't be unilaterally spelled.

## 4. Proposed staging

- **F0 — this census.** The table above; refresh per session (the
  tree moves).
- **F1 — korufe fullset-parse.** Every construct in 2a–2d parses to
  canon `ast.json` or refuses with the upstream axis name. Bucket-1
  work only. Success metric: corpus of upstream regression `.kz`
  files, koruc `-c` parity on parse verdicts.
- **F2 — krun/eval coverage.** Extend the runK twin to everything
  `comptime_eval` models; where the kernel refuses, our claim
  format carries the refusal as data (it already does).
- **F3 — korufe-as-data.** The killer app: the frontend spelled in
  koru surface itself, running on the widened eval domain — needs
  arr/cell/str operations at scale, not the int-expr subset.
  Retires the last handwritten component.
- **G — semantic preservation.** The actual Option-1 theorem:
  `∀ src ∈ fullset, runK(src) ≈ target_semantics(emit(src))` — with
  the target formalized in Lean beside runK. Only meaningful once
  the emit is *our* map into *our* formalized target — i.e., once
  the C99-by-CompCert leg is demoted from basis to witness (which
  it already is in the catalogs).

## 5. What stays outside the theorem — declared vertices, not gaps

**A note on "the compiler through ccomp."** Two different
"C-compile" tasks are easy to conflate: `c_emitter`'s program
fragment refuses concurrency because arbitrary koru *programs* use
pump/rings/threads; a *compiler* is a batch transducer — stdin →
stdout, sequential, deterministic — the "finite byte transducer"
class G-CC-1 names as the oracle's first program. The concurrency
axis doesn't exist for the artifact. Already demonstrated at small
scale: `h1v`/`h2` legs compile generated `kemit.c` through
`ccomp -S` and observe corpus-identical results on i386. The real
bounds for a compiled korufe are emitProgC's program subset
(arr/cell/str at scale), freestanding headers (solved), and the
i386 image's <4GB address space — not concurrency.

- `proc` bodies and host lines: the host boundary is a vertex in
  the graph, never a term in the theorem.
- Zig/JS/CS emitters: upstream's realizations; the theorem covers
  *our* realization maps.
- Kernel-unmodeled constructs (`!`, stores, metatypes): extension
  of FlowKernel is upstream's decision. Until then, refusal *is*
  the faithful semantics — a refusal row, not a hole.
- The runtime prelude: under Option 1 it stops being a template
  and becomes part of the formalized target — same obligation,
  better accounting.

## 6. Open questions

- **Foreach/cond/switch nodes:** surface-level desugar into the
  arm/invoke grammar, or first-class wire nodes? Upstream lowers
  `~for` through transforms — our answer should match wherever
  upstream puts the boundary.
- **`proc` as parseable declaration:** admit the signature row so
  fullset .kz parses, or keep the item refusal? Admitting means
  the corpus can hold upstream files verbatim; the boundary is
  already honest.
- **The `!` frontier:** wait for upstream kernel extension, or
  model resume semantics in our port (`FlowDialect.lean`) as a
  proposed-semantics branch? The latter is a real offer to Lars,
  not a fork.
- **Checker legs ordering:** phantom (obligations) is the largest
  single checker and the affine layer — highest value per the
  basis doc, also the hardest. Shape checking is cheaper and
  gates more corpus coverage.
