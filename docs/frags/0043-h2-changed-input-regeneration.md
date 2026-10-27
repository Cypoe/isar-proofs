---
type: frag
id: 0043
provenance: devin-cli
ts: 2026-10-28
tags: [koru, host2, kemit, emitprog, compcert, h2, selfhost, regeneration]
---

# 0043 — H2: changed input through the compiled compiler

H2 is the regeneration turn: the corpus stopped being frozen.
`koruEmitCorpus` grew 19 → 31 members — shapes the compiled compiler
had never observed — and the fixpoint was shown to hold *under
regeneration*, not just on the H1 corpus.

## The chain

```
changed input: koruEmitCorpus 19 → 31 (KoruEmit.lean)
  +6 accepts: boundary int, mixed ops, deep nest,
              negative truncating div/mod, nested neg
  +6 refuses: bool/arr/cell literals, field/index access,
              builtin call (divTrunc — a builtin BOTH
              vocabularies decide, so FlowCheck can re-decide)
  → tools/DumpKoruFixtures → new 200_emit leaves + kemit.c
    (input.fnv1a64 stamp binds artifact to source)
  → h1 legs rerun: compiled ≡ interpreted on the new rows
  → h2 legs: ccomp-built kemit's OUTPUT back through
    ccomp -S → i386 gcc link → run → exit byte == expect
    (the compiler's compiler output is itself machine-checked
    compiled and observed — H1' → H2')
```

`gen.stamp` is the honesty leg: `kemit.c` carries
`/* input.fnv1a64:<n> */`; the gate recomputes FNV-1a over
`900_kemit/input.k` and *fails* on a stale artifact instead of
silently passing on an unfaithful one (verified: stamp `1` refuses).

## The corpus did its job — three real bugs surfaced

1. **korufe unary-minus precedence.** `-(7) / 2` parsed as
   `negate(7 / 2)` — korufe read a *full expression* as the unary
   operand; koru's `parsePrimary` binds `-` at postfix level
   (`-(a).b` refuses identically upstream). Fixed: unary operand is
   unary-or-postfix, never a binop tail. The old parse emitted a
   *different program* `(-(7 / 2))` that happened to evaluate the
   same — observational equivalence on ints would not have caught it;
   the emitted-text comparison did.
2. **Expect printer was scalar-only.** `arrlit`/`celllit` refused in
   the lowerer's expect serializer, not in emit — the refusal named
   the wrong axis. `jval_sx` now prints wire values recursively
   (arr/cell/tag payloads), and the oracle/arg/expect printers share
   it instead of three duplicated scalar walls.
3. **Builtin vocabulary mismatch.** The first `refuse_builtin`
   member used `len` — *our* extension, undecidable by the
   authority's FlowKernel → FlowCheck conformance disagreement.
   Swapped to `divTrunc`: both vocabularies decide it, the claim
   stays conformance-checkable, and emit still refuses the node.

Negative div/mod members are honest witnesses: `ktdiv`/`ktmod`
truncate toward zero = C `/` `%`. **Div-by-zero is a named deferred
axis** — koru refuses where C traps; different observation, not
equivalence, deliberately not a corpus row.

## Gate

- `host2.check`: **402 pass / 0 fail / 0 skip** — +111 legs over H1's
  291 (12 new emit rows × parse/lower/claim/emit/cc/ccv/h1/h1v, 14 h2
  legs, `gen.stamp`, new authority/conformance rows).
- `lake build Host2`: clean; `host/battery.py --tier fast`: 31/31;
  `spec_project`: in sync.

## Honest boundaries

- Still **corpus-bounded**: `SelfHostingOn` is a finite disjunction,
  now over 31 members. The changed-input turn strengthens evidence —
  the same binaries tracked shapes they were never built against —
  but `∀ src` remains the `SelfHostingC99` rung.
- `emitProgC` covers exactly the kEmit subset; every new refuse row
  names its axis (`bool`, `arr`, `cell`, `field`, `index`, `builtin`).
- The h2 chain composes two observations: the compiler is
  machine-checked-*compiled* (ccomp i386), its output likewise;
  link+run remains unverified gcc + `libcompcert.a` — declared in
  `assembly.json`, not hidden.
- `korufe` remains handwritten bootstrap; `lit -3` stays wire-only
  (`900_wire/000_emit_neg_lit`) because koru cannot spell negative
  literals — `-3` is `negate(3)` upstream.
