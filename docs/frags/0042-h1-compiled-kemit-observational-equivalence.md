---
type: frag
id: 0042
provenance: devin-cli
ts: 2026-11-17
tags: [koru, host2, kemit, emitprog, compcert, h1, selfhost, freestanding-c]
---

# 0042 — H1: the koru-spelled compiler runs as compiled code

H1 turned the loop: `kEmit` is no longer only *interpreted*. The koru
program itself is now a reusable compiler binary — built twice, once by
clang and once by CompCert — and it observes the interpreted `krun
--emit` on every corpus row.

## The chain

```
100_kemit/input.k → korufe → kemit.claim (KProg as wire data)
                  → ISAR.KoruProgEmit.emitProgC → specs/gen/kemit.c
                  → clang AND ccomp -S → i386 gcc link + libcompcert.a
                  → binary
per corpus row:  krun claim --quote | kemit_bin → stdout
                 ≡ krun kemit.claim --emit   (byte-identical or exit 4)
```

`emitProgC` is program-structure codegen, not an interpreter: per-
callable C functions, arm dispatch unrolled to mirror `dispatchTag` /
`dispatchBare` (bind + `when`-guard skip, `_chain` continuations as
nested dispatch sites, fuel counter). The fixed runtime prelude (Val
union, sexpr decoder, `len`/`intToString`, truncating div/mod) is a
declared template — the generated program logic is what carries the
compiler.

`krun --quote` emits the `(cell (src <quoted-program>))` wire value;
the compiled binary reads it on stdin. One binary serves the whole
corpus — it is a real reusable compiler, not a per-case artifact.

## Honest boundaries

- **Corpus-bounded.** `emitProgC` covers exactly the kEmit subset
  (vars, int/str lits, `field`, `index`, `len`, `intToString`,
  `bin {and,eq,concat}`, `invoke`/`produce`, bind+when+conts).
  Thunks, floats/bools, `retCtor`, `jump` refuse at codegen with a
  named axis — no silent default.
- **Freestanding C99.** The generated source uses `stddef.h` + its own
  extern prototypes because glibc's headers defeat CompCert's parser
  (`__asm__`, `__restrict__`, attributes). That makes the *entire*
  generated compiler — program logic and prelude — directly
  `ccomp -S`-parseable; the machine-checked span covers the whole file.
- **The prelude is a template, not a proof.** It is observed faithful
  (291/0/0) but not mechanically verified; only the emitted program
  logic rides CompCert's verified C→asm span. The i386 gcc link +
  `libcompcert.a` + run legs remain unverified — now declared in
  `assembly.json` (`link_run.lib`, `lib_from` the compcert image).
- **Equivalence is observational, not a theorem.** Compiled ≡
  interpreted on 37 rows × 2 backends (accepts byte-identical,
  refuses exit 4). There is no `∀ src` correctness statement yet —
  that is the `SelfHostingC99` rung.

## Gate

- `host2.check`: **291 pass / 0 fail / 0 skip** — +74 h1/h1v legs over
  the prior 215, plus `h1.build` (clang) and `h1.ccv` (CompCert).
- `lake build Host2`: clean; `host/battery.py --tier fast`: 31/31;
  `spec_project`: in sync.

## What H2 still means

The compiled kemit emits C *text* — the emitted program is not yet
itself compiled-and-run by a koru-spelled stage, and no koru-spelled
frontend exists (`korufe` is handwritten bootstrap). H2 is the
changed-input regeneration turn: feed a *new* corpus through the
compiled compiler and show the fixpoint holds under regeneration —
`H1' → H2'`.
