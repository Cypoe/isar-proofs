---
type: frag
id: 0035
provenance: devin-cli
ts: 2026-10-27
tags: [koru, host2, c99, flow-eval, witness, bootstrap, dot-k]
---

# 0035 — host2 pivot: the C99 checker over `.k` claims

## What changed

Frag 0034's host2 was a Python witness tree over a `.kv` JSON
interchange. Two corrections landed: the substrate is **C**, and the
interchange is **koru files** — specifically the `[flow-eval]` claim
format that `w:/src/koru`'s `FlowCheck.lean` already decides and
`golden.txt` lists, not an invented syntax.

`host2/` now owns exactly one piece of logic: `src/krun.c`, a C99
witness that

- reads `[flow-eval] ((entry …) (fuel N) (result R) (graph …)
  (oracle …))` claims — total decoders, malformed structure refuses,
  duplicated claim/arm fields refuse, `refuse` is an expectation only
  (never a leaf result);
- re-decides each claim with a `runK` twin — invoke/flow/loop/
  dispatchTag/dispatchBare/armTry/armWalk, oracle as trust boundary,
  fuel as a resource cap;
- compares with the asserted result — forged claims report `drift`
  (exit 4), never pass;
- `--emit SRC.k` quotes SRC's program into the `qnode 30` calling
  convention and invokes the claim's `emit` entry — the compiler
  (`kemit.k`) is *data evaluated by the checker*, never reimplemented
  in C.

`tools/DumpKoruFixtures.lean` now writes `.k` claims:
`case-0…7.k` (accept + refuse rows), `case-forged.k` (asserts 6 where
the graph returns 5), `kemit.k` (the compiler program; arg-less
invocation refuses — `src` is unbound).

`check.py` is a pure orchestrator: clang build leg (`-std=c99 -Wall
-Wextra -Werror`), claim legs, forged rejection, emit legs (expected
text read from each file's `# emit:` header), and the cc leg — emitted
C compiled and run, exit code vs the literal.

## Verified

`python host2/check.py` — **21 pass, 0 fail, 0 skip**, including
`int main(void) { return 5; }` compiled and exiting `5`, and
`return -3` exiting `4294967293`. Battery 31/31.

## Retired

`run.py`, `quote.py`, `kwire.py`, `fixtures.py`,
`specs/koru-fixtures.json` — the Python witness + `.kv` interchange.
The C checker is authoritative; keeping two substrates would make the
witness story ambiguous.

## Trade-offs (stated, not absorbed)

- **krun.c is handwritten logic.** It is the bootstrap that dies when
  a machine-checked evaluator (the CompCert leg) replaces it — same
  role the C99 bootstrap compiler plays for the spec. Until then it
  is the one piece of unverified logic in host2, which is why its
  discipline matters: total decoders, refuse-by-default, checked
  int64 arithmetic (overflow refuses where Lean's Int decides — a
  named divergence, corpus never nears it).
- **`# emit:` comments carry expectations.** Check legs are
  data-driven off generated headers — the corpus stays self-describing
  without a second manifest.
- **CompCert subset**: C99 only — no VLA, `_Complex`, nested
  functions. The emitted fragments are deeper inside the subset than
  krun.c itself needs to be; krun's obligation is merely to compile
  clean under `-Werror` today and be *rewritable* later.
- **`residue` claim field**: a real FlowCheck field krun does not
  model — it refuses the claim, naming the axis, rather than
  approximating it.
- **Bash vs DWORD exit codes**: `-3` returns DWORD `0xFFFFFFFD`;
  POSIX shells truncate to `253`, Python's subprocess reports
  `4294967293`. The cc leg compares masked 32-bit values.

## The rung after this

`FlowEvalCongruent` (the TTerm-resident evaluator + decoder +
congruence) and subset growth: each new `emitC99` match arm wants a
mirrored `kEmit.shapeOk` conjunct, a corpus row, and regenerated `.k`
files — agreement stays checked on both substrates.
