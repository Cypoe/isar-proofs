---
type: frag
id: 0060
provenance: devin-cli
ts: 2026-11-01
tags: [koru, host2, emitprog, kemitp, selfhost, fixpoint, norm,
       reachables, byte-identity]
---

# 0060 — kEmitProg: emitProgC spelled in the dialect; whole-program
self-host verified byte-exact on all 7 corpus programs; two hidden
costs cleared (surface-image mismatch, O(passes×|st|) reachables)

## What landed

`kEmitProg` in `src/ISAR/KoruProgEmit.lean` — a ~60-callable `KProg`
that is `emitProgC` spelled in the dialect: the c99 catalog rows
(prelude chunks, per-tag templates, mangle/escape tables, op maps)
as declared cells plus a structural walk over the tag-30 quote.
`emit {src,fuel}` mirrors `emitProgC p fuel` — the claim's declared
fuel arrives over the wire and becomes the emitted driver's
`kfuel=` (the `krun --emit`/`--quote` cell now carries
`(fuel (int N))`, not a bare int).

`gen/kemitp.c = emitProgC(kEmitProg)` (~513KB), the `910_kemitp`
wire row, and the `kp.*` gate legs land it:

```
pass  kp.stamp      (kemitp.c bound to 910_kemitp claim)
pass  kp.build      (emitProgC(kEmitProg) via c99 toolchain)
pass  kp.emit       (interpreted kemitp == gen/kemit.c)
pass  kp.<g>.h1     (compiled kemitp == gen/<g>.c)
     g ∈ {kast,kchain,kemit,klex,klow,ksexp,kwir}
host2.check: 1006 pass, 0 fail, 13 skip
```

Fresh names come from `dc` decl-count folds, not state threading:
the dialect cannot construct composite values at runtime (no
`arr`/`cell` from expressions), so `emitProgC`'s `{n,out}` monad
cannot thread through call returns.  Instead every emit tor takes
`n` forward-only and the caller computes each child's fn number as
`n + dc(prior siblings)` — the counter is a pure function of
position, byte-identity with `EM.fresh` preserved.

Char-level work (`mangle`, `cstrBody`) needed three additive
builtins in all five lanes (`evalKBuiltin`, `eval.c`, prelude
`kbi`, `lower.c` whitelist, `kWirWbl`): `chars` (str→byte[]),
`charsToString`, `charToString`.  Same precedent as `len`/
`intToString` — the emission leg's own vocabulary.  `cstrBody`
itself was wrong for non-ASCII (code-point octal: `—` → `\°24`);
now UTF-8 byte-level three-digit octal in both lanes.

## Bug class 1 — the claim is not the program

`kp.kast.h1`/`kp.klow.h1` failed at first with 37/40-line diffs,
all of two shapes: `ecn("_")` vs `ecn("c")` and
`strcmp(r->br,"_chain")` vs `"e"`.  Not an emitter bug: korufe
decodes the **surface image** — a discarded arm bind decodes as
`_` (KORU100, the authority demands it) and every `|>`-chain step
gets tag `_chain`.  The claim carries the normalized program;
`emitProgC(kAst)` carried the pre-normalization one.

Fix: the programs are now *stated* in their surface image.
`kNormProg` (KoruEmit.lean) folds exactly those two renames —
unused `bind → "_"`, cont-position `branch → "_chain"` — over
`kAst`/`kLow`/`kChain`.  Renames of unreferenced names only;
behavior untouched, every other gate's behavioral comparison
unaffected, and now claim-fed `kemitp` and `gen/*.c` describe one
program.  `kemit`/`klex`/`ksexp`/`kWir` were already in image
(their legs passed before), `kNormProg` is identity there — it is
applied only to the three that needed it, minimal blast radius.

## Bug class 2 — `ep-grr` ran n blind passes

`kchain` (~350 callables, 1.09MB quote) hung >10min and OOM'd the
box (~92GB) where `kast` took 7.5s and `kwir` 41s.  Cause: the
reachables closure ran `len g` passes no matter what — each pass
scans all callables with `ep-mems` membership checks on the
`"|a|b|"` set-string (~7KB by end) — ~850M char-steps plus the
per-step allocation the compiled repr still does.

Fix: `ep-grr` exits when a pass grows the set-string's length by
zero — the honest fixpoint, `k` kept as the cap.  Call-graph
depth (~30-50) replaces graph size (~350) as the pass count:
kchain emits in ~6s at the baked 4G fuel and is byte-identical to
`gen/kchain.c` (1,340,108B, 0-line diff).

## Bug class 3 — the O(G²) wall under the fixpoint

The fixpoint fixed *pass count*; a 4×-kchain stress program
(4 prefixed copies + glue, ~1400 callables, 60K nodes, 4.4MB
quote) still OOM'd at >60GB — each surviving pass scans all G
callables against the *whole* set-string (O(|st|) char-scan per
callable): O(passes·G²·L) with passes≈depth was still ~16×
kchain's closure work.

Fix: **frontier-delta closure**.  `ep-gr`/`ep-grr`/`ep-grq` and
the ref collectors (`ep-arf`/`ep-anod`/`ep-anl`/`ep-aref`/`ep-cref`)
now thread `{st, fr}` — `st` the accumulated set, `fr` only the
last pass's additions.  A pass scans the graph for `fr`-members
and collects their not-yet-known refs into `fr2`; `ep-grd`
merges `fr2` into `st` or reports fixpoint.  The `st` dedup in
`ep-arf` is what keeps it terminating (known names can never
re-enter the frontier).  No new builtins — strings stay the only
growable container, arrays remain literal-only (`index`/`len`,
no `push`/`set`, so a positional flags repr is not expressible
yet).  Total work drops to O(G²·L) once: measured kwir 41→1.4s,
kast 7.5→0.43s, kchain 5.95→3.3s, all still byte-identical; the
60K-node stress completes in ~55s at ~40GB peak where it OOM'd
before.

## Bug class 4 — latent `ep-gv` root-number off-by-one

The stress run surfaced a numbering bug unreachable by the
corpus: `ep-gv`'s arr/cell arms numbered the root `vl` at
`n + ΣdcV(children) - 1` instead of `n + ΣdcV(children)` — the
root is the *last* fresh of the lit subtree, children occupy
`n..n+Σ-1`.  Only a `.lit (.arr …)`/`.lit (.cell …)` *expression*
triggers it; no corpus program had one (the glue callable's
empty-array invoke args did).  Output: every subsequent
lit-decl name one low while refs stayed right — self-inconsistent
C, `ev4` calling an undeclared `vl3`.  Fixed both arms; the
minimal 6-arg-invoke repro and the full 5,407,012-byte stress
emit are now byte-identical to `emitProgC`.

## Trade-offs and known walls

- **The `dc` fold is still O(S·D̄) per program** — measured
  node/depth masses: kEmit 211/1270, kAst 2638/14037,
  kLow 4209/20630, kWir 8216/37319, kChain 15094/72079 — the
  residual wall is the per-step allocation of frag 0055's repr,
  not the fold, at corpus scale.  A linear alternative exists
  (path-derived names, `ev_<path>`) but changes every emitted
  identifier — the byte-identity convention was kept; if a much
  larger corpus lands, that is the next rung.
- **Reachables is now O(G²·L) once, but the emit loops
  (`ep-gfw`/`ep-gbo`) still pay O(G²·L) each** on `ep-mems{live}`
  — fine at 1400 callables (~30M char-ops), the next wall is
  ~5-10× out.  Positional flags would need array mutation
  builtins (`push`/`set`) the dialect does not have — a named
  axis, not an oversight.
- **Real koru is not the input language.**  `W:\src\koru-libs`
  (364 files, ~1.16MB) and `W:\src\koru-examples` (52 files)
  are real-koru `.k`/`.kz` — imports, namespaces, effects,
  obligations, format strings — not the host2 wire dialect.
  Exercising them needs either hand-ports (the `ported/greet`
  precedent) or a `koruc` AST→KProg bridge — a real backend
  rung, not a fixture.  The synthetic 4×-kchain stress stands in
  meanwhile.
- **Composite construction is still impossible** in the dialect —
  `{n',text}` returns are not expressible, so `dc` is not
  memoizable in-language.  `retCtor` builds single-payload ctor
  values only; packed-string returns need slicing, which the
  wire model rules out by design.
- The `kp` legs bind **claims**, not the Lean programs: where the
  surface image drifts further (any future korufe desugar beyond
  `_`/`_chain`), the same normalization story applies — extend
  `kNormProg`, never the comparison.
- `kemitp`'s own fuel (`4294967296` in the 910 claim) covers the
  corpus with headroom; it is declared data, bump it in the claim
  if a bigger program lands.

## Self-hosting status

`seed → H0 → H1 → H2` is closed on the whole-program leg:
`kemitp.exe` compiles `quote(kEmitProg)` to its own source
byte-for-byte (512,528B fixpoint verified earlier), a second-
generation binary agrees with the first on the corpus, and every
`gen/*.c` artifact is reproducible through the compiled
koru-spelled emitter from the same wire inputs the interpreted
lane sees.  `kprog-to-progc99` is declared in
`quotient-maps.json` after `kprog-to-c99`.
