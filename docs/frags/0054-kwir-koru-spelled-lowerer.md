---
type: frag
id: 0054
provenance: devin-cli
ts: 2026-10-29
tags: [koru, host2, kwir, emitprog, selfhost, wire, boundary, claim]
---

# 0054 — kwir: the lowerer spelled in Koru, and where the boundary actually is

The backend does not consume `ast.json`. It never did — the
boundary document between front and back is **rows + source +
name/string tables**, and `wir` is the leg that re-walks that
wire: a Koru-spelled `lower.c` that turns the flattened six-int
row stream into the `(graph …)` claim. `ast.json` stays where it
belongs — an authority/debugging projection for checking the
parser, never the semantic compile boundary. The claim sexp is
the stable form: names resolved, spans dropped, only
semantics-carrying structure — Koru's own claim dialect, not a
foreign Lisp.

`wir.k` (~95 tors, `_scratch/wir.k`) is transliterated into
`ISAR.kWir` by `_scratch/wir_to_lean.py`, which walks korufe's
**internal ast** (bare `korufe FILE.k`, or `--ast-canon`) and
emits `KCallable`/`KDecl` rows. `kChain` mounts it under the
`w-` prefix; `emitProgC(kWir)` produces `specs/gen/kwir.c`,
compiled wide-stack as `kwir_wiw`. `906_kwir` is the corpus
leaf holding the generated surface.

## The race

Every corpus leaf now runs two more legs after `kl`/`kli`:

- `wi.*` — compiled `kwir` fed `(cell (rows…) (src…) (names…)
  (nsp…) (strs…) (ssp…))`, graph compared to `korufe --lower`'s
  `(graph …)` slice.
- `wii.*` — the same program interpreted (korufe `--lower` +
  krun on a case cell), same comparison.

`names`/`nsp`/`strs`/`ssp` cross the boundary as data — koru
cannot slice strings, so the token tables a lexer would produce
are supplied as wire arrays (`wir_tables` in check.py).

## What the race caught

1. **`_chain` dispatch convention.** Transliteration emitted
   `(tag "")` for retbind continuations; `eval.c`'s
   `dispatchBare` refuses empty-branch arms while `lower.c`
   writes `(tag _chain)`. Empty AST branch → `_chain`.
2. **Auth-vs-authority frontend drift.** `-> nsp[…]` parses as
   an *invocation of decl `nsp[`* in koruc but an index
   expression in korufe — same trap family as `-> if(`. Emitted
   produces whose head is `IDENT [`/`(`/`{` are now wrapped by
   `kProduceSrc`; `wpmc(src, j, hi)` needed `i: j` (positional
   args must pun or be labelled); unused binds must be `_`
   (KORU100 enforced at source level by koruc).
3. **`xval` string atoms had no escape handling.** A
   `(str "a\"b")` truncated at the inner quote → NULL → "args
   not a cell". `xatom` now skips `\"` in the scan and `xunesc`
   decodes the authority's five-escape set (frag's declared
   contract — the runtime never implemented it).
4. **`wsti3` dropped the `(node (invoke` close.** On a
   `(step invoke)` row following an invoke step (a `|>`-chain
   link), a2/a3 emitted ` (conts (arm …` with the previous
   `(node (invoke` still open — `(conts` landed *inside* the
   invoke as a pseudo-arg. Fix: emit `")) (conts …" — close
   invoke+node, then open conts. `dep`/`iopen`/`wcls` accounting
   was already correct for everything else; this was the one
   transition that bypassed `wcls`.
5. **`--ast-json` is a lossy projection.** The readable ast
   (type-discriminated, flat) drops `return_binding` — every
   `: name` chain retbind came back `null`, so the generated
   surface lost `: c`/`: t` binds and `w-wk` recursion refused
   on unbound vars. The authority documents are the bare
   `korufe FILE.k` internal ast and `--ast-canon`; `--ast-json`
   is for humans. Generator now reads the internal ast again.
6. **Timeouts are a verdict, not a crash.** `klow_kl` on the
   grown 12K-row 905 wire exceeded its 600s budget and the
   unhandled `TimeoutExpired` killed the whole gate mid-run.
   `run_t` converts timeout → named `time axis` skip, same
   honesty category as the stack axis (frag 0047): a resource
   verdict, not a silent pass.
7. **~100GB RSS was scan volume × a never-free arena, not a
   leak.** `wdpe`/`whi`/`wdk`/`wnat`/`wpun` did O(n)–O(nn) row
   and name scans *per ev row / per arg*, each iteration
   allocating into `xm`'s bump arena. On the 12K-row wire that's
   ~1.5B arithmetic ops and tens of GB of live Val. The fix is
   declared data, not faster logic: `nsp` now packs
   `pix | pairs | eix | hix | xix` — position→name-index,
   first-ev-row, has-impl, dup-count — all keyed by name *text*
   (duplicate tors are distinct tokens with identical text).
   `wpix`/`wnm`/`wne`/`wevf`/`wdk`/`wthi`/`wdpe` probe the index
   segments; `wst` keeps plain pair-scan `wnat` semantics
   (it re-runs the same helper over `ssp`). Both wire
   producers (`wir_pack_nsp` in check.py, `wir_drive`) emit the
   packed layout. 905 went from OOM to 13.1s; 906: 5.6s at
   ~4.6GB peak (residual cost is the `out ++` accumulator).
8. **`&&` does not guard reads — koru evaluates both operands
   eagerly.** `(i < hi) && (src[i] == c)` still reads `src[hi]`
   at span end → `k_index` refusal (the 906 EOF case: row 6591's
   span ends exactly at `len(src)`). `pkb` is the bounds-checked
   read, but `KExpr` is pure — no invoke is legal in `when`
   conditions or head args, and `pkb(...)` inside a condition
   parses in neither frontend. The working shape is
   `if((k < hi)) (src[k] OP x) else false` — `.cond` is lazy in
   `evalKE` and a C ternary in emitProgC — with the comparison
   *inside* the then-branch. Two grammar traps had to be
   avoided: korufe binds `else` greedily (else absorbs a
   trailing `== 47` — found by graph diff, not inspection), so
   the else must be terminal `false`/`true`; and koru's
   if-branch expr grammar refuses left-deep `||` trees while
   accepting right-nested `A || (B || (C || D))` — the
   ident-class disjunctions are right-nested now. `weql` got
   `else true` (out-of-range means mismatch, the arm should
   fire); `wpun3` needed a chain split (`wpun3b`) because `|`
   dispatch can't follow a `|>` head. `warg5`'s off-by-one
   (`argi + 1` could read one arg-row past the fld run) is
   guarded. `wfpn`/`wfeln`'s `src[i]` head-arg reads stay
   unguarded — the loop arms already prove `i < hi`.

## Trade-off stated

The `wi`/`wii` races prove the Koru-spelled lowerer equals the C
lowerer on the corpus — observational equivalence on emitted
text, which is stronger than behavioral equivalence on ints (the
frag-0043 argument again). What they do not yet prove: `wir` is
row-order-sensitive in `w-wk`'s accumulator state, and the
`(bad …)` marker parity is spot-checked by the refuse corpus
members but not enumerated per marker. The stack axis still
walls the `wii` lane out of the five big generated fixtures —
compiled kwir handles all of them. The packed `nsp` is a wire
*shape* change — both producers must emit `pix|pairs|eix|hix|xix`
or every lookup reads garbage; the wire carries no shape tag, so
a stale producer fails loudly on the first arg row, not silently.
The `out ++` per-row accumulator is still quadratic in live
string churn (the 4.6GB residual) — a chunked emit is the
obvious next cut, deliberately deferred: correctness of the
race outranks allocator pressure.

Gate: 866 pass, 0 fail, 34 skip.
