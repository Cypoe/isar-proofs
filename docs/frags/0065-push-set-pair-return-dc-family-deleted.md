---
type: frag
id: 0065
provenance: host-invariant-realization-pipeline
ts: 2025-11-18
tags: [koru, kemitp, selfhost, builtins, composite-return, dc-fold, performance]
---

# 0065 — push/set builtins; emit family returns `[text,cnt]`; `ep-d*` shadow fold deleted

Frag 0060 left two named walls. Both fell to the same primitive.

## The wall, precisely

`KExpr` has no computed composite constructor: `lit` carries
constants only, `retCtor` one payload. So the emit fold could
not return `{count, text}` from a subtree — the `dc` family
existed solely to re-walk each subtree and recount the fresh
names `gen*` would allocate, once per sibling base. That is
the O(S·D̄) mass: every node visited ~3× (decl pass, set-line
pass, recount).

## Rung 1 — `push`/`set`, pure functional array ops

The dialect values are immutable, so the honest primitives are
copy-on-write, not mutation:

- `push(arr, v) → arr'` — `arr'` shares `arr`'s prefix, `v`
  appended. No aliasing hazard: `arr` is untouched.
- `set(arr, i, v) → arr'` — copy with `arr'[i] = v`; refuses
  (`0`) on non-arr, non-int, or out-of-range index. Refusal is
  the runtime `0`/`NULL` path, same axis as `index`.

`push` alone supplies the missing composite constructor:
`[a,b]` is `push(push([],a),b)` — the `{n',text}` pair the
dialect lacked, spelled without new `KExpr` forms. `set` is the
positional-flag rung (name→index mapping is the remaining
piece — a dict, not `set` alone, which the earlier wall-list
over-claimed).

Landed in all five lanes, mirroring `contains` (frag 0064):
`FlowDialect.evalKBuiltin`, `krun/eval.c` `kbi`, `lower.c`
whitelist, the emitted `kbi` runtime in `KoruProgEmit.prelude`,
and `kWirWbl` in `KoruEmit.lean`.

## Rung 2 — pair returns; the `ep-d*` family is gone

Every `ep-g*` emitter now returns `[text, cnt]` via `push`;
`cnt` is exactly the fresh names it allocated. `qa0/qa1/qa2`
project. Consequences:

- The three-pass child loops (`ep-gvl`+`ep-gvs`, `ep-gpl`+`ep-gps`,
  `ep-geb2`+`ep-gebd`+`ep-ges2`/`ep-gebs`, `ep-gaed`+`ep-dal`)
  merged into single folds returning `[decls, slots, cnt]`.
- Consumers needing per-child positions get an `idx` `arr`
  accumulated by the same fold (`ep-gaed` → arg `ev` indices;
  `ep-gal2` → arm `aw` indices; `ep-gas`/`ep-gdt`/`ep-gdb` read
  `idx[i]` instead of recomputing bases).
- 18 `ep-d*` shadow-fold callables deleted — `ep-dv`/`ep-dvl`/
  `ep-dpl`/`ep-dbc`/`ep-dbb`/`ep-de`/`ep-doc`/`ep-dc0`/`ep-dn`/
  `ep-don`/`ep-dal`/`ep-dd`/`ep-da`/`ep-dgl`/`ep-dg`/`ep-df2`/
  `ep-df`/`ep-dc` — plus the four slot-line companions. The
  count is never computed twice; each subtree is walked once.
- `ep-gbo3` takes its advance from `ep-gc`'s pair, not `ep-dc`.

Numbering contract unchanged: child decls first at the caller's
base, root fresh last (`n + cnt - 1`), next sibling at
`n + cnt`. The `[text,cnt]` shape also lands the `li`/`ev`/`ds`
arguments arithmetically instead of as extra `ep-d*` calls.

## Measured

| | dc-fold (pre-0060) | frontier+contains | +pair-return |
|---|---|---|---|
| kemitp self-emit | — | ~2s | **0.117s** |
| big (60K-node, 4.4MB quote) | OOM ~60GB | 1.3s / 767MB | **0.96s / 639MB** |
| kwir | 41s | 0.33s | sub-second |

Corpus: all seven `gen/*.c` byte-identical through the compiled
pair-return emitter (`kp.*.h1`); `kast`/`kemit`/`klex`/`klow`/
`ksexp` differ from pre-refactor `emitProgC` only in the 8-line
`push`/`set` `kbi` prelude — the emission proper is unchanged,
so numbering held. `kchain`/`kwir` bodies differ because the
*program* changed (`kWirWbl` rows), not the emission. The 60K
stress output differs from the pre-`push` host emit only in the
same prelude lines — the pair-return emitter is
observation-identical to the dc-fold emitter on 194K emitted
lines.

Gate: `host2.check: 1003 pass, 0 fail, 14 skip` — all 10 `kp.*`
legs green; skips are the documented interpreter-stack axis
(frag 0047) and missing koru toolchain on this machine.

## Trade-offs stated

- Pair projection (`index`) is O(1) in the runtime but each
  `push` copies the spine — pairs/triples only, never lists of
  length >3 in the hot path. The `idx` arrays are the one
  linear-list use; each arm's `push` is O(len(idx)) → O(A²) per
  dispatch, A ≤ ~50 arms — bounded and dwarfed by the removed
  recount.
- `set`'s copy semantics mean repeated `set` on a hot structure
  is O(n) per op — correct for the immutable dialect, but a
  positional-flags repr built on `set` alone pays O(n²) on a
  rewrite loop. A dict primitive or an amortized write-buffer
  shape is the named rung if that wall is hit; the emitter does
  not currently need it.
- The composite return is a convention, not a type — nothing in
  the dialect checks that `ep-g*` results are pairs. The
  convention holds because every consumer projects `[0]`/`[1]`
  of the same call it invoked; a Lean-side type discipline
  (`KExpr` result schemas) would formalize it later.

## Remaining named walls

- name→index dict (positional flags need it; `set` alone is
  insufficient — earlier notes overstated `set`'s reach).
- The real-koru bridge: `koruc` AST→`KProg` so `koru-libs` and
  `koru-examples` become direct emitter input.
