# 044 — reclaim="redirect" realized natively: consume-on-collapse + persist zone (2026-10)

The IR kernel now realizes the `HeapDev` store model (`Heap.redirect` +
`repr`) instead of tree-copy reduction. This is W3 (write-back + reclaim)
landed as a `Realization` axis, not a separate kernel.

## Semantics

- `FWD` (tag 10) cell = consumed redex; `repr` resolves chains at every
  reader (`step` entry, tag checks, `emit_nf`, `emit_bytes`, `count_nodes`).
- **Root-only consume**: only the redex root mutates/FWDs. Spine-internal
  writes were tried and are *unsound under DAG sharing* — a shared spine
  cell has multiple referrers with different arguments, so `N.r := q`
  corrupts every other application. This was the deduped-`(S I)(S I)`
  crash.
- **Era-ordered arena**: `[perm ds/vocab][input cells][root table]
  [persist][<irstart> reduction]` in one reserved VA. Write rule:
  `T >= permend and (v < irstart or T >= irstart)` — permanent cells are
  never targets; input/persist cells may only point backward (below
  irstart), which makes acyclicity a single address compare (`v < C`),
  the asm-level `RedirectOk`.
- **Persist zone** `[pcur, pend)` between root table and `irstart`:
  reducts for input-tier roots allocate there (`mkapp_p`) so the FWD
  survives per-root arena resets — shared *input* redexes collapse once
  per stream, not per occurrence. `persist_bytes` (default 256 MiB) caps
  it; exhaustion is exit4.
- In-place root rewrite when `O >= irstart` (dup/swap/comp/s reduce with
  0–1 allocs); fresh persist reduct + FWD when `permend <= O < irstart`;
  fresh copy, no consume, when `O < permend` (template).
- Token mode: `irstart = permend` (no resets) — all non-perm cells
  writable; `mkapp_p` aliases `mkapp`.

## Measured (win64 IR exe)

- 17-case corpus incl. deduped DAGs + multi-root: **naive == redirect and
  fuse == fuse+redirect byte-for-byte** on every convergent term.
  Alloc −45–60%; shared-redex steps dedup (e.g. dag `(KSI)y,xx` 13→8
  steps naive-vs-redirect; multi-5 26→13).
- **`program_query` (the G10 stage-1 term): completes** — 84506 steps,
  125793 allocs, 347s, working set ~bounded (was: naive >48GB,
  pre-persist redirect >10min). Steps **identical to graph.lo** (84506)
  and **NF byte-identical** — the kernel now executes genuine graph
  reduction.
- Per-step rate ~5x slower than graph.lo (repr chains + guards vs tuned
  runtime) — acceptable; the O-class is now the same.
- G10 `--ir-redir` default leg: program (84506 steps ~330s) + link
  (363217 steps) + assemble*/pack* all on the native redirect kernel —
  emitted PE **byte-identical** (3584B) to the reference. W1b's
  "naive kernel can't run program/link" objection is obsolete.
- Fuse-s+redirect kernel is bounded identically, but the *marshal seam*
  dominates at G10 scale: `lower_s_view` expands primitive-S leaves and
  **renormalizes the whole lowered NF in Python** (`_l0_nf`) — on the
  3.4MB program NF that's a multi-10-min pure-Python pass, killing the
  fuse_s step-count win end-to-end. If fuse_s legs matter: teach
  `decode_program` the primitive-S surface or push lowering into the
  exe's NF emitter.

## Bugs found by the corpus, fixed

- `rep()` clobbers `rax` — write-backs must save the cell base (`r8`/`r12`
  /`r13`), not rely on `rax` surviving `repr`.
- `st_comp_fr` clobbered `rsi` (f) by reusing it for x before saving —
  produced `I (g x)` instead of `f (g x)` → wrong NFs (`B K K I → K I`).
- `ir_depack` is jumped into — no extra `sub rsp` or the VirtualAlloc
  frame misaligns (AV on every input).
- `irstart` must be page-aligned — `MEM_DECOMMIT` rounds down and would
  free the page holding the input/root-table tail.

## Open issues

- **bytes+redirect exes fail to load** (CreateProcess 193 / Zugriff
  verweigert). PE is structurally identical to working builds, Defender
  clean, LoadLibrary→126. Term-mode and none+bytes unaffected. Probably
  an emit_image/link quirk in the combination — uninvestigated.
- **Divergent terms**: resolved under persist — Ω (`S I I` self-app)
  now exits rc=4 (bounded OOM) on both redirect builds; the earlier
  rc=0 `? ? @` bogus-NF artifact is gone because input cells may only
  point backward, so divergent structures exhaust the zone.
- G16 byte-egress verification under redirect is pending the loader fix.

## Revision 2026-10-14 — final-root dynamic routing (decision 067, frag 0029)

`mkapp_p` now routes reducts of the **final** root
(`irj == irnroots-1`) into the ordinary dynamic arena: no future
root can observe that root's input-cell FWDs, so persist's
decommit-safety guarantee is vacuous there. Non-final roots keep
persist allocation + FWD (cross-root memoization unchanged).
GC marking is also precise: roots = stack + `[irj, irnroots)`
root-table window, traversal passes through input cells (never
swept), input mark bits cleared post-collect. Measured: the
single-root persist wall (frag 0028) is gone — `ret16 @256MiB`
rc=4@656s → rc=2@33s, `pfree` untouched.
