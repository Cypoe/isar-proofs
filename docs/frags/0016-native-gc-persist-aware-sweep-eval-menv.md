---
type: frag
id: 0016
provenance: devin-cli
ts: 2026-02-19
tags: [gc, reclaim, persist, mkapp_p, eval-menv, l2-wall, win64]
---

# 0016 — native mark/sweep GC + persist-zone reclamation; eval<menv> completes past the retention wall

## What landed

- `Realization.gc` axis (`"none" | "sweep"`), gated:
  `gc='sweep' requires reclaim='redirect'` — refusal by name,
  no fallback.
- Native Schorr–Waite collector in
  `host/routines_x86_64_win64.py`: conservative stack+register
  scan, pointer-reversal mark in the tag's hi dword
  (bit0 marked, bit1 return-via-.r), sweep to `FREE_TAG` cells
  chained on `flhead`; `mkapp`/`mkleaf`/`mkstk` pop the freelist;
  `grow_heap` collects once on commit failure before conceding
  (exit4).
- **Persist-aware extension** for IR+redirect: the swept space is
  `[pcur0, pcur) ∪ [irstart, rbx)` on two different 24-lattices
  (pcur0 absolute-aligned, irstart page-aligned — each branch
  subtracts its own base).  Input cells `[permend, pcur0)` are
  scanned as roots (their FWD .l points into persist).  A second
  freelist `flhead_p` is segregated: `mkapp_p` pops only
  `flhead_p` — an input cell may never point above `irstart`
  because `ir_bloop` decommits the arena per root.
  `flhead` is reset per root; `flhead_p` is not.

## Bugs found by bisect/trace (each verified by a counter-probe)

1. **Freelist pop clobbered `rcx`** (`mov rcx,[rax+8]` loads the
   dead-cell link).  `st_swap` holds `x` in `rcx` across `mkapp`
   and stores it to `O.r` — a fabricated child edge, recycled-cell
   aliasing, graph cycle, divergent `step`.  The write-log ring
   showed `mkapp` birthing a cell that was *already referenced*
   70 writes earlier.  Fix: `push rcx/pop rcx` around every pop.
2. **`VirtualAlloc` clobbers `rcx, rdx, r8–r11`** — the same
   hazard one frame deeper.  Fix: `grow_heap` (token, IR, MT)
   pushes the full volatile set around the call.
3. **`scan_body` token branch lost its first compare** during the
   persist refactor: `jb` read flags left by the scan loop's
   `cmp r8,r9` — always CF=1 mid-scan, so *no stack root ever
   marked*.  Sweep freed everything (`nfree > nalloc` — the
   impossible tell), emit printed `?`s at `steps=0`.  IR mode was
   unaffected (its branch has its own compare) — a reminder that
   the token path must be re-run after any collector refactor.

## Numbers

- token `full` (church 2500, ~1.6MB arena):
  `steps=112502 alloc=120026 gc=3 free=152059` — identical to the
  pre-persist build.
- forced collection, 64KB arena: NF-equality vs 8GB baseline on
  church/drop/compose terms.
- IR `rfold maps=[asm]` (eval<menv>, mfuel=32768, step-fuel 2B):
  **completes** — `1,226,343,461 steps` in ~52min → `[]`.
  Previously: exit4 at the 256MB persist zone (`mkapp_p` OOM,
  `nalloc≈11.18M`).  With persist reclamation the same run did
  `nalloc≈149.8M` at the 100M-step cap, `ngc=15`,
  `nfree=141,029,488` — the collector cycles the persist zone
  ~13× under steady ~1M allocs/s (live-polled `.data`).
- `host/gates/cross_verify.py`: **139 probes, 0 divergences**
  (both previously-failing legs — `stream >granule`, `tree WWW` —
  now congruent).

## Honest edges

- `[]` for `rfold maps=[asm]` is a well-formed empty stream, not
  a clipped tail — but `assemble_x86` applied to a raw spec term
  may legitimately have no unifier; the semantic verdict needs
  the Python-witness `h0_call("rfold", …, mfuel=32768)` or the
  full-map `cogen` probe.  Not yet run (Python substrate cost).
- `nfree > nalloc` in a *single* collect is now a hard anomaly —
  it was the tell for bug 3.  No gate asserts it yet.
- Battery: `host/dialect.py` selftest fails on `rels==27`
  (pre-existing — `phi2/eval.plex` is modified in-tree; not
  GC-related).
