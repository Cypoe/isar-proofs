# ADR-005: Packed IR — canonical binary node format for basis terms

**Status**: Accepted
**Date**: 2026-09-26
**Commits**: emit_chain staged seams (`93ab171`, `08cd4d3`) · memory decisions 030, 036
**Supersedes at the seam**: token-stream marshal (`bc_decompile`/`_parse_native_out`) and `pickle` checkpoints; JSON stays untouched (catalog config, never a term carrier)

---

## Context

The staged self-emission chain (decision 036) exposed that Python is still a
*runtime* dependency on every seam: terms are marshaled to postfix token text
(`t_from_host` → `bc_decompile` → exe stdin → `_parse_native_out`), costing
~4s per per-insn encode — ~80% of the win64 assemble wall time — and checkpoints
persist `pickle` blobs, which only Python can re-consume. Two prior formats
exist but neither is this layer:

- **`.plex` wire** (`isa-physics/ref/plex-core/.../wire.py`): artifact
  *container* — magic+header, 4 ISAR kernel matrices, bytechunk payload,
  JSON-in-TLV sidecars (metadata/symbols/manifest/capabilities). It
  containerizes byte blobs; it has no node/sharing notion.
- **bytechunk rule** (`plex/core/bytechunk.py`): lossless payload encoding —
  8 bytes ↔ 16 nibbles ↔ 4×4 nibble matrix. Resonant with `byte_term`'s
  nibble-pair cells, but it encodes *bytes*, not *graphs*.
- **token stream** (current seam): text marshal, tree-shaped (no sharing),
  spawn+parse per query.

The missing layer is the **term-graph serialization** itself — the packed IR.
It is also the substrate the `typed-ir-packages` research note's manifest/
capability/content-addressing layer must eventually wrap: content-addressing
requires a canonical serialization, which this provides.

## Decision

Packed IR file = header + roots + node array:

```
u32   magic   0x30524950  ("PIR\0" LE)
u32   version  1
u32   n_nodes
u32   n_roots
u32[] roots[n_roots]              — node indices, in argument order
node  n_nodes × 9B:  u8 tag | u32 l | u32 r
```

- **Tag byte = `seed.Tag`** — the kernel's own numbering
  (`APP=0, norm=1, konst=2, s=3, comp=4, dup=5, swap=6`), extended with
  `VAR=0xFE` (n in `l`) for probe markers. The emitted host's depacker is
  `arena[i] = mkleaf(tag)` / `mkapp(arena[l], arena[r])` — no parser, no
  stack discipline; ~50 lines replacing the `bc_compile` stdin loop.
- **Canonical order**: postorder DFS; children always precede parents, so
  depack is a single forward pass. No backpatching, no forward references.
- **Hash-consing dedup** on `(tag, l_idx, r_idx)`: structural sharing is
  preserved even though `Graph.export_tree` unrolls into a fresh tree, and
  **equal NFs serialize to identical bytes** — the format is
  content-addressable by construction (the Merkle/package layer's hook).
- Multi-root: one file can carry `program_nf + link_nf` or a batch of
  encode-query closures — the fork-pool/CUDA work unit.

## Consequences

- Python exits the *stage loop*: `reducer stage.ir input.ir → nf.ir`,
  stages chain as files/pipes. Python remains compile-time *authoring*
  (λ-source, `bracket`, `rts.program`) — acceptable, like a compiler needing
  its prior bootstrap.
- The seam stops being text; `.ir` checkpoints carry *terms*, so resume
  keeps NF spines rather than re-decoding artifacts.
- **Not fixed by this**: the naive reducer's O(term)-per-step copying
  (72GB `LENB4` blowup is marshal-free). Evaluator cost is orthogonal —
  sharing-arena-native or Futamura-2 specialization are the levers there.
- The audit layer gets a structural basis: node-level diffs, per-closure
  byte/step accounting, canonical identity.
- Scope honesty: VAR markers serialize for probe/test completeness but are
  not stage payloads; `STK` (kernel-internal stack cells) is never on the
  wire — it is a runtime structure, not a term node.
