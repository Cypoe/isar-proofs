# ADR-006: .plex bundle — one COO store, sectioned relations, run/emit roles

**Status**: Accepted (design; no code in this wave)
**Date**: 2026-09-30
**Depends on**: ADR-005 (packed IR), plan 003 (fused store, run-vs-emit §1),
memory decisions 030, 036, 042, 044; research/plex-wire-provenance.md

---

## Context

Three incompatible `.plex` headers exist across the worktrees, and none of
them describes the store the bootstrap actually needs:

- **plex `format.py` v1** (`isa-physics/plex/core/format.py`): `PLEX` magic,
  u8 version, u8 flags, u16 header_size, then a chunk table and JSON TLVs.
  Containerizes byte blobs plus an inline kernel; no node/sharing notion.
- **plex-agent `bundle.py` V2** (`isa-physics/plex-agent/src/dialect/bundle.py`):
  same magic, 68B reserved, *inline* 64B kernel at offset 76 (I,R,A,S
  matrices hard-wired into the header), u32 chunk_count, 16B chunks, TLVs
  appended. The inline kernel slot is exactly the silent-inheritance shape
  the fused model removes — the kernel is a relation like any other, not
  header furniture.
- **plexus `wire.rs`** (retired tree): u32 version, u32 flags, Adler32 per
  TLV, `0x0007 TENSOR_PAYLOAD`. Idea reference only; no obligation.

Meanwhile ADR-005 gave us the term-graph layer (PIR: canonical,
hash-consed, content-addressable node streams), and the fused model
(plan 003 §0) settled that PIR is not a separate payload from the store:
a PIR node set *is* a COO relation with invariants — rows `(i, tag, l, r)`,
implicit value 1, functional in `i`, topologically sorted, hash-consed.
Kernel matrices, bytechunks, nibble numbers, symbol interning, catalog/
Realization/dialect maps, ISA encodings, relocations, capabilities and
proofs are all relations in the same store.

So the container's job is exactly: section the store into typed COO
relations under an interned symbol schema, self-describing enough that a
host can validate once at load and then run or emit without a parser.

## Decision

### 1. Canonical header — a successor, not a pick

None of the three existing headers is adopted. **`.plex` v3** is declared:

```
u32   magic        "PLEX" (0x58454C50)
u8    version      3
u8    flags        bit0: directory present (always set in v3)
u16   header_size  bytes to first section
u32   n_sections
directory  n_sections × { u32 type | u32 arity | u32 kind | u32 reserved |
                         u64 offset | u64 length | u64 rows }
sections   COO relation payloads, 8B-aligned
```

- The directory replaces the stream-walk: random access replaces
  ADR-005's sequential element scan **inside** a bundle. A bare PIR file
  (no directory) remains valid input to the reducer — it is a degenerate
  bundle whose only sections are the node relation and the root list.
- No inline kernel. V2's offset-76 matrix slot becomes section rows;
  a v3 reader never special-cases header bytes into semantics.
- No Adler32. Integrity is the *content-addressing* layer's job
  (Merkle digests per ADR-005 `pack_ir_keyed`), not a transport CRC —
  a bundle that lies about its rows fails validation, not checksum.

**Migration**: no compat reader is written. V1/V2 producers live in
`isa-physics` reference code (`format.py`, `bundle.py`); nothing in this
tree consumes them. Migration = re-emit under v3: inline kernel →
`REL_KERNEL` section, chunks → `REL_BYTECHUNK`, JSON TLVs → typed
relations (metadata stays a bytechunk of JSON if it must). plexus needs
nothing — the tree is retired.

### 2. Sections are COO relations

Every section is a relation: `arity` columns, `kind` per column
(`u32 idx | u64 val | bytes8 nibble-exact`), `rows` row count, then the
row array. The schema section says which columns exist and which
invariants a section claims — schema is a relation too (self-describing
to the bottom).

| type | name | rows | notes |
|---|---|---|---|
| 0x0001 | `REL_NODE` | `(i, tag, l, r)` | **= the ADR-005 PIR node array verbatim** — u8 tag + u32 l + u32 r, 9B rows, postorder, hash-consed. The reducer's depack contract is unchanged: `cells + i*24`, validate once → exit3. |
| 0x0002 | `REL_ROOTS` | `(ord, node_idx)` | argument order = row order; == PIR root list. |
| 0x0003 | `REL_SYMBOLS` | `(idx, nibble-str)` | interned names; every other section references by idx. |
| 0x0004 | `REL_CAPS` | 192-bit rows | `ExtendedCapability` (offset\|perms\|type\|graph_id\|tlv_offset), standard ports 0–4 (parent, stdin, stdout, stderr, scratch). The G18 declared-set lives here. |
| 0x0005 | `REL_BYTECHUNK` | `(idx, bytes8)` | arbitrary binary payloads (section bodies, manifest, JSON if unavoidable). |
| 0x0006 | `REL_PROOF` | `(subject_hash, cert)` | proof certificates — the wire's `0x0006 PROOF_CERTIFICATE` slot kept. |
| 0x0007 | `REL_MATRIX` | `(i, j, v)` sparse | ISAR kernel matrices / any COO numeric relation; non-unit values are **nibble-exact** — IEEE only as a declared numeric-dialect realization. |
| 0x0008 | `REL_SCHEMA` | `(section_type, col, kind, invariant)` | which invariants each section claims (functional-in-i, topo-sorted, hash-consed, …). |
| 0x0009 | `REL_CATALOG` | relations | toolchain/Realization/dialect maps, ISA encodings, relocations — the spec-as-data tables. |
| 0x000A | `REL_CELLS` | 24B arena cells | optional derived section; see §3. |

Type tags `0x8000+` are dialect-private; a reader that meets an unknown
*required* relation refuses (`exit3`), one that meets an unknown
*advisory* section (flags bit1 per directory entry — reserved column)
skips it.

### 3. mmap-and-run: 9B canonical, 24B derived

The trade-off the plan deferred:

- **9B packed rows (canonical).** What ADR-005 ships. Depack is ~50
  lines of address arithmetic over `cells + i*24`; validation once at
  load; endian/canonical-form-free; content-addressable (equal graphs
  serialize identically — the Merkle hooks depend on this).
- **24B arena cells (`REL_CELLS`, derived).** Stored rows *are* runtime
  cells — zero depack, mmap the section and point `irstart`-style
  regions at it. Costs: 2.7× the bytes, bakes machine layout (tag
  qword, pointer order, little-endian) into the wire, and forfeits
  canonical form (two equal graphs can differ in cell order → distinct
  hashes → broken content addressing).

**Decided:** the wire's canonical node relation stays 9B. `REL_CELLS`
is admitted as an *optional derived section* a producer may append for
zero-depack hosts — it must name the node relation it derives from
(schema invariant `derives REL_NODE`) and a reader that doesn't know it
still works. This keeps "run a `.plex` directly" true without making
the format hostage to one host's arena layout. The redirect kernel's
persist zone (decision 044) is a consumer hint, not a wire concept.

### 4. Run vs emit is binding time, not payload

The bundle never records its role. From plan 003 §1:

- The same host/store/reducer serves both. A bundle is **run** when the
  host reduces its node relation against the declared ports
  (`paths.runtime`); it is **emitted** when the host runs the realizer
  relations with the program relation as static data (`paths.native`,
  Futamura P1/P2) and egresses bytes.
- Emitting *is* running a bundle whose output port carries bytes —
  native byte egress (W1, io=("stdin","bytes")) is the pivot; a dialect
  decode (C text, fasm text) is the same egress with a different
  output map.
- Caps are per-bundle declared data (`REL_CAPS`): runtime hosts compare
  congruence on the operation's ports; emitter-role hosts must hold
  caps ⊆ {stdin, stdout, stderr, scratch} — the G18 subset gate, now
  driven by bundle data rather than toolchain.json alone.
- Claims differ, payload doesn't: run = `OperEq` on declared ports;
  emit = seam bytes identical plus downstream congruence when the
  artifact runs.

## Consequences

- The bootstrap product shape is now one file: `H₀` reads a v3 bundle —
  `REL_NODE`+`REL_ROOTS` it already depacks; dialect maps, realization
  parameters and stage steps arrive as relations in the same file, so
  the bundle *carries its own compiler* — "pull out of thin air" is
  `REL_CATALOG` joins plus stage NFs appended as rows (W3 write-back).
- G14/G15 read as bundle statements: `H₁ = H₀(bundle)` requires the
  bundle to be a *fixed point of self-description* — the emitter that
  emits the emitter is section data in the same store it emits.
- `REL_CELLS` admits the mmap host (SASOS/UEFI realizations) without
  forking the format — declared dialect, not ambient convention.
- **Not decided here** (recorded as open): the nibble-exact encodings
  for `REL_MATRIX` values (IEEE-vs-nibble belongs to the numeric
  dialect work); join-as-fused-rule admissibility still wants the
  `OperEq` proof (plan 003 §0, research item); bundle *signing*
  (beyond Merkle identity) is deferred to the provenance layer.
- The three old headers are legacy reference in `isa-physics`; nothing
  here reads them, and plexus remains idea-reference only.
