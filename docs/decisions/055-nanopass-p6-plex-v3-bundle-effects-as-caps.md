# 055 — nanopass phase 6: .plex v3 bundle container + effects-as-capabilities

## Status

implemented and gated (gate 18).  `host/plex_bundle.py` is the v3
archive: the stage DAG + artifact keys + realization + evidence +
capabilities + image payload in ONE self-contained binary, written
beside `manifest.json` by `emit_image._write_manifest` on both
decompose paths.

## Wire format

Header: `PLEX` magic, u8 version=3, u8 flags, u16 header_size,
u32 n_sections.  Directory: n_sections x 32B rows
`{type,arity,kind,rsvd,offset,length,rows}`; every payload 8B-aligned.

Role-table kinds, all fixed-width rows over an interned string pool
(u32 off+len refs):

- `STR` — string pool bytes
- `STAGES` — `{name,artifact,key,runner}` per stage row
- `DEPS` — `{src,dst}` COO edges in DECLARED order (preserved, never
  re-sorted — reconstruction must reproduce the manifest's declared
  dependency order exactly)
- `QUERIES` — `{stage,blob,digest}` blob refs
- `EVIDENCE` — `{k,v}` decode counters / creation metadata
- `CAPS` — `{name,mode-or-ports}` for declared ports plus
  `binding -> served-ports` rows
- `IMAGE` — raw emitted image payload

## Capabilities as data

`check_bundle_caps(bundle, declared)` enforces bundle caps ⊆ the
declared caps dict — enforced at WRITE time inside
`emit_chain._write_bundle` (emit raises `NotRealized` rather than
produce an archive claiming more than the record, after a
`read_bundle` self-check on its own output), and the same predicate is
the loader-side contract: the gate verifies a widened archive is
rejected by it.  The capability surface is exactly what the toolchain record
declares: `ports` ({name: R|W|RW|RW+grow}) and `os` bindings
({import: [served-ports]}, `[]` = intrinsic).

Found-and-fixed in the same pass: the P5 MT record declared
`"threads": "spawn/join"` as a port — outside the R/W/RW mode grammar.
Removed; the thread APIs (`CreateThread`, `WaitForMultipleObjects`,
`CloseHandle`, `ExitThread`) stay declared as intrinsic `[]` os
bindings, and `caps_gate` verifies used=10 declared=10 for the MT
record.  An "effect" that isn't a byte channel is an intrinsic
binding, not a port — the schema already had the right shape.

## Reconstruction discipline

`sections_manifest(bundle)` rebuilds the `plex.stage-manifest/1` dict
field-for-field — verified equal to the manifest `emit_image` wrote.
The one real bug found in gate development: an early version re-sorted
reconstructed dep edges by stage index, which silently reordered the
manifest's declared `["program.items", "link.sections"]` into
`["link.sections", "program.items"]`.  The fix preserves encoded
insertion order — round-trip equality is defined on DECLARED order,
not topological order.

## Verification (gate 18, `gate_plex_bundle`)

- pack/read round-trip on a synthetic manifest+caps+image
- `sections_manifest(read(pack(m))) == m` including dep order
- emit-produced bundle (real `_write_manifest` output) parses, image
  bytes equal, caps ⊆ `x86_64.win64.ir` record
- refusals: bad magic, version != 3, truncated header, truncated
  directory, section span outside archive, missing required section,
  malformed kind/arity, dangling string ref, widened caps

## Boundaries

- The archive is emission-side only: the KERNEL-side `.plex` directory
  depacker (native runtime ingesting a bundle and resolving stage
  artifacts itself) is NOT built — that is the deferred
  ".plex wire format as native input" item, now unblocked because the
  wire format exists.
- `manifest.json` stays the human-readable projection; `image.plex` is
  the self-contained artifact.  Both are written; neither is derived
  from the other at read time (replay uses the JSON; the bundle is
  independently verified against it).
- Deterministic encoding: string pool is interned in first-use order,
  sections are written in a fixed kind order — same inputs give
  byte-identical archives.
