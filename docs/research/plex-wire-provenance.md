# PLEX wire / sparse store: where each idea actually lives

This file corrects `chat-history.md`. The off-site chat attributed a sparse 4D tensor (`Coord (i,s,a,r)`, `Value=float`, `encode(plex)`) and `encode_bundle`/`decode_bundle` to `isa-physics/plex/core/format.py` and `bundle.py`. Those files contain neither.

| idea | real location |
|---|---|
| `U[i,s,a,r]=value` sparse COO, float values | `isar-proofs/visualizations/isar_substrate.html` (hello-world syscall tensor, COO card, sparse diff) |
| arbitrary-precision floats (nibble sign/exp/digits) | `isa-physics/plex/lib/symbolic/arbitrary_precision.py` (mirror in `plex-agent/src/symbolic/`) |
| number parsing, scientific notation | `plex/lib/symbolic/base_systems.py` |
| quantity calculus Q=(S,Y,M,E) | `plex/lib/structural_arithmetic/tensor_quantity.py` |
| sparse kernel axioms | `plex-agent/src/phi/core/tensor_primitives.py` |
| tensor coords in wire | `plexus/crates/plex-core/src/wire.rs` TLV `0x0007 TENSOR_PAYLOAD` (plexus is retired) |
| `.plex` container | `plex/core/format.py`: header + 4×4×4 nibble kernel + bytechunk + JSON TLV |
| bundle resolution | `plex/core/bundle.py`: a 1–4 lookup order; its generators are stubs |
| V2 container with caps/deps TLV | `plex-agent/src/dialect/bundle.py` |

## Incompatible headers

There are at least three incompatible PLEX headers:

- Python `format.py`: u8 version, u8 flags, u16 header size
- Rust `wire.rs`: u32 version, u32 flags, Adler32 per TLV
- plex-agent V2: 68 reserved bytes, kernel at offset 76

Declare one canonical header before PIR goes in as a TLV payload.

## Relationship to the isar-proofs host

- ADR-005 weighed `.plex` explicitly. `.plex` is the container; PIR is the term-graph layer (nodes, sharing) that `.plex` should wrap.
- **Fusion (revised):** PIR is not a different payload from the COO store. It *is* COO with invariants: rows `(i, tag, l, r)` with implicit value 1, functional in `i`, topologically sorted (`l, r < i`), and hash-consed. Kernel matrices, bytechunks, nibble numbers, symbol interning and data relations (catalog, dialect maps, ISA encodings, relocations) are all relations in one COO store sectioned by TLV. Non-unit values must be nibble-exact; IEEE is only a declared numeric-dialect realization.
- The real distinction is in execution, not payload: **rewrite** (reduction on the node relation; the proved semantics) versus **join** (indexed lookup on data relations). spec-as-term encodes the catalog as terms, which is why `pathOf` takes about 400K steps × 24 and spec_term takes 5 h. A native join is admissible only as a fused rule with an `OperEq` argument, following the `fuse_s` precedent.
- Bootstrap in the fused store: stage NFs are appended as rows (write-back), a fixed native driver loops over roots, and egress writes bytes. This replaces the Python decomposition (crossings in emit_chain: `_l0_nf` glue, `decode_program`/`decode_link`, the `assemble_staged` fold, `_decode_bytecells`). The blocker is memory retention (027/028) rather than Python; write-back plus per-root reset is the memory-safe path.
- **Capabilities and apertures in the same store.** `plex-agent/src/dialect/capability.py` defines `ExtendedCapability` (192 bits: offset|perms|type|graph_id|tlv_offset) and standard ports 0–4 (parent, stdin, stdout, stderr, scratch). `plexus/crates/plex-os/src/exo.rs` defines `HardwareAperture` (phys_base, size, kind, read_only, contains_address), and `sasos_alloc.rs` a flat lock-free arena.
  - Our kernels already use those ports implicitly: stdin input, stdout NF, stderr stats, scratch = bump arena, the res blob = a read-only aperture. The res graft range check `[rescells, resend)` is a `contains_address`.
  - Making caps explicit ties together three things. Caps declare the effect surface. `O` selects which ports a claim compares. "Legal for this host" becomes a structural gate: the image's syscall/import set must be a subset of the declared caps.
  - Verify once at load (the PIR depack validator already exits 3), then run unchecked. Proofs go in `.plex` TLV 0x0006 PROOF_CERTIFICATE.
- **Running a .plex directly:** the IR/res kernels already run PIR with no parser (index → `cells + i*24`). The remaining choice for mmap-and-run is whether stored rows equal arena cells: zero depack, but 24 B vs 9 B per node.
- **SASOS as a Realization, not a system:** `x86_64.uefi.lo` and `pe64.uefi` are already declared (NotRealized). A SASOS host is abi=uefi, with an aperture map instead of VirtualAlloc/syscalls, emitted from the same routine graph and gated the same way. The plexus benchmark claims (`benchmarks/STATUS.md`) have not been verified; the tree is retired.
- Gates for H₀→H₁→H₂→H′:
  - G14: `H₁ == H₂ == seed.emit(R_host)`.
  - G15: `H₁(bundle + peepholeOf) == seed.emit(R(peephole=True))`, and H′ is a fixed point. The seed route is the independent oracle.
- `native.x86_64.res` already loads a PIR blob once and reduces it without Python.
- `programOf`, `linkOf`, `assembleOf` and `pack2Of` are terms.
- The missing native operation is byte egress: writing a byte-list NF as raw bytes, which is currently Python's `_decode_bytecells`. With that, H₀ plus a PIR bundle produces an image without Python in between, checked by G10.
- Do not link or port the plexus Rust crate as the native reducer. That would be a second implementation. Use it as a format and idea reference only.
