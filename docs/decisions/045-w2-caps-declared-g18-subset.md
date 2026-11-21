# 045 — W2: capability declaration + G18 cap-subset gate (2026-10)

## Declaration shape (toolchain.json `routines.*.caps`)

- `ports`: semantic surface — `{stdin: R, stdout: W, stderr: W,
  scratch: RW+grow}` on every realized routines entry (all kernels
  write a `steps=/alloc=` stats line to stderr, so stderr is always
  used). `payload` exists in the port vocabulary for runtime hosts.
- `os`: raw OS bindings → port list. `kernel32!ReadFile → [stdin]`,
  `kernel32!WriteFile → [stdout, stderr]`, `kernel32!VirtualAlloc/
  VirtualFree → [scratch]`, `kernel32!ExitProcess → []` (intrinsic,
  no port). Linux syscall tables likewise (`sys:0/1/9/60` x86_64;
  `sys:63/64/222/93` arm64+rv64). C hosted: `libc!malloc/fread/
  putchar/fprintf/exit` + `includes` for the header set.
- The binding→port map is **data in the spec**, not code in the gate —
  same "strategy is data" rule as Realization.

## G18 (host/caps_gate.py, tier fast, ~0.3s)

- Extracts the **used** set from program data, never the declaration:
  win64/pe64+fasmg → `rts.imports` (IAT surface); linux ABIs → SYS_*
  immediates in force at each `syscall`/`svc_imm16`/`ecall` trap site
  (number reg eax/x8/a7; `xor eax,eax` reads as sys:0); C → `libc!fn`
  call sites in emitted items + header ⊆ `includes`.
- Checks used ⊆ declared, each used binding's port list intersects
  declared ports, port vocabulary/modes well-formed, and
  **emitter-role** hosts (path=native, currently xdu) ⊆
  {stdin, stdout, stderr, scratch}.
- Negative cases in-process: undeclared used binding and emitter
  claiming payload both rejected.
- Toolchains are covered by routines-component resolution, not full
  `resolve(tc)` — see finding below.

## Finding: resolve only what a gate inspects

`toolchain.resolve(tc)` resolves dialect+isa+routines+target — and
`import spec_term` (packed.ir dialect) builds the whole catalog term
at module level: **~3min**. The gate's first version paid that per
invocation. Resolving the routines `Component` directly
(`components()["routines"][name].resolve()`) drops G18 from ~174s to
~0.3s and widens coverage: toolchains with realized routines but
declared dialects (lambda.bracket, phi.rel) are now checked too.
Any future gate that only reads routine/ISA program data should do the
same.
