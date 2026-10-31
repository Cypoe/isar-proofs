---
type: frag
id: 0059
provenance: devin-cli
ts: 2026-10-30
tags: [koru, host2, kwir, koruc, ccomp, compcert, race, toolchain]
---

# 0059 — three-lane stage race: compile path AND runtime

The 0057 race compared two binaries. This rung instruments the whole
pipeline: every stage from spec to native binary, then the binaries
themselves — three lanes now, since the ccomp (CompCert 3.5, docker)
leg already declared in `assembly.json` produces a runnable i386
`kwir_wi_ccv` in `host2/build`.

Measured by `_scratch/kdrv/race.py`: wall time everywhere, peak RSS
via Job Objects on Windows (covers whole process trees — zig→lld,
clang→ld) and `/usr/bin/time -v` inside docker where the image has it.

## Compile path (spec → binary)

| stage | wall | peak RSS |
|-------|------|----------|
| emitProgC (`lake env lean --run tools/DumpKoruFixtures.lean`) | 178.9s | 5330MB |
| clang -O0 `-std=c99` `kwir.c` → `kwir_wiw.exe` | 1.6s | 196MB |
| `ccomp -S kwir.c` → i386 `.s` (docker) | 7.4s | 226MB |
| `gcc` i386 link `+libcompcert.a` (docker) | 0.8s | — |
| koruc frontend+emit (`--deep-check`) | 4.8s | 1403MB |
| koruc full build `-OReleaseSafe` (emit+backend+native) | 24.6s | 2371MB |

Caveats carried honestly: the 179s emitProgC figure regenerates the
**whole corpus** (`specs/gen/*.c` + fixture `input.k` files) — the
kwir.c slice is not separable without instrumenting the dump; the
regen was content-identical (git clean after). koruc's input is the
transformed koru program (wirn.k), emitProgC's input is the Lean spec
— "same program" via the transform chain, not same input file.

## Runtime race

| binary | 906 (122KB out) | 905 (229KB out) | vs authority |
|--------|-----------------|------------------|--------------|
| emitProgC + clang -O0 (win64) | 2.09s / 1084MB | 4.13s / 2318MB | identical |
| emitProgC + ccomp i386 (linux/docker) | 2.36s / — | 4.07s / — | identical modulo `\r\n` |
| koruc + zig ReleaseSafe (win64) | 0.32s / 586MB | 0.80s / 1775MB | identical |

The ccomp binary's one-byte-short output is the CRT text-mode newline
(`\n` vs `\r\n`) — content-identical, same class as the driver fix
in 0057. RSS for the i386 run is unmeasured (the slim ccrun image has
no `/usr/bin/time`; wall includes docker container start ~0.4s).

## What the numbers actually say

- **koruc+zig wins both axes**: ~25s emit→binary and the fastest
  runtime by 2.6–6.5× with the least RSS. Its compile path is a
  different input (koru surface), so "faster compiler" is a lane
  property, not a same-input comparison.
- **CompCert's binary holds up at runtime**: within ~13% of
  clang -O0 — remarkable for verified codegen with essentially no
  optimization — and its compile step is the only machine-checked
  leg in the race (link+run unverified).
- **emitProgC is the correctness-authority lane, not the speed
  lane**: the Lean emit is the corpus regen bottleneck (179s/5.3GB),
  but it's the step that carries the checked semantics. The
  interesting split isn't clang-vs-koruc — it's that the
  verified-compile lane (ccv) costs ~8s over the fast C lane, so
  machine-checked compilation of this program is cheap; the
  expensive part is generating the C in the first place.

For the self-hosting loop this is the honest picture: the
ccomp-verified leg is runtime-competitive with -O0 clang; koruc is
the lane to race for throughput; emitProgC remains the semantics
authority whose emit cost lives upstream of both.

**ccomp on the koru lane — named refusal.** Probed
`zig build-obj output_emitted.zig -target x86_64-linux-gnu -ofmt=c`:
the zig C backend emits a complete 216K-line `out.c`, but it
`#include "zig.h"` which pulls hosted glibc headers
(`limits.h` → `sys/cdefs.h`) that the freestanding compcert image
lacks — ccomp dies in the preprocessor before seeing the program.
A koru-side ccomp axis needs either a koruc C backend (upstream
feature) or a freestanding `zig.h` shim; neither exists today, so
the axis is declared blocked, not silently absent.

Artifacts: `_scratch/kdrv/race.py`, `race_report.json`,
`host2/build/kwir_wi_ccv{,.s}`, `_scratch/kdrv/out.c` (zig
C-backend output, kept as the probe's evidence).
