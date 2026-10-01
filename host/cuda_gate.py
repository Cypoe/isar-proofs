"""
cuda_gate — G17: CUDA evaluator behavioural parity (quotient/congruence,
operEq NF + steps/alloc + rc).

Runs ir_cuda.exe (built via build_cuda.bat conventions; a -DFUSE_S twin
covers the fused realization) and the emitted native.x86_64.pe.ir kernel
on IDENTICAL packed-IR batches and requires:

  - identical stdout (one NF postfix line per root, in root order)
  - identical stderr totals (steps=/alloc= aggregates)
  - identical return codes (0 clean, 2 fuel, 3 malformed)

Corpus:
  - the xisa probe corpus as PIR — the same terms G12 feeds the linux
    kernels, bc_compile'd and pack_ir'd into one multi-root batch
  - the G9b instantiation batch — _residual_state()'s real Futamura
    instance terms, packed the same way
  - fuel leg: the t24/t28 towers under a small per-root budget —
    native fuel is baked into the emitted exe, CUDA's is IR_CUDA_FUEL
  - malformed legs: bad version, truncated body, bad tag, forward
    reference — both readers must refuse with rc 3

Both views run: default and FUSE_S.  Never prints or records wall time
— GPU-vs-CPU tempo is not the claim.

Exit 1 on any mismatch; exit 77 when nvcc or a CUDA device is absent.
"""
from __future__ import annotations

import os
import re
import struct
import subprocess
import sys

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_SEED_DIR = os.path.join(_HOST, "..", "seed")
if _SEED_DIR not in sys.path:
    sys.path.insert(0, _SEED_DIR)

import seed  # noqa: E402
import toolchain  # noqa: E402
import reduce  # noqa: E402


def _tok(s: str):
    """token text -> reduce.T — pack_ir takes spec_term's term type."""
    return seed.t_to_host(seed.bc_compile(s + "\n"), reduce)

WORK = os.path.join(_HOST, "emit_work")
VCVARS = (r"C:\Program Files\Microsoft Visual Studio\2022\Community"
          r"\VC\Auxiliary\Build\vcvars64.bat")

IR_TC = "native.x86_64.pe.ir"


def tower(n: int) -> str:
    """(W I)^n K — iterated application of (W I) around K."""
    t = "K"
    for _ in range(n):
        t = "W I @ " + t + " @"
    return t


# the xisa probe corpus as terms (the malformed legs below cover input
# validation — everything here must parse)
TOKENS = ("I", "K I @", "S K K I @ @ @",
          "B W I @ B B C K @ @ @ I @ @",
          "W I @ K @", tower(24), tower(28))


def available() -> bool:
    try:
        cp = subprocess.run(["nvcc", "--version"], capture_output=True,
                            timeout=30)
        if cp.returncode != 0:
            return False
        import ctypes
        n = ctypes.cdll.LoadLibrary("nvcuda.dll")
        return n.cuInit(0) == 0
    except (OSError, subprocess.TimeoutExpired, AttributeError):
        return False


def _build_cuda(out: str, fuse_s: bool) -> None:
    """nvcc build through the build_cuda.bat convention (vcvars64)."""
    define = " -DFUSE_S" if fuse_s else ""
    bat = os.path.join(WORK, "_g17_build.bat")
    with open(bat, "w", newline="\r\n") as f:
        f.write("@echo off\n")
        f.write(f'call "{VCVARS}" >nul\n')
        f.write("if errorlevel 1 exit /b 1\n")
        f.write(f'nvcc -O2{define} -o "{out}" "{_HOST}\\ir_cuda.cu"\n')
        f.write("exit /b %errorlevel%\n")
    cp = subprocess.run(["cmd", "/c", bat], capture_output=True,
                        timeout=600)
    if cp.returncode != 0 or not os.path.exists(out):
        raise RuntimeError(
            f"nvcc build failed rc={cp.returncode}: "
            f"{cp.stdout.decode(errors='replace')[-800:]}"
            f"{cp.stderr.decode(errors='replace')[-800:]}")


def _run(exe: str, blob: bytes, env_extra=None, timeout=3600):
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    return subprocess.run([exe], input=blob, capture_output=True,
                          timeout=timeout, env=env)


def _stats(stderr: bytes):
    m = re.search(rb"steps=(\d+)\s+alloc=(\d+)", stderr)
    return (int(m.group(1)), int(m.group(2))) if m else None


def main() -> int:
    if not available():
        print("SKIP cuda_gate (nvcc or CUDA device missing)")
        return 77

    import spec_term as st  # heavy import — only after the env check

    os.makedirs(WORK, exist_ok=True)
    cuda = os.path.join(WORK, "ir_cuda.exe")
    cuda_f = os.path.join(WORK, "ir_cuda_fuse.exe")
    print("building ir_cuda (default + FUSE_S) ...", flush=True)
    _build_cuda(cuda, fuse_s=False)
    _build_cuda(cuda_f, fuse_s=True)

    native = seed._exe_for(seed.Realization(), tc=toolchain.by_name(IR_TC))
    native_f = seed._exe_for(seed.Realization(fuse_s=True),
                             tc=toolchain.by_name(IR_TC))
    native_fuel = seed._exe_for(seed.Realization(fuel=10),
                                tc=toolchain.by_name(IR_TC))

    ok = True

    def leg(name: str, exe_a: str, exe_b: str, blob: bytes,
            n_roots: int, exp_rc: int = 0, cuda_env=None):
        """One (cuda, native) comparison on the same PIR blob."""
        nonlocal ok
        a = _run(exe_a, blob, env_extra=cuda_env)
        b = _run(exe_b, blob)
        out_eq = a.stdout == b.stdout
        stats_a, stats_b = _stats(a.stderr), _stats(b.stderr)
        stat_eq = stats_a == stats_b
        n_lines = len(a.stdout.splitlines())
        good = (out_eq and stat_eq and a.returncode == exp_rc
                and b.returncode == exp_rc
                and (exp_rc != 0 or n_lines == n_roots))
        ok = ok and good
        print(f"{'ok ' if good else 'FAIL'} {name}: "
              f"rc {a.returncode}/{b.returncode} (want {exp_rc}) "
              f"nf_equal={out_eq} ({n_lines}/{n_roots} roots) "
              f"stats_equal={stat_eq} {stats_a}", flush=True)
        if not good:
            print(f"  cuda:   out={a.stdout[:200]!r} "
                  f"err={a.stderr[:200]!r}")
            print(f"  native: out={b.stdout[:200]!r} "
                  f"err={b.stderr[:200]!r}")

    # --- xisa corpus as one multi-root batch -------------------------
    terms = [_tok(t) for t in TOKENS]
    blob = st.pack_ir(*terms)
    leg("xisa/plain", cuda, native, blob, len(terms))
    leg("xisa/fuse_s", cuda_f, native_f, blob, len(terms))

    # --- G9b instantiation batch --------------------------------------
    # the real Futamura instance queries — the batch shape the fork
    # pool already carries.  The CUDA arena is ONE shared bump counter
    # across all roots of a stream (the native kernel DECOMMIT-resets
    # per root instead) — ~935K-node terms × 24 need ~343M cells >
    # the 2^28 cells the 3GB default holds (Cell = 12B).  Sizing the
    # arena for the stream is the host's declared realization knob —
    # same contract as Realization.ir_arena_bytes on the exe.
    insts = st._residual_state()[3]
    if insts:
        iblob = st.pack_ir(*insts)
        leg("g9b/plain", cuda, native, iblob, len(insts),
            cuda_env={"IR_CUDA_HEAP_MB": "8192"})
        leg("g9b/fuse_s", cuda_f, native_f, iblob, len(insts),
            cuda_env={"IR_CUDA_HEAP_MB": "8192"})

    # --- fuel: heavy towers must die at rc 2 --------------------------
    ft = [_tok(tower(24)), _tok(tower(28))]
    fblob = st.pack_ir(*ft)
    a = _run(cuda, fblob, env_extra={"IR_CUDA_FUEL": "10"})
    b = _run(native_fuel, fblob)
    good = a.returncode == 2 and b.returncode == 2
    ok = ok and good
    print(f"{'ok ' if good else 'FAIL'} fuel/t24+28: "
          f"rc {a.returncode}/{b.returncode} (want 2)", flush=True)

    # --- malformed legs: both readers refuse with rc 3 -----------------
    one = st.pack_ir(terms[0])
    tag_at = 16 + 4                # hdr(16) + roots[1](4) -> node0.tag
    bad = {
        "badversion": b"PIR\x00\x02\x00\x00\x00" + b"\x00" * 8,
        "truncated": one[:len(one) - 3],
        "badtag": one[:tag_at] + b"\x07" + one[tag_at + 1:],
        # node0 = app(0,0): self-edge — the l,r < i invariant fails
        "selfref": struct.pack("<IIII", 0x30524950, 1, 1, 1)
                   + struct.pack("<I", 0) + b"\x00" * 9,
    }
    for name, bb in bad.items():
        a = _run(cuda, bb)
        b = _run(native, bb)
        good = a.returncode == 3 and b.returncode == 3
        ok = ok and good
        print(f"{'ok ' if good else 'FAIL'} malformed/{name}: "
              f"rc {a.returncode}/{b.returncode} (want 3)", flush=True)

    print(f"{'OK' if ok else 'FAIL'} cuda_gate", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
