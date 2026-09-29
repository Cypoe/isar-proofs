"""
xisa_gate — G12: cross-ISA reducer parity (quotient/congruence,
stdout+stderr+rc).

Emits the linux.lo reducer for x86_64 / aarch64 / riscv64 via
seed.emit(R, toolchain.by_name(tc)) into C:\\tmp\\isar_xisa\\, runs every
(variant, case) under WSL (binfmt executes aarch64/riscv64 ELFs
directly) and requires the (stdout, stderr, rc) triple to be IDENTICAL
across the three ISAs, with expected rcs (invalid -> 3, fuel -> 2,
others -> 0).

Variants: plain / fuse_s / audit (rules= histogram on stderr) / fuel
(fuel=10, n=24 tower only).  Never prints or records wall time —
QEMU-time is not a measurement.

Exit 1 on any mismatch; exit 77 when WSL or the qemu binfmt handlers
are missing.
"""
from __future__ import annotations

import os
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

WORK = r"C:\tmp\isar_xisa"
WWORK = "/mnt/c/tmp/isar_xisa"

ISAS = (("x86_64", "x86_64.linux.lo"),
        ("aarch64", "aarch64.linux.lo"),
        ("riscv64", "riscv64.linux.lo"))

VARIANTS = (
    ("plain", seed.Realization(abi="linux")),
    ("fuse", seed.Realization(abi="linux", fuse_s=True)),
    ("audit", seed.Realization(abi="linux", audit=True)),
    ("fuel", seed.Realization(abi="linux", fuel=10)),
)


def tower(n: int) -> str:
    """(W I)^n K — iterated application of (W I) around K."""
    t = "K"
    for _ in range(n):
        t = "W I @ " + t + " @"
    return t


# (name, stdin bytes, expected rc on non-fuel builds)
CASES = (
    ("i", b"I\n", 0),
    ("ki", b"K I @\n", 0),
    ("skki", b"S K K I @ @ @\n", 0),
    ("bwc", b"B W I @ B B C K @ @ @ I @ @\n", 0),
    ("wi", b"W I @ K @\n", 0),
    ("empty", b"", 0),
    ("bad", b"(\n", 3),
    ("t24", (tower(24) + "\n").encode(), 0),
    ("t28", (tower(28) + "\n").encode(), 0),
)


def _wsl_tool(name: str) -> bool:
    try:
        return subprocess.run(
            ["wsl", "-e", "sh", "-c", f"command -v {name}"],
            capture_output=True, timeout=30).returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def available() -> bool:
    return (_wsl_tool("true")
            and _wsl_tool("qemu-aarch64-static")
            and _wsl_tool("qemu-riscv64-static"))


def emit_all() -> None:
    os.makedirs(os.path.join(WORK, "elf"), exist_ok=True)
    os.makedirs(os.path.join(WORK, "cases"), exist_ok=True)
    for name, data, _rc in CASES:
        with open(os.path.join(WORK, "cases", name + ".bin"), "wb") as f:
            f.write(data)
    for isan, tc_name in ISAS:
        tc = toolchain.by_name(tc_name)
        for vname, R in VARIANTS:
            out = os.path.join(WORK, "elf", f"{isan}-{vname}.elf")
            with open(out, "wb") as f:
                f.write(seed.emit(R, tc=tc))


RUN_SH = """\
#!/bin/bash
cd %(wwork)s || exit 3
chmod +x elf/*.elf
rm -rf out
mkdir -p out
CASES="i ki skki bwc wi empty bad t24 t28"
for isa in x86_64 aarch64 riscv64; do
  for v in plain fuse audit; do
    for c in $CASES; do
      b=out/$isa-$v-$c
      ./elf/$isa-$v.elf < cases/$c.bin > $b.out 2> $b.err
      echo $? > $b.rc
    done
  done
  b=out/$isa-fuel-t24
  ./elf/$isa-fuel.elf < cases/t24.bin > $b.out 2> $b.err
  echo $? > $b.rc
done
"""


def main() -> int:
    if not available():
        print("SKIP xisa_gate (wsl/qemu-aarch64-static/"
              "qemu-riscv64-static missing)")
        return 77
    emit_all()
    with open(os.path.join(WORK, "run.sh"), "w", newline="\n") as f:
        f.write(RUN_SH % {"wwork": WWORK})
    env = dict(os.environ)
    env["MSYS_NO_PATHCONV"] = "1"
    cp = subprocess.run(["wsl", "-e", "bash", WWORK + "/run.sh"],
                        capture_output=True, text=True, env=env)
    if cp.returncode != 0:
        print(f"FAIL runner: rc={cp.returncode}\n{cp.stdout}{cp.stderr}")
        return 1

    ok = True
    jobs = [(v, c) for v, _R in VARIANTS for c, _d, _r in CASES
            if v != "fuel" or c == "t24"]
    for v, c in jobs:
        triples = {}
        for isan, _tc in ISAS:
            b = os.path.join(WORK, "out", f"{isan}-{v}-{c}")
            try:
                triples[isan] = (open(b + ".out", "rb").read(),
                                 open(b + ".err", "rb").read(),
                                 int(open(b + ".rc").read().strip()))
            except OSError as e:
                print(f"FAIL {v}/{c}/{isan}: {e}")
                ok = False
                break
        else:
            exp_rc = 2 if v == "fuel" else dict(
                (n, r) for n, _d, r in CASES)[c]
            same = (triples["x86_64"] == triples["aarch64"]
                    == triples["riscv64"])
            stats = triples["x86_64"][1].decode(
                "utf-8", "replace").strip().splitlines()
            stat = stats[-1] if stats else ""
            good = same and triples["x86_64"][2] == exp_rc
            ok = ok and good
            print(f"{'ok ' if good else 'FAIL'} {v:5s} {c:5s} "
                  f"rc={triples['x86_64'][2]} (want {exp_rc}) "
                  f"identical={same}  {stat}")
            if not same:
                for isan, _t in ISAS:
                    print(f"  {isan}: {triples[isan]!r:.200}")
    print(f"{'OK' if ok else 'FAIL'} xisa_gate")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
