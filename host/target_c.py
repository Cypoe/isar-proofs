"""
target_c — C11 source container writer.

Same Target record shape and two-call contract as target_pe64 /
target_elf64: symbols() before assemble, pack() after.  What changes
is the realization medium, not the stage machinery: assemble emits
C statement text (isa_c), imports name standard headers (emitted as
#include lines), data_slots become file-scope `static unsigned char`
arrays, and pack() wraps everything into a complete translation unit.

Resolution is nominal — C has no assembler-time addresses, so
symbols() is the identity name table documenting that slot names
reach the source unchanged; text_base is 0.

`compile_c`/`run_exe` are the container's exec path: emitted sources
build with a system C compiler (clang by default) and run as native
processes — the behavioral cross-verification seam against the
Python host.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Sequence, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized               # noqa: E402


def symbols(imports: Sequence[str],
            data_slots: Sequence[Tuple[str, int]]) -> Dict[str, str]:
    """Nominal symbol table: slot names reach C source as identifiers.
    No IAT exists at this layer — headers resolve at C-compile time,
    and an import that is not a header name is refused."""
    for h in imports:
        if not (h.endswith(".h") or h == h.strip("<>")):
            raise NotRealized(f"target_c: import {h!r} is not a header name")
    return {name: name for name, _sz in data_slots}


def pack(text: bytes, labels: Dict[str, int], imports: Sequence[str],
         data_slots: Sequence[Tuple[str, int]], R) -> bytes:
    """Pack assembled C text into a complete translation unit:
    generated banner + #include lines + static data slots + text.
    `labels` is kept for the caller's diagnostics (same as pe64/elf64)."""
    del labels, R
    parts: List[str] = [
        "/* target_c — generated C11 source; do not edit */",
    ]
    for h in imports:
        parts.append(f"#include <{h}>")
    if data_slots:
        parts.append("")
        for name, sz in data_slots:
            parts.append(f"static unsigned char {name}[{sz}];")
    parts.append("")
    return "\n".join(parts).encode() + text


@dataclass(frozen=True)
class Target:
    name: str         # "c"
    os: str           # "hosted" — any libc-bearing C target
    abi: str          # "c11"
    ext: str          # ".c"
    pack: Callable    # pack(text, labels, imports, data_slots, R) -> bytes
    symbols: Callable  # symbols(imports, data_slots) -> {name: ident}
    text_rva: Callable  # text_rva(imports, data_slots) -> 0 — no load
                        # address at this layer


C = Target(
    name="c",
    os="hosted",
    abi="c11",
    ext=".c",
    pack=pack,
    symbols=symbols,
    text_rva=lambda _i, _s: 0,
)


# ----------------------------------------------------------------------
# exec path: emitted sources compile via a system C compiler
# ----------------------------------------------------------------------

def find_cc() -> str:
    """First available C compiler on PATH (clang preferred)."""
    for cc in ("clang", "gcc", "cl"):
        p = shutil.which(cc)
        if p:
            return p
    raise NotRealized("no C compiler on PATH (need clang, gcc, or cl)")


def compile_c(src_path: str, out_exe: str,
              cc: Optional[str] = None) -> str:
    """Compile a generated .c to a native executable."""
    cc = cc or find_cc()
    cp = subprocess.run(
        [cc, "-std=c11", "-O1", src_path, "-o", out_exe],
        capture_output=True)
    if cp.returncode != 0:
        raise RuntimeError(
            f"{cc} failed rc={cp.returncode}: {cp.stderr[:400]!r}")
    return out_exe


def run_exe(path: str, data: bytes,
            timeout: Optional[int] = 600) -> Tuple[bytes, bytes, int]:
    """Run a compiled artifact -> (stdout, stderr, rc).
    `timeout` is a test-run guard (same discipline as target_elf64)."""
    cp = subprocess.run([path], input=data,
                        capture_output=True, timeout=timeout)
    return cp.stdout, cp.stderr, cp.returncode


def main() -> int:
    """Stage-machinery check for the C target: hand-build a Program in
    the C ISA, assemble, pack into a .c, compile with the system
    compiler, run — exit code and stdout are the observation."""
    import isa_c as _isa
    ok = True

    slots = (("blob", 4),)
    imports = ("stdio.h",)
    prog: _isa.Program = [
        ("i", "note", "stage-machinery smoke"),
        _isa.FN("int", "main", "void"),
        _isa.I("assign", "blob[2]", "42"),
        _isa.I("do", 'puts("ok")'),
        _isa.I("ret", "blob[2]"),
        _isa.I("end"),
    ]
    syms = symbols(imports, slots)
    text, labels = _isa.assemble(prog, {}, base=C.text_rva((), ()))
    c_src = C.pack(text, labels, imports, slots, None)
    src = c_src.decode()
    checks = [
        ("banner", src.startswith("/* target_c")),
        ("include", "#include <stdio.h>" in src),
        ("slot", "static unsigned char blob[4];" in src),
        ("fn open", "int main(void) {" in src),
        ("assign", "blob[2] = 42;" in src),
        ("ret", "return blob[2];" in src),
    ]
    for name, good in checks:
        print(f"  {'ok' if good else 'FAIL'} {name}")
        ok = ok and good
    # real compile+run — hard gate, no skip (same as target_elf64's wsl run)
    with tempfile.TemporaryDirectory() as td:
        c_path = os.path.join(td, "t.c")
        exe_path = os.path.join(td, "t.exe")
        with open(c_path, "wb") as f:
            f.write(c_src)
        compile_c(c_path, exe_path)
        out, err, rc = run_exe(exe_path, b"")
        good = rc == 42 and out.strip() == b"ok"
        print(f"  {'ok' if good else 'FAIL'} cc build + run: rc={rc} "
              f"stdout={out.strip()!r} stderr={err[:80]!r}")
        ok = ok and good
    print(f"{'OK' if ok else 'FAIL'} target_c")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
