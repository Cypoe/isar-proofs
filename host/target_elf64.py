"""
target_elf64 — ELF64 (Linux x86-64 static executable) container writer.

Mirrors target_pe64: same Target record shape, same two-call contract
(symbols() before assemble, pack() after).  Layout is the canonical
static pair — one RX PT_LOAD covering ehdr+phdrs+.text, one RW PT_LOAD
covering .data — so both bases are constants independent of .text size
(the emit chain needs data symbols before the text length exists):

  file : ehdr(64) phdr(56) phdr(56) | .text | pad->page | .data
  vaddr: 0x400000 ................. | 0x4000B0          | 0x500000

No section headers (execution needs none), no imports: a static ELF has
no IAT — a non-empty `imports` is refused (NotRealized), never dropped.
`wsl_path`/`prepare`/`run_elf` are the container's exec path: emitted
images run under WSL on drvfs (/mnt/<drive>/...).
"""
from __future__ import annotations

import os
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from types import SimpleNamespace
from typing import Callable, Dict, List, Sequence, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from toolchain import NotRealized               # noqa: E402

VBASE = 0x400000
EHDR_SIZE = 64
PHDR_SIZE = 56
HDRS = EHDR_SIZE + 2 * PHDR_SIZE        # 0xB0
TEXT_VA = VBASE + HDRS                  # 0x4000B0 — _start lands here
DATA_VA = 0x500000                      # .data segment base (fixed)
PAGE = 0x1000

ET_EXEC, EM_X86_64 = 2, 0x3E
PT_LOAD = 1
PF_X, PF_W, PF_R = 1, 2, 4


def _align(v: int, a: int) -> int:
    return (v + a - 1) // a * a


def build_data(data_slots: Sequence[Tuple[str, int]]) -> Tuple[bytes, Dict[str, int]]:
    syms: Dict[str, int] = {}
    off = 0
    for name, sz in data_slots:
        syms[name] = DATA_VA + off
        off += sz
    return b"\x00" * off, syms


def symbols(imports: Sequence[str],
            data_slots: Sequence[Tuple[str, int]]) -> Dict[str, int]:
    """Absolute data VAs — what .text resolves against.  A static ELF has
    no import table: non-empty imports are refused, never ignored."""
    if imports:
        raise NotRealized(
            f"elf64: imports {tuple(imports)!r} not realized (no IAT)")
    _, ds = build_data(data_slots)
    return ds


def pack(text: bytes, labels: Dict[str, int], imports: Sequence[str],
         data_slots: Sequence[Tuple[str, int]], R) -> bytes:
    """Pack an assembled .text into a static ELF64 image: ehdr + 2 phdrs +
    text (RX @VBASE) + page pad + data (RW @DATA_VA)."""
    if imports:
        raise NotRealized(
            f"elf64: imports {tuple(imports)!r} not realized (no IAT)")
    data, _ds = build_data(data_slots)
    entry = labels["_start"]
    data_off = _align(HDRS + len(text), PAGE)

    ident = b"\x7fELF" + bytes((2, 1, 1, 0)) + b"\x00" * 8
    ehdr = ident + struct.pack(
        "<HHIQQQIHHHHHH",
        ET_EXEC, EM_X86_64, 1,            # type, machine, version
        entry, EHDR_SIZE, 0, 0,           # entry, phoff, shoff, flags
        EHDR_SIZE, PHDR_SIZE, 2,          # ehsize, phentsize, phnum
        0, 0, 0)                          # shentsize, shnum, shstrndx
    assert len(ehdr) == EHDR_SIZE, len(ehdr)
    seg1 = HDRS + len(text)
    phdrs = struct.pack(
        "<IIQQQQQQ", PT_LOAD, PF_R | PF_X,
        0, VBASE, VBASE, seg1, seg1, PAGE) + struct.pack(
        "<IIQQQQQQ", PT_LOAD, PF_R | PF_W,
        data_off, DATA_VA, DATA_VA, len(data), len(data), PAGE)
    out = ehdr + phdrs + text
    out += b"\x00" * (data_off - len(out))
    return out + data


@dataclass(frozen=True)
class Target:
    name: str         # "elf64"
    os: str           # "linux"
    abi: str          # "linux"
    ext: str          # ".elf"
    pack: Callable    # pack(text, labels, imports, data_slots, R) -> bytes
    symbols: Callable  # symbols(imports, data_slots) -> {name: vaddr}
    text_base: int    # TEXT_VA — .text load address for assembly


ELF64 = Target(
    name="elf64",
    os="linux",
    abi="linux",
    ext=".elf",
    pack=pack,
    symbols=symbols,
    text_base=TEXT_VA,
)


# ----------------------------------------------------------------------
# exec path: emitted images run under WSL (drvfs /mnt/<drive>/...)
# ----------------------------------------------------------------------

def wsl_path(path: str) -> str:
    """Windows path -> WSL path (C:\\x\\y -> /mnt/c/x/y)."""
    p = os.path.abspath(path).replace("\\", "/")
    if len(p) < 3 or p[1] != ":":
        raise ValueError(f"cannot translate to a WSL path: {path!r}")
    return f"/mnt/{p[0].lower()}{p[2:]}"


def prepare(path: str) -> str:
    """chmod +x through wsl (drvfs metadata) so the image executes."""
    cp = subprocess.run(["wsl", "-e", "chmod", "+x", wsl_path(path)],
                        capture_output=True)
    if cp.returncode != 0:
        raise RuntimeError(
            f"wsl chmod +x failed rc={cp.returncode}: {cp.stderr!r}")
    return path


def run_elf(path: str, data: bytes) -> Tuple[bytes, bytes, int]:
    """Execute an emitted ELF under WSL -> (stdout, stderr, rc)."""
    cp = subprocess.run(["wsl", "-e", wsl_path(path)], input=data,
                        capture_output=True, timeout=600)
    return cp.stdout, cp.stderr, cp.returncode


def main() -> int:
    ok = True
    import isa_x86_64 as _isa

    slots = (("x", 8),)
    prog = [
        _isa.LBL("_start"),
        _isa.I("mov_r32_imm32", "edi", 42),
        _isa.I("mov_r32_imm32", "eax", 60),       # exit(42)
        _isa.I("syscall"),
    ]
    text, labels = _isa.assemble(prog, symbols((), slots), base=TEXT_VA)
    elf = pack(text, labels, (), slots, SimpleNamespace())
    checks = [
        ("\\x7fELF", elf[:4] == b"\x7fELF"),
        ("ELFCLASS64+LE", elf[4] == 2 and elf[5] == 1),
        ("ET_EXEC", struct.unpack_from("<H", elf, 16)[0] == ET_EXEC),
        ("EM_X86_64", struct.unpack_from("<H", elf, 18)[0] == EM_X86_64),
        ("e_entry==_start",
         struct.unpack_from("<Q", elf, 24)[0] == labels["_start"]),
        ("phnum=2", struct.unpack_from("<H", elf, 56)[0] == 2),
        ("seg2 vaddr",
         struct.unpack_from("<Q", elf, EHDR_SIZE + PHDR_SIZE + 16)[0]
         == DATA_VA),
    ]
    for name, good in checks:
        print(f"  {'ok' if good else 'FAIL'} {name}")
        ok = ok and good
    # imports must refuse, never drop
    try:
        symbols(("mmap",), slots)
        print("  FAIL imports accepted silently")
        ok = False
    except NotRealized as e:
        print(f"  ok refused imports: {e}")
    # real exec under wsl — hard gate, no skip
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, "t.elf")
        with open(path, "wb") as f:
            f.write(elf)
        prepare(path)
        out, err, rc = run_elf(path, b"")
        good = rc == 42
        print(f"  {'ok' if good else 'FAIL'} wsl exec exit(42): rc={rc} "
              f"stderr={err[:80]!r}")
        ok = ok and good
    print(f"{'OK' if ok else 'FAIL'} target_elf64")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
