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
from typing import Callable, Dict, List, Optional, Sequence, Tuple

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

ET_EXEC, EM_X86_64, EM_AARCH64, EM_RISCV = 2, 0x3E, 0xB7, 0xF3
PT_LOAD = 1
PF_X, PF_W, PF_R = 1, 2, 4

# ET_REL section/symbol constants for pack_obj
ET_REL = 1
SHT_NULL, SHT_PROGBITS, SHT_SYMTAB, SHT_STRTAB, SHT_RELA, SHT_NOBITS = \
    0, 1, 2, 3, 4, 8
SHF_WRITE, SHF_ALLOC, SHF_EXECINSTR = 1, 2, 4
STB_LOCAL, STB_GLOBAL = 0, 1
STT_NOTYPE, STT_OBJECT, STT_FUNC, STT_SECTION = 0, 1, 2, 3
SHN_UNDEF = 0


def _align(v: int, a: int) -> int:
    return (v + a - 1) // a * a


def build_data(data_slots) -> Tuple[bytes, Dict[str, int]]:
    """Slots are (name, size) zero-fill or (name, size, init) with
    initialized content (residual payloads ride .data)."""
    syms: Dict[str, int] = {}
    out = bytearray()
    for slot in data_slots:
        name, sz = slot[0], slot[1]
        syms[name] = DATA_VA + len(out)
        init = slot[2] if len(slot) > 2 else b""
        out += init[:sz] + b"\x00" * (sz - len(init))
    return bytes(out), syms


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
         data_slots: Sequence[Tuple[str, int]], R,
         machine: int = EM_X86_64) -> bytes:
    """Pack an assembled .text into a static ELF64 image: ehdr + 2 phdrs +
    text (RX @VBASE) + page pad + data (RW @DATA_VA).  `machine` selects
    e_machine — the container is ISA-agnostic row data."""
    if imports:
        raise NotRealized(
            f"elf64: imports {tuple(imports)!r} not realized (no IAT)")
    data, _ds = build_data(data_slots)
    entry = labels["_start"]
    data_off = _align(HDRS + len(text), PAGE)

    ident = b"\x7fELF" + bytes((2, 1, 1, 0)) + b"\x00" * 8
    ehdr = ident + struct.pack(
        "<HHIQQQIHHHHHH",
        ET_EXEC, machine, 1,              # type, machine, version
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


def pack_obj(text: bytes, labels: Dict[str, int],
             relocs: List[Tuple[int, str, int, int]],
             data_slots, R, machine: int = EM_X86_64) -> bytes:
    """Pack an ET_REL object: .text + .data + .symtab + .strtab +
    .rela.text + shdrs.  `labels` are .text-section-relative offsets
    (local FUNC symbols); `data_slots` name .data OBJECTs (global —
    the audit interface); `relocs` are (text_off, sym, rtype, addend)
    produced by isa.assemble_obj."""
    data, dsyms = build_data_rel(data_slots)
    strtab = bytearray(b"\x00")

    def _stname(s: str) -> int:
        off = len(strtab)
        strtab.extend(s.encode() + b"\x00")
        return off

    # symbol order: null, section syms, label syms (local), data (global)
    syms: List[Tuple] = [(0, STB_LOCAL << 4 | STT_NOTYPE, 0, SHN_UNDEF,
                          0, 0)]
    # st_shndx: .text=1, .data=2 (section index into the shdr table)
    SEC_TEXT, SEC_DATA = 1, 2
    syms.append((0, STB_LOCAL << 4 | STT_SECTION, 0, SEC_TEXT, 0, 0))
    syms.append((0, STB_LOCAL << 4 | STT_SECTION, 0, SEC_DATA, 0, 0))
    for name, off in labels.items():
        if name != "_start":
            syms.append((_stname(name), STB_LOCAL << 4 | STT_FUNC, 0,
                         SEC_TEXT, off, 0))
    first_global = len(syms)
    # _start is GLOBAL — the entry contract a linker resolves by name
    if "_start" in labels:
        syms.append((_stname("_start"), STB_GLOBAL << 4 | STT_FUNC, 0,
                     SEC_TEXT, labels["_start"], 0))
    symidx: Dict[str, int] = {}
    for name, off in dsyms.items():
        symidx[name] = len(syms)
        syms.append((_stname(name), STB_GLOBAL << 4 | STT_OBJECT, 0,
                     SEC_DATA, off, 0))
    symtab = b"".join(
        struct.pack("<IBBHQQ", *s) for s in syms)

    rela = b"".join(
        struct.pack("<QQq", off,
                    (symidx[sym] << 32) | rtype, addend)
        for off, sym, rtype, addend in relocs)

    # ---- layout: ehdr | .text | .data | .symtab | .strtab | .rela | shstrtab | shdrs
    shstr = bytearray(b"\x00")
    sec_names: List[int] = []
    for s in (b"", b".text", b".data", b".symtab", b".strtab",
              b".rela.text", b".shstrtab"):
        sec_names.append(len(shstr))
        shstr += s + b"\x00"

    SEC_SYMTAB, SEC_STRTAB, SEC_RELA, SEC_SHSTR = 3, 4, 5, 6
    NSEC = 7

    body = bytearray()
    body += b"\x00" * EHDR_SIZE
    sec_off = {}

    def _sec(idx: int, blob: bytes, align: int = 1) -> None:
        pad = _align(len(body), align) - len(body)
        body.extend(b"\x00" * pad)
        sec_off[idx] = (len(body), len(blob))
        body.extend(blob)

    _sec(SEC_TEXT, text, 16)
    _sec(SEC_DATA, data, 16)
    _sec(SEC_SYMTAB, symtab, 8)
    _sec(SEC_STRTAB, bytes(strtab), 1)
    _sec(SEC_RELA, rela, 8)
    _sec(SEC_SHSTR, bytes(shstr), 1)
    shoff = _align(len(body), 8)
    body += b"\x00" * (shoff - len(body))

    ident = b"\x7fELF" + bytes((2, 1, 1, 0)) + b"\x00" * 8
    ehdr = ident + struct.pack(
        "<HHIQQQIHHHHHH",
        ET_REL, machine, 1,
        0, 0, shoff, 0,
        EHDR_SIZE, 0, 0,
        64, NSEC, SEC_SHSTR)
    assert len(ehdr) == EHDR_SIZE, len(ehdr)
    body[:EHDR_SIZE] = ehdr

    def _sh(idx: int, typ: int, flags: int, align: int,
            link: int = 0, info: int = 0, entsize: int = 0) -> bytes:
        off, size = sec_off.get(idx, (0, 0))
        return struct.pack(
            "<IIQQQQIIQQ",
            sec_names[idx], typ, flags, 0, off, size,
            link, info, align, entsize)

    shdrs = _sh(0, SHT_NULL, 0, 0)
    shdrs += _sh(SEC_TEXT, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 16)
    shdrs += _sh(SEC_DATA, SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, 16)
    shdrs += _sh(SEC_SYMTAB, SHT_SYMTAB, 0, 8,
                 link=SEC_STRTAB, info=first_global, entsize=24)
    shdrs += _sh(SEC_STRTAB, SHT_STRTAB, 0, 1)
    shdrs += _sh(SEC_RELA, SHT_RELA, 0, 8,
                 link=SEC_SYMTAB, info=SEC_TEXT, entsize=24)
    shdrs += _sh(SEC_SHSTR, SHT_STRTAB, 0, 1)
    body += shdrs
    return bytes(body)


def build_data_rel(data_slots) -> Tuple[bytes, Dict[str, int]]:
    """.data contents + section-relative symbol offsets for pack_obj."""
    syms: Dict[str, int] = {}
    out = bytearray()
    for slot in data_slots:
        name, sz = slot[0], slot[1]
        pad = _align(len(out), 8) - len(out)
        out += b"\x00" * pad
        syms[name] = len(out)
        init = slot[2] if len(slot) > 2 else b""
        out += init[:sz] + b"\x00" * (sz - len(init))
    return bytes(out), syms


@dataclass(frozen=True)
class Target:
    name: str         # "elf64"
    os: str           # "linux"
    abi: str          # "linux"
    ext: str          # ".elf"
    pack: Callable    # pack(text, labels, imports, data_slots, R) -> bytes
    symbols: Callable  # symbols(imports, data_slots) -> {name: vaddr}
    text_base: int    # TEXT_VA — .text load address for assembly
    pack_obj: Callable = None  # pack_obj(text, labels, relocs, slots, R)


ELF64 = Target(
    name="elf64",
    os="linux",
    abi="linux",
    ext=".elf",
    pack=pack,
    symbols=symbols,
    text_base=TEXT_VA,
)


ELF64_AARCH64 = Target(
    name="elf64.aarch64",
    os="linux",
    abi="linux",
    ext=".elf",
    pack=lambda *a: pack(*a, machine=EM_AARCH64),
    symbols=symbols,
    text_base=TEXT_VA,
)


ELF64_RISCV64 = Target(
    name="elf64.riscv64",
    os="linux",
    abi="linux",
    ext=".elf",
    pack=lambda *a: pack(*a, machine=EM_RISCV),
    symbols=symbols,
    text_base=TEXT_VA,
)


# ---- relocatable (.o) variants — same container family, ET_REL layout
# symbols() unused for .o (assemble_obj resolves locally); keep it as the
# import-guard so the NotRealized policy stays centralized.

ELFO64 = Target(
    name="elfo64",
    os="linux",
    abi="linux",
    ext=".o",
    pack=lambda *a: (_ for _ in ()).throw(
        NotRealized("elfo64 emits relocatables, not executables")),
    symbols=symbols,
    text_base=0,
    pack_obj=lambda *a: pack_obj(*a, machine=EM_X86_64),
)

ELFO64_AARCH64 = Target(
    name="elfo64.aarch64",
    os="linux",
    abi="linux",
    ext=".o",
    pack=lambda *a: (_ for _ in ()).throw(
        NotRealized("elfo64 emits relocatables, not executables")),
    symbols=symbols,
    text_base=0,
    pack_obj=lambda *a: pack_obj(*a, machine=EM_AARCH64),
)

ELFO64_RISCV64 = Target(
    name="elfo64.riscv64",
    os="linux",
    abi="linux",
    ext=".o",
    pack=lambda *a: (_ for _ in ()).throw(
        NotRealized("elfo64 emits relocatables, not executables")),
    symbols=symbols,
    text_base=0,
    pack_obj=lambda *a: pack_obj(*a, machine=EM_RISCV),
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


def run_elf(path: str, data: bytes,
            timeout: Optional[int] = 600) -> Tuple[bytes, bytes, int]:
    """Execute an emitted ELF under WSL -> (stdout, stderr, rc).
    `timeout` is a test-run guard; actual toolchain runs pass None."""
    cp = subprocess.run(["wsl", "-e", wsl_path(path)], input=data,
                        capture_output=True, timeout=timeout)
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
