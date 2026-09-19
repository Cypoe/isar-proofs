"""
target_pe64 — PE64 (Windows x86-64 console exe) container writer.

Moved verbatim from seed/seed.py §6: section RVAs, import directory,
.data layout, and `pack` (was build_pe) now take assembled .text plus
the routines' imports/data_slots as parameters — the target no longer
knows the reducer program.  `pack` rebuilds idata/data deterministically
(the emit chain already needed their symbols to assemble .text).
"""
from __future__ import annotations

import os
import struct
import sys
from dataclasses import dataclass
from types import SimpleNamespace
from typing import Callable, Dict, List, Sequence, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

TEXT_RVA = 0x1000
IDATA_RVA = 0x2000
DATA_RVA = 0x3000
FILE_ALIGN = 0x200
SECT_ALIGN = 0x1000
IMAGE_BASE = 0x140000000


def build_idata(imports: Sequence[str]) -> Tuple[bytes, Dict[str, int]]:
    """Import directory + ILT + IAT + hint/names; returns bytes and iat symbols."""
    n = len(imports)
    idt_sz, ilt_sz = (n // n + 1) * 20, (n + 1) * 8   # 1 dll desc + null; n+1 thunks
    idt_sz = 40
    ilt_off = idt_sz
    iat_off = ilt_off + ilt_sz
    names_off = iat_off + ilt_sz
    off = names_off
    hn_rvas: List[int] = []
    for name in imports:
        hn = struct.pack("<H", 0) + name.encode() + b"\x00"
        if len(hn) & 1:
            hn += b"\x00"
        hn_rvas.append(IDATA_RVA + off)
        off += len(hn)
    dll_rva = IDATA_RVA + off
    dll = b"kernel32.dll\x00"
    off += len(dll)
    ilt = b"".join(struct.pack("<Q", r) for r in hn_rvas) + b"\x00" * 8
    idt = struct.pack("<IIIII", IDATA_RVA + ilt_off, 0, 0, dll_rva,
                      IDATA_RVA + iat_off) + b"\x00" * 20
    body = idt + ilt + ilt  # ILT and IAT identical content
    names = b"".join(
        struct.pack("<H", 0) + nm.encode() + b"\x00"
        + (b"\x00" if (2 + len(nm) + 1) & 1 else b"")
        for nm in imports)
    body += names + dll
    syms = {f"iat_{nm}": IDATA_RVA + iat_off + i * 8
            for i, nm in enumerate(imports)}
    return body, syms


def build_data(data_slots: Sequence[Tuple[str, int]]) -> Tuple[bytes, Dict[str, int]]:
    syms: Dict[str, int] = {}
    off = 0
    for name, sz in data_slots:
        syms[name] = DATA_RVA + off
        off += sz
    return b"\x00" * off, syms


def _align(v: int, a: int) -> int:
    return (v + a - 1) // a * a


def pack(text: bytes, labels: Dict[str, int], imports: Sequence[str],
         data_slots: Sequence[Tuple[str, int]], R) -> bytes:
    """Pack an assembled .text into a PE64 image.  `labels` is the
    assembler's symbol table (kept for the caller's diagnostics)."""
    code = text
    idata, _iat = build_idata(imports)
    data, _ds = build_data(data_slots)

    def sect(name: bytes, vsize: int, vaddr: int, raw: bytes, chars: int,
             rawptr: int) -> bytes:
        return struct.pack("<8sIIIIIIHHI", name, vsize, vaddr,
                           _align(len(raw), FILE_ALIGN), rawptr, 0, 0, 0, 0,
                           chars)

    text_raw = code + b"\x00" * (_align(len(code), FILE_ALIGN) - len(code))
    idata_raw = idata + b"\x00" * (_align(len(idata), FILE_ALIGN) - len(idata))
    data_raw = data + b"\x00" * (_align(len(data), FILE_ALIGN) - len(data))
    text_ptr = FILE_ALIGN
    idata_ptr = text_ptr + len(text_raw)
    data_ptr = idata_ptr + len(idata_raw)
    size_image = _align(DATA_RVA + len(data), SECT_ALIGN)

    dos = bytearray(0x40)
    dos[0:2] = b"MZ"
    struct.pack_into("<I", dos, 0x3C, 0x40)
    coff = struct.pack("<HHIIIHH", 0x8664, 3, 0, 0, 0, 0xF0, 0x0022)
    dd = [(0, 0)] * 16
    dd[1] = (IDATA_RVA, len(idata))
    opt = struct.pack(
        "<HBBIIIIIQIIHHHHHHIIIIHHQQQQII",
        0x20B, 0, 0,                      # magic, linker ver
        len(text_raw), len(idata_raw) + len(data_raw), 0,
        TEXT_RVA, TEXT_RVA,               # entry, base of code
        IMAGE_BASE, SECT_ALIGN, FILE_ALIGN,
        6, 0, 0, 0, 6, 0,                 # OS/img/subsys ver
        0, size_image, FILE_ALIGN, 0,     # win32ver, img, hdrs, checksum
        3, 0x8100,                        # subsystem CUI, dllchars (no DYNAMIC_BASE)
        R.stack_reserve, 0x1000,          # stack reserve/commit
        0x100000, 0x1000,                 # heap reserve/commit
        0, 16,                            # loader flags, #rva+size
    ) + b"".join(struct.pack("<II", r, s) for r, s in dd)
    assert len(opt) == 0xF0, len(opt)
    sh = (sect(b".text\x00\x00\x00", len(code), TEXT_RVA, text_raw, 0x60000020,
               text_ptr)
          + sect(b".idata\x00\x00", len(idata), IDATA_RVA, idata_raw, 0x40000040,
                 idata_ptr)
          + sect(b".data\x00\x00\x00", len(data), DATA_RVA, data_raw, 0xC0000040,
                 data_ptr))
    headers = bytes(dos) + b"PE\x00\x00" + coff + opt + sh
    headers += b"\x00" * (FILE_ALIGN - len(headers))
    return headers + text_raw + idata_raw + data_raw


def symbols(imports: Sequence[str],
            data_slots: Sequence[Tuple[str, int]]) -> Dict[str, int]:
    """IAT + .data symbol table (absolute RVAs) — what .text resolves against."""
    _, iat = build_idata(imports)
    _, ds = build_data(data_slots)
    out = dict(iat)
    out.update(ds)
    return out


@dataclass(frozen=True)
class Target:
    name: str         # "pe64"
    os: str           # "windows"
    abi: str          # "win64"
    ext: str          # ".exe"
    pack: Callable    # pack(text, labels, imports, data_slots, R) -> bytes
    symbols: Callable  # symbols(imports, data_slots) -> {name: rva}
    text_base: int    # TEXT_RVA — .text load address for assembly


PE64 = Target(
    name="pe64",
    os="windows",
    abi="win64",
    ext=".exe",
    pack=pack,
    symbols=symbols,
    text_base=TEXT_RVA,
)


def main() -> int:
    ok = True
    R = SimpleNamespace(stack_reserve=64 << 20)
    pe = pack(b"\xC3", {}, ("ExitProcess",), (("x", 8),), R)
    checks = [
        ("MZ", pe[:2] == b"MZ"),
        ("PE\\0\\0", pe[0x40:0x44] == b"PE\x00\x00"),
        ("machine 0x8664", struct.unpack_from("<H", pe, 0x44)[0] == 0x8664),
        ("stack_reserve", struct.unpack_from("<Q", pe, 0x58 + 72)[0]
         == R.stack_reserve),
    ]
    for name, good in checks:
        print(f"  {'ok' if good else 'FAIL'} {name}")
        ok = ok and good
    print(f"{'OK' if ok else 'FAIL'} target_pe64")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
