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

IDATA_RVA = 0x1000
FILE_ALIGN = 0x200
SECT_ALIGN = 0x1000
IMAGE_BASE = 0x140000000


def _align(v: int, a: int) -> int:
    return (v + a - 1) // a * a


def data_rva(imports: Sequence[str]) -> int:
    """.data RVA: .idata is the first section (VA 0x1000, right after
    the headers — Windows requires contiguous VA coverage from there);
    .data follows at the next SectionAlignment boundary.  The address
    is computed, not assumed — the layout admits arbitrarily many
    imports."""
    return _align(IDATA_RVA + len(build_idata(imports)[0]), SECT_ALIGN)


def text_rva(imports: Sequence[str],
             data_slots: Sequence[Tuple[str, int]]) -> int:
    """.text RVA: emitted LAST in VA order.  .text is assembled against
    only iat_/slot symbols — both computable before .text exists — and
    its bytes are fully position-independent (every label/symbol ref
    encodes as a rel32 displacement), so placing code after the data
    removes the old fixed-slot ceiling where .text > 4KiB overlapped
    .idata at 0x2000 and CreateProcess rejected the image (193 /
    STATUS_INVALID_IMAGE_FORMAT)."""
    drva = data_rva(imports)
    return _align(drva + len(build_data(data_slots, drva)[0]),
                  SECT_ALIGN)


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


def build_data(data_slots, drva: int) -> Tuple[bytes, Dict[str, int]]:
    """Slots are (name, size) zero-fill or (name, size, init) with
    initialized content — residual programs bake their packed-IR
    payload into .data this way.  `drva` is the section's RVA (see
    data_rva — it depends on the import table)."""
    syms: Dict[str, int] = {}
    out = bytearray()
    for slot in data_slots:
        name, sz = slot[0], slot[1]
        syms[name] = drva + len(out)
        init = slot[2] if len(slot) > 2 else b""
        out += init[:sz] + b"\x00" * (sz - len(init))
    return bytes(out), syms


def pack(text: bytes, labels: Dict[str, int], imports: Sequence[str],
         data_slots: Sequence[Tuple[str, int]], R) -> bytes:
    """Pack an assembled .text into a PE64 image.  `labels` is the
    assembler's symbol table (kept for the caller's diagnostics).
    Section order is VA order: .idata, .data, .text."""
    code = text
    idata, _iat = build_idata(imports)
    drva = data_rva(imports)
    data, _ds = build_data(data_slots, drva)
    trva = _align(drva + len(data), SECT_ALIGN)

    def sect(name: bytes, vsize: int, vaddr: int, raw: bytes, chars: int,
             rawptr: int) -> bytes:
        return struct.pack("<8sIIIIIIHHI", name, vsize, vaddr,
                           _align(len(raw), FILE_ALIGN), rawptr, 0, 0, 0, 0,
                           chars)

    text_raw = code + b"\x00" * (_align(len(code), FILE_ALIGN) - len(code))
    idata_raw = idata + b"\x00" * (_align(len(idata), FILE_ALIGN) - len(idata))
    data_raw = data + b"\x00" * (_align(len(data), FILE_ALIGN) - len(data))
    idata_ptr = FILE_ALIGN
    data_ptr = idata_ptr + len(idata_raw)
    text_ptr = data_ptr + len(data_raw)
    size_image = _align(trva + len(code), SECT_ALIGN)

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
        trva, trva,                       # entry, base of code
        IMAGE_BASE, SECT_ALIGN, FILE_ALIGN,
        6, 0, 0, 0, 6, 0,                 # OS/img/subsys ver
        0, size_image, FILE_ALIGN, 0,     # win32ver, img, hdrs, checksum
        3, 0x8100,                        # subsystem CUI, dllchars (no DYNAMIC_BASE)
        R.stack_reserve, 0x1000,          # stack reserve/commit
        0x100000, 0x1000,                 # heap reserve/commit
        0, 16,                            # loader flags, #rva+size
    ) + b"".join(struct.pack("<II", r, s) for r, s in dd)
    assert len(opt) == 0xF0, len(opt)
    sh = (sect(b".idata\x00\x00", len(idata), IDATA_RVA, idata_raw, 0x40000040,
               idata_ptr)
          + sect(b".data\x00\x00\x00", len(data), drva, data_raw, 0xC0000040,
                 data_ptr)
          + sect(b".text\x00\x00\x00", len(code), trva, text_raw, 0x60000020,
                 text_ptr))
    headers = bytes(dos) + b"PE\x00\x00" + coff + opt + sh
    headers += b"\x00" * (FILE_ALIGN - len(headers))
    return headers + idata_raw + data_raw + text_raw


def symbols(imports: Sequence[str],
            data_slots: Sequence[Tuple[str, int]]) -> Dict[str, int]:
    """IAT + .data symbol table (absolute RVAs) — what .text resolves against."""
    _, iat = build_idata(imports)
    _, ds = build_data(data_slots, data_rva(imports))
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
    text_rva: Callable  # text_rva(imports, data_slots) -> .text load address


PE64 = Target(
    name="pe64",
    os="windows",
    abi="win64",
    ext=".exe",
    pack=pack,
    symbols=symbols,
    text_rva=text_rva,
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
