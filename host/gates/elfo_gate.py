"""
elfo_gate — G13: ET_REL seam check (staging/seam, regime bytes).

For each linux.lo ISA (x86_64 / aarch64 / riscv64) emit both routes:
  exec route: toolchain <isa>.linux.lo -> ET_EXEC elf64
  obj  route: toolchain <isa>.linux.o  -> ET_REL elfo64
Parse the .o (.text/.symtab/.strtab/.rela.text), apply each .rela.text
entry at EXEC virtual addresses (TEXT_VA + r_offset; S from the exec
route's data symbols) using the ISA's reloc semantics:
  R_X86_64_PC32 (2)            word32  = S + A - P
  R_AARCH64_MOVW_UABS_G0_NC (264)  imm16[20:5] = (S+A)&0xFFFF
  R_AARCH64_MOVW_UABS_G1_NC (266)  imm16[20:5] = (S+A)>>16 & 0xFFFF
  R_RISCV_HI20 (26)            imm20[31:12] = (S+A+0x800)>>12
  R_RISCV_LO12_I (27)          imm12[31:20] = (S+A)&0xFFF
The patched .text must equal the executable .text byte-for-byte, and
`_start` must be a GLOBAL FUNC symbol.

Optional second leg (only when wsl:ld is resolvable): `ld` the x86_64
.o inside WSL and run it on "S K K I @ @ @" — stdout must be the
basis-expanded NF and rc 0.  Missing ld prints SKIP (PASS* leg).

Exit 1 on mismatch.
"""
from __future__ import annotations

import os
import struct
import subprocess
import sys

_HOST = os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_SEED_DIR = os.path.join(_HOST, "..", "seed")
if _SEED_DIR not in sys.path:
    sys.path.insert(0, _SEED_DIR)

import seed  # noqa: E402
import toolchain  # noqa: E402
import target_elf64 as te64  # noqa: E402

R_X86_64_PC32 = 2
R_AARCH64_G0_NC, R_AARCH64_G1_NC = 264, 266
R_RISCV_HI20, R_RISCV_LO12_I = 26, 27

ISAS = (("x86_64", "x86_64.linux.lo", "x86_64.linux.o", 7),
        ("aarch64", "aarch64.linux.lo", "aarch64.linux.o", 14),
        ("riscv64", "riscv64.linux.lo", "riscv64.linux.o", 14))


def _sections(obj: bytes):
    """ET_REL section table -> {name: (offset, size)} + shdr list."""
    shoff = struct.unpack_from("<Q", obj, 40)[0]
    shentsize = struct.unpack_from("<H", obj, 58)[0]
    shnum = struct.unpack_from("<H", obj, 60)[0]
    shstrndx = struct.unpack_from("<H", obj, 62)[0]
    sh = [struct.unpack_from("<IIQQQQIIQQ", obj, shoff + i * shentsize)
          for i in range(shnum)]
    strtab_off = sh[shstrndx][4]
    out = {}
    for s in sh:
        n = s[0]
        end = obj.index(b"\x00", strtab_off + n)
        out[obj[strtab_off + n:end].decode()] = s
    return out


def _exec_text(elf: bytes):
    """.text bytes of the exec image: phdr[0] filesz - HDRS."""
    filesz = struct.unpack_from("<Q", elf, te64.EHDR_SIZE + 32)[0]
    return elf[te64.HDRS: te64.HDRS + filesz - te64.HDRS]


def _patch(text: bytearray, relas, sym_va) -> None:
    for off, rtype, addend, S in relas:
        P = te64.TEXT_VA + off
        if rtype == R_X86_64_PC32:
            struct.pack_into("<i", text, off, S + addend - P)
        elif rtype in (R_AARCH64_G0_NC, R_AARCH64_G1_NC):
            w = struct.unpack_from("<I", text, off)[0]
            imm = ((S + addend) & 0xFFFF if rtype == R_AARCH64_G0_NC
                   else ((S + addend) >> 16) & 0xFFFF)
            struct.pack_into("<I", text, off,
                             (w & ~(0xFFFF << 5)) | (imm << 5))
        elif rtype == R_RISCV_HI20:
            w = struct.unpack_from("<I", text, off)[0]
            hi = (S + addend + 0x800) >> 12
            struct.pack_into("<I", text, off,
                             (w & 0xFFF) | (hi << 12))
        elif rtype == R_RISCV_LO12_I:
            w = struct.unpack_from("<I", text, off)[0]
            lo = (S + addend) & 0xFFF
            struct.pack_into("<I", text, off,
                             (w & 0xFFFFF) | (lo << 20))
        else:
            raise ValueError(f"unhandled rtype {rtype}")


def check_isa(isan: str, tc_exec: str, tc_obj: str,
              expect_relocs: int) -> bool:
    R = seed.Realization(abi="linux")
    elf = seed.emit(R, tc=toolchain.by_name(tc_exec))
    obj = seed.emit(R, tc=toolchain.by_name(tc_obj))
    secs = _sections(obj)
    otext = bytearray(
        obj[secs[".text"][4]:secs[".text"][4] + secs[".text"][5]])
    symtab = secs[".symtab"]
    strtab = secs[".strtab"]
    nsyms = symtab[5] // 24
    names = {}
    start_global = False
    for i in range(nsyms):
        st_name, st_info, _oth, _shx, st_val, _sz = struct.unpack_from(
            "<IBBHQQ", obj, symtab[4] + i * 24)
        end = obj.index(b"\x00", strtab[4] + st_name)
        nm = obj[strtab[4] + st_name:end].decode()
        names[i] = nm
        if nm == "_start":
            start_global = (st_info >> 4 == te64.STB_GLOBAL
                            and st_info & 0xF == te64.STT_FUNC)
    # exec VAs for the data-slot syms via the exec route's symbols()
    _isa_e, rts_e, tgt_e = toolchain.resolve(
        toolchain.by_name(tc_exec))
    slots = rts_e.data_slots(R) if callable(rts_e.data_slots) \
        else rts_e.data_slots
    exec_syms = tgt_e.symbols(rts_e.imports, slots)
    rela = secs[".rela.text"]
    relas = []
    for i in range(rela[5] // 24):
        r_off, r_info, r_add = struct.unpack_from(
            "<QQq", obj, rela[4] + i * 24)
        relas.append((r_off, r_info & 0xFFFFFFFF, r_add,
                      exec_syms[names[r_info >> 32]]))
    text_e = _exec_text(elf)
    # relocs must carry information: an unpatched .text equal to the
    # exec .text would make the patched==exec check vacuous
    needs_patch = bytes(otext) != text_e
    _patch(otext, relas, exec_syms)
    good = (bytes(otext) == text_e and start_global and needs_patch
            and len(relas) == expect_relocs)
    print(f"{'ok ' if good else 'FAIL'} {isan}: relocs={len(relas)} "
          f"(expect {expect_relocs}) patched==exec "
          f"{bytes(otext) == text_e} _start GLOBAL FUNC {start_global}")
    return good


def _wsl_tool(name: str) -> bool:
    try:
        return subprocess.run(
            ["wsl", "-e", "sh", "-c", f"command -v {name}"],
            capture_output=True, timeout=30).returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def ld_leg() -> bool:
    """Optional: link the x86_64 .o inside WSL and run it."""
    work = r"C:\tmp\isar_elfo"
    os.makedirs(work, exist_ok=True)
    obj = seed.emit(seed.Realization(abi="linux"),
                    tc=toolchain.by_name("x86_64.linux.o"))
    opath = os.path.join(work, "reducer.o")
    with open(opath, "wb") as f:
        f.write(obj)
    wo = te64.wsl_path(opath)
    welf = te64.wsl_path(os.path.join(work, "reducer.elf"))
    cp = subprocess.run(
        ["wsl", "-e", "sh", "-c", f"ld -o {welf} {wo} && printf "
         "'S K K I @ @ @\\n' | " + welf],
        capture_output=True, timeout=120)
    want = b"B W @ B B C K K I @ @ @ @ @ I @ @ \n"
    good = cp.returncode == 0 and cp.stdout == want
    print(f"{'ok ' if good else 'FAIL'} ld-link leg: rc="
          f"{cp.returncode} stdout={cp.stdout!r:.120}")
    return good


def main() -> int:
    ok = True
    for isan, te, to, nrel in ISAS:
        ok = check_isa(isan, te, to, nrel) and ok
    if _wsl_tool("ld"):
        ok = ld_leg() and ok
    else:
        print("SKIP ld-link (wsl:ld missing)")
    print(f"{'OK' if ok else 'FAIL'} elfo_gate")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
