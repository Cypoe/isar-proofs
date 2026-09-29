"""Bisect the xdu native crash: progressively larger programs."""
import os
import subprocess
import sys

HOST = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "host"))
SEED = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "seed"))
for p in (HOST, SEED):
    if p not in sys.path:
        sys.path.insert(0, p)

import isa_x86_64 as _isa
from isa_x86_64 import I, LBL
import target_pe64
import routines_x86_64_win64_xdu as X
from seed import Realization

R = Realization()
iat = X._ctx()["iat"]
IMPORTS = X.IMPORTS
DATA_SLOTS = X.DATA_SLOTS


def run(name, prog):
    syms = target_pe64.symbols(IMPORTS, DATA_SLOTS)
    text, labels = _isa.assemble(prog, syms, base=target_pe64.TEXT_RVA)
    blob = target_pe64.pack(text, labels, IMPORTS, DATA_SLOTS, R)
    exe = os.path.join(SEED, "..", "seed", "build", f"dbg_{name}.exe")
    exe = os.path.normpath(exe)
    with open(exe, "wb") as f:
        f.write(blob)
    r = subprocess.run([exe], input=b"", capture_output=True)
    print(f"{name}: rc={r.returncode} out={r.stdout!r}")


# 1: bare ExitProcess(42)
run("exit42", [
    LBL("_start"),
    I("sub_r64_imm", "rsp", 0x28),
    I("mov_r32_imm32", "ecx", 42),
    I("call_mrip", iat("ExitProcess")),
])

# 2: + GetStdHandle
run("handles", [
    LBL("_start"),
    I("sub_r64_imm", "rsp", 0x28),
    I("mov_r32_imm32", "ecx", -10), I("call_mrip", iat("GetStdHandle")),
    I("mov_rip_r64", ("p", "hin"), "rax"),
    I("mov_r32_imm32", "ecx", 42),
    I("call_mrip", iat("ExitProcess")),
])

# 2b: one VirtualAlloc only
run("alloc1", [
    LBL("_start"),
    I("sub_r64_imm", "rsp", 0x28),
    I("xor_r32_r32", "ecx", "ecx"),
    I("mov_r32_imm32", "edx", R.read_buf_bytes),
    I("mov_r32_imm32", "r8d", X.VA_COMMIT_RESERVE),
    I("mov_r32_imm32", "r9d", X.PAGE_RW),
    I("call_mrip", iat("VirtualAlloc")),
    I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "bad")),
    I("mov_r64_r64", "r12", "rax"),
    I("mov_r32_imm32", "ecx", 43),
    I("call_mrip", iat("ExitProcess")),
    LBL("bad"),
    I("mov_r32_imm32", "ecx", 4), I("call_mrip", iat("ExitProcess")),
])

# 3: + VirtualAlloc pair + out-buf setup
run("alloc", [
    LBL("_start"),
    I("sub_r64_imm", "rsp", 0x28),
    I("xor_r32_r32", "ecx", "ecx"),
    I("mov_r32_imm32", "edx", R.read_buf_bytes),
    I("mov_r32_imm32", "r8d", X.VA_COMMIT_RESERVE),
    I("mov_r32_imm32", "r9d", X.PAGE_RW),
    I("call_mrip", iat("VirtualAlloc")),
    I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "bad")),
    I("mov_r64_r64", "r12", "rax"),
    I("xor_r32_r32", "ecx", "ecx"),
    I("mov_r32_imm32", "edx", X.OUT_BUF_BYTES),
    I("mov_r32_imm32", "r8d", X.VA_COMMIT_RESERVE),
    I("mov_r32_imm32", "r9d", X.PAGE_RW),
    I("call_mrip", iat("VirtualAlloc")),
    I("test_r64_r64", "rax", "rax"), I("je_rel32", ("l", "bad")),
    I("mov_rip_r64", ("p", "obase"), "rax"),
    I("mov_r64_r64", "rbx", "rax"),
    I("lea_r64_m64", "rbp", ("m", "rax", X.OUT_BUF_BYTES)),
    I("mov_m64_imm32", ("p", "pend"), -1),
    I("mov_r32_imm32", "ecx", 43),
    I("call_mrip", iat("ExitProcess")),
    LBL("bad"),
    I("mov_r32_imm32", "ecx", 4), I("call_mrip", iat("ExitProcess")),
])
