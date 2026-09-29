import sys, time
sys.path.insert(0, ".")
import isa_x86_64 as isa
import spec_term as st
from graph_runtime import reduce_tree_cd, reduce_tree_lo

CASES = [
    ("ret",),
    ("syscall",),
    ("push_r64", "rcx"),
    ("pop_r64", "r8"),
    ("mov_r64_r64", "rax", "rbx"),
    ("mov_r64_r64", "r8", "r9"),
    ("mov_r32_imm32", "rcx", 7),
    ("mov_r64_imm", "rax", 5),
    ("mov_r64_imm", "rax", 0x1122334455),
    ("add_r64_imm", "rax", 5),
    ("add_r64_imm", "rcx", 300),
    ("add_r64_imm", "rcx", 5),
    ("cmp_r64_imm", "rax", 5),
    ("mov_r64_m64", "rax", ("m", "rsp", 8)),
    ("mov_r64_m64", "rax", ("m", "rbp", 0)),
    ("mov_m64_r64", ("m", "r12", 16), "rdx"),
    ("mov_r64_m64", "rax", ("m", "rcx", 300)),
    ("call_rel32", ("l", "x")),
    ("je_rel32", ("l", "loop")),
    ("mov_r64_rip", "rax", ("p", "scratch")),
    ("mov_m8_imm8", ("m", "rbx", 4), 9),
    ("xor_r32_r32", "eax", "eax"),
    ("inc_r64", "rsi"),
    ("div_r64", "rcx"),
    ("shl_r64_imm8", "rax", 3),
    ("lea_r64_rip", "rbx", ("p", "data")),
]

import io
log = open("_probe_g9f_enc.log", "w", buffering=1)
fails = 0
for insn in CASES:
    want = isa.encode(insn, resolve=lambda nm: 0)
    t = st.encode_query(("i",) + insn)
    t0 = time.time()
    try:
        nf, steps, al = reduce_tree_cd(t, fuel=20000)
        got = st.decode_encode(nf)
    except Exception as e:
        got, steps = None, -1
    ok = got == want
    fails += not ok
    line = ("OK " if ok else "FAIL") + f" {insn[0]:<16} "\
        f"want={want.hex()} got={got.hex() if got is not None else None} "\
        f"steps={steps} {time.time()-t0:.1f}s"
    print(line); log.write(line + "\n")
print("fails:", fails); log.write(f"fails: {fails}\n")
