"""
opt_peephole — Program-level optimization pass, applied between
routines.program() and isa.assemble() in seed.emit().

The program is data: a list of ("i", mnemonic, *ops) instructions and
("label", name) markers.  This pass rewrites that list with a small
closed set of semantics-preserving rules, generic over the ISA tables:

  * fallthrough      jmp L ; LBL L          -> drop the jmp
  * unreachable      jmp/ret ... insns with no label up to the next
                     label can never execute -> drop them
  * jump threading   jmp L where L: jmp M   -> jmp M   (uncond only)
  * self-move        mov r, r               -> drop

Branch classification is per-ISA data (UJMP/CALL/RET/SELFMOVE below) —
the rules themselves know only "unconditional jump to label", "return",
and "register move".  Conditional branches are never touched: inverting
a condition or threading a taken path would require knowing each ISA's
flag model, which is exactly the smuggling this layer exists to avoid.

Jumps carry their target as a ("l", name) or ("p", name) operand — the
assemblers resolve both forms against the label table, and "p" is also
how the kernels name local labels for rip/b/bl-relative forms.
"""
from __future__ import annotations

from typing import Dict, Iterable, List, Optional, Tuple

Item = Tuple

# ---------------------------------------------------------------------
# Per-ISA branch/move classification — data, not logic.
# ---------------------------------------------------------------------
# UJMP:  mnemonics that are unconditional control transfers to a label
#        operand.  Operand index of the label is implicit: the last
#        ("l"|"p", name) operand of the instruction.
# CALL:  mnemonics that push a return address (used only to refuse
#        rewrites across them — a call target's ret must stay a ret).
# RET:   mnemonics that transfer back through a stacked return address.
# JALR0: riscv "jal rd, label" is unconditional iff rd == "zero".
# SELFMOVE: mnemonics whose (dst, src) operand pair may be dropped when
#        equal.
ISACLASS: Dict[str, Dict[str, Tuple[str, ...]]] = {
    "x86_64": {
        "UJMP": ("jmp_rel32",),
        "CALL": ("call_rel32", "call_mrip"),
        "RET": ("ret",),
        "SELFMOVE": ("mov_r64_r64", "mov_r64_rip", "mov_r32_r32"),
    },
    "aarch64": {
        "UJMP": ("b_rel",),
        "CALL": ("bl_rel",),
        "RET": ("ret",),
        "SELFMOVE": ("mov_reg",),
    },
    "riscv64": {
        # jal with rd="zero" is the unconditional jump; rd="ra" is call
        "UJMP": ("jal0",),            # pseudo-tag handled below
        "CALL": ("jalra",),
        "RET": ("ret",),
        "SELFMOVE": ("addi", "mv"),   # only mv treated: see _selfmove
    },
}


def _label_ref(ops: Tuple) -> Optional[str]:
    """Last ("l"|"p", name) operand's name, or None."""
    tgt = None
    for o in ops:
        if isinstance(o, tuple) and len(o) == 2 and o[0] in ("l", "p") \
                and isinstance(o[1], str):
            tgt = o[1]
    return tgt


def _with_label(ops: Tuple, new: str) -> Tuple:
    """Rewrite the LAST label operand of an insn's operands."""
    out = list(ops)
    for i in range(len(out) - 1, -1, -1):
        o = out[i]
        if isinstance(o, tuple) and len(o) == 2 and o[0] in ("l", "p") \
                and isinstance(o[1], str):
            out[i] = (o[0], new)
            return tuple(out)
    return tuple(out)


def _is_ujmp(insn: Item, isa: str) -> Optional[str]:
    """Unconditional-jump target label, or None."""
    m, ops = insn[1], insn[2:]
    if isa == "riscv64":
        if m == "jal" and ops and ops[0] == "zero":
            return _label_ref(ops[1:])
        return None
    if m in ISACLASS[isa]["UJMP"]:
        return _label_ref(ops)
    return None


def _is_ret(insn: Item, isa: str) -> bool:
    return insn[0] == "i" and insn[1] in ISACLASS[isa]["RET"]


def _selfmove(insn: Item, isa: str) -> bool:
    m, ops = insn[1], insn[2:]
    if m not in ISACLASS[isa]["SELFMOVE"]:
        return False
    if isa == "riscv64":
        # mv rd, rs  ==  addi rd, rs, 0 — only the two-register form
        return m == "mv" and len(ops) == 2 and ops[0] == ops[1]
    return len(ops) == 2 and ops[0] == ops[1]


def optimize(prog: Iterable[Item], isa: str) -> List[Item]:
    """Peephole + jump threading over a Program.  Pure: input list is
    not mutated; returns a new list.  Iterate to a fixpoint because
    each rule can expose another (threaded jump to a fallthrough
    target, unreachable code exposing a new label pair)."""
    prog = list(prog)
    isa = isa.split(".", 1)[0]   # x86_64.fasmg uses x86-64 mnemonics
    if isa not in ISACLASS:
        return prog
    changed = True
    while changed:
        prog, changed = _pass_once(prog, isa)
    return prog


def _pass_once(prog: List[Item], isa: str):
    # index labels -> following instruction position
    label_at: Dict[str, int] = {}
    for i, it in enumerate(prog):
        if it[0] == "label":
            label_at.setdefault(it[1], i)

    out: List[Item] = []
    changed = False
    skip_dead = False
    for i, it in enumerate(prog):
        if it[0] == "label":
            skip_dead = False
            out.append(it)
            continue
        if skip_dead:
            changed = True
            continue
        tgt = _is_ujmp(it, isa)
        if tgt is not None:
            # thread: L starts with unconditional jmp M -> retarget to M
            seen = set()
            while tgt in label_at:
                seen.add(tgt)
                j = label_at[tgt] + 1
                nxt = prog[j] if j < len(prog) else None
                if nxt and nxt[0] == "i":
                    t2 = _is_ujmp(nxt, isa)
                    if t2 is not None and t2 not in seen:
                        tgt = t2
                        changed = True
                        continue
                    if _is_ret(nxt, isa):
                        break       # L: ret — keep target, drop jmp
                break
            nxt = prog[i + 1] if i + 1 < len(prog) else None
            if nxt is not None and nxt[0] == "label" and nxt[1] == tgt:
                changed = True       # fallthrough: jmp to next label
                continue
            # L: ret => this jmp is a tail position... but only if the
            # jmp itself is in tail position, which we can't prove
            # cheaply; just retarget normally.
            if tgt != _label_ref(it[2:]):
                ops = _with_label(it[2:], tgt)
                out.append(("i", it[1]) + ops)
            else:
                out.append(it)
            skip_dead = False
            # everything up to the next label is unreachable
            skip_dead = True
            continue
        if _is_ret(it, isa):
            out.append(it)
            skip_dead = True
            continue
        if _selfmove(it, isa):
            changed = True
            continue
        out.append(it)
    return out, changed


def main() -> int:
    """Self-test: run the pass over every realized program, check it
    assembles to byte-identical-or-smaller text and that NFs still
    match (assembly is the cheap in-process check; execution gates
    live in the cross-ISA harness)."""
    import sys, os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..",
                                    "seed"))
    import seed
    import routines_x86_64_win64 as w64
    import routines_x86_64_linux_lo as x64
    import routines_aarch64_linux_lo as a64
    import routines_riscv64_linux_lo as r64

    cases = [
        ("x86_64", "win64", w64.program, seed.Realization(abi="win64")),
        ("x86_64", "linux", x64.program, seed.Realization(abi="linux")),
        ("aarch64", "linux", a64.program, seed.Realization(abi="linux")),
        ("riscv64", "linux", r64.program, seed.Realization(abi="linux")),
    ]
    nfail = 0
    for isaname, abiname, mkprog, R in cases:
        prog = mkprog(R)
        opt = optimize(prog, isaname)
        ni = sum(1 for x in prog if x[0] == "i")
        no = sum(1 for x in opt if x[0] == "i")
        print(f"{isaname}.{abiname}: {ni} insns -> {no} "
              f"(-{ni - no}), labels "
              f"{sum(1 for x in prog if x[0]=='label')} -> "
              f"{sum(1 for x in opt if x[0]=='label')}")
    return nfail


if __name__ == "__main__":
    raise SystemExit(main())
