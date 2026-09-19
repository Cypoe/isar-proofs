"""
toolchain — the catalog cogen chooses from.

A Toolchain names (dialect, isa, routines, target).  Exactly one entry is
realized today: native.x86_64.pe = bytecode.postfix tokens ->
x86_64.win64.lo routines -> pe64 container.  Everything else is
*declared*: resolve() raises NotRealized — refusal, never fallback.

Owns `NotRealized` (seed/seed.py re-exports it).
"""
from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)


class NotRealized(Exception):
    """Declared-but-unrealized strategy/toolchain value (refusal, never fallback)."""


# Registries: component name -> (module, record attribute).  A toolchain is
# realized iff every component resolves — the catalog cannot assert a status
# the registries can't back.
ISAS: Dict[str, Tuple[str, str]] = {
    "x86_64": ("isa_x86_64", "X86_64"),
}
ROUTINES: Dict[str, Tuple[str, str]] = {
    "x86_64.win64.lo": ("routines_x86_64_win64", "X86_64_WIN64"),
}
TARGETS: Dict[str, Tuple[str, str]] = {
    "pe64": ("target_pe64", "PE64"),
}
DIALECTS: Dict[str, Tuple[str, str]] = {
    "bytecode.postfix": ("bytecode_dialect", "bytecode_map"),
}


def components() -> Dict[str, Dict[str, Tuple[str, str]]]:
    return {"dialect": DIALECTS, "isa": ISAS, "routines": ROUTINES,
            "target": TARGETS}


@dataclass(frozen=True)
class Toolchain:
    name: str
    dialect: str       # "bytecode.postfix"
    isa: str           # "x86_64"
    routines: str      # "x86_64.win64.lo"
    target: str        # "pe64"
    note: str = ""

    @property
    def status(self) -> str:        # "realized" | "declared" — derived
        regs = components()
        vals = {"dialect": self.dialect, "isa": self.isa,
                "routines": self.routines, "target": self.target}
        return "realized" if all(vals[k] in regs[k] for k in regs) \
            else "declared"


CATALOG: Tuple[Toolchain, ...] = (
    Toolchain(
        "native.x86_64.pe", "bytecode.postfix", "x86_64",
        "x86_64.win64.lo", "pe64",
        "seed/seed.py emit chain: IStepBasis reducer -> PE exe"),
    # declared ISAs
    Toolchain("isa.aarch64", "bytecode.postfix", "aarch64",
              "aarch64.win64.lo", "pe64",
              "no aarch64 ISA table"),
    Toolchain("isa.riscv64", "bytecode.postfix", "riscv64",
              "riscv64.linux.lo", "elf64",
              "no riscv64 ISA table"),
    # declared routine sets
    Toolchain("x86_64.win64.cd", "bytecode.postfix", "x86_64",
              "x86_64.win64.cd", "pe64",
              "Lean ParStep / host reduce_cd contract, native unrealized"),
    Toolchain("x86_64.linux.lo", "bytecode.postfix", "x86_64",
              "x86_64.linux.lo", "elf64",
              "syscall ABI, no kernel32 IAT"),
    Toolchain("x86_64.uefi.lo", "bytecode.postfix", "x86_64",
              "x86_64.uefi.lo", "pe64.uefi",
              "UEFI boot services ABI"),
    # declared targets
    Toolchain("elf64", "bytecode.postfix", "x86_64",
              "x86_64.linux.lo", "elf64",
              "ELF64 container writer"),
    Toolchain("macho64", "bytecode.postfix", "x86_64",
              "x86_64.macho.lo", "macho64",
              "Mach-O 64 container writer"),
    Toolchain("flat", "bytecode.postfix", "x86_64",
              "x86_64.baremetal.lo", "flat",
              "flat binary, no loader"),
    Toolchain("pe64.uefi", "bytecode.postfix", "x86_64",
              "x86_64.uefi.lo", "pe64.uefi",
              "PE32+ EFI application subsystem"),
    # declared dialects
    Toolchain("lambda.bracket", "lambda.bracket", "x86_64",
              "x86_64.win64.lo", "pe64",
              "host QuotientMap exists (lambda_dialect.py); "
              "no native token alphabet"),
    Toolchain("phi.rel", "phi.rel", "x86_64",
              "x86_64.win64.lo", "pe64",
              "spec only, no parser"),
)

# Realization strategy axes: which values are realized vs declared.
STRATEGY_AXES: Dict[str, Dict[str, str]] = {
    "order":   {"lo": "realized", "cd": "declared"},
    "fuse_s":  {"False": "realized", "True": "realized"},
    "alloc":   {"bump-chunked": "realized", "arena": "declared"},
    "reclaim": {"none": "realized", "refcount": "declared",
                "mark-sweep": "declared"},
    "stack":   {"machine": "realized", "explicit": "declared"},
    "io":      {"stdin/stdout": "realized", "memory": "declared"},
    "fuel":    {"None": "realized", "int": "realized"},
}


def realized() -> List[Toolchain]:
    return [t for t in CATALOG if t.status == "realized"]


def declared() -> List[Toolchain]:
    return [t for t in CATALOG if t.status == "declared"]


def by_name(name: str) -> Toolchain:
    for t in CATALOG:
        if t.name == name:
            return t
    raise KeyError(f"unknown toolchain {name!r}")


def resolve(tc: Toolchain):
    """(ISA, Routines, Target) records for a realized toolchain.
    Each component is dispatched through its registry; a miss raises
    NotRealized naming the missing component — never a fallback."""
    import importlib
    regs = components()
    vals = {"dialect": tc.dialect, "isa": tc.isa,
            "routines": tc.routines, "target": tc.target}
    recs = {}
    for comp, value in vals.items():
        ent = regs[comp].get(value)
        if ent is None:
            raise NotRealized(
                f"{tc.name}: {comp} {value!r} not realized")
        modname, attr = ent
        recs[comp] = getattr(importlib.import_module(modname), attr)
    return recs["isa"], recs["routines"], recs["target"]


def main() -> int:
    print("toolchain catalog:")
    for t in CATALOG:
        print(f"  {t.status:9s} {t.name:22s} {t.dialect} | {t.isa} | "
              f"{t.routines} | {t.target}  {t.note}")
    ok = True
    for t in realized():
        isa, rts, tgt = resolve(t)
        good = (isa.name == t.isa and rts.name == t.routines
                and tgt.name == t.target)
        print(f"  {'ok' if good else 'FAIL'} resolve {t.name}")
        ok = ok and good
    for t in declared():
        try:
            resolve(t)
            print(f"  FAIL {t.name} resolved silently")
            ok = False
        except NotRealized as e:
            print(f"  ok refused: {e}")
    print(f"{'OK' if ok else 'FAIL'} toolchain")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
