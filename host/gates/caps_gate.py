"""
caps_gate — G18: cap-subset check (quotient/structural, tier fast).

Every realized routines entry in toolchain.json declares `caps`:

    "caps": {
      "ports": {"stdin": "R", "stdout": "W", "stderr": "W",
                "scratch": "RW+grow"},
      "os":    {"<binding>": [<acceptable ports>], ...}
    }

  ports     — the semantic surface the host may touch.
  os        — the raw OS bindings it may use, each mapped to the
              port(s) it can serve ([] = intrinsic, e.g. exit).

The gate extracts the *used* binding set from the routines Program
data itself — never from the declaration:

  win64/pe64 & fasmg   routines record `.imports`  -> kernel32!<name>
  linux syscall ABIs   SYS_* immediates at trap sites in the emitted
                       insns (syscall / svc_imm16 / ecall; number reg
                       eax / x8 / a7 — xor eax,eax reads as sys:0)
  C hosted             libc!<fn> call sites in the emitted C items

then checks, per realized toolchain:

  1. used ⊆ declared os bindings
  2. every used binding lists a port that is declared ([] = ok)
  3. declared ports ⊆ the known port set; modes well-formed
  4. declared os entries name only declared ports ([] = intrinsic)
  5. emitter-role hosts (path == "native"): declared ports ⊆
     {stdin, stdout, stderr, scratch} — an emitter needs a bundle in,
     an artifact out, stats, and scratch; nothing else

Negative cases (mutated declarations MUST fail) are checked in-process
at the end — an undeclared used binding, and an emitter claiming
payload.

Exit 1 on any violation.
"""
from __future__ import annotations

import os
import re
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

KNOWN_PORTS = {"stdin", "stdout", "stderr", "scratch", "payload"}
PORT_MODE = re.compile(r"^(R|W|RW|RW\+grow)$")
EMITTER_PORTS = {"stdin", "stdout", "stderr", "scratch"}

# trap-site conventions: isa -> (trap form, number-register readers)
_TRAP = {
    "x86_64": "syscall",
    "aarch64": "svc_imm16",
    "riscv64": "ecall",
}
_NREG_FORMS = {
    "x86_64": (("mov_r32_imm32", "eax"), ("xor_r32_r32", "eax")),
    "aarch64": (("movz", "x8"),),
    "riscv64": (("addi", "a7"),),
}
_LIBC = re.compile(
    r"\b(malloc|calloc|realloc|free|fread|fwrite|fgetc|fputc|putchar"
    r"|getchar|ungetc|puts|printf|fprintf|sprintf|snprintf|exit|abort"
    r"|memset|memcpy|memmove|strlen)\s*\(")


def _used_syscalls(prog, isa_name: str) -> set:
    """Collect the syscall-number immediate in force at each trap."""
    trap = _TRAP[isa_name]
    nr_forms = _NREG_FORMS[isa_name]
    used = set()
    nr = None
    for it in prog:
        if not (isinstance(it, tuple) and len(it) >= 2 and it[0] == "i"):
            continue
        form = it[1]
        if any(form == f and len(it) >= 3 and it[2] == reg
               for f, reg in nr_forms):
            if form == "xor_r32_r32":
                nr = 0
            else:
                nr = it[-1]
        elif form == trap:
            if nr is None:
                raise RuntimeError(
                    f"{isa_name}: trap site with no syscall number")
            used.add(f"sys:{nr}")
    return used


def _used(tc, rts) -> set:
    """The used OS-binding set, extracted from program data.
    Only the routines component is resolved — importing the dialect
    record (spec_term builds the catalog term at import, ~3min) buys
    the gate nothing."""
    if tc.isa == "c":
        prog = rts.program(seed.Realization())
        used = set()
        for it in prog:
            for op in it[1:] if isinstance(it, tuple) else ():
                if isinstance(op, str):
                    used.update("libc!" + m for m in _LIBC.findall(op))
        return used
    imports = getattr(rts, "imports", ())
    if imports:
        return set(f"kernel32!{n}" for n in imports)
    if tc.isa in _TRAP:
        prog = rts.program(seed.Realization(abi="linux"))
        return _used_syscalls(prog, tc.isa)
    raise RuntimeError(f"{tc.name}: no binding extractor for isa "
                       f"{tc.isa!r}")


def check_caps(name: str, caps, used: set, path: str) -> list:
    """Subset check; returns error strings ([] = pass)."""
    errs = []
    if not isinstance(caps, dict):
        return [f"{name}: no caps declared"]
    ports = caps.get("ports", {})
    osb = caps.get("os", {})
    if not isinstance(ports, dict) or not isinstance(osb, dict):
        return [f"{name}: caps.ports / caps.os must be objects"]
    for p, m in ports.items():
        if p not in KNOWN_PORTS:
            errs.append(f"{name}: unknown port {p!r}")
        if not (isinstance(m, str) and PORT_MODE.match(m)):
            errs.append(f"{name}: port {p!r} bad mode {m!r}")
    for b, plist in osb.items():
        if not isinstance(plist, list) or any(
                p not in KNOWN_PORTS for p in plist):
            errs.append(f"{name}: binding {b!r} bad port list {plist!r}")
            continue
        if plist and not any(p in ports for p in plist):
            errs.append(f"{name}: binding {b!r} serves no declared "
                        f"port {plist}")
    for b in sorted(used):
        if b not in osb:
            errs.append(f"{name}: used binding {b} not declared")
            continue
        plist = osb[b]
        if plist and not any(p in ports for p in plist):
            errs.append(f"{name}: used binding {b} needs one of "
                        f"{plist} — none declared")
    if path == "native" and not set(ports) <= EMITTER_PORTS:
        errs.append(f"{name}: emitter ports {sorted(ports)} exceed "
                    f"{sorted(EMITTER_PORTS)}")
    return errs


def _caps_of(routines_name: str):
    comp = toolchain.components()["routines"].get(routines_name)
    if comp is None:
        return None
    return dict(comp.data).get("caps")


def _rts(name: str):
    """The routines record; None when the component is declared-only."""
    comp = toolchain.components()["routines"].get(name)
    if comp is None:
        return None
    try:
        return comp.resolve()
    except toolchain.NotRealized:
        return None


def _negatives() -> bool:
    ok = True
    caps = _caps_of("x86_64.win64.lo")
    tc = toolchain.by_name("native.x86_64.pe")
    used = _used(tc, _rts(tc.routines))
    bad = {"ports": dict(caps["ports"]),
           "os": {k: v for k, v in caps["os"].items()
                  if k != "kernel32!ReadFile"}}
    errs = check_caps("neg:win64.lo minus ReadFile", bad, used, "runtime")
    if errs:
        print(f"  ok rejected (undeclared used binding): {errs[0]}")
    else:
        print("  FAIL negative case accepted: undeclared binding")
        ok = False
    em = _caps_of("x86_64.win64.xdu")
    tcx = toolchain.by_name("xdu.x86_64.pe")
    used_x = _used(tcx, _rts(tcx.routines))
    bad2 = {"ports": dict(em["ports"], **{"payload": "R"}),
            "os": dict(em["os"])}
    errs = check_caps("neg:xdu emitter + payload", bad2, used_x, "native")
    if errs:
        print(f"  ok rejected (emitter over-caps): {errs[0]}")
    else:
        print("  FAIL negative case accepted: emitter payload")
        ok = False
    return ok


def main() -> int:
    ok = True
    used_cache = {}   # routines name -> (used set, isa name, includes)
    for tc in toolchain.load()["toolchains"]:
        rts = _rts(tc.routines)
        if rts is None:
            continue   # declared-only routines: nothing to extract
        if tc.routines not in used_cache:
            used_cache[tc.routines] = (
                _used(tc, rts), tc.isa, getattr(rts, "imports", ()))
        used, isa_name, inc = used_cache[tc.routines]
        caps = _caps_of(tc.routines)
        errs = check_caps(tc.name, caps, used, tc.path)
        if isa_name == "c" and isinstance(caps, dict):
            want = caps.get("includes", [])
            for h in inc:
                if h not in want:
                    errs.append(f"{tc.name}: include {h!r} not in "
                                f"caps.includes")
        if errs:
            ok = False
            for e in errs:
                print(f"  FAIL {e}")
        else:
            print(f"  ok {tc.name:24s} used={len(used)} "
                  f"declared={len(caps['os'])} "
                  f"ports={sorted(caps['ports'])}")
    ok = _negatives() and ok
    print(f"{'OK' if ok else 'FAIL'} caps_gate")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
