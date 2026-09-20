"""
xdu_dialect — nibble transducer plex (xdu.json) for the `native` path and
its `runtime`-path mirror.  First program class realized on BOTH paths
(toolchain.json: dialects."xdu.json", toolchains."xdu.x86_64.pe").

Program class (data, programs/xdu/*.json):
    {"name", "alphabet": "nibble", "start",
     "states": {<s>: {"on": {key: {"emit": [...], "next": <s>}},
                     "eof": {"emit": [...], "halt": rc}}}}
key = nibble "0".."f" or "*" default; emit item = nibble literal "0".."f"
or "$in" (the input nibble that dispatched the arm); eof = final emit +
halt rc in 0..15.  Deterministic finite transducers only — every state
must cover all 16 nibble keys (literally or via "*"); counting (unbounded
state) and byte alphabets are declared uncovered in paths.native.

Declared maps (toolchain.json dialects."xdu.json".maps):
  input:   nibbles_to_term(bytes) -> T
  output:  term_to_nibbles(nf) -> (bytes, rc)
  program: to_lambda(XDU) -> str

INPUT MAP — bytes become a Scott list of nibble selectors: each input
byte contributes hi then lo nibble; nibble k is the 16-ary selector
`\\c0. … \\c15. ck` (bracket-abstracted); the list is `cons h t` =
`\\n. \\c. c h t` cells ending in `nil` = `\\n. \\c. n` = K.

OUTPUT MAP / spine convention — the NF of `encode(xdu, input)` is
    C h1 (C h2 (… (C h_last K)))
where C is the SWAP atom used as the declared cons tag: 2-arg-inert in
every realized basis (swapβ needs a third argument on graph.lo/graph.cd;
reduce.py carries no swapβ at all).  The plan's `S h t` sketch was
verified NOT inert on the runtime path: graph.lo expands S to derived_s
on import, and `derived_s h t` keeps reducing — so C is the cons tag.
Each element h decodes as `B^k I` → nibble k (the cube's canonical
k-distinct NF: B (B (… I)), inert at 1 arg everywhere).  The LAST spine
element before K is the halt rc nibble; the elements before it are output
nibbles packed pairwise hi|lo into bytes.  An odd output-nibble count
drops the pending nibble and OVERRIDES rc to 3 — the identical
convention in term_to_nibbles, interpret(), and the native routines.

PROGRAM MAP — to_lambda produces λ-source for
    \\l. \\n. n STEP (\\k. k l SEL_start (\\r. r))
i.e. a Church-numeral-bounded iteration of one STEP over the input list.
Recursion is deliberately NOT a fixpoint combinator: `λf.(λx.f(xx))(λx.f(xx))`
was verified to diverge under graph.cd — complete development re-develops
the self-reproducing ΩΩ redex inside dead selector arms every round and
never reaches a fixpoint (on graph.lo it only survived through LO
laziness).  STEP consumes one Scott cell, `tl EOF CONS`:
  EOF  = `(st E_0 … E_{N-1}) o`      — state selector picks eof handler
  CONS = `\\h. \\t. (st H_0 … H_{N-1}) h t o`
where `st` is an N-ary state selector, E_j = `\\o. o <eof spine>` and
H_j = `\\h. \\t. \\o. h a_0 … a_15` — the per-state 16-arm dispatch.
Arm a_k emits into the output continuation `o` (CPS difference list,
each emit wraps `o` as `\\r. o (C nib … r)`) and rebuilds the
accumulator `\\k. k t SEL_next o'`.  A `$in` emit at arm position k
emits `B^k I` — the position's nibble IS the input nibble (also for "*"
arms, which are replicated per position).  encode() applies the program
to `nibbles_to_term(input)` and `church(n+1)`: after the last nibble the
accumulator's tail is nil, so the (n+1)-th STEP fires the eof branch and
the result is the output spine.  States are compile-time constants;
nothing recursive is ever a residual — graph.cd reaches its fixpoint.

The module imports only host modules (reduce/lambda_dialect/observation_
regime) — never seed.
"""
from __future__ import annotations

import json
import os
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)

from reduce import T, K, I, KK, B, S, C, app  # noqa: E402
from lambda_dialect import parse, bracket_abstract0  # noqa: E402
from observation_regime import ObservationRegime  # noqa: E402

NIB_KEYS = tuple(f"{k:x}" for k in range(16))
STAR = "*"
IN = "$in"

_PROGRAMS = os.path.normpath(os.path.join(_HOST, "..", "programs", "xdu"))


# ---------------------------------------------------------------------------
# XDU record + loader
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class XDU:
    """Loaded nibble transducer (the toolchain.json dialect record)."""
    name: str
    alphabet: str           # "nibble"
    start: str
    states: Dict[str, dict]  # name -> {"on": {key: rule}, "eof": {...}}
    path: str = ""


def _validate_rule(xdu_name: str, state: str, key: str, rule: dict,
                   states) -> None:
    if not isinstance(rule, dict):
        raise ValueError(f"{xdu_name}.{state}[{key}]: rule must be an object")
    emit = rule.get("emit")
    nxt = rule.get("next")
    if not isinstance(emit, list) or not all(
            isinstance(it, str) and (it == IN or it in NIB_KEYS)
            for it in emit):
        raise ValueError(
            f"{xdu_name}.{state}[{key}]: emit must be a list of "
            f"'0'..'f' or '$in', got {emit!r}")
    if nxt not in states:
        raise ValueError(f"{xdu_name}.{state}[{key}]: next {nxt!r} not a state")


def _validate(xdu: XDU) -> XDU:
    name = xdu.name
    if xdu.alphabet != "nibble":
        raise ValueError(f"{name}: alphabet {xdu.alphabet!r} != 'nibble'")
    if not xdu.states:
        raise ValueError(f"{name}: no states")
    if xdu.start not in xdu.states:
        raise ValueError(f"{name}: start {xdu.start!r} not a state")
    for s, st in xdu.states.items():
        on = st.get("on")
        eof = st.get("eof")
        if not isinstance(on, dict) or not isinstance(eof, dict):
            raise ValueError(f"{name}.{s}: needs 'on' object and 'eof' object")
        for key, rule in on.items():
            if key != STAR and key not in NIB_KEYS:
                raise ValueError(
                    f"{name}.{s}: on-key {key!r} not '0'..'f' or '*'")
            _validate_rule(name, s, key, rule, xdu.states)
        uncovered = [k for k in NIB_KEYS
                     if k not in on and STAR not in on]
        if uncovered:
            raise ValueError(
                f"{name}.{s}: uncovered nibble keys {uncovered} (no '*' "
                "default)")
        emit = eof.get("emit")
        halt = eof.get("halt")
        if not isinstance(emit, list) or not all(
                isinstance(it, str) and it in NIB_KEYS for it in emit):
            raise ValueError(
                f"{name}.{s}.eof: emit must be literal nibbles "
                f"('0'..'f', no '$in' at eof), got {emit!r}")
        if not isinstance(halt, int) or not 0 <= halt <= 15:
            raise ValueError(f"{name}.{s}.eof: halt {halt!r} not in 0..15")
    return xdu


def load(path: str) -> XDU:
    """Load and validate a programs/xdu/*.json transducer."""
    with open(path, encoding="utf-8") as f:
        d = json.load(f)
    return _validate(XDU(
        name=d["name"], alphabet=d.get("alphabet", "nibble"),
        start=d["start"], states=d["states"], path=path))


def probe_path(name: str) -> str:
    return os.path.join(_PROGRAMS, name + ".json")


def rule_for(xdu: XDU, state: str, nibble: int) -> dict:
    """The rule a state applies to an input nibble ('*' = default arm)."""
    on = xdu.states[state]["on"]
    return on.get(f"{nibble:x}", on.get(STAR))


# ---------------------------------------------------------------------------
# interpret — the independent expected value (direct JSON table walk).
# The gate compares native stdout+rc and the runtime-path decode against
# this; it shares no code with either path.
# ---------------------------------------------------------------------------

def interpret(xdu: XDU, data: bytes) -> Tuple[bytes, int]:
    out: List[int] = []
    st = xdu.start
    for byte in data:
        for k in (byte >> 4, byte & 15):
            rule = rule_for(xdu, st, k)
            for it in rule["emit"]:
                out.append(k if it == IN else int(it, 16))
            st = rule["next"]
    eof = xdu.states[st]["eof"]
    for it in eof["emit"]:
        out.append(int(it, 16))
    rc = eof["halt"]
    if len(out) & 1:                    # odd pending nibble: dropped, rc 3
        rc = 3
        out = out[:-1]
    return bytes(out[i] << 4 | out[i + 1]
                 for i in range(0, len(out), 2)), rc


def stdout_rc_regime() -> ObservationRegime:
    """Declared regime `stdout+rc` (toolchain.json regimes): a (XDU, bytes)
    presentation is observed as (stdout_bytes, returncode) — the direct
    table interpretation is the regime's own observer."""
    return ObservationRegime(
        name="stdout+rc",
        observe=lambda pd: interpret(pd[0], pd[1]),
        obs_eq=lambda a, b: a == b,
    )


# ---------------------------------------------------------------------------
# input map: bytes -> Scott list of 16-ary nibble selectors
# ---------------------------------------------------------------------------

def _appn(*xs: T) -> T:
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t


_CONS = bracket_abstract0(parse("\\h. \\t. \\n. \\c. c h t"))
_NIL = KK                                # \n. \c. n = K

_SELECTORS: Tuple[T, ...] = tuple(
    bracket_abstract0(parse(
        "".join(f"\\c{i}. " for i in range(16)) + f"c{k}"))
    for k in range(16))


def nibbles_to_term(data: bytes) -> T:
    """bytes -> Scott list, one cell per nibble (hi then lo per byte)."""
    t = _NIL
    for byte in reversed(data):
        t = _appn(_CONS, _SELECTORS[byte & 15], t)
        t = _appn(_CONS, _SELECTORS[byte >> 4], t)
    return t


# ---------------------------------------------------------------------------
# output map: NF spine `C h t` … `K`; elements `B^k I`; last element = rc
# ---------------------------------------------------------------------------

def _decode_nib(h: T) -> int:
    """B^k I -> k."""
    k = 0
    while h.k == K.APP and h.l is not None and h.l.k == K.COMP:
        k += 1
        h = h.r
    if h is None or h.k != K.NORM:
        raise ValueError(f"output map: nibble element is not B^k I: {h}")
    return k


def term_to_nibbles(nf: T) -> Tuple[bytes, int]:
    """Walk the inert output spine: `C h t` cells until `K`; last element
    before K is the rc nibble; earlier elements pack pairwise to bytes;
    odd output count drops the pending nibble and overrides rc to 3."""
    nibs: List[int] = []
    t = nf
    while (t.k == K.APP and t.l is not None and t.l.k == K.APP
           and t.l.l is not None and t.l.l.k == K.SWAP):
        nibs.append(_decode_nib(t.l.r))
        t = t.r
    if t is None or t.k != K.KONST:
        raise ValueError(f"output map: spine does not end in K: {t}")
    if not nibs:
        raise ValueError("output map: empty spine (no rc element)")
    rc = nibs[-1]
    out = nibs[:-1]
    if len(out) & 1:
        rc = 3
        out = out[:-1]
    return bytes(out[i] << 4 | out[i + 1]
                 for i in range(0, len(out), 2)), rc


# ---------------------------------------------------------------------------
# program map: XDU -> λ-source (bounded Church iteration of one STEP)
# ---------------------------------------------------------------------------

def _b_src(k: int) -> str:
    """B^k I as λ-source text."""
    s = "I"
    for _ in range(k):
        s = f"(B {s})"
    return s


def _nsel(n: int, i: int) -> str:
    """N-ary selector \\x0. … \\x_{N-1}. x_i."""
    return "(" + "".join(f"\\x{j}. " for j in range(n)) + f"x{i})"


def _spine_src(vals: List[int], tail: str) -> str:
    out = tail
    for v in reversed(vals):
        out = f"(C {_b_src(v)} {out})"
    return out


def to_lambda(xdu: XDU) -> str:
    """XDU -> λ-source of `\\l. \\n. n STEP (acc0 l)` — see module docstring."""
    states = list(xdu.states)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    e_hs, h_hs = [], []
    for s in states:
        st = xdu.states[s]
        on, eof = st["on"], st["eof"]
        spine_j = _spine_src([int(it, 16) for it in eof["emit"]],
                             f"(C {_b_src(eof['halt'])} K)")
        e_hs.append(f"(\\o2. o2 {spine_j})")
        arms = []
        for k in range(16):
            rule = on.get(f"{k:x}", on.get(STAR))
            vals = [(k if it == IN else int(it, 16))
                    for it in rule["emit"]]
            out2 = "\\r. o " + _spine_src(vals, "r")
            arms.append(
                f"(\\k2. k2 t {_nsel(n, idx[rule['next']])} ({out2}))")
        h_hs.append("(\\h. \\t. \\o. h " + " ".join(arms) + ")")
    e_sel = "(st " + " ".join(e_hs) + ")"
    h_sel = "(st " + " ".join(h_hs) + ")"
    step = ("\\acc. acc (\\tl. \\st. \\o. tl (" + e_sel + " o) "
            "(\\h. \\t. " + h_sel + " h t o))")
    return ("(\\l. \\n. n (" + step + ") "
            "(\\k. k l " + _nsel(n, idx[xdu.start]) + " (\\r. r)))")


# ---------------------------------------------------------------------------
# encode: program applied to input map + iteration count (nibbles + 1 —
# the last STEP fires the eof branch on the nil tail)
# ---------------------------------------------------------------------------

# church(k): c_k = \\f. \\x. f^k x — built iteratively as
# S A (S A (… (K I))) with A = S (K S) (S (K K) I), so no bracket
# recursion depth grows with k (the gate's 64KiB corpus needs k ~ 131073).
_CHURCH_A = _appn(S, app(KK, S), _appn(S, app(KK, KK), I))


def church(k: int) -> T:
    """Church numeral c_k as a combinator term (iterative construction)."""
    t = app(KK, I)                          # c_0 = K I
    for _ in range(k):
        t = _appn(S, _CHURCH_A, t)
    return t


def encode(xdu: XDU, data: bytes) -> T:
    """XDU + input bytes -> substrate term for the runtime path."""
    prog = bracket_abstract0(parse(to_lambda(xdu)))
    n = 2 * len(data) + 1
    return _appn(prog, nibbles_to_term(data), church(n))


# ---------------------------------------------------------------------------
# self-test
# ---------------------------------------------------------------------------

PROBES = ("echo", "hexdump", "drop0", "toggle")


def main() -> int:
    ok = True
    for name in PROBES:
        xdu = load(probe_path(name))
        for data in (b"", b"Hi", bytes(range(16))):
            out, rc = interpret(xdu, data)
            print(f"  {name} {data!r:24s} -> out={out!r} rc={rc}")
        # a couple of spot expectations
        if name == "echo":
            good = interpret(xdu, b"Hi") == (b"Hi", 0)
        elif name == "hexdump":
            good = interpret(xdu, b"Hi") == (b"4869", 0)
        elif name == "drop0":
            good = interpret(xdu, bytes([0x10, 0x01])) == (b"\x11", 0)
        else:
            good = interpret(xdu, b"Hi") == (b"F", 0)
        if not good:
            print(f"  FAIL {name} expectation")
            ok = False
    xdu = load(probe_path("echo"))
    src = to_lambda(xdu)
    print(f"  to_lambda(echo): {len(src)} chars")
    print(f"{'OK' if ok else 'FAIL'} xdu_dialect")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
