"""
lean_eval — witness 3b: batched Lean #eval spot oracle.

to_lterm renders an NExpr as de Bruijn `LTerm` text (free vars are an
error — the oracle runs closed terms only); each NComb atom becomes
its standard lambda definition as an abs-chain (I/K/S/B/D/C).

run_batch writes ONE temp .lean file (`import ISAR.LambdaEval`, one
`#eval IO.println` line per probe carrying `PROBE\\t<label>\\t<repr>`)
and invokes `lake env lean` ONCE from the repo root — the ~25 s olean
load dominates, so every probe batches into a single invocation.
The `ISAR.ITerm` Repr output is parsed back to host T.

Comparison is at the FINAL NF only — and even there spelling differs:
Lean `compile` emits abstract0-class terms (`compile constL = B K I`,
a 2-arg comp spine) where host atoms stay atoms (`K`).  So the oracle
batches BOTH the probe and its expected value through the same
lambda-expansion path and compares their reducedFuels — identical
syntactic NFs by the proved confluence (ParStep diamond), never a
host-spelling match.

`--with-lean` gates the real run; without it (or without lake) the
suite prints SKIP — never silent, never FAIL.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from typing import Dict, List, Optional, Tuple

_HOST = os.path.dirname(os.path.abspath(__file__))
if _HOST not in sys.path:
    sys.path.insert(0, _HOST)
_REPO = os.path.dirname(_HOST)

from reduce import T, K, I, KK, B, S, D, C, app  # noqa: E402
from lambda_dialect import NVar, NAbs, NApp, NComb, NExpr, parse  # noqa: E402


# ---------------------------------------------------------------------------
# NExpr -> LTerm text (de Bruijn)
# ---------------------------------------------------------------------------

_COMB_LTERM = {
    K.NORM: "(LTerm.abs (LTerm.var 0))",
    K.KONST: "(LTerm.abs (LTerm.abs (LTerm.var 1)))",
    K.S: ("(LTerm.abs (LTerm.abs (LTerm.abs "
          "(LTerm.app (LTerm.app (LTerm.var 2) (LTerm.var 0)) "
          "(LTerm.app (LTerm.var 1) (LTerm.var 0))))))"),
    K.COMP: ("(LTerm.abs (LTerm.abs (LTerm.abs "
             "(LTerm.app (LTerm.var 2) "
             "(LTerm.app (LTerm.var 1) (LTerm.var 0))))))"),
    K.DUP: ("(LTerm.abs (LTerm.abs "
            "(LTerm.app (LTerm.app (LTerm.var 1) (LTerm.var 0)) "
            "(LTerm.var 0))))"),
    K.SWAP: ("(LTerm.abs (LTerm.abs (LTerm.abs "
             "(LTerm.app (LTerm.app (LTerm.var 2) (LTerm.var 0)) "
             "(LTerm.var 1)))))"),
}


def to_lterm(e: NExpr, env: Tuple[str, ...] = ()) -> str:
    if isinstance(e, NVar):
        try:
            return f"(LTerm.var {env.index(e.name)})"
        except ValueError:
            raise ValueError(f"to_lterm: free var {e.name!r}")
    if isinstance(e, NAbs):
        return f"(LTerm.abs {to_lterm(e.body, (e.param,) + env)})"
    if isinstance(e, NApp):
        return f"(LTerm.app {to_lterm(e.left, env)} " \
               f"{to_lterm(e.right, env)})"
    return _COMB_LTERM[e.atom.k]


# ---------------------------------------------------------------------------
# ISAR.ITerm Repr -> T
# ---------------------------------------------------------------------------

_ITERM_ATOMS = {"norm": I, "konst": KK, "dup": D, "swap": C,
                "comp": B, "sₛ": S}


def parse_iterm(s: str) -> T:
    """Parse `ISAR.ITerm.<ctor>` Repr output (atoms may appear
    parenthesized in argument position)."""
    toks = s.replace("(", " ( ").replace(")", " ) ").split()
    pos = [0]

    def go() -> T:
        tok = toks[pos[0]]
        pos[0] += 1
        if tok == "(":
            t = go()
            if toks[pos[0]] != ")":
                raise ValueError(f"parse_iterm: expected ')' in {s!r}")
            pos[0] += 1
            return t
        name = tok.rsplit(".", 1)[-1]
        if name == "app":
            return app(go(), go())
        if name == "var":
            n = int(toks[pos[0]])
            pos[0] += 1
            return T(K.VAR, n=n)
        if name in _ITERM_ATOMS:
            return _ITERM_ATOMS[name]
        raise ValueError(f"parse_iterm: unknown ctor {tok!r} in {s!r}")

    t = go()
    if pos[0] != len(toks):
        raise ValueError(f"parse_iterm: trailing tokens in {s!r}")
    return t


# ---------------------------------------------------------------------------
# batched oracle — one lake env lean invocation for ALL probes
# ---------------------------------------------------------------------------

def available() -> bool:
    return (shutil.which("lake") is not None
            and os.path.exists(os.path.join(_REPO, "lakefile.toml")))


def run_batch(probes: List[Tuple[str, NExpr]], fuel: int = 2_000_000,
              timeout: int = 300, echo: bool = False) -> Dict[str, T]:
    """One `lake env lean` invocation for ALL probes; returns
    label -> NF as host T."""
    lines = ["import ISAR.LambdaEval", "", "open ISAR", ""]
    for label, e in probes:
        lt = to_lterm(e)
        lines.append(
            f'#eval IO.println s!"PROBE\\t{label}\\t'
            f'{{repr (reduceFuel {fuel} (compile {lt}))}}"')
    src = "\n".join(lines) + "\n"
    fd, path = tempfile.mkstemp(suffix=".lean", prefix="lean_eval_")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as f:
            f.write(src)
        cp = subprocess.run(["lake", "env", "lean", path],
                            cwd=_REPO, capture_output=True, text=True,
                            encoding="utf-8", errors="replace",
                            timeout=timeout)
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    if cp.returncode != 0:
        raise RuntimeError(
            f"lake env lean failed (rc={cp.returncode}):\n"
            f"{cp.stdout}{cp.stderr}")
    # derived Repr pretty-prints large terms across multiple lines:
    # a `PROBE\t<label>\t<chunk>` line starts a record, continuation
    # lines append to its repr text.
    out: Dict[str, T] = {}
    cur_label: Optional[str] = None
    chunks: List[str] = []
    for line in cp.stdout.splitlines():
        if line.startswith("PROBE\t"):
            if cur_label is not None:
                out[cur_label] = parse_iterm(" ".join(chunks))
            _tag, cur_label, chunk = line.split("\t", 2)
            chunks = [chunk]
        elif cur_label is not None:
            chunks.append(line)
        if echo and cur_label is not None:
            enc = sys.stdout.encoding or "utf-8"
            print("  " + line.encode(enc, "backslashreplace").decode(enc))
    if cur_label is not None:
        out[cur_label] = parse_iterm(" ".join(chunks))
    missing = [label for label, _ in probes if label not in out]
    if missing:
        raise RuntimeError(
            f"lean_eval: no output for probes {missing}; "
            f"stdout was:\n{cp.stdout}\nstderr:\n{cp.stderr}")
    return out


# ---------------------------------------------------------------------------
# self-test — goldens: closed lambda terms with known NFs.
# Probe AND expected go through the same lambda-expansion oracle;
# confluence makes their NFs syntactically identical.  Host lstep on
# the same sources pins the spelling (str(host NF) == expected text).
# ---------------------------------------------------------------------------

_GOLDENS: Tuple[Tuple[str, str, str], ...] = (
    ("id K",      "(\\x. x) K",                              "K"),
    ("const S I", "((\\x. \\y. x) S) I",                     "S"),
    ("s K K I",   "(((\\x. \\y. \\z. (x z) (y z)) K) K) I",  "I"),
    ("flip S I",  "((\\x. \\y. (y x)) S) I",                 "S"),
    ("c2 B I",    "((\\f. \\x. f (f x)) B) I",               "(B (B I))"),
)


def main() -> int:
    want_lean = "--with-lean" in sys.argv[1:]
    if not want_lean:
        print("SKIP lean.eval (--with-lean not passed)")
        return 0
    if not available():
        print("SKIP lean_eval (lake not found)")
        return 0

    import lambda_eval  # noqa: E402

    ok = True
    batch: List[Tuple[str, NExpr]] = []
    exprs = []
    for label, src, exp_src in _GOLDENS:
        e, x = parse(src), parse(exp_src)
        exprs.append((label, e, x, exp_src))
        batch.append((label, e))
        batch.append((label + " [expected]", x))
    got = run_batch(batch, echo=True)
    for label, e, x, exp_src in exprs:
        lean_nf, lean_x = got[label], got[label + " [expected]"]
        host_nf = lambda_eval.observe(lambda_eval.eval(e)[0])
        host_x = lambda_eval.observe(lambda_eval.eval(x)[0])
        good = (lean_nf == lean_x and host_nf == host_x
                and str(host_nf) == exp_src)
        ok = ok and good
        print(f"{'OK' if good else 'FAIL'} {label}: "
              f"lean==expected ({lean_nf} ~ {lean_x})  "
              f"host==expected ({host_nf} ~ {host_x})")
    print(f"{'OK' if ok else 'FAIL'} lean_eval")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
