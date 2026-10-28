#!/usr/bin/env python3
"""host2.check — the C witness gate.

host2's witnesses are two C99 tools over the declared rows in
`specs/`:

  korufe : .k (real koru surface) -> program.ast.json (canon shape)
           --lower -> [flow-eval] claim (the lower-layer wire)
  krun   : the [flow-eval] claim checker / evaluator / emitter host

The suite convention — every case is a leaf folder (bend-style,
numbered like koru's own regression tests):

  specs/tests/<GGG>_<group>/<NNN>_<leaf>/   generated corpus
      100_flow/    flow grammar: arms, dispatch, guards, labels
      200_emit/    the emission fixpoint: accepts + kEmit refusals
                   + kemit itself (emit_prog)
      800_forged/  asserted-wrong expectations (drift probes)
      900_wire/    rows with no surface spelling — cases.json only,
                   the claim is generated data (residual |* catchall
                   dispatch; koru binds residuals through metatypes)
  specs/benches/<NNN>_<name>/               fuel-heavy authored cases
  specs/ported/<name>/                      authored real-koru
                                            programs (named, like
                                            koru's own examples/)

Each leaf holds `input.k` (surface rows) + `cases.json` (rows keyed
by leaf name).  `check.py` walks all three trees uniformly and
enforces the convention: NNN_name dirs, file:"input.k", wire rows
carry "claim" and no file.

The pipeline per case row:

  parse : korufe input.k -> build/KEY.ast.json
  lower : korufe --lower ast cases.json KEY -> build/KEY.claim
  wire  : rows carrying "claim" skip parse/lower
  claim : krun claim -> "ok ..." | forged -> "drift" exit 4
  witness : every emitted claim re-decided by the AUTHORITY's
          mechanized semantics — w:/src/koru's FlowCheck over
          FlowKernel (koru/flowcheck row in realizations.json);
          conformance corpus all-MATCH, forged corpus all-REJECT.
          This is the eval.c-is-runK witness: two independent
          evaluators agreeing on the same wire
  emit  : krun kemit.claim --emit claim -> row's expected emit text
          ("refuse" for out-of-subset rows)
  cc    : emitted .c compiled by the assembly.json c99 toolchain row,
          run -> exit DWORD == claim's expect value
  ccv   : emitted .c through the machine-checked CompCert row (docker
          ccomp -S -> i386 gcc link+run) -> exit byte == expect's low
          byte (host DWORD vs shell exit are two observations of the
          same int; both recorded)
  gen.stamp : kemit.c's input.fnv1a64 stamp must equal fnv of
          900_kemit/input.k — a stale generated artifact fails,
          never silently passes
  h1    : the COMPILED kemit — specs/gen/kemit.c is emitProgC(kEmit)
          generated C; `krun --quote claim | kemit_bin` must emit the
          same C text as `krun --emit` (or refuse, exit 4) on every
          row — compiled ≡ interpreted, the loop's first turn
  h1v   : the same compiled compiler through the CompCert row —
          a machine-checked-compiled compiler observing identically
  h2    : the compiled compiler's OUTPUT back through the checked
          backend — ccomp-built kemit's C -> ccomp -> i386 run ->
          exit byte == expect.  Changed input -> H1' -> H2'
  kl/ks : compiled emit_args programs — specs/gen/<g>.c is
          emitProgC(<prog>) for emit_args leaves (klex, ksexp);
          `krun --args claim | <g>_bin` must re-decide the claim's
          text — leg suffix = first two letters of the gen name,
          <code>v = the ccomp-compiled twin
  <code>r : the AST race — for `race` rows (kast): `koruc
          --ast-json` normalized to the same flat `(kind span…)`
          row text must equal what the program decided —
          authority AST ≡ koru-spelled parser output
  kw    : the WIDE race — every specs/tests input.k through the
          compiled kast (enlarged-stack build, invoke-recursion
          axis) vs `koruc --ast-json` normalized; row-identical
          plus refusal parity both directions
  kwj   : the JSON race — the same corpus through `korufe
          --ast-json` vs `koruc --ast-json`, deep-equal modulo the
          path-dependent location.file.  The readable view is the
          authority/interop document
  kwc   : the CANON race — `korufe --ast-canon` vs `koruc
          --ast-canon`, deep-equal with zero normalization.  The
          reflective dump is lossless: retbind, jump args, and
          expression trees (parsed_expression/condition_expr) all
          compare — the full-shape boundary, and the target the
          typed-koru reifier should emit

Spec rows consumed as data: cases.json (entry/fuel/expect/emit/oracle/
claim), assembly.json (cc + flags + run semantics). Refusal probes
assert the frontend's refuse-by-default contract incl. koruc-parity
axes (PARSE003/005/006, KORU021/104, retired `| *`). This script is
orchestration only — no evaluator, parser, or emission logic lives
here.

specs/tests/ is GENERATED by tools/DumpKoruFixtures.lean — real
koru syntax (every input.k passes `koruc -c`), never edited.
benches/ + ported/ are authored the same way: input.k plus
entry rows + oracle leaves, each file checked against the `koruc`
authority declared in realizations.json.
"""
from __future__ import annotations

import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

_HOST2 = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HOST2)
SRC_KRUN = [os.path.join(_HOST2, "src", "krun", f)
            for f in ("sx.c", "wire.c", "eval.c", "quote.c", "main.c")]
SRC_KORUFE = [os.path.join(_HOST2, "src", "korufe", f)
              for f in ("util.c", "lex.c", "parse.c", "astio.c",
                        "lower.c", "main.c")]
KRUN = os.path.join(_HOST2, "build", "krun.exe" if os.name == "nt" else "krun")
KORUFE = os.path.join(_HOST2, "build", "korufe.exe" if os.name == "nt" else "korufe")
SPECS = os.path.join(_HOST2, "specs")
BUILD = os.path.join(_HOST2, "build")

# the suite convention (see the module docstring): every case is a
# leaf folder holding cases.json (+ input.k for surface rows)
TREES = ("tests", "benches", "ported")
NUM_RE = re.compile(r"^\d{3}_[a-z0-9_]+$")
NAME_RE = re.compile(r"^[a-z0-9_]+$")

CLANG = r"C:\Program Files\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang"


def _clang():
    if os.path.exists(CLANG):
        return CLANG
    return shutil.which("clang")


def _load(spec):
    with open(os.path.join(SPECS, spec), encoding="utf-8") as f:
        return json.load(f)


def _fnv1a64(b: bytes) -> int:
    """FNV-1a-64 — the generated-artifact freshness stamp, twin of
    the generator's.  Callers normalize CRLF first: the stamp binds
    content, not checkout line-endings."""
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h


# ---- the kast race: koruc --ast-json → the flat (kind span…) row
# text the koru-spelled parser emits, so both sides can be diffed.
# The authority's schema maps onto ours row-for-row; where it
# normalizes text (arg values, conditions) the comparison boundary
# is the source SPAN, and where it injects structure (the implicit
# import_decl) the location's own text is what keeps it honest —
# a location that doesn't point at an `import` token drops out.

_AST_ATOM = (
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-")


def ast_view_norm(o):
    """Normalize a readable `--ast-json` document for cross-frontend
    equality: `location.file` is path-dependent (koruc echoes the
    argv path, korufe sees the relative one), so it collapses to the
    basename without extension.  Everything else compares exact —
    the readable view is the shared interop document, and the whole
    point of the mirror is that no printer dialect remains."""
    if isinstance(o, dict):
        return {k: (os.path.basename(v).rsplit(".", 1)[0]
                    if k == "file" and isinstance(v, str)
                    else ast_view_norm(v))
                for k, v in o.items()}
    if isinstance(o, list):
        return [ast_view_norm(v) for v in o]
    return o


def ast_view_diff(a, b, path="$"):
    """First structural difference between two normalized view
    docs — returns (path, theirs, ours) or None."""
    if type(a) is not type(b):
        return path, a, b
    if isinstance(a, dict):
        if set(a) != set(b):
            return path, "keys " + repr(sorted(set(a) ^ set(b))), ""
        for k in a:
            r = ast_view_diff(a[k], b[k], path + "." + k)
            if r:
                return r
        return None
    if isinstance(a, list):
        if len(a) != len(b):
            return path, f"len {len(a)}", f"len {len(b)}"
        for i, (x, y) in enumerate(zip(a, b)):
            r = ast_view_diff(x, y, f"{path}[{i}]")
            if r:
                return r
        return None
    return (path, a, b) if a != b else None


def ast_norm_rows(src, ast):
    """`koruc --ast-json` output → list of `(kind i j …)` row text,
    the same flat wire kAst's `out` carries.  All offsets are BYTE
    positions: the wire carries the source as an int array of bytes
    and the authority's zig lexer counts []const u8 columns, so
    every scan below works on src.encode() — never on codepoints."""
    src = src.encode("utf-8")
    rows = []
    lstart = [0]
    for ln in src.split(b"\n")[:-1]:
        lstart.append(lstart[-1] + len(ln) + 1)

    def loff(loc):
        return lstart[loc["line"] - 1] + loc["col"]

    def line_end(pos):
        e = src.find(b"\n", pos)
        return len(src) if e < 0 else e

    def ws_fwd(pos):
        while pos < len(src) and src[pos] in b" \t\n\r":
            pos += 1
        return pos

    def hws_fwd(pos):
        while pos < len(src) and src[pos] in b" \t":
            pos += 1
        return pos

    def word_end(pos):
        e = pos
        while e < len(src) and src[e] in _AST_ATOM:
            e += 1
        return e

    def find_word(pat, lo, hi):
        """First occurrence of `pat` in src[lo:hi] with non-atom
        boundaries, like the parser's `word` scanner."""
        pat = pat.encode("utf-8")
        n = len(pat)
        i = lo
        while True:
            i = src.find(pat, i, hi)
            if i < 0:
                return -1
            if (i == 0 or src[i - 1] not in _AST_ATOM) and \
               (i + n >= len(src) or src[i + n] not in _AST_ATOM):
                return i
            i += 1

    def parens_args(pos):
        """`name(args)` at pos → list of (named?, nj, ne, vj, ve)
        arg spans, and the offset just past `)`."""
        o = src.find(b"(", pos)
        if o < 0:
            return None
        depth, i, segs, s0, ins = 0, o, [], o + 1, 0
        while i < len(src):
            c = src[i:i + 1]
            if c == b'"':
                ins = 1 - ins
            elif ins:
                pass
            elif c == b"(":
                depth += 1
            elif c == b")":
                depth -= 1
                if depth == 0:
                    segs.append((s0, i))
                    break
            elif c == b"," and depth == 1:
                segs.append((s0, i))
                s0 = i + 1
            i += 1
        args = []
        for a, b in segs:
            a = ws_fwd(a)
            if a >= b:
                continue
            # named arg iff a depth-0 ':' before any '('
            colon = None
            d = ins = 0
            for k in range(a, b):
                if src[k:k + 1] == b'"':
                    ins = 1 - ins
                elif ins:
                    pass
                elif src[k:k + 1] == b"(":
                    d += 1
                elif src[k:k + 1] == b")":
                    d -= 1
                elif src[k:k + 1] == b":" and d == 0:
                    colon = k
                    break
            if colon is not None:
                nj = a
                ne = word_end(nj)
                vj = hws_fwd(colon + 1)
                args.append((True, nj, ne, vj, b))
            else:
                args.append((False, 0, 0, a, b))
        return args, i + 1

    def emit_args(pos):
        for named, nj, ne, vj, ve in parens_args(pos)[0] or []:
            rows.append(f"(arg {nj} {ne} {vj} {ve})")

    def arm_line(loc):
        """The cont's `|` line → (line_start, line_end)."""
        return loff(loc), line_end(loff(loc))

    def emit_step_rows(st, v0, cle, via_pipe):
        """Step rows for the step whose value text starts at v0 and
        whose line ends at cle.  `via_pipe` is True when the step
        rides `|>` (invocation-shaped), False for `->` produce.
        Returns the offset just past the step's closing `)` for
        invocation/jump steps (the retbind `:` decision point),
        else None."""
        sty = st.get("type")
        if sty == "expression":
            rows.append(f"(step expr {v0} {cle})")
            return None
        if sty == "invocation":
            # `-> if(c) a else b` is an `["if"]` invocation in
            # the authority's schema — the else tail is not in
            # args.  kAst spans the whole expression; project to
            # the same `(step expr v0 cle)` row.  `|> if(g)` keeps
            # its invoke shape — the nested `| then`/`| else` arms
            # arrive as continuation rows on both sides.
            if st["invocation"]["event"] == ["if"] and not via_pipe:
                rows.append(f"(step expr {v0} {cle})")
                return None
            sj = v0
            se = word_end(sj)
            rows.append(f"(step invoke {sj} {se})")
            pa = parens_args(se)
            for named, nj2, ne2, vj, ve in (pa[0] if pa else []):
                rows.append(f"(arg {nj2} {ne2} {vj} {ve})")
            return pa[1] if pa else None
        if sty == "label_jump":
            sj = v0 + 1 if src[v0:v0 + 1] == b"@" else v0
            se = word_end(sj)
            rows.append(f"(step jump {sj} {se})")
            pa = parens_args(se)
            for named, nj2, ne2, vj, ve in (pa[0] if pa else []):
                rows.append(f"(arg {nj2} {ne2} {vj} {ve})")
            return pa[1] if pa else None
        if sty == "branch_constructor":
            sj = v0
            se = word_end(sj)
            rows.append(
                f"(ctor {sj} {se} {hws_fwd(se)} {cle})")
            return None
        return None

    def emit_cont(c, v0_hint=None):
        """Rows for one continuation plus its nested continuations.
        Named conts re-derive their `| branch` span from location;
        anonymous `|>`-chain conts (retbind / chained step) have
        branch "" — they emit no (cont) row and take their step
        position from the caller's `|>` scan."""
        if c["branch"]:
            cl0, cle = arm_line(c["location"])
            bj = hws_fwd(cl0 + 1)
            be = word_end(bj)
            rows.append(f"(cont {bj} {be})")
            t = hws_fwd(be)
            # bind / when / tail in source order
            if c.get("binding"):
                bb = c["binding"].encode("utf-8")
                rows.append(f"(bind {t} {t + len(bb)})")
                t = hws_fwd(t + len(bb))
            tt = t
            if c.get("condition") and src[t:t + 4] == b"when":
                c0 = hws_fwd(t + 4)
                tt = min(
                    (k for tok in (b"->", b"|>", b"=>")
                     for k in [src.find(tok, c0, cle)] if k >= 0),
                    default=cle)
                rows.append(f"(cond {c0} {tt})")
            st = c.get("step")
            if not st:
                return
            v0 = hws_fwd(tt + 2)
            via_pipe = src[tt:tt + 2] == b"|>"
        else:
            if v0_hint is None:
                rows.append("(bad 0 -2)")
                return
            v0 = v0_hint
            cle = line_end(v0)
            st = c.get("step")
            via_pipe = True
        ae = emit_step_rows(st, v0, cle, via_pipe) if st else None
        nested = c.get("continuations", [])
        if ae is None:
            for nc in nested:
                emit_cont(nc)
            return
        # after the step's `)`: `: name |>` retbind, `|>` chain, or
        # `| name` nested-dispatch arms (those re-derive by location)
        p2 = hws_fwd(ae)
        hint = None
        if src[p2:p2 + 1] == b":":
            w0 = hws_fwd(p2 + 1)
            w1 = word_end(w0)
            rows.append(f"(rbind {w0} {w1})")
            p3 = hws_fwd(w1)
            if src[p3:p3 + 2] == b"|>":
                hint = hws_fwd(p3 + 2)
        elif src[p2:p2 + 2] == b"|>":
            hint = hws_fwd(p2 + 2)
        for nc in nested:
            emit_cont(nc, hint)
            hint = None

    for it in ast.get("items", []):
        ty = it.get("type")
        loc = it.get("location") or {}
        if ty == "import_decl":
            p = ws_fwd(loff(loc))
            if src[p:p + 6] != b"import":
                continue  # injected prelude — no row
            s = hws_fwd(p + 6)
            rows.append(f"(imp {s} {line_end(s)})")
        elif ty == "event_decl":
            p = ws_fwd(loff(loc))
            nameb = it["name"].encode("utf-8")
            j = src.find(nameb, p)
            if j < 0:
                rows.append("(bad 0 -1)")
                continue
            rows.append(f"(ev {j} {j + len(nameb)})")
            le = line_end(j)
            for f in it["input"]["fields"]:
                fnb = f["name"].encode("utf-8")
                nj = find_word(f["name"], j, le)
                if nj < 0:
                    rows.append("(bad 0 -1)")
                    continue
                c = src.find(b":", nj + len(fnb), le)
                tj = hws_fwd(c + 1) if c >= 0 else nj + len(fnb)
                te = min((x for x in (src.find(b",", tj, le),
                                     src.find(b"}", tj, le))
                          if x >= 0), default=le)
                rows.append(f"(fld {nj} {nj + len(fnb)} "
                            f"{tj} {te})")
            # the authority drops `-> T` entirely; on a tor line
            # a post-fields `->` can only be the return annotation
            ar = src.find(b"->", j, le)
            if ar >= 0:
                rows.append(
                    f"(ret {hws_fwd(ar + 2)} {line_end(ar + 2)})")
            # `| name [type]` lines after the decl
            q = le + 1
            n_br = len(it["branches"])
            seen = 0
            while seen < n_br and q < len(src):
                q = ws_fwd(q)
                if src[q:q + 1] != b"|" or src[q + 1:q + 2] == b">":
                    break
                nj = hws_fwd(q + 1)
                ne = word_end(nj)
                t0 = hws_fwd(ne)
                qe = line_end(t0)
                if t0 < qe and src[t0] != 0x0A:
                    rows.append(f"(brd {nj} {ne} {t0} {qe})")
                else:
                    rows.append(f"(brd {nj} {ne} 0 0)")
                seen += 1
                q = qe + 1
        elif ty == "immediate_impl":
            p = ws_fwd(loff(loc))
            nj = word_end(p)
            le = line_end(p)
            ar = src.find(b"->", nj, le)
            v0 = ws_fwd(ar + 2) if ar >= 0 else le
            rows.append(f"(impl {p} {nj} {v0} {le})")
        elif ty == "flow":
            p = ws_fwd(loff(loc))
            le = line_end(p)
            if it.get("pre_label"):
                lj = src.find(b"#" + it["pre_label"].encode("utf-8"),
                              p, le)
                if lj >= 0:
                    rows.append(
                        f"(lbl {lj + 1} "
                        f"{lj + 1 + len(it['pre_label'].encode('utf-8'))})")
            nj = word_end(p)
            rows.append(f"(flw {p} {nj})")
            ev = it["invocation"]["event"]
            ename = (ev[-1] if ev else "").encode("utf-8")
            ej = src.find(ename, nj, le) if ename else -1
            if ej >= 0:
                rows.append(f"(call {ej} {ej + len(ename)})")
                emit_args(ej + len(ename))
            for c in it["continuations"]:
                emit_cont(c)
    return rows


def parse_row_text(txt):
    """kAst's `out` → the same `(kind i j …)` row list."""
    return [f"({m.group(1)}{m.group(2)})"
            for m in re.finditer(r"\(([a-z]+)((?: [-\w]+)*)\)", txt)]


def _target_row(tid):
    for t in _load("assembly.json")["targets"]:
        if t["id"] == tid:
            return t
    return None


def _c99_row():
    return _target_row("c99")


def _docker_probe(images):
    """None = docker unavailable; set of present images otherwise."""
    try:
        r = subprocess.run(["docker", "info"], capture_output=True,
                           timeout=20)
        if r.returncode != 0:
            return None
        have = set()
        for img in images:
            r = subprocess.run(["docker", "image", "inspect", img],
                               capture_output=True, timeout=30)
            if r.returncode == 0:
                have.add(img)
        return have
    except (OSError, subprocess.TimeoutExpired):
        return None


def _docker_path(p):
    return p.replace("\\", "/")


def _ccv_run(ccv_tc, src_name, asm_name, exe_name, lib_name):
    """Run the declared compcert row end-to-end on a file already in
    BUILD/: ccomp -S -> i386 gcc link (+libcompcert.a) -> execute.
    Returns (stage, detail, exit): stage 'ok' carries the run's exit
    code; 'compile'/'link' carry the refusing step's stderr."""
    argv_c = [a.format(src=src_name, asm=asm_name, exe=exe_name)
              for a in ccv_tc["compile"]["argv"]]
    r1 = subprocess.run(
        ["docker", "run", "--rm", "-v", f"{_docker_path(BUILD)}:/src",
         "-w", "/src", ccv_tc["compile"]["image"], *argv_c],
        capture_output=True, text=True, timeout=180)
    if r1.returncode != 0:
        return ("compile", (r1.stderr or r1.stdout).strip()[:160], None)
    argv_l = [a.format(asm=asm_name, exe=exe_name, lib=lib_name)
              for a in ccv_tc["link_run"]["argv"]]
    r2 = subprocess.run(
        ["docker", "run", "--rm", "-v", f"{_docker_path(BUILD)}:/src",
         "-w", "/src", ccv_tc["link_run"]["image"], *argv_l],
        capture_output=True, text=True, timeout=120)
    if r2.returncode != 0:
        return ("link", r2.stderr.strip()[:160], None)
    r3 = subprocess.run(
        ["docker", "run", "--rm", "-v", f"{_docker_path(BUILD)}:/src",
         "-w", "/src", ccv_tc["link_run"]["image"],
         "sh", "-c", f"./{exe_name}"],
        capture_output=True, timeout=60)
    return ("ok", "", r3.returncode)


def gate():
    npass = nfail = nskip = 0

    def ok(name, detail=""):
        nonlocal npass
        npass += 1
        print(f"  pass  {name}" + (f"  ({detail})" if detail else ""))

    def bad(name, detail):
        nonlocal nfail
        nfail += 1
        print(f"  FAIL  {name}  ({detail})")

    def skip(name, detail):
        nonlocal nskip
        nskip += 1
        print(f"  skip  {name}  ({detail})")

    cc = _clang()
    if cc is None:
        bad("build", "no clang found")
        print(f"host2.check: {npass} pass, {nfail} fail, {nskip} skip")
        return 1
    os.makedirs(BUILD, exist_ok=True)

    target = _c99_row()
    if target is None:
        bad("specs", "assembly.json has no c99 target row")
        return 1
    tc = target["toolchain"]

    # compcert target row: images are declared data; presence is
    # probed once and cached — missing provider skips, never fakes.
    ccv_row = _target_row("compcert")
    ccv_tc = (ccv_row or {}).get("toolchain") if (
        ccv_row and ccv_row.get("realized")) else None
    ccv_have = False
    ccv_lib = None
    if ccv_tc:
        imgs = [ccv_tc["compile"]["image"], ccv_tc["link_run"]["image"]]
        have = _docker_probe(imgs)
        ccv_have = have is not None and all(i in have for i in imgs)
    if ccv_have:
        # CompCert's i386 runtime helpers (64-bit div/mod) — pulled
        # from the declared image path once, cached in build/.
        lspec = ccv_tc["link_run"].get("lib_from", "")
        lname = ccv_tc["link_run"].get("lib", "libcompcert.a")
        ccv_lib = os.path.join(BUILD, lname)
        if not os.path.isfile(ccv_lib) and lspec:
            img, _, lpath = lspec.rpartition(":")
            subprocess.run(
                ["docker", "run", "--rm",
                 "-v", f"{_docker_path(BUILD)}:/src", "-w", "/src",
                 img, "sh", "-c", f"cp {lpath} /src/{lname}"],
                capture_output=True, timeout=120)
        if not os.path.isfile(ccv_lib):
            ccv_lib = None

    # ---- the suite walk: every leaf folder holding cases.json is a
    # case dir.  tests/ is two levels (<GGG>_<group>/<NNN>_<leaf>/);
    # benches/ and ported/ are one (<NNN>_<name>/ or <name>/). ----
    case_dirs = []   # (display_key, leaf_dir, cases_path)
    layout_bad = []
    for tree in TREES:
        tdir = os.path.join(SPECS, tree)
        if not os.path.isdir(tdir):
            continue
        numbered = tree != "ported"
        for a in sorted(os.listdir(tdir)):
            d1 = os.path.join(tdir, a)
            if not os.path.isdir(d1):
                continue
            if numbered and not NUM_RE.match(a):
                layout_bad.append(f"{tree}/{a} not NNN_name")
            if os.path.isfile(os.path.join(d1, "cases.json")):
                case_dirs.append((f"{tree}/{a}", d1,
                                  os.path.join(d1, "cases.json")))
                continue
            for b in sorted(os.listdir(d1)):
                d2 = os.path.join(d1, b)
                if not os.path.isdir(d2):
                    continue
                if numbered and not NUM_RE.match(b):
                    layout_bad.append(f"{tree}/{a}/{b} not NNN_name")
                if not os.path.isfile(os.path.join(d2, "cases.json")):
                    layout_bad.append(f"{tree}/{a}/{b} has no cases.json")
                    continue
                case_dirs.append((f"{tree}/{a}/{b}", d2,
                                  os.path.join(d2, "cases.json")))
    if layout_bad:
        for m in layout_bad:
            bad("layout", m)
    else:
        ok("layout", f"{len(case_dirs)} case dirs, NNN_name enforced")

    # ---- build legs: both witnesses compile clean ----
    built = True
    for tag, src, out in (("krun", SRC_KRUN, KRUN),
                          ("korufe", SRC_KORUFE, KORUFE)):
        c = subprocess.run(
            [cc, "-std=c99", "-Wall", "-Wextra", "-Werror", "-O1",
             *src, "-o", out],
            capture_output=True, text=True)
        if c.returncode != 0:
            bad(f"build.{tag}", c.stderr.strip()[:300])
            built = False
        else:
            ok(f"build.{tag}", "clang -std=c99 -Werror")
    if not built:
        print(f"host2.check: {npass} pass, {nfail} fail, {nskip} skip")
        return 1

    # ---- every row in every leaf's cases.json, plus the convention
    # checks: surface rows carry file:"input.k" that exists; wire rows
    # carry claim and no file ----
    all_rows = []   # (dkey, rowname, row, cases_path, leaf_dir)
    for dkey, leaf_dir, cpath in case_dirs:
        with open(cpath, encoding="utf-8") as f:
            leaf_cases = json.load(f)["cases"]
        leaf = os.path.basename(leaf_dir)
        for rowname in sorted(leaf_cases):
            row = leaf_cases[rowname]
            disp = dkey if rowname == leaf else f"{dkey}/{rowname}"
            if row.get("claim"):
                if row.get("file"):
                    bad(f"{disp}.layout",
                        "wire row must not carry a surface file")
                    continue
            else:
                fref = row.get("file")
                if fref != "input.k":
                    bad(f"{disp}.layout",
                        f"surface row file must be input.k, got {fref!r}")
                    continue
                if not os.path.isfile(os.path.join(leaf_dir, fref)):
                    bad(f"{disp}.layout",
                        f"{fref} missing in {dkey}")
                    continue
            all_rows.append((disp, rowname, row, cpath, leaf_dir))

    # ---- koruc authority: every surface file must pass the real
    # frontend — path lives in realizations.json (declared data) ----
    koruc = None
    for row in _load("realizations.json")["rows"]:
        if row["id"] == "koru/authority":
            mech = row.get("arm", {}).get("mechanism")
            if mech:
                # the bare name may shadow a platform binary (an ELF
                # 'koruc' beside 'koruc.exe') — prefer the host's
                # executable spelling, then probe that it runs
                cands = [mech + ".exe", mech] if os.name == "nt" \
                    else [mech]
                for cand in cands:
                    if not os.path.exists(cand):
                        continue
                    try:
                        p = subprocess.run([cand, "--version"],
                                           capture_output=True,
                                           timeout=20)
                        if p.returncode in (0, 2):
                            koruc = cand
                            break
                    except (OSError, subprocess.TimeoutExpired):
                        continue
            break
    for src in sorted({os.path.join(d, "input.k")
                       for _, _, r, _, d in all_rows
                       if not r.get("claim")}):
        rel = os.path.relpath(src, SPECS)
        if koruc:
            r = subprocess.run([koruc, "-c", src],
                               capture_output=True, text=True)
            if r.returncode == 0:
                ok(f"{rel}.authority", "koruc -c")
            else:
                bad(f"{rel}.authority",
                    r.stderr.strip()[:160] or r.stdout.strip()[:160])
        else:
            skip(f"{rel}.authority", "koruc toolchain not on this machine")

    # ---- per-case legs: parse -> lower -> claim ----
    def run_case(dkey, rowname, row, cases_path, leaf_dir):
        bkey = f"{dkey}-{rowname}".replace("/", "-") \
            if rowname != os.path.basename(dkey) \
            else dkey.replace("/", "-")
        ast = os.path.join(BUILD, f"{bkey}.ast.json")
        claim = os.path.join(BUILD, f"{bkey}.claim")

        if row.get("claim"):
            # wire row — the claim is generated data; no .k surface
            with open(claim, "w", encoding="utf-8") as f:
                f.write(row["claim"])
            ok(f"{dkey}.wire", "claim declared (residual-arm axis)")
        else:
            src = os.path.join(leaf_dir, row["file"])
            r = subprocess.run([KORUFE, src], capture_output=True, text=True)
            if r.returncode == 0:
                with open(ast, "w", encoding="utf-8") as f:
                    f.write(r.stdout)
                ok(f"{dkey}.parse", "ast.json")
            else:
                bad(f"{dkey}.parse", r.stderr.strip()[:160])
                return None

            r = subprocess.run([KORUFE, "--lower", ast, cases_path,
                                rowname], capture_output=True, text=True)
            if r.returncode == 0 and r.stdout.startswith("[flow-eval]"):
                with open(claim, "w", encoding="utf-8") as f:
                    f.write(r.stdout)
                ok(f"{dkey}.lower", "claim")
            else:
                bad(f"{dkey}.lower",
                    f"exit={r.returncode} {r.stderr.strip()[:160]}")
                return None

        forged = row.get("forged")
        r = subprocess.run([KRUN, claim], capture_output=True, text=True)
        if forged:
            if r.returncode == 4 and r.stderr.startswith("drift:"):
                ok(f"{dkey}.claim", "forged rejected with drift")
            else:
                bad(f"{dkey}.claim",
                    f"forged not caught: exit={r.returncode} "
                    f"{r.stdout.strip()[:120]}")
        else:
            if r.returncode == 0 and r.stdout.startswith("ok "):
                ok(f"{dkey}.claim", r.stdout.strip()[:80])
            else:
                bad(f"{dkey}.claim",
                    f"exit={r.returncode} out={r.stdout.strip()[:120]} "
                    f"err={r.stderr.strip()[:120]}")
        return claim

    kemit_claim = None
    args_progs = {}   # leaf_dir -> gen name for emit_prog rows
                      # marked emit_args — their sibling rows are
                      # the compiled binary's inputs via the
                      # `krun --args` wire
    built = {}   # (dkey,rowname) -> claim path
    for dkey, rowname, row, cpath, leaf_dir in all_rows:
        claim = run_case(dkey, rowname, row, cpath, leaf_dir)
        if claim:
            built[(dkey, rowname)] = (claim, row)
            if row.get("emit_prog"):
                if row.get("emit_args"):
                    args_progs[leaf_dir] = row.get("gen")
                else:
                    kemit_claim = claim

    # ---- FlowCheck witness leg: the AUTHORITY's mechanized
    # semantics (w:/src/koru FlowKernel via FlowCheck) re-decides
    # every emitted claim — krun agreeing with it on the same wire
    # is the eval.c-is-runK witness.  Forged rows go to the --forged
    # corpus (all must REJECT).  Paths+toolchain live in
    # realizations.json; missing pieces skip, never fail. ----
    fc = None
    for row in _load("realizations.json")["rows"]:
        if row["id"] == "koru/flowcheck":
            mech = row.get("arm", {}).get("mechanism")
            if (mech and os.path.exists(mech["kernel"])
                    and os.path.exists(mech["checker"])
                    and shutil.which("elan")):
                fc = mech
            break
    if fc is None:
        skip("witness.flowcheck",
             "koru flowcheck toolchain not on this machine")
    else:
        odir = os.path.join(BUILD, "flowcheck-oleans")
        os.makedirs(odir, exist_ok=True)
        k_olean = os.path.join(odir, "FlowKernel.olean")
        built_kernel = (os.path.exists(k_olean)
                        and os.path.getmtime(k_olean)
                        >= os.path.getmtime(fc["kernel"]))
        fc_dir = os.path.dirname(fc["kernel"])
        if not built_kernel:
            r = subprocess.run(
                ["elan", "run", fc["toolchain"], "lean",
                 "-o", k_olean, fc["kernel"]],
                capture_output=True, text=True, cwd=fc_dir)
            built_kernel = r.returncode == 0
            if not built_kernel:
                bad("witness.flowcheck.build",
                    f"FlowKernel.olean: {r.stderr.strip()[:160]}")
        if built_kernel:
            env = {**os.environ, "LEAN_PATH": odir}
            conf, forg, ext = set(), set(), 0
            for claim, row in built.values():
                line = open(claim, encoding="utf-8").read().strip()
                # extension builtins (`len`, `intToString`) are OUR
                # axis — the authority's kernel cannot decide a
                # claim that mentions them, so they leave the
                # conformance corpus by name rather than failing it
                if "(builtin len" in line or \
                        "(builtin intToString" in line:
                    ext += 1
                    continue
                (forg if row.get("forged") else conf).add(line)
            if ext:
                ok("witness.extension",
                   f"{ext} claims on extension builtins "
                   f"(len/intToString) — outside FlowKernel's table")
            for tag, lines, extra in (("conformance", conf, []),
                                      ("forged", forg, ["--forged"])):
                if not lines:
                    continue
                cf = os.path.join(BUILD, f"flowcheck-{tag}.corpus")
                with open(cf, "w", encoding="utf-8") as f:
                    f.write("\n".join(sorted(lines)) + "\n")
                r = subprocess.run(
                    ["elan", "run", fc["toolchain"], "lean", "--run",
                     fc["checker"], *extra, cf],
                    capture_output=True, text=True, env=env,
                    cwd=fc_dir)
                tail = (r.stdout.strip().splitlines() or [""])[-1]
                if r.returncode == 0:
                    ok(f"witness.{tag}", tail.strip()[:90])
                else:
                    bad(f"witness.{tag}",
                        f"exit={r.returncode} {tail.strip()[:120]} "
                        f"{r.stderr.strip()[:120]}")

    # ---- emit legs: kemit's claim + --emit against every case claim ----
    if kemit_claim is None:
        bad("emit", "kemit claim not built")
    else:
        for (dkey, rowname), (claim, row) in sorted(built.items()):
            if row.get("emit_prog") or row.get("forged"):
                continue
            want = row.get("emit")
            if want is None:
                continue
            bkey = os.path.splitext(os.path.basename(claim))[0]
            r = subprocess.run([KRUN, kemit_claim, "--emit", claim],
                               capture_output=True, text=True)
            if want == "refuse":
                if r.returncode == 3:
                    ok(f"{dkey}.emit", "outside subset refuses")
                else:
                    bad(f"{dkey}.emit",
                        f"expected refusal, exit={r.returncode} "
                        f"{r.stdout.strip()[:120]}")
                continue
            if r.returncode == 0 and r.stdout.strip() == want:
                ok(f"{dkey}.emit", want[:60])
            else:
                bad(f"{dkey}.emit",
                    f"exit={r.returncode} got={r.stdout.strip()[:80]!r} "
                    f"want={want[:80]!r}")
                continue

            # ---- cc leg: assembly.json toolchain, run, exit DWORD ----
            # expected exit code is the kernel-decided bare int of the
            # case's own claim — observational equivalence, not text
            # scraping of the emitted expr.
            exp = row.get("expect")
            bare = exp.get("bare") if isinstance(exp, dict) else None
            if not (isinstance(bare, dict) and "int" in bare):
                skip(f"{dkey}.cc", "expect is not a bare int")
                continue
            expect = bare["int"] & 0xFFFFFFFF
            csrc = os.path.join(BUILD, f"{bkey}.emit.c")
            cexe = os.path.join(BUILD, f"{bkey}.emit.exe")
            with open(csrc, "w", encoding="utf-8") as f:
                f.write(r.stdout)
            c = subprocess.run([tc["cc"], *tc["flags"], csrc, "-o", cexe],
                               capture_output=True, text=True)
            if c.returncode != 0:
                bad(f"{dkey}.cc", f"{tc['cc']} refused: {c.stderr.strip()[:160]}")
                continue
            run = subprocess.run([cexe], capture_output=True)
            got = run.returncode & 0xFFFFFFFF
            if got == expect:
                ok(f"{dkey}.cc", f"exit {got}")
            else:
                bad(f"{dkey}.cc", f"exit {got} != {expect}")

            # ---- ccv leg: machine-checked CompCert compile ----
            # ccomp -S emits verified i386 asm; a second docker image
            # assembles+links+runs it (unverified witness of the
            # artifact).  Provider/images come from the declared
            # assembly.json compcert row; absence -> skip, never fake.
            if not ccv_have or not ccv_lib:
                skip(f"{dkey}.ccv", "compcert provider/images unavailable")
                continue
            try:
                stage, detail, got3 = _ccv_run(
                    ccv_tc, f"{bkey}.emit.c", f"{bkey}.ccv.s",
                    f"{bkey}.ccv", os.path.basename(ccv_lib))
                if stage == "compile":
                    bad(f"{dkey}.ccv", f"ccomp refused: {detail}")
                elif stage == "link":
                    bad(f"{dkey}.ccv", f"i386 link refused: {detail}")
                # linux i386 exit status is 8-bit: compare masked
                elif (got3 & 0xFF) == (expect & 0xFF):
                    ok(f"{dkey}.ccv", f"ccomp i386 exit {got3 & 0xFF}")
                else:
                    bad(f"{dkey}.ccv",
                        f"exit {got3 & 0xFF} != {expect & 0xFF}")
            except subprocess.TimeoutExpired:
                bad(f"{dkey}.ccv", "docker step timed out")

    # ---- h1 legs: the COMPILED kemit ----
    # specs/gen/kemit.c is ISAR.KoruProgEmit.emitProgC(kEmit) — the
    # koru-spelled compiler as generated C99 (callables, unrolled
    # dispatch, chains — program logic, not an interpreter) plus the
    # declared runtime prelude.  Feeding each claim's quotation
    # (`krun --quote`) to the compiled binary must observe the same
    # emission as `krun kemit.claim --emit` — compiled ≡ interpreted
    # on the whole corpus.  The compiler binary itself also rides
    # the CompCert row: a machine-checked-compiled compiler.
    kemit_c = os.path.join(SPECS, "gen", "kemit.c")
    h1_bin = os.path.join(BUILD,
                          "kemit_h1.exe" if os.name == "nt" else "kemit_h1")
    have_h1 = False
    if not os.path.isfile(kemit_c):
        skip("h1.build", "specs/gen/kemit.c not generated")
    else:
        # gen.stamp: the artifact must be bound to its source — a
        # stale kemit.c (input.k regenerated without re-running the
        # generator, or hand-edited) fails here rather than silently
        # passing on an unfaithful artifact.
        ik_src = os.path.join(SPECS, "tests", "200_emit",
                              "900_kemit", "input.k")
        with open(kemit_c, encoding="utf-8") as f:
            stamp = re.match(r"/\* input\.fnv1a64:(\d+) \*/",
                             f.read(200))
        ik = (open(ik_src, "rb").read().replace(b"\r\n", b"\n")
              if os.path.isfile(ik_src) else b"")
        if stamp and int(stamp.group(1)) == _fnv1a64(ik):
            ok("gen.stamp", "kemit.c bound to 900_kemit/input.k")
        else:
            bad("gen.stamp",
                "kemit.c stamp stale vs 900_kemit/input.k — "
                "regenerate tools/DumpKoruFixtures")
        c = subprocess.run([tc["cc"], *tc["flags"], kemit_c,
                            "-o", h1_bin],
                           capture_output=True, text=True)
        if c.returncode != 0:
            bad("h1.build",
                f"{tc['cc']} refused: {c.stderr.strip()[:160]}")
        else:
            ok("h1.build", "emitProgC(kEmit) via c99 toolchain")
            have_h1 = True

    # the same artifact through the machine-checked backend
    have_h1v = False
    h1v_name = "kemit_h1_ccv"
    if not ccv_have or not ccv_lib:
        skip("h1.ccv", "compcert provider/images unavailable")
    else:
        try:
            shutil.copy(kemit_c, os.path.join(BUILD, "kemit_h1.c"))
            argv_c = [a.format(src="kemit_h1.c", asm="kemit_h1_ccv.s",
                               exe=h1v_name)
                      for a in ccv_tc["compile"]["argv"]]
            r1 = subprocess.run(
                ["docker", "run", "--rm",
                 "-v", f"{_docker_path(BUILD)}:/src", "-w", "/src",
                 ccv_tc["compile"]["image"], *argv_c],
                capture_output=True, text=True, timeout=300)
            if r1.returncode != 0:
                bad("h1.ccv",
                    f"ccomp refused: {(r1.stderr or r1.stdout).strip()[:160]}")
            else:
                argv_l = [a.format(asm="kemit_h1_ccv.s", exe=h1v_name,
                                   lib=os.path.basename(ccv_lib))
                          for a in ccv_tc["link_run"]["argv"]]
                r2 = subprocess.run(
                    ["docker", "run", "--rm",
                     "-v", f"{_docker_path(BUILD)}:/src", "-w", "/src",
                     ccv_tc["link_run"]["image"], *argv_l],
                    capture_output=True, text=True, timeout=120)
                if r2.returncode != 0:
                    bad("h1.ccv",
                        f"i386 link refused: {r2.stderr.strip()[:160]}")
                else:
                    ok("h1.ccv", "emitProgC(kEmit) via ccomp (verified)")
                    have_h1v = True
        except subprocess.TimeoutExpired:
            bad("h1.ccv", "docker step timed out")

    # observational equivalence per row: compiled ≡ interpreted emit
    for (dkey, rowname), (claim, row) in sorted(built.items()):
        if row.get("emit_prog") or row.get("forged"):
            continue
        want = row.get("emit")
        if want is None:
            continue
        if not have_h1:
            skip(f"{dkey}.h1", "kemit binary not built")
        else:
            q = subprocess.run([KRUN, "--quote", claim],
                               capture_output=True, text=True)
            if q.returncode != 0:
                bad(f"{dkey}.h1",
                    f"--quote refused: {q.stderr.strip()[:80]}")
                continue
            rb = subprocess.run([h1_bin], input=q.stdout,
                                capture_output=True, text=True)
            if want == "refuse":
                if rb.returncode == 4:
                    ok(f"{dkey}.h1", "compiled kemit refuses")
                else:
                    bad(f"{dkey}.h1",
                        f"expected refusal, exit={rb.returncode} "
                        f"{rb.stdout.strip()[:60]!r}")
            elif rb.returncode == 0 and rb.stdout.strip() == want:
                ok(f"{dkey}.h1", want[:60])
            else:
                bad(f"{dkey}.h1",
                    f"exit={rb.returncode} "
                    f"got={rb.stdout.strip()[:60]!r}")
            if not have_h1v:
                continue
            try:
                rv = subprocess.run(
                    ["docker", "run", "--rm", "-i",
                     "-v", f"{_docker_path(BUILD)}:/src", "-w", "/src",
                     ccv_tc["link_run"]["image"],
                     "sh", "-c", f"./{h1v_name}"],
                    input=q.stdout, capture_output=True, text=True,
                    timeout=60)
            except subprocess.TimeoutExpired:
                bad(f"{dkey}.h1v", "docker run timed out")
                continue
            if want == "refuse":
                if rv.returncode == 4:
                    ok(f"{dkey}.h1v", "ccomp kemit refuses")
                else:
                    bad(f"{dkey}.h1v",
                        f"expected refusal, exit={rv.returncode} "
                        f"{rv.stdout.strip()[:60]!r}")
            elif rv.returncode == 0 and rv.stdout.strip() == want:
                ok(f"{dkey}.h1v", f"ccomp: {want[:50]}")
            else:
                bad(f"{dkey}.h1v",
                    f"exit={rv.returncode} "
                    f"got={rv.stdout.strip()[:60]!r}")

            # ---- h2 leg: H1' -> H2' — the COMPILED compiler's own
            # output rides the checked backend again: the ccomp-built
            # kemit's emitted C -> ccomp -S -> i386 link+run -> exit
            # byte == expect's low byte.  Two machine-checked-compiled
            # stages in sequence: a verified-compiled compiler
            # producing verified-compiled artifacts on changed input.
            if want == "refuse" or rv.returncode != 0:
                continue
            exp2 = row.get("expect")
            bare2 = exp2.get("bare") if isinstance(exp2, dict) else None
            if not (isinstance(bare2, dict) and "int" in bare2):
                skip(f"{dkey}.h2", "expect is not a bare int")
                continue
            h2key = os.path.splitext(os.path.basename(claim))[0]
            with open(os.path.join(BUILD, f"{h2key}.h2.c"), "w",
                      encoding="utf-8") as f:
                f.write(rv.stdout)
            try:
                stage, detail, got2 = _ccv_run(
                    ccv_tc, f"{h2key}.h2.c", f"{h2key}.h2.s",
                    f"{h2key}.h2", os.path.basename(ccv_lib))
                if stage == "compile":
                    bad(f"{dkey}.h2", f"ccomp refused: {detail}")
                elif stage == "link":
                    bad(f"{dkey}.h2", f"i386 link refused: {detail}")
                elif (got2 & 0xFF) == (bare2["int"] & 0xFF):
                    ok(f"{dkey}.h2",
                       f"ccomp-kemit->ccomp i386 exit {got2 & 0xFF}")
                else:
                    bad(f"{dkey}.h2",
                        f"exit {got2 & 0xFF} != {bare2['int'] & 0xFF}")
            except subprocess.TimeoutExpired:
                bad(f"{dkey}.h2", "docker step timed out")

    # ---- compiled emit_args programs: kl/ks/… legs ----
    # specs/gen/<g>.c is ISAR.KoruProgEmit.emitProgC(<prog>) — a
    # koru-spelled frontend component as C99 (ordered bare dispatch,
    # invoke tails; cond/index/len/intToString/++ only — no new
    # builtins).  Each sibling row in the program's leaf feeds its
    # entry args through `krun --args` to the compiled binary, which
    # must re-decide the same text the interpreted claim decided —
    # compiled ≡ interpreted for data-arg programs.  `code` is the
    # leg suffix: first two letters of the gen name (klex→kl,
    # ksexp→ks).
    for aleaf, gname in args_progs.items():
        if not gname:
            bad("emit_args.gen",
                f"emit_args row in {os.path.basename(aleaf)} "
                "lacks a gen name")
            continue
        code = gname[:2]
        gsrc = os.path.join(SPECS, "gen", gname + ".c")
        gbin = os.path.join(BUILD, f"{gname}_{code}"
                            + (".exe" if os.name == "nt" else ""))
        have_g = False
        if not os.path.isfile(gsrc):
            skip(f"{code}.build", f"specs/gen/{gname}.c not generated")
        else:
            ik_src = os.path.join(aleaf, "input.k")
            with open(gsrc, encoding="utf-8") as f:
                stamp = re.match(r"/\* input\.fnv1a64:(\d+) \*/",
                                 f.read(200))
            ik = (open(ik_src, "rb").read().replace(b"\r\n", b"\n")
                  if os.path.isfile(ik_src) else b"")
            leafname = os.path.basename(aleaf)
            if stamp and int(stamp.group(1)) == _fnv1a64(ik):
                ok(f"gen.stamp.{gname}",
                   f"{gname}.c bound to {leafname}/input.k")
            else:
                bad(f"gen.stamp.{gname}",
                    f"{gname}.c stamp stale vs {leafname}/input.k — "
                    "regenerate tools/DumpKoruFixtures")
            c = subprocess.run([tc["cc"], *tc["flags"], gsrc,
                                "-o", gbin],
                               capture_output=True, text=True)
            if c.returncode != 0:
                bad(f"{code}.build",
                    f"{tc['cc']} refused: {c.stderr.strip()[:160]}")
            else:
                ok(f"{code}.build",
                   f"emitProgC({gname}) via c99 toolchain")
                have_g = True

        have_gv = False
        gv_name = f"{gname}_{code}_ccv"
        if not ccv_have or not ccv_lib:
            skip(f"{code}.ccv", "compcert provider/images unavailable")
        elif not os.path.isfile(gsrc):
            skip(f"{code}.ccv", f"specs/gen/{gname}.c not generated")
        else:
            try:
                shutil.copy(gsrc, os.path.join(BUILD,
                                               f"{gname}_{code}.c"))
                argv_c = [a.format(src=f"{gname}_{code}.c",
                                   asm=f"{gv_name}.s", exe=gv_name)
                          for a in ccv_tc["compile"]["argv"]]
                r1 = subprocess.run(
                    ["docker", "run", "--rm",
                     "-v", f"{_docker_path(BUILD)}:/src", "-w", "/src",
                     ccv_tc["compile"]["image"], *argv_c],
                    capture_output=True, text=True, timeout=300)
                if r1.returncode != 0:
                    bad(f"{code}.ccv",
                        f"ccomp refused: "
                        f"{(r1.stderr or r1.stdout).strip()[:160]}")
                else:
                    argv_l = [a.format(asm=f"{gv_name}.s", exe=gv_name,
                                       lib=os.path.basename(ccv_lib))
                              for a in ccv_tc["link_run"]["argv"]]
                    r2 = subprocess.run(
                        ["docker", "run", "--rm",
                         "-v", f"{_docker_path(BUILD)}:/src",
                         "-w", "/src", ccv_tc["link_run"]["image"],
                         *argv_l],
                        capture_output=True, text=True, timeout=120)
                    if r2.returncode != 0:
                        bad(f"{code}.ccv",
                            f"i386 link refused: "
                            f"{r2.stderr.strip()[:160]}")
                    else:
                        ok(f"{code}.ccv",
                           f"emitProgC({gname}) via ccomp (verified)")
                        have_gv = True
            except subprocess.TimeoutExpired:
                bad(f"{code}.ccv", "docker step timed out")

        # per input row: --args cell -> compiled program -> text;
        # a bare str decides and prints raw, refuse is exit 4 —
        # compare byte-exact (trailing space is observed too)
        for dkey, rowname, row, cpath, leaf_dir in all_rows:
            if leaf_dir != aleaf or row.get("emit_prog"):
                continue
            cl = built.get((dkey, rowname))
            if cl is None:
                continue
            claim = cl[0]
            exp = row.get("expect")
            bare = exp.get("bare") if isinstance(exp, dict) else None
            want = bare["str"] if (isinstance(bare, dict)
                                   and "str" in bare) else "refuse"
            q = subprocess.run([KRUN, "--args", claim],
                               capture_output=True, text=True)
            if q.returncode != 0:
                bad(f"{dkey}.{code}",
                    f"--args refused: {q.stderr.strip()[:80]}")
                continue
            if have_g:
                rb = subprocess.run([gbin], input=q.stdout,
                                    capture_output=True, text=True)
                got = (rb.stdout[:-1]
                       if rb.stdout.endswith("\n") else rb.stdout)
                if want == "refuse":
                    if rb.returncode == 4:
                        ok(f"{dkey}.{code}",
                           f"compiled {gname} refuses")
                    else:
                        bad(f"{dkey}.{code}",
                            f"expected refusal, exit={rb.returncode}")
                elif rb.returncode == 0 and got == want:
                    ok(f"{dkey}.{code}", want[:60])
                else:
                    bad(f"{dkey}.{code}",
                        f"exit={rb.returncode} "
                        f"got={got[:60]!r}")
            else:
                skip(f"{dkey}.{code}", f"{gname} binary not built")

            # ---- the AST race: `koruc --ast-json` normalized to the
            # same flat row text must equal what the koru-spelled
            # parser decided (and the compiled legs re-decided).
            # Refusal parity: a source the authority refuses must
            # carry a `(bad i c)` row on our side.
            if row.get("race"):
                rt = f"{dkey}.{code}r"
                if not koruc:
                    skip(rt, "koruc toolchain not on this machine")
                else:
                    with open(os.path.join(BUILD, "race_in.k"), "w",
                              encoding="utf-8") as f:
                        f.write(row.get("src", ""))
                    ra = subprocess.run(
                        [koruc, "--ast-json",
                         os.path.join(BUILD, "race_in.k")],
                        capture_output=True, text=True)
                    if ra.returncode != 0:
                        if "(bad " in want:
                            ok(rt, "authority refuses; (bad) parity")
                        else:
                            bad(rt, "koruc refused but rows lack "
                                f"(bad): {ra.stderr.strip()[:100]}")
                    else:
                        try:
                            ast = json.loads(ra.stdout)
                        except json.JSONDecodeError as e:
                            bad(rt, f"ast-json unreadable: {e}")
                        else:
                            mine = parse_row_text(want)
                            theirs = ast_norm_rows(
                                row.get("src", ""), ast)
                            if mine == theirs:
                                ok(rt, f"ast race: {len(mine)} "
                                       "rows agree")
                            else:
                                diff = next(
                                    (i for i, (a, b) in
                                     enumerate(zip(mine, theirs))
                                     if a != b),
                                    min(len(mine), len(theirs)))
                                bad(rt,
                                    f"row {diff}: mine="
                                    f"{mine[diff] if diff < len(mine) else '∅'} "
                                    f"theirs="
                                    f"{theirs[diff] if diff < len(theirs) else '∅'}")

            if not have_gv:
                continue
            try:
                rv = subprocess.run(
                    ["docker", "run", "--rm", "-i",
                     "-v", f"{_docker_path(BUILD)}:/src", "-w", "/src",
                     ccv_tc["link_run"]["image"],
                     "sh", "-c", f"./{gv_name}"],
                    input=q.stdout, capture_output=True, text=True,
                    timeout=60)
            except subprocess.TimeoutExpired:
                bad(f"{dkey}.{code}v", "docker run timed out")
                continue
            gotv = (rv.stdout[:-1]
                    if rv.stdout.endswith("\n") else rv.stdout)
            if want == "refuse":
                if rv.returncode == 4:
                    ok(f"{dkey}.{code}v", f"ccomp {gname} refuses")
                else:
                    bad(f"{dkey}.{code}v",
                        f"expected refusal, exit={rv.returncode}")
            elif rv.returncode == 0 and gotv == want:
                ok(f"{dkey}.{code}v", f"ccomp: {want[:50]}")
            else:
                bad(f"{dkey}.{code}v",
                    f"exit={rv.returncode} got={gotv[:60]!r}")

    # ---- wide AST race: every input.k in the corpus goes through
    # the compiled kast binary and `koruc --ast-json`, both
    # normalized to the flat row wire, refusal parity included.
    # The race binary gets an enlarged stack — emitProgC compiles
    # each invoke to a C call (no tail-call flattening), so |> chains
    # and per-arm dispatch are mutual recursion: the 14KB kast
    # source overflows the 1MB default.  Host-resource axis, not a
    # parse limit; the fuel argument stays well above decidedness. ----
    kw_leaf = next((a for a, g in args_progs.items() if g == "kast"),
                   None)
    if not koruc:
        skip("kw.build", "koruc toolchain not on this machine")
    elif kw_leaf is None:
        skip("kw.build", "no kast emit_args row")
    else:
        kw_src = os.path.join(SPECS, "gen", "kast.c")
        kw_bin = os.path.join(BUILD, "kast_kw"
                              + (".exe" if os.name == "nt" else ""))
        kw_flags = list(tc["flags"])
        if os.name == "nt":
            kw_flags.append("-Wl,/STACK:67108864")
        c = subprocess.run([tc["cc"], *kw_flags, kw_src, "-o", kw_bin],
                           capture_output=True, text=True)
        if c.returncode != 0:
            bad("kw.build",
                f"{tc['cc']} refused: {c.stderr.strip()[:160]}")
        else:
            ok("kw.build", "emitProgC(kast) wide-stack build")
            for ik in sorted(glob.glob(
                    os.path.join(SPECS, "tests", "**", "input.k"),
                    recursive=True)):
                rel = os.path.relpath(
                    ik, os.path.join(SPECS, "tests"))
                tag = "kw." + rel.replace("\\", "/").replace(
                    "/", ".").replace("input.k", "").rstrip(".")
                raw = open(ik, "rb").read()
                src_text = raw.decode("utf-8")
                ra = subprocess.run(
                    [koruc, "--ast-json", os.path.abspath(ik)],
                    capture_output=True, text=True)
                auth_bad = ra.returncode != 0
                theirs = ([] if auth_bad else ast_norm_rows(
                    src_text, json.loads(ra.stdout)))
                cell = ("(cell (chars (arr "
                        + " ".join(f"(int {b})" for b in raw) + ")))")
                rm = subprocess.run([kw_bin, "4000000"], input=cell,
                                    capture_output=True, text=True,
                                    timeout=300)
                mine = parse_row_text(rm.stdout)
                mine_bad = any(r.startswith("(bad") for r in mine)
                if auth_bad != mine_bad:
                    bad(tag, f"refusal mismatch auth_bad={auth_bad}")
                elif mine != theirs:
                    i = next((k for k, (a, b)
                              in enumerate(zip(mine, theirs)) if a != b),
                             min(len(mine), len(theirs)))
                    bad(tag, f"first diff @{i}: "
                             f"{mine[i:i + 1]} vs {theirs[i:i + 1]}")
                elif auth_bad:
                    ok(tag, "refusal parity")
                else:
                    ok(tag, f"{len(mine)} rows agree")

    # ---- wide JSON race: the SAME corpus through `korufe
    # --ast-json` vs `koruc --ast-json` — the readable view is the
    # authority/interop document, so the C lane must mirror it
    # exactly (modulo the path-dependent location.file).  This is a
    # second, independent evidence boundary to the row race: rows
    # prove the koru-spelled parser, JSON proves the C frontend. ----
    if not koruc:
        skip("kwj", "koruc toolchain not on this machine")
    else:
        for ik in sorted(glob.glob(
                os.path.join(SPECS, "tests", "**", "input.k"),
                recursive=True)):
            rel = os.path.relpath(ik, os.path.join(SPECS, "tests"))
            tag = "kwj." + rel.replace("\\", "/").replace(
                "/", ".").replace("input.k", "").rstrip(".")
            ra = subprocess.run(
                [koruc, "--ast-json", os.path.abspath(ik)],
                capture_output=True, text=True)
            rb = subprocess.run([KORUFE, "--ast-json", ik],
                                capture_output=True, text=True)
            auth_bad, fe_bad = ra.returncode != 0, rb.returncode != 0
            if auth_bad != fe_bad:
                bad(tag, f"refusal mismatch auth={auth_bad} "
                         f"fe={fe_bad} {rb.stderr.strip()[:80]}")
            elif auth_bad:
                ok(tag, "refusal parity")
            else:
                try:
                    da = ast_view_norm(json.loads(ra.stdout))
                    db = ast_view_norm(json.loads(rb.stdout))
                except Exception as e:
                    bad(tag, f"view not JSON: {e}")
                    continue
                r = ast_view_diff(da, db)
                if r is None:
                    ok(tag, "ast-json agree")
                else:
                    bad(tag, f"first diff @{r[0]}: "
                             f"{r[1]!r} vs {r[2]!r}"[:200])

    # ---- canon race: `korufe --ast-canon` vs `koruc --ast-canon`
    # on the same corpus — the LOSSLESS document (retbind, jump
    # args, expression trees; trivia-stripped so locations never
    # figure).  Deep-equal with NO normalization: this is the full-
    # shape boundary — the same document the typed-koru lane's
    # reifier should target, rows→trees being a data transform. ----
    if not koruc:
        skip("kwc", "koruc toolchain not on this machine")
    else:
        for ik in sorted(glob.glob(
                os.path.join(SPECS, "tests", "**", "input.k"),
                recursive=True)):
            rel = os.path.relpath(ik, os.path.join(SPECS, "tests"))
            tag = "kwc." + rel.replace("\\", "/").replace(
                "/", ".").replace("input.k", "").rstrip(".")
            ra = subprocess.run(
                [koruc, "--ast-canon", os.path.abspath(ik)],
                capture_output=True, text=True)
            rb = subprocess.run([KORUFE, "--ast-canon", ik],
                                capture_output=True, text=True)
            auth_bad, fe_bad = ra.returncode != 0, rb.returncode != 0
            if auth_bad != fe_bad:
                bad(tag, f"refusal mismatch auth={auth_bad} "
                         f"fe={fe_bad} {rb.stderr.strip()[:80]}")
            elif auth_bad:
                ok(tag, "refusal parity")
            else:
                try:
                    da = json.loads(ra.stdout)
                    db = json.loads(rb.stdout)
                except Exception as e:
                    bad(tag, f"canon not JSON: {e}")
                    continue
                r = ast_view_diff(da, db)
                if r is None:
                    ok(tag, "ast-canon agree")
                else:
                    bad(tag, f"first diff @{r[0]}: "
                             f"{r[1]!r} vs {r[2]!r}"[:200])

    # ---- refusal probes: the frontend refuses by default, and the
    # same surfaces koruc refuses refuse here (PARSE003/005 parity,
    # retired glyphs, declared-contract checks) ----
    probes = [
        ("malformed", "parse", "tor main {\n", "unterminated decl refuses"),
        ("unknown-item", "parse", "frobulate x\n", "unknown item refuses"),
        ("impl-ctor", "parse", "tor s {}\n| go\ns => go\n",
         "name => b impl refuses (subset axis)"),
        ("residual-spaced", "parse",
         "tor main {}\nmain = tick()\n| * -> 9\n\ntick -> 5\n",
         "'| *' retired deref spelling refuses"),
        ("residual-bare", "parse",
         "tor main {}\nmain = tick()\n|* -> 9\n\ntick -> 5\n",
         "'|* ->' bare residual produce refuses (metatype axis)"),
        ("redundant-pun", "parse", "tor main {}\nmain -> f(x: x)\n",
         "'x: x' redundant explicit label refuses (PARSE005 parity)"),
        ("one-variant", "parse", "tor t {}\n| go i64\n",
         "single-branch union refuses (PARSE003 parity)"),
        ("when-call", "parse",
         "tor main {}\nmain = tick()\n| go when(1) -> 1\n\ntick -> 5\n",
         "'when(' call-shaped guard refuses"),
        ("decl-param", "lower",
         "tor t {a: i64}\nt -> a\n\nmain = t(b: 1)\n| ok -> 1\n",
         "unknown param on declared tor refuses (PARSE006 parity)"),
        ("decl-branch", "lower",
         "tor t {}\n| go i64\n| stop\n\nmain = t()\n| nope -> 1\n",
         "undeclared branch arm refuses (KORU021 parity)"),
        ("no-such-case", "row", None, "missing case row refuses"),
    ]
    for tag, kind, text, desc in probes:
        if kind == "row":
            r = subprocess.run(
                [KORUFE, "--lower",
                 os.path.join(BUILD,
                              "tests-200_emit-000_accept_int.ast.json"),
                 os.path.join(SPECS, "tests", "200_emit",
                              "000_accept_int", "cases.json"), "nope"],
                capture_output=True, text=True)
        else:
            with tempfile.NamedTemporaryFile(
                    "w", suffix=".k", delete=False) as f:
                f.write(text)
                tmpk = f.name
            try:
                r = subprocess.run([KORUFE, tmpk],
                                   capture_output=True, text=True)
                if kind == "lower" and r.returncode == 0:
                    # parse must succeed; the declared-contract refusal
                    # lives in --lower against a minimal case row
                    astf = tmpk + ".ast.json"
                    with open(astf, "w", encoding="utf-8") as f:
                        f.write(r.stdout)
                    rowf = tmpk + ".cases.json"
                    with open(rowf, "w", encoding="utf-8") as f:
                        json.dump({"cases": {"probe": {
                            "entry": "main", "fuel": 64, "args": {},
                            "expect": "refuse", "emit": "refuse"}}}, f)
                    r = subprocess.run(
                        [KORUFE, "--lower", astf, rowf, "probe"],
                        capture_output=True, text=True)
            finally:
                os.unlink(tmpk)
        if r.returncode == 2 and "refuse" in r.stderr:
            ok(f"refuse.{tag}", desc)
        else:
            bad(f"refuse.{tag}",
                f"exit={r.returncode} out={r.stdout.strip()[:100]} "
                f"err={r.stderr.strip()[:100]}")

    print(f"host2.check: {npass} pass, {nfail} fail, {nskip} skip")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(gate())
