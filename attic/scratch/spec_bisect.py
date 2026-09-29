"""Bisect spec_term cost: small spec first, then scale up."""
import os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "host"))
sys.path.insert(0, os.path.dirname(__file__))
from spec_proto import (json_to_term, str_term, query_src, SPECGET, EQSTR,
                        EMIT, PATH_OF, str_src, church_src, _appn, tsize)
from lambda_dialect import parse, bracket_abstract0
from graph_runtime import reduce_tree_lo


def run(label, t, fuel=2_000_000_000):
    t0 = time.time()
    nf, steps, alloc = reduce_tree_lo(t, fuel)
    dt = time.time() - t0
    print(f"{label}: {steps} steps alloc={alloc} {dt:.1f}s")
    if dt > 60:
        print(f"nf={nf}")
    return nf


def compile_src(src):
    return bracket_abstract0(parse(src))


def main():
    # --- eqStr alone: "name" vs "name", "name" vs "path" ----------
    eq = compile_src(EQSTR)
    for a, b, bound in [("name", "name", 16), ("name", "path", 16),
                        ("name", "note", 16), ("xdu.x86_64.pe", "xdu.x86_64.pe", 40)]:
        t = _appn(eq, str_term(a), str_term(b),
                  compile_src(church_src(bound)))
        nf = run(f"eqStr {a!r} vs {b!r} (b={bound})", t)
        print(f"   nf={nf}")

    # --- specGet on a 3-pair object --------------------------------
    sg = compile_src(SPECGET.replace("__NB__", church_src(48)))
    obj = {"name": "xdu.x86_64.pe", "path": "native", "isa": "x86_64"}
    OT = json_to_term(obj)
    for key in ("name", "path", "zzz"):
        t = _appn(sg, OT, str_term(key), compile_src(church_src(len(obj))))
        nf = run(f"specGet {key!r} on 3-pair obj", t)
        print(f"   nf={nf}")

    # --- emit on "native" -------------------------------------------
    em = compile_src(EMIT)
    t = _appn(em, str_term("native"), compile_src(church_src(48)))
    nf = run("emit 'native' bound 48", t)
    print(f"   nf={nf}")

    # --- pathOf on a small spec -------------------------------------
    small = {"toolchains": [
        {"name": "xdu.x86_64.pe", "dialect": "xdu.json", "isa": "x86_64",
         "routines": "x86_64.win64.xdu", "target": "pe64", "path": "native",
         "note": "nibble transducer plex -> PE exe (W3)"},
        {"name": "flat", "dialect": "bytecode.postfix", "isa": "x86_64",
         "routines": "x86_64.baremetal.lo", "target": "flat",
         "path": "runtime", "note": "flat binary, no loader"},
    ]}
    ST = json_to_term(small)
    src = query_src(n_top=len(small), n_ent=7, n_arr=2,
                    n_emit=48, n_beq=40, n_bkey=48)
    Q = compile_src(src)
    for name in ("xdu.x86_64.pe", "flat", "nope"):
        t = _appn(Q, ST, str_term(name))
        nf = run(f"pathOf {name!r} on 2-entry spec", t)
        print(f"   nf={nf}")


if __name__ == "__main__":
    main()
