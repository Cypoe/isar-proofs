#!/usr/bin/env python3
"""rel_witness — the bounded basis-term slice of 10c.

The plan's heavy item is a full miniKanren in basis terms; the slice
that proves the claim (rel ops as DERIVED term constructions, not a
privileged host) is UNIFY computed by the same reducer the emitted
kernel runs.

Encoding — the phi.rel term model as Scott data:

    VAR k    = \\v a p. v k       k = 16-ary selector (var id 0-15)
    ATOM n   = \\v a p. a n       n = 16-ary selector (atom val 0-15)
    PAIR l r = \\v a p. p l r

subst = Scott list of PAIR-encoded (k . t) entries; nil = K.
maybe = \\ok no. ok x | \\ok no. no.   unify returns (ok s') | no.

unify is depth-unfolded: U_i expands self-calls to U_{i-1}, bound
once per level via \\self — linear source, not 4^d.  Depth is the
same honesty as the evaluator's fuel: a declared bound, exhaustion
observable.  No Y, no magic recursion — the unfold depth IS the
fuel here.

    python host/rel_witness.py
"""

import sys
from typing import Tuple

from lambda_dialect import bracket, parse
import reduce as _r
from graph_runtime import reduce_tree_cd
import spec_term as _st


# ---------------------------------------------------------------------------
# λ-source encoders — the rel term model as Scott data
# ---------------------------------------------------------------------------

_NIL = "K"                                    # Scott nil
_FAIL = "(K I)"


def _sel(k: int) -> str:
    assert 0 <= k < 16
    return _st._sel_src(k)


def r_var(k: int) -> str:
    return f"(\\v. \\a. \\p. v {_sel(k)})"


def r_atom(n: int) -> str:
    return f"(\\v. \\a. \\p. a {_sel(n)})"


def r_pair(l: str, r: str) -> str:
    return f"(\\v. \\a. \\p. p {l} {r})"


_JUST = "(\\x. \\ok. \\no. ok x)"
_NOTHING = "(\\ok. \\no. no)"


def _lookup(depth: int) -> str:
    """lookup k s -> maybe term — fold with early exit, bounded
    unfold (depth >= subst length)."""
    def body(d: int) -> str:
        if d <= 0:
            return "(\\k. \\s. " + _NOTHING + ")"
        inner = body(d - 1)
        return (
            "(\\k. \\s. s " + _NOTHING +
            " (\\h. \\t. h (\\kk. \\tt. (EQNIB k kk) "
            "(" + _JUST + " tt) (" + inner + " k t))))")
    return body(depth).replace("EQNIB", _st.EQNIB)


def _unify(depth: int) -> str:
    """unify u v s ok no -> (ok s') | no — depth-bounded unfold;
    U_{i-1} bound once per level via \\self (linear source)."""
    def body(d: int) -> str:
        if d <= 0:
            return "(\\u. \\v. \\s. \\ok. \\no. no)"
        inner = body(d - 1)
        core = (
            "u (\\k. (LK k s) (\\b. self b v s ok no) "
            "(ok (CNS (PR k v) s)))"
            " (\\n. v (\\k2. (LK k2 s) (\\b. self u b s ok no) "
            "(ok (CNS (PR k2 u) s)))"
            " (\\m. (EQNIB n m) (ok s) no)"
            " (\\l2. \\r2. no))"
            " (\\l. \\r. v (\\k2. (LK k2 s) "
            "(\\b. self u b s ok no) (ok (CNS (PR k2 u) s)))"
            " (\\m. no)"
            " (\\l2. \\r2. self l l2 s "
            "(\\s2. self r r2 s2 ok no) no))")
        return ("(\\self. \\u. \\v. \\s. \\ok. \\no. " + core +
                ") (" + inner + ")")
    src = body(depth)
    # LK embeds first: the lookup source carries its own EQNIB
    # literals, replaced in the shared pass below.  It has no
    # LK/CNS/PR tokens of its own.
    src = src.replace("LK", "(" + _lookup(6) + ")")
    src = src.replace("CNS", _st._CONSS)
    src = src.replace("PR ", _st._PAIR_SRC + " ")
    src = src.replace("EQNIB", _st.EQNIB)
    return src


# ---------------------------------------------------------------------------
# reduce + decode
# ---------------------------------------------------------------------------

def _cmp(a, b) -> bool:
    """Structural term equality on the T tree."""
    if a.k != b.k:
        return False
    if a.k == _r.K.APP:
        return _cmp(a.l, b.l) and _cmp(a.r, b.r)
    return True


def _run(src: str, fuel: int = 2_000) -> Tuple[_r.T, int]:
    """bracket(parse) -> graph reduce_cd — the same cd fixpoint the
    emitted kernel runs (D/C real; plain reduce() stalls on them).
    fuel is in cd rounds, not LO steps."""
    nf, rounds, _alloc = reduce_tree_cd(bracket(parse(src)), fuel)
    return nf, rounds


def _expect(src: str) -> _r.T:
    return _run(src)[0]


def _query(u_src: str, v_src: str, var_id: int,
           depth: int = 4) -> str:
    """unify u v [] then return the term var_id bound to (or FAIL)."""
    return (
        "(" + _unify(depth) + " " + u_src + " " + v_src + " " + _NIL +
        " (\\sf. ((" + _lookup(6) + " " + _sel(var_id) + " sf) "
        "(\\b. b) " + _FAIL + ")) " + _FAIL + ")")


def main() -> int:
    # witness 1: PAIR(VAR1, ATOM2) = PAIR(ATOM3, VAR4), ask VAR1
    got, steps = _run(_query(r_pair(r_var(1), r_atom(2)),
                             r_pair(r_atom(3), r_var(4)), 1))
    want = _expect(r_atom(3))
    assert _cmp(got, want), "witness1: VAR1 did not bind ATOM3"
    print(f"  unify PAIR(VAR1,ATOM2) PAIR(ATOM3,VAR4) -> "
          f"VAR1:=ATOM3  ({steps} steps)")

    # witness 2: ATOM5 vs ATOM7 -> FAIL marker
    fail_q = ("(" + _unify(4) + " " + r_atom(5) + " " + r_atom(7) +
              " " + _NIL + " (\\s2. s2) " + _FAIL + ")")
    got2, steps2 = _run(fail_q)
    want2 = _expect(_FAIL)
    assert _cmp(got2, want2), "witness2: atom mismatch did not fail"
    print(f"  unify ATOM5 ATOM7 -> fail marker  ({steps2} steps)")

    # witness 3: nested pair-of-pairs, ask VAR2
    got3, steps3 = _run(
        _query(r_pair(r_pair(r_var(0), r_atom(1)), r_var(2)),
               r_pair(r_pair(r_atom(9), r_atom(1)), r_atom(4)), 2))
    want3 = _expect(r_atom(4))
    assert _cmp(got3, want3), "witness3: nested unify drifted"
    print(f"  unify nested pairs -> VAR2:=ATOM4  ({steps3} steps)")

    # witness 4: occurs-adjacent — VAR1 vs PAIR(VAR1, ATOM2):
    # VAR1 free -> binds to the pair (occurs check deferred, honest
    # bound declared in the frag)
    got4, _ = _run(_query(r_var(1),
                          r_pair(r_var(1), r_atom(2)), 1))
    want4 = _expect(r_pair(r_var(1), r_atom(2)))
    assert _cmp(got4, want4), "witness4: free-var bind drifted"
    print("  unify VAR1 PAIR(VAR1,ATOM2) -> VAR1 binds the pair "
          "(no occurs check — declared bound)")

    print("rel_witness: unify on basis terms (var/atom/pair, subst "
          "as data, bounded unfold as fuel): pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
