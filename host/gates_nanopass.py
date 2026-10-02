"""nanopass gate — Phase 1 query-engine program stage +
Phase 2 record-driven programOf.

Gates (cheap, no full emit — the byte-equality run is separate):

  1. FRAG-CONCAT: per-routine `routine_query` frags decode and
     concatenate to exactly `decode_program(program_query)` — the
     split is a pure projection of the monolithic stage.
  2. INVALIDATION: patching one routine's builder changes exactly
     its `program.<name>` checkpoint key plus the downstream
     program.items/text.bin/image.bin — all other frag keys and
     link.sections are untouched.
  3. PASS-INVARIANT: an unknown pass name refuses (ValueError), and
     a registered pass returning a non-frag shape fails decode
     rather than emitting a malformed item list.
  4. ID-CHAIN: passes=('id','id') leaves a frag unchanged — the
     chain spine itself adds no semantics.
  5. RECORD==MONOLITH: `program_query_rt(ROUTINES)` — routine names
     arriving as term data through the nibble trie — decodes to
     exactly `decode_program(program_query)`.
  6. RECORD IR+BYTES: `routine_names_ir(Rb)` under the redirect+bytes
     pin decodes to exactly `program_ir(Rb)` — the production kernel
     is stageable.
  7. TRIE-MISS: an unknown routine name in the record produces the
     malformed frag — decode refuses it.
  8. SENTINEL-LEAK: `_val_expr` refuses unmapped sentinel arithmetic
     (nb-2 style) instead of baking a literal.
  9. BOUNDED-BATCH: `_batch_bounded` halves on kernel OOM (rc=4),
     preserves query order, propagates other failures unsplit.

The per-routine stage is exercised byte-exact by
`emit_image(decompose_asm=True, workdir=...)` — see the
`staged==direct: True 3584B` run recorded in decision 050 and the
IR redirect+bytes emit (6656B, staged==oracle) in decision 051.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import emit_chain as ec                                        # noqa: E402
import routines_x86_64_win64 as rts                            # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import target_pe64                                            # noqa: E402
from graph_runtime import reduce_tree_lo                       # noqa: E402


def gate_frag_concat(R) -> bool:
    mono = st.decode_program(reduce_tree_lo(st.program_query(R),
                                            500_000)[0])
    all_it = []
    for name in rts.ROUTINES:
        nf, _, _ = reduce_tree_lo(st.routine_query(name, R),
                                  500_000)
        all_it.extend(st.decode_frag(nf))
    return all_it == mono


def gate_invalidation(R) -> bool:
    tb = target_pe64.text_rva(rts.IMPORTS, rts.DATA_SLOTS)
    k1 = ec._ck_keys(R, rts.IMPORTS, rts.DATA_SLOTS, tb)
    orig = rts._BUILDERS["itoa"]
    try:
        # swap itoa's builder for a different function object —
        # same effect as editing its source under _src()
        rts._BUILDERS["itoa"] = rts._BUILDERS["repr"]
        k2 = ec._ck_keys(R, rts.IMPORTS, rts.DATA_SLOTS, tb)
    finally:
        rts._BUILDERS["itoa"] = orig
    frag_same = all(k1[f"program.{n}"] == k2[f"program.{n}"]
                    for n in rts.ROUTINES if n != "itoa")
    return (k1["program.itoa"] != k2["program.itoa"]
            and frag_same
            and k1["program.items"] != k2["program.items"]
            and k1["link.sections"] == k2["link.sections"]
            and k1["text.bin"] != k2["text.bin"]
            and k1["image.bin"] != k2["image.bin"])


def gate_pass_refusal(R) -> bool:
    try:
        st.routine_query("mkapp_p", R, passes=("bogus",))
        return False
    except ValueError:
        pass
    # a pass that returns a malformed item must hit the frag
    # invariant — "bad item tag" at decode, not a smuggled shape
    # downstream.  `bad = λf. [ ["bogus"] ]`: one item whose tag is
    # neither "label" nor "i".
    from reduce import KK, app
    bad_item = app(app(st._CONS,
                       app(app(st._CONS, st.str_term("bogus")), KK)),
                   KK)
    st._PASS_BUILDERS["bad"] = lambda: app(KK, bad_item)
    try:
        nf, _, _ = reduce_tree_lo(
            st.routine_query("mkapp_p", R, passes=("bad",)),
            200_000)
        st.decode_frag(nf)
        return False
    except ValueError as e:
        return "bad item tag" in str(e)
    finally:
        del st._PASS_BUILDERS["bad"]
        st._PASS_TERMS.pop("bad", None)


def gate_id_chain(R) -> bool:
    a = st.decode_frag(reduce_tree_lo(
        st.routine_query("mkapp_p", R), 200_000)[0])
    b = st.decode_frag(reduce_tree_lo(
        st.routine_query("mkapp_p", R, passes=("id", "id")),
        200_000)[0])
    return a == b


_PROG_AXES = {"fuse_s", "fuel", "read_buf_bytes", "chunk_bytes",
             "node_bytes", "stack_reserve", "peephole"}


def _fixed_of(R) -> dict:
    """emit_image's generation-pin rule: every non-λ Realization
    field pins at generation time."""
    return {k: getattr(R, k) for k in vars(seed.Realization())
            if k not in _PROG_AXES}


def gate_record_eq_monolith(R) -> bool:
    """program_rt folded over the ROUTINES record decodes to exactly
    the monolithic programOf NF — the record is pure projection."""
    rt = st.decode_program(reduce_tree_lo(
        st.program_query_rt(rts.ROUTINES, R), 1_000_000)[0])
    mono = st.decode_program(reduce_tree_lo(st.program_query(R),
                                            500_000)[0])
    return rt == mono


def gate_record_ir_bytes() -> bool:
    """the production kernel staged: ROUTINES_IR_BYTES under the
    redirect+bytes pin decodes to exactly program_ir(R) — the staged
    chain can now emit the byte-egress kernel itself."""
    R = seed.Realization(reclaim="redirect", io=("stdin", "bytes"))
    items = st.decode_program(reduce_tree_lo(
        st.program_query_rt(rts.routine_names_ir(R), R,
                            fixed=_fixed_of(R)), 2_000_000)[0])
    return items == list(rts.program_ir(R))


def gate_record_refusal(R) -> bool:
    """a name the trie doesn't know must produce the malformed frag —
    decode refuses it rather than skipping a routine."""
    try:
        nf, _, _ = reduce_tree_lo(
            st.program_query_rt(("mkapp_p", "no_such_routine"), R),
            500_000)
        st.decode_program(nf)
        return False
    except ValueError as e:
        return "bad item tag" in str(e)


def gate_sentinel_leak() -> bool:
    """a builder doing Python arithmetic on a sentinel (nb-2 style)
    must refuse at _val_expr, not bake a literal."""
    try:
        st._val_expr(-0x3335)          # nb - 2 — unmapped derivation
        return False
    except ValueError as e:
        return "sentinel" in str(e)
    # derived-but-declared ones pass
    # (checked implicitly by the IR record gate)


def gate_batch_bounded() -> bool:
    """_batch_bounded halves on kernel OOM (rc=4) and preserves
    query order; a persistent rc=4 on a single root and any other
    rc propagate without splitting.  The pass-2 resolver terms are
    what actually OOM — measured 32 roots OK / 64 OOM, 2026-10."""
    def oom_above(n):
        def b(qs):
            if len(qs) > n:
                raise RuntimeError(
                    "exe bytes batch failed rc=4 stderr=b''")
            return (list(qs), 0, 0)
        return b
    got = ec._batch_bounded(oom_above(8), list(range(100)))
    if got != list(range(100)):
        return False
    try:                                # single root that OOMs
        ec._batch_bounded(oom_above(0), ["x"])
        return False
    except RuntimeError as e:
        if "rc=4" not in str(e):
            return False
    try:                                # non-OOM failure: no split
        def bad_rc(qs):
            raise RuntimeError("exe bytes batch failed rc=3")
        ec._batch_bounded(bad_rc, list(range(100)))
        return False
    except RuntimeError as e:
        return "rc=3" in str(e)
    return True


if __name__ == "__main__":
    R = seed.Realization()
    gates = [
        ("frag-concat == monolithic", lambda: gate_frag_concat(R)),
        ("per-routine invalidation", lambda: gate_invalidation(R)),
        ("pass refusal/invariant", lambda: gate_pass_refusal(R)),
        ("id chain transparent", lambda: gate_id_chain(R)),
        ("record == monolith", lambda: gate_record_eq_monolith(R)),
        ("record IR+bytes == program_ir", gate_record_ir_bytes),
        ("record trie-miss refusal", lambda: gate_record_refusal(R)),
        ("sentinel-arithmetic refusal", gate_sentinel_leak),
        ("bounded batches halve on OOM", gate_batch_bounded),
    ]
    fail = 0
    for name, g in gates:
        try:
            ok = g()
        except Exception as e:                        # noqa: BLE001
            print(f"  {name}: ERROR {e}")
            fail += 1
            continue
        print(f"  {name}: {'PASS' if ok else 'FAIL'}")
        fail += not ok
    print(f"nanopass gate: {len(gates)-fail}/{len(gates)}")
    sys.exit(1 if fail else 0)
