"""nanopass gates — record/programOf stage: per-routine frags,
pass chains, trie dispatch, sentinel discipline."""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))

import emit_chain as ec                                        # noqa: E402
import routines_x86_64_win64 as rts                            # noqa: E402
import seed                                                    # noqa: E402
import spec_term as st                                         # noqa: E402
import target_pe64                                            # noqa: E402
from graph_runtime import reduce_tree_lo                       # noqa: E402
from np_common import _fixed_of                                # noqa: E402


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
    k1, _ = ec._ck_keys(R, rts.IMPORTS, rts.DATA_SLOTS, tb)
    orig = rts._BUILDERS["itoa"]
    try:
        # swap itoa's builder for a different function object —
        # same effect as editing its source under _src()
        rts._BUILDERS["itoa"] = rts._BUILDERS["repr"]
        k2, _ = ec._ck_keys(R, rts.IMPORTS, rts.DATA_SLOTS, tb)
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

