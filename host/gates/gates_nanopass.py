"""nanopass gate suite — the runner.

Gate bodies live in the family modules (same directory):

  np_gates_record   — record/programOf: frags, passes, trie,
                      sentinel discipline (gates 1-8)
  np_gates_streams  — arena-boundary: bounded batches, pins,
                      blob store, staged link, ir egress (9-16)
  np_gates_emit     — emit chain: manifest replay, staged frames,
                      fixpoint, serialized emit.plex DAG (13,19-21,24)
  np_gates_kernel   — kernel/container: bundle format, MT equiv,
                      .plex ingest, layer legs (17-18,22-23)
  np_gates_rel      — phi.rel contract: verbatim parse, admissible
                      construction, eval, shape/lowerings, fuel,
                      meta-call, carry chain, congruence, basis
                      unify (25-32)
  np_common         — shared helpers (_fixed_of)

Registry order below is the evidence order — cheap structural
gates first, exe-level emits last."""

import os
import sys
import tempfile

_HOST = os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))
sys.path.insert(0, _HOST)
sys.path.insert(0, os.path.join(_HOST, "..", "seed"))

import seed                                                    # noqa: E402
import np_gates_record as rec                                  # noqa: E402
import np_gates_streams as strm                                # noqa: E402
import np_gates_emit as emit                                   # noqa: E402
import np_gates_kernel as kern                                 # noqa: E402
import np_gates_rel as rel                                     # noqa: E402


if __name__ == "__main__":
    R = seed.Realization()
    gates = [
        ("frag-concat == monolithic", lambda: rec.gate_frag_concat(R)),
        ("per-routine invalidation", lambda: rec.gate_invalidation(R)),
        ("pass refusal/invariant", lambda: rec.gate_pass_refusal(R)),
        ("id chain transparent", lambda: rec.gate_id_chain(R)),
        ("record == monolith", lambda: rec.gate_record_eq_monolith(R)),
        ("record IR+bytes == program_ir", rec.gate_record_ir_bytes),
        ("record trie-miss refusal",
         lambda: rec.gate_record_refusal(R)),
        ("sentinel-arithmetic refusal", rec.gate_sentinel_leak),
        ("bounded batches halve on OOM", strm.gate_batch_bounded),
        ("pin-splice digest equality",
         lambda: strm.gate_pin_splice(R)),
        ("blob-store disk round-trip",
         lambda: strm.gate_blob_store(R, tempfile.mkdtemp(
             prefix="nanopass_blob_"))),
        ("split-link == linkOf", strm.gate_split_link),
        ("manifest replay == emit",
         lambda: emit.gate_manifest_replay(
             tempfile.mkdtemp(prefix="nanopass_man_"))),
        ("decode-crossing evidence", strm.gate_decode_evidence),
        ("emit_ir blob round-trip", strm.gate_emit_ir),
        ("link blob seam == dict join", strm.gate_link_blob_seam),
        ("MT threads==serial observable", kern.gate_mt_equiv),
        ("plex v3 bundle round-trip", lambda: kern.gate_plex_bundle(
            tempfile.mkdtemp(prefix="nanopass_plex_"))),
        ("emit frames on emitted host", emit.gate_emit_frames),
        ("self-hosting fixpoint", lambda: emit.gate_selfhost_fixpoint(
            tempfile.mkdtemp(prefix="nanopass_selfhost_"))),
        ("emit.plex bundle replay", lambda: emit.gate_emit_bundle(
            tempfile.mkdtemp(prefix="nanopass_emitplex_"))),
        ("kernel .plex v3 ingest", lambda: kern.gate_plex_ingest(
            tempfile.mkdtemp(prefix="nanopass_plexin_"))),
        ("kernel layer composition", kern.gate_layer_chain),
        ("kernel plex.emit schedule exec",
         lambda: emit.gate_pexec_schedule(
             tempfile.mkdtemp(prefix="nanopass_pexec_"))),
        ("emit schedule serialized", lambda: emit.gate_emit_schedule(
            tempfile.mkdtemp(prefix="nanopass_sched_"))),
        ("phi.rel verbatim parse + bundle", rel.gate_rel_parse_verbatim),
        ("phi.rel schema admissible", rel.gate_rel_schema_admissible),
        ("phi.rel shape lowering contract", rel.gate_rel_shape_lowering),
        ("phi.rel fuel quotient", rel.gate_rel_fuel_quotient),
        ("phi.rel meta-level call", rel.gate_rel_meta_call),
        ("phi.rel nibble carry chain", rel.gate_rel_carry_chain),
        ("phi.rel phi_boot congruence", rel.gate_rel_boot_congruence),
        ("phi.rel basis-term unify", rel.gate_rel_basis_unify),
    ]
    only = {s for a in sys.argv[1:] if a.startswith("--only=")
            for s in a.split("=", 1)[1].lower().split(",")}
    fail = 0
    for name, g in gates:
        if only and not any(s in name.lower() for s in only):
            continue
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
