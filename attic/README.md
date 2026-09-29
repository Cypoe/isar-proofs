Staging area for deletion. Nothing here is on any discovery path (not in
toolchain.json, not imported by host/seed). Files are kept until we are sure
they're unneeded; full provenance: commit 9831de6 (probes commit) and
`git log --follow`. wip/lean/ is NOT attic — those are unfolded proofs.

Cited as reproductions by host code comments (delete only together with
updating those citations): attic/host/_probe_g9f_enc.py (spec_term.py),
attic/host/_probe_g9g_e2e_staged.py (spec_term.py, emit_chain.py),
attic/host/_probe_g9g_pack.py (spec_term.py).
