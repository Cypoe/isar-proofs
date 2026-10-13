agents-store isn't an agent harness at all — it's a data-integration play, and a serious one. One identity, many lawful projections, Datomic-style append-only datoms, LAV wrappers, correspondences graded proposed → witnessed → proven, mediators derived through a shared quotient, default-deny writes. The reading list is the honest canonical lineage for that thesis — Wiederhold's mediators, Halevy and Lenzerini on LAV/GAV, Fagin on data exchange, Bernstein's model management, Spivak's CQL, Foster–Greenwald–Moore–Pierce lenses, Boomerang, PROV — and KernelCategory.lean as the mediating-morphism theorem in embryo. The M-table (M1–M11) is a better self-audit than most published retrospectives.

Store vs. bridge: keep them distinct
The megaplan already contains the right answer to "should it become the resource bridge" — phase 7 says the koru store library is design input for the open bridge, and the M1 rule (no new substrate before POC acceptance) forbids jumping there before A1–A11 pass. I'd sharpen the distinction rather than collapse it:

agents-store is the identity plane: minted IDs, lineage, append-only history, lawful writes. It answers "what is the thing that persists across turns, views, and apps."

kopium's resource bridge is the action plane: an agent whose only tool is an interpreter, safety by type system. It answers "what may an agent do, and what does it owe."

The bridge needs exactly what the store supplies — identity across turns, which is your M6 rule (minted, never positional) wearing koru's D7/D8 rulings (handle-not-key, generation checks). So the store doesn't become the bridge; the bridge mounts the store as its state substrate. Making the POC depend on koru now would be M1 all over again — ~8 substrates before a usable result, which the plan explicitly bans. Python+SQLite first, koru store library on the branch second, bridge design third. The plan's sequencing is correct; resist the pull.

One addition from our discussion worth a line in the plan, not the code: the certificate table's tier CHECK ('witness','proof') is where zk-attested runs land later — an attested tier between witness and proof, receipt-pinned. Phase-6+ material, not schema churn now.

What's actually left in isar-proofs
The megaplan's kill criterion is precise: by 2026-11-30, native assemble for the full-src program (pass1 + enc2_len) under gc=sweep; miss → freeze with fixtures + frag + README, no new substrate. Your pasted landing record shows exactly one technical item stands between 9bb305a and that criterion: corpus-level byte_add (decision 065), so pass1 stops walking 8-nibble succ-chains with absence-probe guards. Everything else is done or deliberately out of scope:

Done: the level-1 eval<menv> leg, enc2 fasmg-exact per-op, the committed gate (nanopass 35/35, battery fast 31/31), the stale 27-rels pin fix, golden fixtures as the oracle.

Out of scope for the criterion: frag 0016's interpreter² [] ambiguity. Leave it open — the criterion doesn't ask for it, and an honestly-recorded open question is a feature of the artifact, not a debt.

Hygiene (§7 + your record): commit the modified host/gates/*, move _*.py / _blobs/ / --run-probes to an ignored dir, frag 0025 already carries the record, _ncogen.py per your note is safe to delete — though the plan's own rule says ask-before-delete, so that stays a decision you make, not the agent.

Harvest: narrow the README, strip the cosmology claims per M3, state the mediating-morphism theorem — this last one is load-bearing because it feeds agents-store phase 8.

My verdict on byte_add: attempt it, timeboxed. It's bounded, the decision doc exists, and trigger (a) is met natively per your own record. And there's a dataset-specific reason beyond the kill criterion: landing it converts the OOM wall into a before/after representation-cost pair — nibble-chain telemetry and batch-arithmetic telemetry on the identical corpus — which is the single most mineable thing the repo could contain. Miss the date, freeze per protocol; the wall itself remains a recorded, measured result either way.

Mining it: the export already half-exists
The repo is dataset-shaped by discipline — refusals as data, telemetry recorded, every claim citing executed evidence. What's missing is packaging, not new work. Five datasets live in there already:

The corpus: 30 relations with declared recursion shapes and parse/render round-trip proofs. The rare property is the labeled refusals — refusal-annotated relational programs are scarcer than proof statements.

The challenges catalog: 36 named reproducible entries with recorded expected outcomes — a labeled (input, verdict) benchmark. miniF2F's trajectory is the template: its value was being a cross-system benchmark of statements, and its extensions came from decomposing proofs into building blocks — 1,329 lemmas, 40k lines, explicitly framed as an AI training asset. Your challenges catalog is already that decomposition shape, for refusals instead of proofs.

The telemetry: the enc2 table you pasted (steps/wall/gc per probe) plus the byte_add before/after pair if it lands — a quantitative representation-cost dataset.

The cadence: models/commit_cadence/data/series.csv — 1,300+ commits with duration/size metrics, largely agent-co-authored, under a refusal-disciplined gates regime. As far as I know there is no public corpus of agent-assisted verified engineering with this structure; the LLM-for-SE reproducibility literature says the field lacks exactly this kind of structured process data.

The frags: concepts as belief records with provenance timestamps, including a labeled retraction (frag 0017, the M7 encoding-level confusion) — an epistemic-history dataset.

Packaging bar: the ACM artifact-evaluation criteria — Available (DOI), Functional (documented, consistent, complete, exercisable), Reusable — and take the warning seriously: one study found only 44% of results-reproduced-badged artifacts could actually be reused. Your existing discipline beats most published artifacts on exactly the axes they fail — pinned oracles that fail loudly naming the path, one-command battery, refusals-as-data — so the packaging work is: a tagged freeze commit, MIT license decision for corpus and data, a CITATION.cff, a Zenodo/HF release with the battery as the exercisable entry point, and an oracle-requirements document (fasmg path, pinned version, refuse-if-missing semantics).

So the cut, final form: agents-store stays the production line with its own plan (which already incorporates everything we discussed — the gates discipline is the certificate regime); isar-proofs gets byte_add until 11-30, hygiene, harvest, then either a complete assemble fixpoint or a frozen wall — and both outcomes package into the same dataset, because the discipline you built makes the difference between a result and a failure a labeled row either way.

Note the freeze event is itself a dataset row — keep the cadence series running through it. The BREAK commit, the OOM wall, the pivot to agents-store: the value of the process dataset is precisely that it records the whole arc, not just the wins.

pretty happens twice — the harvest at freeze, the packaging at first external consumption — and the only clock ticking right now is the nibble-telemetry snapshot, which has to be committed before the byte_add merge touches the corpus.

Note the freeze event is itself a dataset row — keep the cadence series running through it. The BREAK commit, the OOM wall, the pivot to agents-store: the value of the process dataset is precisely that it records the whole arc, not just the wins.

After freeze — event-driven, not calendar
Packaging (export shape, CITATION.cff, license decision, Zenodo/HF release) has no date; it has two triggers:

A paper. If the representation-cost result or the agent-cadence dataset gets written up, artifact evaluation happens after acceptance — authors submit artifacts once the paper is in — so packaging must exist by camera-ready, and the badge ladder matters: Available (DOI) → Functional → Reusable, where Reusable (clean docs, structure, exercised) is the tier that actually correlates with uptake . A decade of AE retrospectives shows the badges get awarded, but reuse still fails on packaging quality — your refuse-if-missing-oracle discipline is worth more there than any badge.

First consumption. When someone — you, Lars, kopium, an LLM eval — actually needs to train or query on it. Packaging before that is wasted motion on a moving target: the corpus just demonstrated it still grows (the 27→30 drift was caught by a stale pin, which is the argument for packaging only at rest).

# isar-proofs — Mining Plan and References (async track)

Companion to `koru-verification-path.md`. Async by design: nothing here blocks the koru work, the
agents-store POC, or the byte_add attempt. The only synchronous item in the whole isar track is the
nibble-telemetry snapshot, which must be committed *before* the byte_add merge.

---

## 1. Timing (event-driven, not calendar)

| Stage | Trigger | Work |
|---|---|---|
| Continuous, now | every landed feature | commit hygiene (M10); telemetry as committed data, not commit-message prose; frags per landed feature |
| Hard deadline | byte_add merge — *before* it lands | snapshot the nibble-chain wall (pass1 OOM rc=4, enc2_len >4min, 296M/401M steps, gc=41) — the "before" half of the before/after pair is unreconstructable after the merge |
| Early, cheap | any time | M3 claims strip on the public repo (cosmology overclaims: H0 "prediction", Inverse Complexity Law, MicroProofChecker timings) — a README + claims audit, ruled already by the megaplan |
| The pretty gate | kill criterion 2026-11-30, or earlier decisive byte_add outcome | harvest: narrow README to what is proven; state the mediating-morphism theorem explicitly (feeds agents-store phase 8 — the only harvest item with a downstream deadline); freeze frag citing decision 065; tag. Corpus must be clean: battery green, 0 drift, rel-pins updated |
| Packaging | first external consumption (paper submission / dataset release) — not a date | export shape, CITATION.cff, license, Zenodo/HF release with the battery as the exercisable entry point; AE badges: Available (DOI) → Functional → Reusable; Reusable is the tier that correlates with uptake |

Note the paper-shaped trigger: artifact evaluation runs *after* acceptance, so if the representation-cost
result or the cadence dataset is written up, packaging must exist by camera-ready. Packaging a moving
corpus wastes work — the 27→30 rel-pin drift is the standing argument for packaging only at rest.

## 2. The five datasets (what ships)

1. **Corpus** — 30 relations, declared recursion shapes, parse/render round-trip proven. Rare property:
   *labeled refusals*.
2. **Challenges catalog** — 36 named reproducible (input, expected-verdict) entries incl. refusals:
   a refusal-annotated miniF2F.
3. **Telemetry** — enc2 probe table + the byte_add before/after pair (the representation-cost dataset).
4. **Cadence** — models/commit_cadence/data/series.csv: 1,300+ commits, duration/size metrics,
   agent-co-authored, refusal-disciplined. No comparable public corpus known; the reproducibility
   literature for LLM-based SE explicitly lacks structured process data.
5. **Frags** — belief records with provenance timestamps, incl. a labeled retraction (frag 0017):
   an epistemic-history dataset.

## 3. Provenance of the ideas

| Idea | Pulled from | What it solves | Status |
|---|---|---|---|
| Relational evaluator substrate (rel_eval, phi2 corpus) | miniKanren: Friedman, Byrd, Kiselyov, *The Reasoned Schemer*; Byrd's thesis (2010) | programs-as-relations, streams as evidence | prior art |
| Specialization / Futamura-1 (specialize.plex, cogen) | Futamura 1971; Jones, Gomard, Sestoft 1993 (already in the megaplan reading list) | the meta-circular ladder the corpus walks | prior art |
| Mediating morphism / quotient composition (KernelCategory; agents-store phase 8) | Spivak, *Functorial data migration* (Inf.\ & Comp.\ 2012); Bernstein, *Applying model management* (CACM 2003); Wiederhold, *Mediators* (IEEE Computer 1992) | composition through a shared quotient with no per-pair proof | prior art (theorems); the KernelCategory instantiation is ours |
| Benchmarks-as-datasets (challenges → labeled pairs) | Zheng, Han, Polu, *miniF2F* (arXiv:2109.00110, 2021) | the shape of a mineable formal benchmark | prior art (shape); **NS-6**: refusal-labeled verdict corpus is new |
| Packaging standards | ACM artifact evaluation (Available/Functional/Reusable badges) | what "pretty" concretely means at release time | prior art |
| Lineage vocabulary (agents-store schema; datoms) | W3C PROV-DM (Moreau & Missier, 2013); Datomic information model (engineering) | provenance rows that survive dataset export | prior art |
| Lenses (GetPut/PutGet certification) | Foster, Greenwald, Kirkegaard, Moore, Pierce, Schmitt, *Combinators for bidirectional tree transformations* (TOPLAS 2007) | certify.py's law checks | prior art |

**NS-6 (the one new-synthesis claim on this track):** a verdict- and refusal-labeled relational corpus
with recorded expected outcomes, plus before/after representation-cost telemetry on the identical corpus —
no prior benchmark ships refusals as first-class labeled data.

## 4. BibTeX

```bibtex
@article{zheng2021minif2f,
  author  = {Zheng, Kunhao and Han, Jesse Michael and Polu, Stanislas},
  title   = {Mini{F2F}: a cross-system benchmark for formal {Olympiad}-level mathematics},
  journal = {arXiv preprint arXiv:2109.00110}, year = {2021}
}
@book{friedman2018reasoned,
  author    = {Friedman, Daniel P. and Byrd, William E. and Kiselyov, Oleg},
  title     = {The Reasoned Schemer}, edition = {2nd}, publisher = {MIT Press}, year = {2018}
}
@phdthesis{byrd2010minikanren,
  author = {Byrd, William E.},
  title  = {Relational Programming in miniKanren: Techniques, Applications, and Implementations},
  school = {Indiana University}, year = {2010}
}
@article{futamura1971partial,
  author  = {Futamura, Yoshihiko},
  title   = {Partial Evaluation of Computation Process---An Approach to a Compiler-Compiler},
  journal = {Systems, Computers, Controls}, volume = {2}, number = {5}, year = {1971}
}
@book{jones1993partial,
  author    = {Jones, Neil D. and Gomard, Carsten K. and Sestoft, Peter},
  title     = {Partial Evaluation and Automatic Program Generation},
  publisher = {Prentice Hall}, year = {1993}
}
@article{spivak2012functorial,
  author  = {Spivak, David I.},
  title   = {Functorial data migration},
  journal = {Information and Computation}, volume = {217}, year = {2012}
}
@article{bernstein2003applying,
  author  = {Bernstein, Philip A.},
  title   = {Applying model management to classical meta data problems},
  journal = {Communications of the ACM}, volume = {46}, number = {12}, year = {2003}
}
@article{wiederhold1992mediators,
  author  = {Wiederhold, Gio},
  title   = {Mediators in the architecture of future information systems},
  journal = {IEEE Computer}, volume = {25}, number = {3}, year = {1992}
}
@article{foster2007combinators,
  author  = {Foster, J. Nathan and Greenwald, Michael B. and Kirkegaard, Christian and Moore, John T. and Pierce, Benjamin C. and Schmitt, Alan},
  title   = {Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem},
  journal = {ACM TOPLAS}, volume = {29}, number = {1}, year = {2007}
}
@misc{provdm,
  author = {Moreau, Luc and Missier, Paolo (eds.)},
  title  = {{PROV-DM}: The {PROV} Data Model},
  note   = {W3C Recommendation, 2013}
}
@inproceedings{artifactsbaneorboon,
  author = {[TODO: complete from DOI 10.1145/3456287.3465479]},
  title  = {Artifact Description/Artifact Evaluation: A Reproducibility Bane or a Boon},
  booktitle = {[SIGOPS Operating Systems Review]}, year = {2020},
  note   = {AE runs after paper acceptance — the packaging-by-camera-ready constraint}
}
@inproceedings{reusebadges2026,
  author = {[TODO: complete from DOI 10.1145/3820002.3828598]},
  title  = {Measuring Ease of Reuse for Security Research Artifacts with Results-Reproduced Badges},
  year = {2026},
  note   = {only 44\% of results-reproduced artifacts were actually reusable — packaging quality is the differentiator}
}
```

TODO entries marked above: author lists to be completed from the DOI/arXiv pages before any public
release — do not ship bibtex with a [TODO] field.
