# Heim 1982: implementation and requirements

2026-09-15. This implements the final mathematical file-change rules and a
substantial set of source-linked consequences. It does **not** establish that
every analysis in the dissertation transfers unchanged, or that every pragmatic
prediction has now been implemented. The question is what each part requires,
not merely whether one can write a small model that compiles.

There are 92 proved statements in four new files, with no admissions. Fresh
compilation and independent kernel rechecking pass. Of these statements, 89 have
no global axiom dependencies; three use only classical excluded middle.
These counts include infrastructure and boundary tests, not 92 independent
linguistic claims. "No global axiom dependencies" does not remove the model,
felicity or policy hypotheses written in individual theorem statements.
Source faithfulness still needs independent human review.

## What formalization required

| Requirement | What was done or established | Effect on the source theory |
| --- | --- | --- |
| Representation | Predicate-valued sets, infinite assignments, separate file domains/satisfaction, arity-indexed tuples, recursive updates and explicit felicity conditions. | No finite-world or finite-individual restriction. No choice or extensionality axiom. These are encoding decisions, not demonstrated necessities or semantic revisions. |
| Classical metatheory | Isolated excluded middle in three named metatheorems; the update core and main donkey results are constructive. | Makes the source's classical reasoning explicit; does not change the update rules. |
| Source model assumptions | Exposed nonempty individual domains where needed, and the best-world existence assumption explicitly mentioned at p.117 fn.8. | A countermodel shows why the latter matters: without best worlds, the simplified necessity clause can hold vacuously. |
| Source clarification | Distinguished unchanged possible-world content from unchanged assignment satisfaction sets in pp.250–251. | The literal satisfaction-set claim has a countermodel. The proposed clarification needs source review; it was not silently substituted for the text. |
| Additional predictive policy | Represented accommodation, relevance repair, prominence and proxy choices as explicit inputs. | A selected policy would add predictions not determined by the supplied rules. Conditional results are not a complete pragmatic theory. |
| Executable processing | Kept felicity as a proposition rather than pretending arbitrary entailment is decidable. | A total informative felicity decider would decide arbitrary propositions. An executable processor needs supplied decisions or declared restrictions; mathematical formalization does not. |
| Remaining implementation | General movement derivations, automatic free-variable extraction and an integrated modal/file/proxy processor are not delivered. | These are implementation boundaries, not evidence of impossibility or necessary theoretical restructuring. |

The machine-readable [requirements and coverage ledger](heim_1982_results.json)
gives a disposition for each of the 19 targets in the
[pre-implementation design](heim_1982_design.md). An implemented interface is
explicitly distinguished there from a derived source prediction.

## Implemented semantics and consequences

| File | Proved | Scope |
| --- | ---: | --- |
| [Heim1982.v](../../atlas/dynamic/Heim1982.v) | 34 | Final file-change rules, literal condition B, local extended novelty/familiarity, entailment, truth/falsity and preservation results. |
| [Heim1982_Examples.v](../../atlas/dynamic/Heim1982_Examples.v) | 17 | Strong donkey reading, nuclear-scope existentials, negative closure, anaphora, scope and intensional-presupposition separating models. |
| [Heim1982_Extensions.v](../../atlas/dynamic/Heim1982_Extensions.v) | 22 | Conditional accommodation runs, father example, local/global distinction, C′ repair and proxy interfaces, and requirement countermodels. |
| [Heim1982_Indexed.v](../../atlas/dynamic/Heim1982_Indexed.v) | 19 | Earlier indexed satisfaction, modal interpretation, bounded correspondences with the final system, and explicit construal constraints. |

The final universal clause is the one on p.234, including **existential closure
of new nuclear-scope indices**, not just the preliminary p.228 clause inspected
in the earlier review. The disjunction extension is the proposal in p.254 fn.28;
its factored implementation is proved equivalent to the displayed single-witness
formulation. Earlier indexed semantics is kept separate: two formula-family
correspondences are proved, not a whole-system equivalence.

The general semantics permits arbitrary world and individual types, predicate
file domains and infinite assignments. Finite examples are countermodels/tests,
not restrictions on the implementation. An AST represents interpreted logical
forms, not a complete English parser. `Use` records definite occurrences and
`Mark` checks the full descriptive body of an NP; felicity is checked at the
intermediate file appropriate to each step. Undefinedness is not falsity.

Substantive checks include:

- `donkey_truth_conditions`: every farmer beats every donkey that farmer owns,
  with nonowners excluded from the restrictor. A model separates this from
  beating merely one owned donkey.
- `nuclear_existential_truth_conditions`: the final universal rule permits an
  existential witness in the nuclear scope. It is not universally bound there.
- `negative_existential_truth_conditions`, `discourse_anaphora_truth`, and
  `scope_blocks_later_pronoun`: existential force, subsequent use and nonexport.
- `actual_truth_is_not_contextual_entailment`: a description true in the actual
  world need not be entailed by the information state across worlds.
- `accommodated_father_run` and `accommodated_father_truth_conditions`: given
  the explicitly permitted old-man/new-father bridge, the actual definite
  syntax yields the p.242 reading that every man has a father he hates.
- `local_global_accommodation_differ`: accommodation under negation and above
  negation yield different truth conditions. The preferred location is not
  selected by a hidden default.

## Requirements established by proofs, not by failed attempts

### Assignment information is not just possible-world information

Heim pp.250–251 calls certain new-card accommodations information-preserving
and describes the files as having "identical satisfaction sets (in all worlds)."
Under the literal total-assignment semantics, these are different claims.

For example, start with an empty file over a two-element individual domain.
Add a fresh card whose entry requires its value to be one particular element.
Every world still has a satisfying assignment. But an assignment mapping the
new index to the other element satisfied the original file and no longer
satisfies the result. Thus world content is unchanged and the satisfaction set
is strictly smaller. `world_preservation_is_not_Sat_preservation` proves this;
`existentially_supported_introduction_preserves_worlds` proves the appropriate
general world-content preservation result under its explicit assumptions.

This diagnoses an assignment/world distinction, not an inability of Coq to
express set comprehension. The historical `FCS.v` comprehension claim is not a
valid obstruction: its existential predicate definition is accepted. The older
`FCS2.v` class-comprehension encoding and `DonkeyScope.v` interpretation are
retained as historical attempts, not silently replaced as evidence.

### Do not strengthen the source's condition B silently

The literal p.197 condition B concerns changing one coordinate outside the file
domain. With infinite assignments this does not imply invariance under every
simultaneous change outside that domain. The eventual-true-sequence countermodel
`B_does_not_imply_full_domain_support` proves the distinction. Both properties
are preserved separately by update; the principal general donkey results use B,
not an unacknowledged stronger premise.

### A mathematical semantics is not automatically a decision procedure

`total_felicity_decider_decides_arbitrary_propositions` reduces deciding any
proposition to deciding felicity for all interpretations admitted here. This is
a precise lower-bound result, not a blanket undecidability theorem or proof
that classical mathematical semantics is unformalizable. The partial update is
represented by its felicity guard and graph, without such a decider.

### Underspecified choices can affect the answer

The accommodation relation permits finite repair/update interleavings, with
explicit strengthening and policy premises. Its no-repair specialization is
proved to coincide with raw licensed update. Strengthening alone is not claimed
to capture conversational appropriateness. Bridge selection, local/global
preference and proxy precedent are not computed by these modules.

Two true weakened files can yield different revised truth values after the
same false input. This establishes that structural weakening alone does not
determine C′; it does not claim both choices satisfy an independently specified
relevance policy. Likewise, the proxy interface exposes policy dependence
without claiming to predict all the paycheck-pronoun contrasts.

## What remains open, and why

The source itself leaves C′ relevance imprecise (pp.218–220), accommodation
governance incomplete (pp.239–241), accommodation preferences tentative
(pp.245–246), and prominence/proxy behavior partly speculative (pp.247–250).
The generic discussion is not a completed theory (pp.126–129). Specific
indefinites and related exceptional scope/crossover behavior are explicitly
left unresolved at pp.147–150. No one of the alternative repairs discussed there
is selected here. Nor is a comprehensive projection theory attributed to the
dissertation: p.210 defers that wider investigation to later work.

Separately, some implementable engineering remains: a general construal
derivation relation, automatic extraction of free indices, broader correspondence
proofs, and integration of indexed modalities with the final file/proxy process.
The existing constraints consume supplied syntax relations and context reference
data. Those inputs must not be mistaken for an implemented parser or a proved
end-to-end analysis. The claim is therefore **not whole-source completion**.

A productive next extension is to define competing, clearly labeled
accommodation policies and derive their differing predictions on the same
examples. That tests what extra commitments buy, instead of retroactively
attributing a chosen completion to Heim. Source review should first settle the
assignment/world clarification and audit the mappings in these records.

## Verification and provenance

All four modules compile with Coq 8.20.1 in a fresh dependency directory and pass
`coqchk`. Every proved declaration was queried for assumptions. Only these three
depend on `Classical_Prop.classic`:

- `Heim1982_Extensions.nontrivial_entailment_forces_familiarity`;
- `Heim1982_Extensions.criterion_C_exhaustive_on_felicitous_true_inputs`;
- `Heim1982_Indexed.modal_duality_classical`.

There are no admissions, top-level axiom declarations, unresolved assumption
queries or unsafe compilation flags. Depth probes completed for all 92
statements: 0 vacuity flags, 22 triviality flags, 0 bailouts. The 22 flags are
retained in the probe sidecars; they concern helpers, direct definition checks
and easy construction tests. Neither their presence nor the other 70 results
is an independent semantic-fidelity judgment.

Integration checks pass: 53 Python atlas tests (including eight new Heim
traceability tests), 14 CI-setup tests, and all three browser-reporting test
scripts. The project make target also succeeds. All 78 previous consolidated
file records and all previous claim fingerprints are unchanged; exactly 92
claims were added. Across the 230 paper records, only Heim's evidence-file links
changed. Existing evidence levels, frozen grades and source outcomes are intact.

Reproduce from the repository root:

```sh
bash atlas_data/campaigns/check_heim_1982.sh
python3 atlas_data/verify.py atlas/dynamic/Heim1982.v atlas/dynamic/Heim1982_Examples.v atlas/dynamic/Heim1982_Extensions.v atlas/dynamic/Heim1982_Indexed.v
python3 atlas_data/probes/run_probes.py atlas__heim1982 atlas__heim1982_examples atlas__heim1982_extensions atlas__heim1982_indexed
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 atlas_data/check_checkpoint.py atlas_data/campaigns/heim_1982_manifest.json
```

When rebuilding the local atlas, provide the external corpus path so unrelated
papers with PDFs keep their sourced status (replace the example path as needed):

```sh
ATLAS_PAPERS=/path/to/formalizing_formal_semantics/papers python3 atlas_data/consolidate.py
python3 atlas_data/build_site.py
```

Source: Heim's 1982 dissertation, consulted in the 2011 Schoubye–Glick
retypesetting; page numbers above refer to that edition. Reading covered the
relevant mathematical definitions, construal passages and accommodation
discussion in Chapters II–III, not a cover-to-cover verification of every
historical argument or example. Heim 1983 was not substituted for this source.
The local PDF is hash-pinned in the new manifest but is not copied into Git.

This is one assistant's implementation and source comparison, not independent
grading or maintainer approval. The four records remain `incomplete`, `partial`
and `unassessed`; Heim stays P4/F3 with `review_required`, and there is no accepted
paper outcome. The frozen formality grades and old research files are unchanged.
The local atlas and site have been rebuilt, but nothing has been committed,
pushed or deployed as part of this implementation. The new manifest supersedes
shared generated-output hashes in earlier checkpoints; historical manifests and
review drafts remain unchanged.
