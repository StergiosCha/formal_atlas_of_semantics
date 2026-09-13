# Second P0/P1/P2 cohort — stage A, frozen before source-body reading

2026-09-13. User authorized this cohort and the immediate deliverable: protocol
and source inventories before new Coq implementation. This is a purposive,
single-researcher extension, not a randomized, blinded or topic-matched study.
General familiarity with the authors is not excluded. Metadata, availability
and frozen grades were inspected before this protocol; source bodies were not
read for this cohort before it was written.

| ID | Frozen tier | Source | Source PDF SHA-256 |
|---|---|---|---|
| 196 | P0 | Spivak 1988, Can the Subaltern Speak? | 96aef1b47c30e7070f420fa62f90d89e1ed00ba0d8f09683768f7d4b3cbd7e12 |
| 122 | P1 | Rosch 1978, Principles of Categorization | 45e33ffdfe2d79f5c63f1d70b28bcc5c8e6e72f3b761c17930a8af4bc50d8fbe |
| 101 | P2 | Hobbs 1985, On the Coherence and Structure of Discourse | 422ce067714e0865ec63f6b549cf96ac87e809d32fe98a79458bb9e96b618d9a |

All three are F1 with no linked Coq files at selection. Retain all three even
if a source is difficult to interpret, resists a mathematical statement or
has no implementable central claim. Do not substitute easier sources after
reading. Reading/implementation order: Rosch, Hobbs, Spivak. Read the full
local texts, recording their editions and page systems; distinguish editorial
matter and notes from the authors' arguments. Verify crucial scanned formulas
or distinctions visually when extraction is unreliable.

Baseline atlas SHA-256:
`1d3457d3faa13c19d336a1432bd82e941e33b2624cdde2e0ccbb2e02f744b5ad`.
Frozen grade file SHA-256:
`35dc302ae28c91e7e7d4c9677713b35bbd6af014ccb3aef6253e126f59eead0e`.
Baseline checkpoint: `claim_comparison_2026_09_13_manifest.json`.

## Two-stage freezing

Stage A fixes selection, reading scope, claim-selection rules and evaluation
before source-body reading. Stage B records the actual source-linked claims
after reading but BEFORE implementation. Do not imply that exact claim wording
was preregistered before reading a text. Freeze the completed inventories and
their hashes at the end of this turn; no new Coq module is part of this turn.

For each source, inventory ontology and distinctions, explicit definitions,
qualifications, argument structure, worked examples and non-formal remainder.
Select central targets because the author uses them in the stated thesis,
summary or a sustained argument, not because they look easy to encode. Give
each selected claim its own ID, page reference and modality/quantifier scope.
Separate empirical generalizations, normative conditions, historical claims,
conceptual distinctions and mathematical implications. Keep dependent claims
linked rather than presenting them as independent observations.

For each central target record:

1. A faithful paraphrase, source location and reason it is central.
2. A source-motivated positive case and a countercase/qualification. If the
   source supplies no appropriate pair, mark it missing rather than inventing
   one and attributing it to the source.
3. A candidate mathematical obligation, if defensible, and what it would NOT
   establish. A conceptual/historical claim may remain without a formal target.
4. Ordinary abstract parameters versus additional semantic commitments.
5. Whether a worked case would be supplied as input or independently derived.
6. A prospective robustness question: two plausible encodings of the SAME
   source claim, where available. Otherwise explicitly mark not yet specified.

Do not force equal numbers of claims, assign post-hoc success percentages,
or hide central claims by reclassifying them as irrelevant after coding.
List unselected/remainder claims and explain the bounded scope. Inventory
completion is not a formalization outcome or a new faithfulness verdict.

## Future implementation criteria, fixed now

A later bounded attempt must retain the stage-B inventory and show a
disposition for every target: representation only, conditional/source-linked
fragment, restricted construction, illustrative model, uncovered, refuted
(with a source-faithful countermodel), or unfinished engineering.

Track source-to-definition matches and substantive semantic additions. A
carrier type, context parameter or external empirical judgment is not by
itself a defect; encoding the desired conclusion into such an input is a
separate commitment. A definition check is not an independent prediction.
Source empirical claims cannot be verified merely by proving properties of
an assigned finite example. Historical evidence cannot be replaced by axioms.

For each implemented case: fresh compilation, assumption checks, kernel
checking, positive/negative cases and triviality/vacuity probes. Preserve
flagged results with their meaning. No axioms/admissions to force planned
successes. A logical inconsistency lemma is not a source refutation merely
because its joint premises are inconsistent.

Alternative-encoding robustness requires keeping source content fixed while
comparing two independently defensible representations. Changing model inputs
or choosing an arbitrary contrary model does not suffice. Record unsupported
alternative interpretations as such; do not force a second encoding to get a
robustness score. Independent semantic review remains a future requirement,
not something single-researcher self-checking can supply.

## Effort and inference limits

Record tool-clock boundaries for source preparation/reading and inventory
construction, extraction/OCR work, and interruptions. Wall-clock elapsed time
is not active human research time. No coding effort exists in this stage.
For later work, separately log source interpretation, encoding, proof/debugging
and robustness tests. Do not retroactively invent an equal-effort comparison
with the earlier pilots or infer efficiency from theorem totals.

The tier hypothesis concerns source-faithful central-claim coverage and added
semantic commitments, not whether more formal papers have more notation.
Topic, length, investigator familiarity and encoding choice remain confounds.
This cohort can broaden qualitative evidence; it cannot by itself establish
a causal tier gradient, general resistance rate or ranking of intellectual
value. Preserve all 230 intrinsic grades and original survey inputs. Do not
promote F levels or create implementation records for inventories alone.

Keep earlier protocols, results, manifests and Coq work unchanged. Record any
necessary departure in a separate deviation note; never rewrite this protocol
to match a later result. No commit, push or deployment is requested here.
