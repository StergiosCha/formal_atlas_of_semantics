# Source outcomes are reviewed, not inherited

The survey prediction, a recorded file assessment, and a reviewed source outcome
are different units. Compilation establishes properties of the encoded objects;
it does not establish that those objects adequately represent a paper or book.
An edge compares specified constructions, not every aspect of two theories.
P grades remain frozen intrinsic-formality annotations. F levels retain their
existing pipeline meaning; even F5 is not independent source-level approval.

## Current state

The [September 13 audit](audits/outcome_flags_2026_09_13.md) withdraws automatic
paper outcomes derived from the first linked file. All original file assessments,
rationales and mechanical evidence are retained. This includes favorable assessments
and assessments agreeing with the survey, not just the ten old disagreement badges.
The source-review registry currently contains no accepted reviews. This means
**unassessed at source level**, not failed formalizations or invalid Coq proofs.

`determination_candidates` lists all linked four-outcome file assessments in a
stable order. `record_outcome_conflict` means those opinions differ; different
attempts may legitimately yield different file assessments. It is not a logical
contradiction in the source. `determination_status` is `review_required` when such
candidates exist, otherwise `unassessed`, until a review is accepted.
`determination_actual` and `prediction_disputed` require a registry entry.
The UI describes a valid mismatch as “Reviewed assessment differs from survey.”

## Accepting a source outcome

Submit a review through a pull request, for maintainer approval. Reviewers must:

1. Identify the exact survey source, including edition/year. A shared Coq file
   does not transfer an outcome automatically to every cited paper or book.
2. State the implemented core, source passages and exclusions. Explain why the
   covered core supports a comparison at this survey entry's unit. A fragment or
   book appendix alone is not a whole-source result.
3. Independently examine the source-to-code mapping and the checked claims.
   State the reviewer's relationship to the implementation and prior assessment.
4. Reconcile all relevant linked records, including conflicting outcomes and
   source-identity mismatches; explain omissions and added commitments.
5. Check compilation, admitted material, proof dependencies and relevant depth
   flags. A signature parameter need not be a problematic logical axiom, but
   mechanically flagged dependencies require an explicit explanation.
6. For `major_restructuring` or `cannot`, document necessity or an obstruction.
   A difficult or unfinished attempt is not evidence that the source cannot
   transfer. A chosen encoding change is not automatically a necessary change.

## Registry schema

`paper_outcome_reviews.json` has `schema_version: 1` and a `reviews` list.
Each entry requires these fields:

| Field | Content |
| --- | --- |
| `paper_id`, `source_citation` | Exact survey ID and citation, including minted addendum IDs |
| `status` | `reviewed` |
| `determination` | `as_is`, `slight_modification`, `major_restructuring`, or `cannot` |
| `coverage` | `source_core`; fragment reviews cannot produce paper outcomes |
| `scope`, `coverage_justification`, `source_passages` | Covered core, justification and precise source locations |
| `reviewer`, `review_reference`, `independence_statement` | Reviewer, accessible review reference and declared independence |
| `rationale`, `record_resolution` | Source-level reasoning and reconciliation of linked assessments |
| `necessity_evidence` | Required nonempty explanation for restructuring/resistance outcomes |
| `support` | Nonempty list of supporting record references, described below |

Each support item contains `record_key`, `code_sha256`, `record_sha256`,
`mechanical_sha256`, and `theorems` (exact proved entries from that record's theorem
ledger; older entries sometimes group declarations). Hashes pin the Coq file,
raw `.json` record and `.mech.json` sidecar respectively. Where the mechanical
record flags undocumented assumptions, `assumption_evidence` maps each flagged
name to its reviewed explanation. Actual declarations and their source mapping
must be inspected, not inferred from a ledger label alone.

The loader rejects unknown/duplicate sources, citation mismatches, fragment
coverage, absent provenance, unlinked evidence, pilot/incomplete support,
unsuccessful or unsafe mechanical checks, admissions, absent proved evidence,
missing assumption queries, unreviewed flagged dependencies, stale hashes and
unsupported resistance claims. Positive outcomes additionally require recorded
faithful support. Do not relabel a pilot merely to pass this gate: completing
coverage and re-reviewing it are substantive work.

These are structural checks on a review declaration. They cannot authenticate
reviewer identity, establish independence, ensure a mechanical run is fresh for
the code, or prove the source interpretation correct. The reviewer must rerun
checks on the pinned code and the maintainer must evaluate the review. No fake
example reviews are installed, and changing a boolean on a file does not approve
a paper outcome.

`stats.determination` remains a backward-compatible count of **file assessments**;
`stats.paper_outcomes` counts only accepted source outcomes. Do not use the former
as the denominator or outcome axis of a formality-versus-transfer result.
