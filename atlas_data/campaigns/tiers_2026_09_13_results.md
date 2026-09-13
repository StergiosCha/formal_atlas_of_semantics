# P0/P1/P2 coverage campaign: bounded results

The three selected attempts are complete against the frozen protocol's
bounded-attempt criterion: every inventory item has a disposition, and the
implemented cases were checked. None is a completed formalization of its
source theory. No selected source was replaced and no intrinsic grade was
changed. Selection is purposive; source assessment is by one researcher,
not an independent second review.

| Source | New artifact | Evidence change | Source-level determination |
|---|---|---|---|
| Derrida 1972, ID172, P0 | `atlas/discursive/Derrida1972.v` | F1 → F3 | unassessed; illustrative reconstruction |
| Austin 1962, ID177, P1 | `atlas/pragmatics/Austin1962.v` | F1 → F3 | unassessed; partial necessary-condition diagnostics |
| Horn 1984, ID67, P2 | `atlas/pragmatics/Horn1984.v` | F2 → F3 | unassessed; logical fragment plus added interpreter |

## What was learned

Derrida's distinctions support useful boundary models, but these do not prove
the philosophical thesis. The same modeled form can have different contextual
effects; conversely, infinitely many quotation frames can retain the same
effect. Thus syntactic iterability alone does not establish semantic
non-saturation. Form-only origin recovery fails under explicit collision
premises; richer evidence is not ruled out.

Austin's taxonomy supports an executable diagnostic report without becoming
a decision procedure for felicity. The six conditions are provisional and
necessary, Gamma applicability is conditional, failures can overlap, and
unknown observations cannot count as successful checks. Insincere achievement
and incidental effects must be represented separately. Determining the actual
conventions, circumstances and intentions remains outside this implementation.

Horn supplies a more directly expressible logical fragment. Q-qualified
non-use of a stronger expression gives ignorance, not negative actual-world
truth. The latter needs competence and actual-world accessibility in the
chosen epistemic reconstruction. Pragmatic division of labor can be executed
over a finite candidate domain once stereotypes and corresponding alternatives
are supplied. Neither the source's empirical interpretation restrictions nor
a general lexical-selection algorithm follows from that calculation.

These are different kinds of formalization boundary, not evidence that one
source is false or that its foundations necessarily require restructuring.

## Inventory disposition ledger

Names below are relative to the corresponding Coq file. Each declaration has
an individual source/new classification in its JSON record. Multiple labels
in a row deliberately separate the implemented portion from what remains.

| Target | Disposition | Evidence and limitation |
|---|---|---|
| D1 | illustrative reconstruction | `ContextualExample.absent_producer_can_still_be_read` and `producer_metadata_invariant_here`; producer metadata is ignored by construction, not proved irrelevant to all language or intentions. |
| D2 | illustrative reconstruction; new structural result | Agrammaticality/graft examples; `fresh_quote_beyond_any_finite_list` proves unboundedness of the added quotation syntax only. |
| D3 | illustrative reconstruction; boundary countermodel | `context_cannot_be_erased_from_this_interpreter`; `unbounded_quotation_can_keep_effect_constant` blocks an unwarranted inference from syntax to changing meaning. |
| D4 | conditional result; illustrative reconstruction | `repeatable_form_cannot_recover_both_origins` requires identical observed forms and distinct origins. Token identity, form equality and origin labels are supplied; `richer_evidence_is_not_ruled_out` is not an authentication algorithm. |
| D5 | illustrative reconstruction | `Risk.necessary_risk_coexists_with_success`; the added two-world model distinguishes necessary possible failure from every actual performance failing. |
| D6 | not statable in this signature | No definition/theorem for universal contextual non-saturation, dissemination, logocentrism or the philosophical critique of Austin. Not classified false, inconsistent or unmechanizable. |
| A1 | restricted representation; conditional result | `required`, `report_exact`, `failed_necessary_condition_blocks_felicity`; six condition labels, conditional Gamma checks and an explicit necessity premise. No automatic social-fact assessment. |
| A2 | conditional result; illustrative reconstruction | `misfire_blocks_intended_act`; separate achievement, `Cases.void_act_can_have_other_effects` and `breach_not_incomplete_execution`. No converse infers achievement from A/B success. |
| A3 | illustrative reconstruction | `Cases.insincere_promise_can_be_achieved`; achievement is supplied as part of the source example, not computed from the checklist. |
| A4 | illustrative reconstruction; new algorithm | `Betting.complete_trace_exact` and positive/negative examples characterize a strict isolated offer/acceptance exchange. A later event falls outside that recognizer; this is not a general procedure grammar or claim about undoing bets. |
| A5 | restricted representation; illustrative reconstruction | `report_exact` returns all failed labels; `Cases.simultaneous_failures` retains A2 and Gamma1. Alternative diagnoses of vague real cases are not decided. |
| A6 | new boundary countermodels; uncovered source scope | `unknown_is_not_success`, `no_report_complete_when_assessed` and `listed_conditions_are_not_sufficient`. The last adds an unmet requirement to disprove an unwarranted sufficiency inference, not Austin. Actual exclusions, uptake conditions and procedural laxness lack a general implementation. |
| A7 | illustrative reconstruction; uncovered general semantics | `Cases.truth_does_not_force_sincere_belief` separates truth and belief coordinates. It is an elementary countercase, not a semantics of assertion or a general account of Moore's paradox. |
| H1 | conditional result; added strengthening; countermodel | `q_yields_ignorance`, `negative_truth_needs_strengthening`, `ignorance_compatible_with_strong_truth`; relevance/norm observance and added epistemic premises remain visible. |
| H2 | direct logical fragment; conditional reconstruction | Q/R content incompatibility and cancellation; withdrawal of the interpreter's defaults restores literal content. Context/contour selection and actual default competition are not inferred. |
| H3 | direct logical fragment; restricted examples; empirical remainder | Descriptive-negation entailment, numeral exactness and cancellation. `logical_entailment_does_not_ban_r_rejection` challenges an entailment-only argument, NOT Horn's empirical restriction on readings of negated utterances. |
| H4 | conditional result; added executable interpreter | `finite_readings_exact`, `labor_disjoint_when_applicable`, `labor_covers_common_extension`; supplied common extension, binary stereotype and ordinary/counterpart conditions. Logical exhaustivity in this model is not an empirical exhaustivity result. |
| H5 | illustrative reconstruction; boundary tests | `Causatives` direct/indirect example; removing the corresponding alternative restores the direct case. No universal shorter-synonym blocking; correspondence and stereotypes are inputs. |
| H6 | not statable/implemented in this signature | No learned stereotypes, general Q/R weighting, grammaticalization or historical/empirical validation. Source reading was sections 1–11 pp.11–31, not the later diachrony/endnotes. |

No selected source claim is reported as refuted. No failed proof has been
hidden behind an axiom or admission. The non-formalized remainder is a scope
or representation limit here, not a demonstrated impossibility result.

## Mechanical checks and reporting

| Artifact | Proved declarations / globally closed | Triviality flags | Vacuity flags |
|---|---|---|---|
| Derrida1972 | 17 / 17 | 3 | 0 |
| Austin1962 | 20 / 20 | 5 | 0 |
| Horn1984 | 24 / 24 | 2 | 1 |
| Total | 61 / 61 | 10 | 1 |

All three were freshly compiled by `verify.py`; `Print Assumptions` reports
all 61 closed, with zero axioms, admissions, unsafe flags, unresolved names or
record-count disputes. Coq 8.20.1 kernel checking of the three modules and their
dependencies reports no axioms, type-in-type, unsafe fixpoints or assumed
positivity. The 77-file project build passes (incremental; the preceding
74-file build was checked in the prior revision).

Probe self-tests pass; all 61 declarations were probed with no bailouts.
The vacuity flag is `Horn1984.q_r_incompatible`: its *purpose* is to prove that
Q content and R content cannot hold together. The conjunction of its premises
is therefore intentionally inconsistent. The raw flag remains in the sidecar
and site; it is not a successful substantive inference from consistent
premises and is excluded from an unflagged-declaration count.

The ten triviality flags are definition/example checks. Other elementary
counterexamples or tautologies can escape the bounded probe. Therefore the
50 unflagged declarations are **not** a count of independently substantive
source claims, and 61 is only a raw checked-declaration count.

Eleven reporting/traceability regression tests pass. The pre-existing parser
emits file-handle ResourceWarnings during three parse checks; there are no test
failures. The claim lock grows from 890 to 951 entries, with no changed old
statements and no deprecations. The generated site has 230 papers, 77 records
and 9 edges; its inline JavaScript and JSON parse successfully. This is a
local build, not a deployment or browser interaction test.

## Coverage after this campaign

| Frozen intrinsic tier | F0 | F1 | F2 | F3 pilot | F4 | F5 |
|---|---|---|---|---|---|---|
| P0 | 9 | 9 | 1 | 1 | 0 | 0 |
| P1 | 23 | 21 | 1 | 2 | 0 | 0 |
| P2 | 19 | 8 | 1 | 2 | 0 | 0 |
| P3 | 17 | 29 | 6 | 4 | 3 | 0 |
| P4 | 18 | 21 | 8 | 11 | 6 | 9 |
| P5 | 0 | 0 | 0 | 1 | 0 | 0 |

There is now pilot contact in P0 as well as P1/P2. There are still **no F4/F5
papers in P0–P2**: the new contact does not close that stronger evidence gap.
All 230 IDs remain unique and all original survey/addendum/grade bytes are
unchanged. New links live in `paper_evidence.json`. Pending determinations
are excluded from prediction/outcome disagreements. Legacy admissions elsewhere
in the repository remain; the zero-admission claim concerns these three files.

This purposive three-source campaign cannot estimate a formality gradient or
resistance rate. Independent source review is the next gate before considering
any higher evidence status. TTR/MTT/Ranta/DTS expansion remains parked.

## Reproduction and checkpoint

From the repository root, with the existing local source corpus:

```sh
coq_makefile -f _CoqProject -o Makefile
make -j4
python3 atlas_data/verify.py atlas/discursive/Derrida1972.v atlas/pragmatics/Austin1962.v atlas/pragmatics/Horn1984.v
TMPDIR=/private/tmp/tiers-campaign.udHc5f python3 atlas_data/probes/run_probes.py atlas__derrida1972 atlas__austin1962 atlas__horn1984
coqchk -silent -o -R atlas '' discursive.Derrida1972 pragmatics.Austin1962 pragmatics.Horn1984
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 atlas_data/verify.py --lock
python3 tool/llm/signatures.py
ATLAS_PAPERS=/Users/graogro/Dropbox/formalizing_formal_semantics/papers python3 atlas_data/consolidate.py
python3 atlas_data/build_site.py
python3 atlas_data/check_checkpoint.py atlas_data/campaigns/tiers_2026_09_13_manifest.json --corpus /Users/graogro/Dropbox/formalizing_formal_semantics/papers
```

The `TMPDIR` above is this run's scratch location; use an existing temporary
directory of your own on another machine. The new hash manifest supersedes
the prior revision checkpoint for the shared README/project, evidence links,
claim lock, signatures and generated atlas/site files. The historical manifest
has deliberately not been rewritten: its old aggregate hashes no longer match
these expanded outputs. Prior comparison/pilot code and records are unchanged.
The new manifest also pins this campaign's protocol, source inventory, results,
code, records, checks and PDF hashes. Work is local and uncommitted; no push.
