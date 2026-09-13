# Rosch 1978 — bounded cue-validity and typicality result

2026-09-13. [Code](../../atlas/pilots/Rosch1978.v) ·
[source record](../records/atlas__pilots__rosch1978.json) ·
[pre-coding design](rosch_2026_09_13_design.md) ·
[frozen inventory](cohort2_2026_09_13_rosch_inventory.md).

The R2-03/R2-04 attempt is complete within its stated boundary: **25 checked
declarations, no axioms or admissions; whole-source determination unassessed**.
Rosch is now linked as a P1/F3 pilot in the local atlas. This is neither a
claim that Rosch transfers as-is nor evidence that restructuring is necessary.
The original protocol, inventories, grade file and earlier proofs are unchanged.

## What was established

For a finite observation sample, cue validity is represented by the number
of observations satisfying both category and cue divided by the number
satisfying the cue. The public optional interface returns no value for a
zero-frequency cue; a positive cue with no category overlap has value zero.
Repeated observations express frequency, not duplicate members of a set.

The principal boundary result is:

> For nested category extensions, the same positive-frequency cues and the
> same nonnegative weights make the containing category score at least as
> highly as the contained one. Therefore those assumptions cannot yield a
> strict interior maximum against a containing category.

This is a theorem about an encoding restriction, **not a refutation of Rosch**.
Local PDF pp. 5–6 explicitly connect category scores to the attributes of each
category. The source's sum uses unit weights; arbitrary nonnegative weights
are an explicit mathematical generalization in this pilot. Ties/weak maxima
are not excluded by the theorem.

The constructed furniture example makes that distinction inspectable:

| Compared score | Furniture | Chair | Kitchen-chair |
|---|---|---|---|
| Same three unit-weight cues for every category | 3 | 8/3 | Not needed for the parent/chair boundary check |
| Assigned category-specific cue lists | 1 | 2 | 1 |

The dataset consists of kitchen-chair, dining-chair, table and stone labels.
The assigned seat/back features are coextensive on the two chairs; support
is assigned to the three furniture items. Furniture receives the support cue;
chair and kitchen-chair receive seat/back cues. These are synthetic assumptions,
not measured feature frequencies, learned cue lists or published Rosch data.
The second row proves that *these supplied lists and counts* allow an interior
maximum; it does not explain why humans select the lists or validate a basic
level. Negative-weight and reversed-inclusion cases test the boundary's scope.

Typicality is kept separate from membership. A constructed bird example has
unequal typicality among members and two tied best members. It therefore does
not require a unique best item. The source motivates graded goodness, but the
numeric scale and robin/sparrow tie are assigned, not experimental findings.
The membership-separation countermodel only shows that an unconstrained rank
does not determine a classifier; its alternative membership is not a proposed
empirical account of birds.

## Same-content representation checks

- `Frequency.normalization_cancels`: with positive sample and cue counts,
  first normalizing counts to event frequencies and then conditioning gives
  the same ratio as conditioning the counts directly. Both routes use the
  same data; this does not compare independently fitted cognitive models.
- `Typicality.best_preserved_by_order`: with fixed membership, equivalent
  orderings on members preserve best-member status. The constructed example
  checks a directly specified ordinal relation against numerical scores and
  their positive affine rescaling. This preserves order, not psychological
  distances, response times, learning or representation mechanisms.

These are limited, proved representation correspondences. They are not
independent confirmation that the whole source has two faithful encodings.
Changing category-specific cue lists is a separate semantic sensitivity test,
not alternative-encoding robustness. Independent semantic review is pending.

## Disposition of every frozen target

| Target | Disposition in this attempt | Uncovered source commitment |
|---|---|---|
| R2-01 economy/perceived structure | Uncovered | No objective, effort measure or empirical world-structure account. |
| R2-02 basic level | Representation only | Three nested assigned predicates; no basic-level selection, common cut, four-measure convergence or knowledge-dependent prediction. |
| R2-03 cue validity | Conditional/source-linked fragment | Finite definition and fixed-cue boundary; no derived attribute selection or empirical maximum at the basic level. |
| R2-04 typicality | Illustrative model, with ordinal correspondence checks | Assigned membership/ranking and ties; no validation of human judgments. |
| R2-05 mechanism underdetermination | Uncovered | No pair of mechanisms evaluated on the chapter's observations. |
| R2-06 context | Uncovered | No contextual update or prediction of judgment changes. |
| R2-07 attribute formation | Uncovered | Explicit feature inputs do not explain their cultural/category dependence or origin. |
| R2-08 events/scripts | Uncovered | No event, memory or comprehension account. |

The groups are not independent, equally weighted observations and do not yield
a meaningful “2/8 formalized” success rate. R2-03 itself remains partial.
The frozen P1 rationale's “no formal apparatus” wording remains in tension
with the chapter's explicit probability definition; this discovered issue is
recorded without regrading. A paper-level tier does not classify every fragment.

## Mechanical checks and their limits

Coq 8.20.1 freshly compiles the file. All 25 theorem/helper/example declarations
were queried with `Print Assumptions` and close under the global context.
`coqchk` reports no axioms, unsafe fixpoints, assumed positivity or type-in-type.
Section carrier types become ordinary quantified arguments, not hidden axioms.
The semantic premises of the theorems, especially inclusion and positive counts,
still matter; closed proofs do not establish their empirical applicability.

The probe self-test passes all six expected judgments. All 25 declarations
were probed: **5 TRIVIAL, 0 VACUOUS, 0 bailouts**. The five flags are retained:

- `ConstructedCategories.fixed_cues_favor_parent`
- `ConstructedCategories.assigned_category_cues_allow_interior_maximum`
- `ConstructedCategories.undefined_is_not_defined_zero`
- `ConstructedCategories.negative_weight_breaks_monotonicity`
- `Typicality.ConstructedBirds.members_can_differ_in_typicality`

These are computations on assigned finite inputs, not five independently
verified source claims. Nor does an unflagged declaration automatically become
substantive: the simple membership-separation example is still a logical
illustration. The tactics are bounded probes, not a semantic grading procedure.
The populated hierarchy/admissibility example supplies a positive witness for
the monotonicity assumptions; zero-cue and assumption-removal cases are explicit.

All 29 Python reporting tests pass, including six new Rosch tests. The project
build covers 78 listed files (incremental build after a fresh Rosch compile).
Existing claim-comparison rendering tests still pass. A new generated-page test
checks Rosch's pilot/unassessed display, theorem mappings, probe flags and F3
paper association, with Hobbs and Spivak still F1. The papers table displays
the Coq filename; the theory record is reached through the theories view.
These are DOM-stub tests, not a
visual browser inspection. Existing verifier resource warnings were observed;
the pre-existing file-handle implementation was not changed in this task.

## Effort ledger and engineering notes

UTC tool-clock boundaries on 2026-09-13:

| Phase | Start | Boundary | Scope |
|---|---|---|---|
| Source/protocol and integration inspection | 16:40:05 | 16:42:51 | Rechecked frozen checkpoint and probability passage; full source reading was in the preceding stage. |
| Design, encoding, proof debugging and initial checking | 16:42:51 | 16:52:55 | New design/code; fresh compile, all-assumption checks and kernel check. |
| Probe correction and completed audit | 16:52:55 | 16:54:40 | Correct record-key selection; all 25 probes completed. |
| Record/reporting integration and initial tests | 16:54:40 | 17:01:19 | Record, project/evidence/signature additions, unit tests, build and local site generation. |

Encoding, proof debugging and the two representation checks were interleaved,
so this ledger does not invent a separate duration for each. Four proof-script
errors concerned case closure/application/constructor handling, not changes to
the mathematical claims. The first probe command selected a nonexistent short
key and matched zero declarations; that was not counted as validation. It was
rerun with `atlas__pilots__rosch1978` and checked against the 25-declaration
census. Final report/page tests and hash packaging follow the last boundary;
the manifest records their completion checkpoint.

Intervals include model/tool overhead and are not active human effort or a
controlled comparison with previous pilots. No independent reviewer participated.

## Reproduction and handoff

From the repository root (use a writable `TMPDIR` of your own if necessary):

```sh
coqc -R atlas '' atlas/pilots/Rosch1978.v
python3 atlas_data/verify.py atlas/pilots/Rosch1978.v
TMPDIR=/private/tmp/rosch-pilot.AorC8R python3 atlas_data/probes/run_probes.py atlas__pilots__rosch1978 --timeout 60
coqchk -silent -o -R atlas '' pilots.Rosch1978
coq_makefile -f _CoqProject -o Makefile
make -j4
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 atlas_data/verify.py --lock
python3 tool/llm/signatures.py
ATLAS_PAPERS=/Users/graogro/Dropbox/formalizing_formal_semantics/papers python3 atlas_data/consolidate.py
python3 atlas_data/build_site.py
node atlas_data/site/test_claim_comparison.cjs
node atlas_data/site/test_rosch_campaign.cjs
python3 atlas_data/check_checkpoint.py atlas_data/campaigns/rosch_2026_09_13_manifest.json --corpus /Users/graogro/Dropbox/formalizing_formal_semantics/papers
```

The new manifest supersedes only the shared integration outputs of the previous
checkpoint; its frozen protocol, inventories, index and historical manifest
remain intact. The old 951 locked claims and 25 prior signature entries are
unchanged; 25 Rosch statements and one signature are added. The existing
five-source claim-comparison profiles are not retrospectively rewritten.

No commit, push, mirror sync or deployment was performed. Next in the fixed
cohort order is Hobbs, after resolving the selected PDF's source-version gate;
Spivak remains inventoried but unimplemented. Do not silently replace either
source because this bounded Rosch fragment was tractable.
