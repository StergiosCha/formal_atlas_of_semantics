# Scoped comparisons, not a theoretical similarity metric

The 2026-09-25 presentation correction retires the mean of ordinal edge grades
and pair-specific Jaccard overlap as active comparison scores. No new theorem,
source-level assessment or theoretical equivalence is established by this change.

## What each profile records

- The declared fragment and observations being compared.
- Representation choices and the direction of the scoped relationship.
- Existing named fragment evidence, linked to the actual Coq source.
- Limitations, information loss and outstanding questions.
- Five theory-level obligations: compositionality, preservation, reflection,
  model coverage and recoverability. All remain **unassessed** in this initial
  migration. A relevant fragment lemma can exist without settling the general
  obligation. Unassessed is neither false nor impossible.

Profiles in [edge_profiles.json](edge_profiles.json) are editorial restatements
of existing artifacts, not new independent source readings. Supporting code
hashes and recorded theorem fingerprints are checked by
[edge_profiles.py](edge_profiles.py). This checks traceability and staleness,
not whether the prose is a correct interpretation of a theorem or source.
Read each statement, premises and assumption audit in the proof reader.

## Why the previous scores were retired

The 0–5 categories mix definitional agreement, equivalence, mediated maps,
counterexamples and re-encoding. Their numerical separation has no justified
metric interpretation. A necessary re-encoding is not demonstrably farther
than divergent predictions. Pair-specific checklists do not supply a common
space on which distances could be compared.

PTQ–Lambek's former 5/5 summarized four selected denotational equalities; it
did not identify their architectures. The TTR–MTT comparison fixes a model
pointwise, translates the man-runs construction and exhibits loss under the
subject projection. It does not rule out other translations or establish
equivalence of the full theories. Lambek–DisCoCat has no Coq bridge yet;
its former grade 3 annotations are not a verified mediated translation.

The PTQ–MTT selection-restriction grade is a prose observation, not a proved
impossibility. Generalized-quantifier conservativity must not be confused with
conservative interpretation of a theory.

## Reading the graph and counts

Positions are editorial. Lines have uniform width and opacity. A solid line
means a comparison file is listed; a dashed line means no bridge file is listed.
Neither line style certifies theoretical equivalence or a completed translation.

Shared/listed counts concern only the original pair-specific checklist. They
are not success rates, empirical coverage or inventories of a theory's expressive
power. One-sided entries can include source descriptions of unimplemented work.
Missing entries and missing bridges must not be interpreted as impossibility.

## Historical compatibility and preservation

Original `edges/*.json` files and their annotations are unchanged. In generated
`atlas.json`, the former `_computed` object is renamed `_legacy_scores`; its
values remain reproducible solely for historical audit. New `_profile` data
contains the scoped presentation and descriptive checklist counts. Consumers
must not read `_legacy_scores` as an active metric. The site shows them only
under a collapsed, explicitly retired annotation-history section.

The preservation test reverses just this schema change and checks the complete
historical atlas hash against the pinned pre-migration baseline. Papers, P/F
grades, outcomes, proof records and original edge annotations are not exempted.
Coq sources, assumptions and the claim lock are unchanged. Existing F-tier
rules are also unchanged; this correction does not introduce a new F policy.

## Next research phase

Define source-grounded comparison contracts: languages, judgments, admissible
models and observations; then specify translations and prove the obligations
within an explicit fragment. Distinguish observational agreement from structural
equivalence. Two directional translations alone do not establish equivalence:
their round trips must satisfy specified compatibility conditions. Investigate
TTR, MTT and Ranta first, with DTS resolution treated as a separate dimension.
No scalar replacement or automatic promotion is authorized by this migration.
