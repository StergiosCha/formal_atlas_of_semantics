# Heim and DisCoCat: source-specific review drafts

Date: 2026-09-15. Baseline: `786e07b3f6f03c7b24212d8aad580f443ea9edfb`.
Status: **findings prepared for maintainer review, not approved paper outcomes**.

These reviews compare primary-source passages with the existing implementations,
rather than inheriting their file assessments. They find an incorrect donkey
translation and unsupported impossibility claims in the Heim-linked material,
and a substantive but narrower-than-advertised DisCoCat implementation.
Neither finding establishes that a source theory resists formalization.

| Source | Supported result | Proposed source-level disposition |
| --- | --- | --- |
| [Heim 1982, ID 7](heim_1982.md) | Predicate-valued comprehension is accepted without classical axioms; the existing donkey translation has different truth conditions. | Keep `review_required`; neither inherited slight nor major restructuring is justified. Implement the source's file/domain/felicity core before proposing a transfer outcome. |
| [Coecke–Sadrzadeh–Clark 2010, ID 159](discocat_2010.md) | Axiom-free rational categorical soundness and selected worked examples; raw similarity differs from normalized similarity. | Keep `review_required`; retain positive evidence, but do not endorse an unqualified `as_is` outcome yet. |

Reviewer: Codex, a single assistant performing retrospective source/code
examination. This is not a second independent agent, an authenticated human
review, or maintainer approval. The review did not author the baseline files in
this pass; it can see and is influenced by their existing assessments. That is
not a guarantee of independence from the project's earlier automated work.

The exact consulted PDF versions, inputs and review artifacts are pinned in
[manifest.json](manifest.json). No PDF is copied into this repository. Page
references use each consulted PDF's printed pagination, not another edition.
The Heim review examines specified dissertation sections, not every page of the
book. The DisCoCat review examines the local arXiv v1, not a separately checked
journal version. Code review focuses on definitions, claim statements, relevant
proofs and their dependencies; successful compilation is not a semantic audit of
every tactic or proof.

## Reproduce the diagnostic evidence

From the repository root, with Coq 8.20.1:

```bash
bash atlas_data/audits/source_reviews_2026_09_15/run_checks.sh
python3 atlas_data/check_checkpoint.py atlas_data/audits/source_reviews_2026_09_15/manifest.json --corpus /absolute/path/to/papers
```

The script copies the four reviewed files and the required Montague dependency
to a fresh temporary directory, compiles them, compiles
[ReviewChecks.v](ReviewChecks.v), prints dependencies and runs `coqchk` on the
result. Build logs are retained at the printed temporary path. Original `.v`
files, verification records and existing build artifacts are not overwritten.
The diagnostic file is deliberately outside `_CoqProject`: its seven lemmas
are audit evidence, not additional theory coverage or F-tier progress.

The dependency output matters: importing a file with axioms or admissions does
not mean every lemma uses them. The three donkey diagnostics depend only on the
entity/predicate signature, not the imported choice axioms, admissions or class
contradiction. The four similarity diagnostics are closed. `FCS.exists_ccp`,
`DisCoCat.F_deq` and `DisCoCat.meaning_deq` are also closed. The existing
`MorseKelley.class_comprehension_inconsistent` instead exposes the unrestricted
comprehension axioms responsible for that contradiction.

Executed on 2026-09-15 with Coq 8.20.1 / OCaml 5.2.1: all six copied modules
compiled, all seven diagnostic lemmas passed, and `coqchk` succeeded. The
existing September 13 outcome-audit checkpoint still matches all 144 hashes.

## Approval and implementation order

1. Review these findings and the proposed coverage boundaries. They do not
   enter `paper_outcome_reviews.json`; the registry remains empty.
2. Implement a separate, explicitly source-bound Heim core: file domain plus
   satisfaction set, domain invariance, partial/felicity-guarded updates,
   novelty/familiarity, and the correct donkey restrictor. Preserve old attempts
   as historical evidence, with links to this correction.
3. Complete the most concrete DisCoCat gaps: lexical negation computations,
   normalized versus raw similarity with zero-vector handling, and the Boolean
   relational case. State which version's numerical claims are being tested.
4. Reconcile the remaining representation/coverage choices, refresh file
   assessments through the normal review process, and submit any justified
   source outcome for maintainer approval under the [policy](../../OUTCOME_POLICY.md).

No P grades, F levels, survey predictions, historical records, site data or
accepted outcomes are changed by these drafts. These local changes have not
been committed, pushed or deployed as part of this review.
