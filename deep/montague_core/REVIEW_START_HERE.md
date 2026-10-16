# Montague checkpoint 7: start here

Prepared for Robin Cooper and Rasmus Blanck | 10 October 2026

This is a scientific review packet, not an approved release. The mathematics
is unchanged from the frozen checkpoint. Document dates identify their
editions, not different mathematical versions. No review endorsement is claimed.

## Reading order

1. [Two-page brief](Montague_Review_Brief_for_Robin_and_Rasmus_Checkpoint_7_2026-10-08.pdf):
   the positive claims, one inference, one countermodel and three review questions.
2. [Code-led walkthrough](Montague_Code_Walkthrough_for_Robin_and_Rasmus_2026-10-09.pdf):
   20 explanatory chapters, 62 exact excerpts and the complete 26-module
   source appendix. This is the main step-by-step explanation.
3. [Technical report](Montague_Proof_Theory_Report_for_Robin_and_Rasmus_Checkpoint_7_2026-10-08.pdf):
   the cumulative technical account and proof inventory, as supporting material.
4. [Review response](REVIEW_RESPONSE.md): record source fidelity, model
   assumptions and linguistic significance. Comments in another format are welcome.

Word versions of all three documents are included for annotation. Keep the
folder structure after unzipping so that relative links continue to work.
Source files are under `proofs/`; PDFs of copyrighted source books are not included.

## What is established

The implementation separates typed syntax, explicit object derivations,
model interpretation and metatheory. It checks soundness under stated
premises, structural transformations of derivations, interpretation-preserving
translations, and guarded agreement between Boolean and Prop interpretations,
including the identity of entity witnesses. The detailed documents state
the domain of each result; the bridges cannot all be composed unrestrictedly.

Coq remains the constructive host. Classical object rules are represented
explicitly; host assumptions and model contracts are separately visible.
These are internal models, not a proved external set-model representation
or a Henkin completeness result. Source fidelity requires scientific review.

## Reproduce

Requirements: Coq 8.20.1 (`coqc`, `coqchk` and `coqtop` on PATH) and Python 3.
The proof checkers use the Python standard library and the enclosed parser.
They build in temporary directories and compare against the frozen audits.

From this unpacked directory:

```sh
cd proofs
python3 deep/montague_core/check.py --check
python3 deep/montague_legacy/check.py --check
```

Expected: 173 core statements and 76 companion statements checked; both
kernel rechecks pass; 23 and 14 invalid fixtures are rejected, respectively.
These counts include supporting lemmas. They are not 249 linguistic results
and do not mean that every theorem is without assumptions.

To replay the interactive walkthrough, still from `proofs/`:

```sh
python3 deep/montague_legacy/check.py --check --inspect < ../WALKTHROUGH_SESSION.txt
```

The four Boolean computations return `true`, `false`, `true`, `false`.
For an editable session, omit the input redirection. Inspection uses a
temporary build, so save any experimental edits separately.

Fresh check logs for this assembled packet are in `checks/`. The earlier
walkthrough-session transcript is retained at the top level. `MANIFEST.json`
pins every delivered file; `provenance/` preserves both input manifests.
The archive's sibling `.zip.sha256` file pins the ZIP bytes.

## Review and next action

Please identify concrete defects by source passage and code location, and
distinguish corrections from requests for stronger results. Implementation
remains frozen during review. Correct identified defects and rerun the checks;
a tagged publication requires a separate approval. This packet does not
claim Gallin equivalence, full PTQ adequacy, completeness or equivalence with
MTT or TTR.
