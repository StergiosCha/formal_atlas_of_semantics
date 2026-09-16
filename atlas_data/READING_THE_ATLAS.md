# Reading the atlas responsibly

Formal Atlas investigates what mechanizing a semantic theory requires. It
connects sources, encodings, proofs and comparisons without treating them as
interchangeable kinds of evidence. Start with the [selected results](../README.md#selected-checked-results)
or [browse the site](https://orange-beach-0c447e210.5.azurestaticapps.net).

## Two axes, not a whole-theory verdict

**P0–P5** records a source's intrinsic formality, from discursive prose through
systematic prose, semi-formal presentation, formal fragments and a full formal
system to a machine-checked artifact. The [rubric](FORMALITY_RUBRIC.md) and
[grades with rationales](formality.json) are frozen survey inputs.

**F0–F5** records progress through this project's evidence pipeline: surveyed,
sourced, designed, piloted, formalized, verified/connected. These labels depend
on linked artifacts and project checks. F5 is not a certificate that an entire
source has been faithfully mechanized, and F0 is not evidence that it cannot be.
Neither axis measures philosophical importance or empirical adequacy.

## Read the statement, scope and assumptions together

A proved theorem establishes its stated conclusion for the encoded definitions
and hypotheses. It does not automatically establish that those definitions
capture every source claim. Counts include helper lemmas, conditional results
and diagnostic examples; they are not counts of independent linguistic results.

The admission-free CI gate applies to the newer `atlas/` layer. Legacy material
retains admissions and parameters. Check the mechanical records, dependency
assumptions and scope of the particular artifact, not just its compilation flag.

In particular:

- The theorem named `kratzer_equals_montague` compares specific modal clauses
  under an induced accessibility relation. It is not an equivalence of complete
  frameworks.
- The TTR → MTT comparison fixes a model and a selected construction. Its
  witness-erasing subject projection has no inverse. Cooper's explicit model
  layer is not identified with MTT's architecture.
- The typed DTS implementation has stated fragment/search boundaries. Incomplete
  coverage does not establish that DTS necessarily requires restructuring.
- The Heim policy comparison derives consequences of candidate commitments.
  It does not select a default pragmatic policy or establish empirical adequacy.
- Derrida, Austin, Horn and Rosch pilots encode bounded fragments and diagnostics.
  Their checked examples do not amount to whole-book formalizations.

## File assessments and source outcomes

A file assessment describes an implementation attempt. Several files linked to
one source can have different scopes, assumptions and recorded assessments.
Those differences are not, by themselves, contradictions in the source or
evidence against the survey prediction.

Source-level outcomes require explicit source-specific review under the
[outcome policy](OUTCOME_POLICY.md). The [review registry](paper_outcome_reviews.json)
currently contains no accepted reviews. “Source review pending” means that
recorded candidate evidence still needs review; “unassessed” is not a negative
finding. An unfinished implementation alone cannot establish necessary
modification or restructuring of a theory.

Development is LLM-assisted. Source comparisons may be assistant-produced;
consult their recorded provenance. Multiple agent passes do not constitute
independent human semantic review. Maintainer approval and independent review
are separate from compilation and from each other.

## Reproducibility and source access

There are three distinct operations:

1. **Build the proof artifacts.** Use the tested Coq 8.20.1 toolchain and the
   [build instructions](../README.md#reproduce-the-checks).
2. **Rebuild the presentation.** `python3 atlas_data/build_site.py` consumes
   the checked-in `atlas.json`; it does not require external PDFs or recompute
   grades and outcomes.
3. **Recompute the consolidated evidence.** `consolidate.py` reads the records
   and an external source corpus selected through `ATLAS_PAPERS`. Currently,
   F1 uses surname/year filename matching and F2 uses surname tokens in design
   documents. Without the same inputs, these levels are not reproducible.

Campaign manifests already pin selected repository artifacts and external PDF
hashes, for example the [September revision](audits/revision_2026_09_13_manifest.json)
and [Heim policy checkpoint](campaigns/heim_1982_policy_manifest.json). They are
historical checkpoints, not promises that later presentation edits leave every
recorded file byte-identical. Preserve their original hashes when documenting
subsequent changes.

The remaining corpus-wide work is an explicit source registry connecting source
IDs to bibliographic identifiers, exact editions, artifact hashes, passages
consulted, reviewer provenance and design/claim bindings. DOI/ISBN identity,
byte-level PDF identity, recorded consultation and availability in a particular
checkout are different facts. The registry must replace heuristic evidence
matching, not merely supplement it. Missing metadata must remain missing rather
than be inferred as if verified. Copyrighted PDFs are not redistributed here.

## Campaigns and correction history

- [TTR, MTT, Ranta and DTS audit](audits/ttr_comparison.md): model-layer repairs,
  restricted translations, source passages and withdrawn DTS outcomes. Also
  records the surname-substring design-detection bug and corrected F2 badges.
- [September 13 revision](audits/revision_2026_09_13.md): typed DTS resolution,
  four shared constructions and the [P1/P2/P3 pilot](campaigns/pilot_2026_09_13_results.md).
- [P0/P1/P2 campaign](campaigns/tiers_2026_09_13_results.md): Derrida, Austin and
  Horn pilots; [claim comparison](campaigns/claim_comparison_2026_09_13.md)
  distinguishes represented examples, source-linked fragments, added commitments
  and uncovered claims. No tier gradient is established.
- [Second cohort](campaigns/cohort2_2026_09_13.md) and [Rosch pilot](campaigns/rosch_2026_09_13_results.md):
  frozen Spivak/Rosch/Hobbs inventories, finite cue validity and
  membership/typicality separation. Rosch's pilot does not derive a psychological
  basic level; Hobbs's local source version needs identification and Spivak has
  not been implemented in that campaign.
- [Outcome-flag audit](audits/outcome_flags_2026_09_13.md): removal of automatic
  “survey call disputed” badges inherited from file assessments. Earlier
  aggregate transfer claims based on those outcomes are not established results.
- Heim 1982: [implementation and requirements](campaigns/heim_1982_results.md),
  [binding/modal/proxy integration](campaigns/heim_1982_integration_results.md)
  and [explicit policy comparisons](campaigns/heim_1982_policy_results.md).
  These retain open pragmatic choices and withhold a whole-dissertation outcome.

To propose corrections, follow [CONTRIBUTING.md](../CONTRIBUTING.md). A proposal
does not edit the deployed site directly or bypass maintainer review.
