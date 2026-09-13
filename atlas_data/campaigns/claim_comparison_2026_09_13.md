# Comparing what transfers from a source into Coq

This is a retrospective, single-researcher comparison of five existing pilots,
added after their code and results were available. It is not a new preregistered
experiment or an independent semantic review. The prior protocols, source
inventories, results and hash manifests remain unchanged.

The local site's **Claim comparison** page (`#/comparison`) compares the
profiles and expands each source-target ledger. The same profile appears on
each relevant theory page; the paper list links to it beneath F3. Structured
data live in `claim_comparison_2026_09_13.json`. No P grade, F level or
source-theory determination is changed by these annotations.

## Observed differences, not a tier success ranking

| Source | What we can substantiate in this attempt | What must not be inferred |
|---|---|---|
| Derrida, P0 | Source-motivated illustrative models and a conditional form/origin information-loss result | Quotation syntax or a chosen interpreter proves universal contextual non-saturation |
| Austin, P1 | Representation of a non-exclusive taxonomy and conditional necessary-condition consequences | Successful diagnostic code decides felicity, or the insincere-promise example independently derives achievement |
| Horn, P2 | Direct logical consequences of weaker/stronger content relations, plus conditional pragmatic reconstructions | Logical entailment alone determines pragmatic interpretation or validates the added stereotype partition |
| Grice, P1, existing-pilot cross-check | Conditional constraints and opt-out/non-entailment examples | The garage belief was independently inferred from the maxims: compatibility was defined to require that belief |
| Tarski, P2, existing-pilot cross-check | A restricted recursive satisfaction construction with structural assignment-invariance results and T-instances | A complete natural-language truth theory, undefinability proof, or classical bivalence result was established |

This gives a substantive contrast between **representation**, **conditional
reasoning**, and **source-constrained construction**. They are not exclusive
ranks assigned to authors: Derrida also has a conditional lemma; Horn also
has illustrative models. Grice and Tarski were already implemented and known
to the assessor, so their inclusion is an exploratory cross-check, not held-out
confirmation. Tarski and Horn also show that a shared P2 grade does not predict
one uniform kind of formalization.

## Units and evaluation rules

The original D1–D6, A1–A7 and H1–H6 inventory groups are retained. They bundle
claims, examples and scope boundaries of different sizes; do not divide the
number of successful groups by 19 to report a formalizability rate. G1–G4 and
T1–T4 are retrospective labels for the earlier narrative inventory, not newly
discovered preregistered atomic claims. There are 27 displayed groups across
five profiles, not 27 equally weighted hypotheses.

Each group records the source statement/topic and pages, its disposition,
what was established, named Coq evidence, and what remains uncovered. Helper
theorems do not become additional source claims. A theorem referring to an
inventory group is not automatically a proof of the group's whole claim.

The dispositions are qualitative:

- **Representation only:** a distinction or assigned case is encoded; its
  correct representation is not an independent prediction.
- **Conditional fragment:** a named conclusion follows with explicit premises;
  the profile states which premises the source supplies and which we add.
- **Direct logical fragment:** a source-specified inferential relationship can
  be expressed directly; this does not establish a complete pragmatic theory.
- **Illustrative model:** a chosen mathematical model illustrates a reading;
  it does not verify the source's universal philosophical or empirical thesis.
- **Restricted construction:** a source-motivated general construction is
  implemented with stated language/domain restrictions.
- **Mixed:** the group contains established and uncovered portions; inspect
  both instead of converting it into a success.
- **Uncovered:** no source result established in this attempt; this is not a
  verdict of falsehood, inconsistency or impossibility.

## Added commitment versus ordinary parameter

A formal account may legitimately quantify over a domain, predicates, context,
accepted conventions or sincere intentions. It does not need an algorithm
that discovers every fact about the world. Such inputs are not automatically
defects or evidence of underspecification.

The meaningful question is whether an encoding choice adds semantic content
on which the desired conclusion depends. Examples here include ignoring
producer metadata in Derrida's interpreter, assigning promise achievement in
Austin's example, fixing the stereotype partition in Horn, and identifying
compatibility with the desired belief in Grice. Tarski's restricted language
and named snow object are disclosed limitations, while arbitrary predicate
interpretations are ordinary model parameters.

No scalar "reconstruction cost" is assigned. Counting every helper definition
or parameter would confuse engineering convenience with semantic change.

## Preservation and robustness

Examples are classified in prose as supplied/represented versus derived.
Source counterexamples and newly invented boundary checks are distinguished.
For instance, the code checks Austin's supplied insincere-promise case; it
does not use it as independent confirmation of the achievement claim.

Every profile records **alternative-encoding robustness: not tested**. Horn's
counterpart withdrawal, Austin's information refinement, Derrida's quote-depth
test and Tarski's assignment invariance concern one chosen representation.
They are useful tests, but not comparisons between two plausible encodings
of the same source claim.

A future robustness test must hold the source claim and its interpretation
fixed, spell out two independently defensible encodings, and test whether the
relevant conclusion survives. Merely choosing an arbitrary contrary model
would not show that the source itself is unstable.

## What would test the tier hypothesis

The non-circular hypothesis is that intrinsic formality predicts greater
source-faithful central-claim coverage with fewer added semantic commitments,
under comparable scope and effort. Merely observing more notation in higher
tiers repeats the rubric and is not an outcome test.

Before a new confirmatory attempt, freeze source selection, selected sections,
atomic central claims, positive/negative cases, semantic-addition criteria and
effort logging. Preserve failures and uncovered claims; do not replace difficult
sources or introduce a success denominator after seeing results. Report topic
and scope differences, assess sensitivity to alternate encodings, and seek
independent source review before promoting any whole-source determination.

Metadata-only follow-up candidates found locally are Spivak 1988 (ID196, P0),
Rosch 1978 (ID122, P1) and Hobbs 1985 (ID101, P2). They are **candidates, not a
frozen or completed second campaign**; no new source-body reading or Coq work
on them is claimed here. They would broaden author coverage, not provide a
topic-matched control. Clark 1996 (ID182, P2) has a design/evidence entry but
no matching PDF was found in the local corpus; F2 alone must not be taken as
proof of source availability.

## Implementation and verification

The comparison loader checks paper/record links, frozen P grades, target
uniqueness, referenced theorem names and SHA-256 hashes of the five Coq files.
Stale or malformed profiles fail the build rather than silently disappearing.
The overlay is separate from evidence-level and determination calculation.

The 23 Python regression tests pass, including a Node-rendered-view test for
the comparison route, five theory pages, F3 links, all 27 groups, text escaping
and the no-profile fallback. These use a minimal DOM stub, not a visual browser
test. Existing parser file-handle ResourceWarnings remain unrelated test
warnings. The generated site's inline script executes in the test harness and
its JSON parses. The 77-file incremental project build also passes; no Coq code,
theorem statement, mechanical sidecar or claim-lock entry was changed here.

Rebuild and check from the repository root:

```sh
ATLAS_PAPERS=/Users/graogro/Dropbox/formalizing_formal_semantics/papers python3 atlas_data/consolidate.py
python3 atlas_data/build_site.py
python3 -m unittest discover -s atlas_data -p 'test_*.py'
node atlas_data/site/test_claim_comparison.cjs
make -j4
python3 atlas_data/check_checkpoint.py atlas_data/campaigns/claim_comparison_2026_09_13_manifest.json --corpus /Users/graogro/Dropbox/formalizing_formal_semantics/papers
```

The new checkpoint supersedes prior aggregate/build hashes, not historical
claims about what the earlier checkpoints contained. Historical manifests,
all 230 frozen grades, original survey/addendum inputs and source records are
preserved. Changes remain local; no commit, push or deployment.
