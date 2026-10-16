# Formal Atlas of Semantics

**A short overview for Robin Cooper and Rasmus Blanck**

Discussion draft | 16 October 2026

## The question

What must be made explicit to implement a semantic theory in a proof assistant,
and what must a translation preserve for a comparison between theories to be
meaningful? The atlas connects source passages, implementation choices, checked
results and remaining obligations. It distinguishes checking a proof from
establishing that its definitions faithfully represent the source.

## The wider atlas

The project connects a 230-source survey with selected Coq implementations,
source-to-code audits and comparisons. It records a source's presentation style
separately from the evidence accumulated by the project; neither is a measure
of theoretical truth or linguistic importance. Existing case studies include
TTR witness information, typed DTS resolution and Heim accommodation policies.
They concern specified fragments and assumptions, not equivalences of whole
frameworks. The public interface provides access to proof sources and a live
Coq workspace. The newer Montague work below is presented in a separate research
area, without changing the atlas's existing assessments.

## The source-first Montague case

A new development follows Montague's PTQ (1973), including the consulted
reprint's editorial corrections. It separates typed English analysis trees,
typed intensional-logic expressions and interpretation in an explicit model.
Four results illustrate the approach:

1. **Translation and interpretation agree.** The recursive T1-T17 translation
   and an independently defined interpretation of English analysis trees give
   the same denotation, for arbitrary typed trees and related assignments.
   This is a general correspondence theorem, not just agreement on examples.
2. **Model restrictions are explicit.** Models have inhabited entity, world
   and time domains, ordered time and Boolean truth values. All nine PTQ
   meaning-postulate families are represented as object-language formulas.
   Their satisfaction is proved equivalent to the encoded admissibility
   conditions. Model existence is established under explicit foundational
   assumptions, described on the next page.
3. **Countermodels satisfy the postulates.** An admissible model makes the two
   premises of the temperature argument true and its conclusion false. The
   formulas are obtained by translating English analysis trees. Further
   examples separate quantifier scopes and referential/nonreferential readings.
4. **Source checking can correct successful code.** An earlier encoding gave
   IVs the wrong result type and restricted necessity to the current time.
   Both definitions type-checked. Comparison with PTQ corrected IV/CN types to
   individual concepts -> truth values, and necessity to all world-time pairs.

## One example to keep in view

The temperature is ninety; the temperature rises; therefore ninety rises.
In the countermodel, the temperature concept picks entity a at the first time
and b at the second. The concept denoted by ninety constantly picks a. The
rising predicate distinguishes the concepts although their current extensions
agree. The checked result reconstructs a familiar source analysis; it is not
a new linguistic discovery or an empirical model of temperature change.

# What is checked, and what needs discussion

## Guarantees and their boundaries

**Proof checking.** The developments have isolated compilation, kernel
rechecking, theorem-signature and assumption audits, and deliberately invalid
test cases. These check consequences of the supplied definitions. LLMs assist
with code and drafting; they are not the verifier, and neither model agreement
nor successful compilation establishes source fidelity.

**Foundations.** The general PTQ interpretation assumes Boolean reflection
and function extensionality explicitly. Boolean reflection converts arbitrary
propositions into truth values and entails excluded middle; it is not an
executable decision procedure for arbitrary higher-order truth. Function domains
are full Coq function spaces. Their use does not by itself prove correspondence
with an independently formalized external set-theoretic model class. Coq remains
the host and metatheory; classical commitments are recorded, not eliminated.

**Source correspondence.** The source map records passages, editorial choices
and implementation locations. Independent semantic-review approval has not yet
been obtained. The grammar audit proves that two printed coordination strings
are not generated under the implemented literal S4/S12 rules. A separately
labelled inflection amendment restores them. The reading study certifies its
registered candidates and discovered analyses, but does not prove exhaustive
coverage of all possible readings. These distinctions remain visible rather
than being folded into a claim of complete PTQ adequacy.

## Why Gallin is the proposed next step

A separate workbench already translates a selected world-only IL fragment into
an explicit-world Ty2 language and proves interpretation preservation. It does
not yet connect the new source-first PTQ implementation to Gallin's full system;
the relevant passages and equivalence theorem in Gallin's monograph still need
direct audit.

The proposed next result is a translation of the actual PTQ implementation into
a source-audited explicit-index target, with a general interpretation-preservation
theorem and specified model correspondence. World/time treatment and any
extension beyond Gallin must be labelled. Equivalence of consequence relations
requires suitable model coverage, not just agreement in paired examples;
expressive equivalence would additionally need the relevant reverse translation
and recovery results. This is a proposed milestone, not a result already obtained.

## Two questions for discussion

1. Does the separation of object language, interpretation, foundational
   assumptions and source review address the methodological concerns we
   discussed? Which source distinction or model condition needs more attention?
2. What should the PTQ/Gallin comparison establish to be theoretically useful:
   interpretation preservation, correspondence of consequence relations, or a
   stronger result? Which model classes should that comparison use?

At this stage, feedback on these choices would be most useful. Detailed code and
reports can be supplied for whichever part interests you; a whole-codebase
review is not requested.

## Optional follow-up

Research area: [Montague research](https://orange-beach-0c447e210.5.azurestaticapps.net/#/research).
Three useful entry
points in `deep/montague_ptq/` are `Meaning.v` (`translation_interpretation`),
`PostulateFormulas.v` (`compiled_postulates_exact`) and `Examples.v`
(`temperature_countermodel`). Their sources can be read and downloaded in the
research area; live execution of these new packages is not yet enabled in the
public worker. This overview records no reviewer endorsement.
