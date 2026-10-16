# Montague in the Formal Atlas: review brief

For Robin Cooper and Rasmus Blanck

Checkpoint 7 | 8 October 2026 | Frozen review scope, not a published release

## The claim we propose to make

We have an inspectable implementation separating semantic syntax, object
derivations, model interpretation and metatheory, with checked connections
between them. The contribution is an auditable architecture and explicit
comparison conditions, not the discovery of familiar linguistic inferences.
Please assess whether the following bounded claims are faithful and useful.
No independent semantic-review endorsement is currently claimed.

## What is proved, and where to inspect it

1. **Explicit proof systems.** A source-informed C calculus has constructive
   rules and a separately enabled classical double-negation rule. Substitution
   preserves derivations; soundness has explicit premises. Inspect
   [Calculus.v](Calculus.v), `constructive_sound` and `classical_sound`, and
   [Structural.v](Structural.v), `derivation_substitution`.
2. **Models and a world-only translation.** Boolean interpretations include
   executable finite full internal function-space models. A specified
   implicit-world IL fragment translates into explicit-world Ty2 with
   interpretation preserved. Inspect [BooleanFinite.v](BooleanFinite.v),
   [Ty2Models.v](Ty2Models.v), and [ILTranslation.v](ILTranslation.v),
   `explicit_world_preservation`.
3. **The actual legacy implementation.** Every constructor and assignment of
   the existing IL evaluator is preserved in a separate Prop-valued target,
   retaining world/time indices, equality and tense. This is code-to-code
   preservation, not source adequacy. Inspect
   [LegacyTranslation.v](../montague_legacy/LegacyTranslation.v),
   `legacy_open_preservation`, against [PTQ_deep2.v](../PTQ_deep2.v).
4. **Restricted observational comparison.** The existing Boolean and Prop
   target evaluators agree on certified observations under related lexicons
   and assignments. Entity-witness agreement retains the same entity. Inspect
   [ObservationBridge.v](../montague_legacy/ObservationBridge.v),
   `observation_preservation` and `observation_entity_witnesses`. This has not
   been composed with every legacy translation.

## Walk through one inference and one countermodel

**Valid inference:** Every man walks; John is a man; therefore John walks.
Represent the premises as `forall x. man(x) -> walk(x)` and `man(john)`.
Instantiate the universal at John, then apply implication elimination.
This is an actual constructive object derivation, not just an implication
proved after evaluation. In
[ObservationExamples.v](../montague_legacy/ObservationExamples.v), inspect
`observed_instantiation_derivation`; `instantiation_agrees_for_all_tables`
then proves both semantic consequences for every paired lexical table.

**Countermodel:** Actual truth does not entail necessity. Take two worlds,
with weather true at the actual world and false at the other. Actual weather
is true, but universal-world weather is false in both paired interpretations.
Inspect `actual_truth_does_not_license_necessity` in the same file. This
refutes that inference under the stated semantics, not a restricted
necessitation rule. Both examples are synthetic tests, not new source findings.

# Assumptions and review decision

## What the foundations do and do not establish

Coq remains the constructive host and metatheory. An object calculus can
nevertheless have explicitly classical rules. General soundness uses function
extensionality (`FunExt`); classical soundness into the original Prop
interpretation also uses excluded middle (`ClassicalTruth`). Boolean
soundness instead uses reflected total quantifiers. Finite model construction
uses FunExt; the optional arbitrary-domain constructor uses
`ClassicalDecision`. Arrow domains are Coq function spaces, not a proved
external set-model representation or a Henkin construction.

Generic observation preservation needs no FunExt, but its finite examples
and derivation transfer do. The guard permits entity/world quantification
and one justified encoded-falsity case. Higher-order application and lambda
require related values; arbitrary proposition/predicate quantification and
unrestricted equality are excluded. Truth correspondence is logical
equivalence, not proposition identity. Requiring Boolean reflection for every
Coq proposition would imply excluded middle; that is a conditional boundary
theorem, not an assumption silently installed here.

We do not claim full PTQ adequacy, Gallin equivalence, Henkin completeness,
unrestricted Prop/Boolean model equivalence, strict constructive/classical
proof-system separation, or equivalence with MTT or TTR.

## Safeguards and evidence

The snapshot contains 249 named proved statements in 26 new Coq files,
fresh-build and kernel checks, per-statement assumption audits, and 37
rejected negative fixtures. Counts include supporting lemmas, not 249
linguistic discoveries. The actual legacy bridge retains old semantic
parameters; a closed global context elsewhere does not remove explicit
theorem premises. Development is AI-assisted: neither an AI judgment nor
successful compilation establishes fidelity to the linguistic source.
Source interpretation still needs your review. The [technical report](TECHNICAL_REPORT.md)
provides details, especially sections 8 and 13-17 and the complete inventory.

## Three questions for your review

1. **Source fidelity:** Does this encoding represent the intended C/selected
   Ty2 fragment? Check Chatzikyriakidis and Luo (2020), section 1.3.1,
   pp. 6-10, and Appendix A1, pp. 175-176. The added classical rule is our
   explicit extension. Identify any mistranslated rule, index dependency or
   unjustified attribution, with the source passage and code location.
2. **Model assumptions:** Are these internal models and explicit premises
   appropriate for the bounded paper claim? Distinguish an encoding defect
   from a stronger result requiring a different model class.
3. **Linguistic significance:** Are the selected observations meaningful for
   comparison? Which reading or witness distinction is essential but missing?
   Please identify a concrete case and the required observation.

## Decision and stopping rule

For each question, return **acceptable within scope**, **needs correction**,
or **out of scope**, with reasons. Freeze implementation during review.
Correct identified defects and repeat checks; publish a tagged snapshot only
after explicit approval. Further theories and stronger equivalence theorems
are separate work. This packet records no approval and has not been sent.

To reproduce, unpack the complete packet and run from its `proofs/` folder,
with Coq 8.20.1 and Python 3:

```sh
python3 deep/montague_core/check.py --check
python3 deep/montague_legacy/check.py --check
```

Source links refer to the enclosed files. `MANIFEST.json` pins the packet's
contents by SHA256; keep the folder structure when sharing it.
