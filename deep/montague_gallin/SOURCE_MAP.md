# Gallin: primary-source map and checkpoint boundary

Date: 2026-10-16. This directory extends the source-first PTQ development.
It does not replace or regrade an atlas record, amend a frozen PTQ source,
or identify Gallin's model classes with those of MTT or TTR.

## Source consulted

Daniel Gallin (1975), *Intensional and Higher-Order Modal Logic: With
Applications to Montague Semantics*, North-Holland Mathematics Studies 19.
The scanned edition lists ISBN 0-7204-0360-X and 0-444-11002-X.

Local file: `Dropbox/book_MTT/Chapter_1_2/Gallin_IL.pdf`.
SHA256: `5c8a00c4b02a53c3f49726aa7e6ccba3fff3c16b6db0ed4e75638877bc204209`.
159 PDF pages. Printed page n corresponds to PDF page n+11 in this copy.
The copyrighted PDF and extracted text are not included in the repository.

Consultation covered the preface, contents, section 2 (pp. 10-17), the
general-model definition and axioms at the start of section 3 (pp. 17-20),
and section 8 (pp. 58-63). The translation equations on printed p. 61 were
checked against a rendered page image because OCR missed several formulas.
This is AI-assisted source consultation, not independent human approval.
No claim is made to have audited the rest of the book or reconstructed its
completeness proofs. Hahn and Richter (2015) is not the primary evidence
for this checkpoint.

## Source-to-code mapping

| Passage | Implementation | Scope and choices |
|---|---|---|
| Section 2, pp. 10-11: IL types and terms | Existing `MontaguePTQ.Syntax` | Uses the actual corrected PTQ datatype, including its additional tense operators. De Bruijn indices replace named bound variables. |
| Section 2, pp. 12-13: standard domains and index-dependent constants | Existing `MontaguePTQ.Models`; `Types.domain_agreement`; `Translation.target_lex` | Boolean truth values and full internal Rocq function spaces. Constants are not frozen. |
| Section 2, pp. 13-16: intension, extension and necessity | `Translation.compile` cases `Up`, `Down`, `Box` | Intension binds an explicit index; extension applies it; necessity quantifies over every index. |
| Section 8, pp. 58-60: Ty2 types, terms and interpretation | `Types.gty`; `Target.gtm`; `Target.geval` | Three base types e, t, s. Gallin calls this two-sorted because entities and indices are the two sorts of individuals. |
| Section 8, p. 61, (i)-(vii): IL-to-Ty2 translation | `Translation.compile` | Variables retain their values. A constant of source type a becomes a target constant of type s -> a applied to the current index. Application, abstraction and equality are structural; Up/Down become abstraction/application. |
| Section 8, p. 62, Lemma 8.2.1 | `interpretation_preservation`; `open_preservation` | The checked analogue is preservation for every actual PTQ term and every source environment, in the constructed target interpretation. This also includes the declared tense extension. |
| Section 8, p. 62, Theorem 8.2 | `Examples.consequence_on_model_image` | A restricted consequence correspondence over source models and their constructed targets. It is not the book's theorem over all independent standard Ty2 models. |
| Section 2, p. 10, footnote 1: tensed English needs an extension | `index_future`, `index_past`; `Will`, `Has` compilation | The target s-domain is the existing PTQ world-time product. Named binary relations require the same world and earlier/later time. No additional logical tense constructor is introduced. |
| Section 3, pp. 17-20; section 8, pp. 59-63 | Boundary only | General/Henkin models, the axiomatic calculi, description principles D, and relative interpretations of those calculi are not implemented here. |

## Representation decisions

1. `Target.geval` is an independently written evaluator. It does not call
   `MontaguePTQ.Models.eval`. The source-to-target equality is proved by
   structural induction, not obtained by defining one evaluator in terms
   of the other.
2. `Types.domain_agreement` identifies the corresponding *internal*
   function-space types. Transport along these equalities gives inverse
   value maps. This is not a theorem identifying all external set-theoretic
   or Henkin models with Rocq types.
3. The target syntax is parameterized by signatures for constants and free
   variables. The translation instantiates those signatures with source
   constants and source free variables, plus two tense relations. Bound
   target variables may have any target type, including s.
4. Unlike Gallin's minimal primitive syntax, the target retains Boolean
   connectives and quantifiers as explicit constructors with their standard
   semantics. Syntactic elimination of these constructors into lambda,
   application and equality has not been checked at this checkpoint.
5. The target interpretation uses the PTQ frame as its entity/index carrier.
   Therefore inhabitation and the linear-time structure remain available.
   This implementation has no independent general-model record yet.
6. Boolean reflection and function extensionality remain explicit fields
   of the source model. No new global axiom is declared. A `Print
   Assumptions` result of closed does not remove these theorem inputs.
7. Free-variable assignments are arbitrary, not selected examples.
   `canonical_environments_match` constructs a matching target environment
   for every source environment, so the preservation premise is not vacuous.

## Existing PTQ results used

`Examples.english_interpretation_preserved` composes the new result with
`MontaguePTQ.Meaning.closed_translation_interpretation` for all implemented
English analysis trees and all categories. The temperature test reuses
the established English trees and the model satisfying all nine PTQ
meaning-postulate families. It does not replace them with hand-written
target formulas or assumed countermodel conditions.

The checker pins every imported PTQ module against the existing
`montague_ptq/verification.json`. The original source audit and the existing
limits of grammar coverage continue to apply.

## What follows, and what does not

Preservation of values, truth, and counterexamples follows for every source
term in every constructed interpretation. Consequently, entailment agrees
when quantified over the same source model class and its image. The model
restriction can be `admissible`, retaining all PTQ meaning postulates.

This does not yet prove Gallin's full Theorem 8.2, a reverse translation,
proof-system correspondence, description principles, or Henkin completeness.
The next mathematical step is to specify independent target models and
prove the appropriate model correspondence, with the tense relations and
the source-image restriction stated explicitly. Eliminating the extra
connective constructors is a separate syntactic fidelity task.
