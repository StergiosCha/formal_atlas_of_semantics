# Gallin: primary-source map and checkpoint boundary

Date: 2026-10-16. This directory extends the source-first PTQ development.
It does not replace or regrade an atlas record, amend a frozen PTQ source,
or identify Gallin's model classes with those of MTT or TTR.

Current checkpoint: 5. Checkpoints 1-4 remain in commits `fb4d9db`,
`f8543aa`, `f26c278` and `503e035`, respectively.

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
Checkpoint 3 rechecked the logical abbreviations on pp. 15-16 and their
use in Ty2 on p. 60. The conjunction on p. 15 was checked visually against
the scan, not reconstructed from the garbled OCR alone.
Checkpoint 4 reread pp. 59-63, particularly the standard-model definition,
Theorem 8.2 and its interpretation lemma, to separate the arbitrary-index
untensed result from the previous tensed PTQ specialization.
Checkpoint 5 checked the rendered image of p. 60 for A1-A3, AS4 and R,
including the variable types, equality signs and the occurrence restriction
on R. The formalization is a typed, locally indexed theorem calculus;
no equivalence with a separate named proof implementation is claimed.
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
| Section 2, pp. 15-16; section 8, p. 60: logical abbreviations | `Minimal.ctrue`, `cfalse`, `cneg`, `cand`, `cimp`, `cor`, `call`, `cex` | Beta-reduced applications of Gallin's definitions. Fresh function binders in conjunction use proved capture-avoiding weakening. Boolean biconditional is equality at type t. |
| Section 8, p. 59: four numbered formation rules covering five term forms | `Minimal.ctm`; `ceval`; `elimination_preserves_interpretation` | Six constructors because bound and free variables are represented separately. The evaluator has no primitive connective or quantifier clauses. Elimination preserves every rich target term over arbitrary signatures, carriers and environments, given BooleanTruth and FunExt. |
| Section 8, pp. 60-62: standard interpretation and translation | `MinimalCorrespondence` | Composes primitive-syntax elimination with the existing PTQ proofs, including open terms, English trees, target-side postulates, entailment, satisfiability and the admissible countermodel. The temporal/model restrictions remain those of checkpoint 2. |
| Section 2, pp. 10-16: untensed IL syntax and standard semantics | `Untensed.itm`, `idomain`, `il_model`, `ieval` | Independent syntax with no Will/Has, an embedding into the actual PTQ datatype, arbitrary inhabited E/I, and independently specified semantics. The connectives and Box have their usual source semantics; the target eliminates them. |
| Section 8, p. 62, Lemma 8.2.1 over arbitrary D and I | `UntensedTranslation.untensed_interpretation_preservation` | All open terms, bound environments and free assignments. Reuses the actual compiler, with no temporal-symbol assumptions. Separate value-domain recursors are related by proved transports. |
| Section 8, p. 62, Theorem 8.2(i)-(iii) | `UntensedModels.untensed_standard_validity`, `untensed_standard_consequence`, `untensed_standard_satisfiability` | Bidirectional standard-semantic correspondence for the implemented IL and target signature, arbitrary inhabited internal entity/index domains and predicate-defined theories. No temporal coherence or PTQ postulates. Minimal s -> t target terms are applied to the arbitrary index i, representing A* under assignment x_s/i. |
| Section 8, p. 61, (i)-(vii): IL-to-Ty2 translation | `Translation.compile` | Variables retain their values. A constant of source type a becomes a target constant of type s -> a applied to the current index. Application, abstraction and equality are structural; Up/Down become abstraction/application. |
| Section 8, p. 62, Lemma 8.2.1 | `interpretation_preservation`; `open_preservation` | The checked analogue is preservation for every actual PTQ term and every source environment, in the constructed target interpretation. This also includes the declared tense extension. |
| Section 8, p. 62, Theorem 8.2 | `Examples.consequence_on_model_image` | A restricted consequence correspondence over source models and their constructed targets. It is not the book's theorem over all independent standard Ty2 models. |
| Section 8, pp. 59-62: standard models and preservation across model classes | `Independent.standard_model`; `embed_model`; `reconstruct_model`; `Correspondence.admissible_consequence_correspondence` | The independent standard record has arbitrary inhabited entity/index types. The full PTQ comparison covers independently chosen valuations on declared world-time frames, with explicit temporal coherence and translated postulates. This is the tensed, restricted analogue, not all of Gallin's Theorem 8.2. |
| Section 2, p. 10, footnote 1: tensed English needs an extension | `index_future`, `index_past`; `Will`, `Has` compilation | The target s-domain is the existing PTQ world-time product. Named binary relations require the same world and earlier/later time. No additional logical tense constructor is introduced. |
| Section 8, p. 60: A1, A2, A3 and AS4 | `Calculus.axiom1` through `axiom4`; `Ty2Axiom`; `Substitution.csubst` | A1-A3 admit contextual and named variables, not arbitrary compound terms as primitive instances. AS4 uses typed capture-avoiding substitution. All displayed logical operations expand into minimal syntax. |
| Section 8, p. 60: rule R | `Substitution.ccontext`, `plug`; `Calculus.Derivation` | One occurrence can be replaced, including under lambdas. Binder declarations are not term positions. The equality derivation is valid at every hole environment. No local-hypothesis-to-global-theorem rule is added. |
| Section 8, pp. 59-60: standard semantics and the Ty2 calculus | `ty2_axioms_sound`, `ty2_derivations_sound`, `standard_model_derivation_soundness` | Soundness by induction on explicit derivation trees. Full internal function spaces and explicit BooleanTruth/FunExt inputs. This is not the generalized completeness asserted on p. 60. |
| Section 8, pp. 61-62: translate formulas and compare their meanings | `CalculusConnections.derived_il_translation_is_valid` | An actual target derivation implies IL semantic validity via the existing translation. A concrete translated-reflexivity proof tree is supplied. This does not construct an IL-to-Ty2 proof translation. |
| Section 3, pp. 17-20; section 8, pp. 59-63 | Remaining boundary | The source IL calculus, general/Henkin models, description principles D, relative proof interpretations and completeness are not implemented here. |

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
4. The intermediate `gtm` syntax retains convenient logical constructors.
   The final `ctm` syntax does not. `eliminate` replaces them by Gallin's
   abbreviations; `ceval` independently interprets only lookup, lambda,
   application and equality. `elimination_preserves_interpretation` proves
   the match to `geval`. No new signature constants are introduced for
   truth, falsity, connectives or quantifiers. The source operator
   applications are beta-reduced as macros, not retained as extra redexes.
5. The generic target evaluator now accepts arbitrary entity and index
   carriers, without a PTQ frame. `standard_model` is independent of any
   source model. The correspondence class `coherent_model F` uses a
   declared inhabited world-time frame F and independently chosen target
   constant valuations. Its two temporal laws require the designated
   future/past relations to mean same-world strict temporal succession.
   A Henkin/general-model record with restricted function domains is not
   implemented.
   Checkpoint 4 additionally uses every `standard_model source_symbol`
   for the untensed comparison. Its indices are not replaced by products.
   The extra temporal symbols in the shared signature have arbitrary
   values and are unused by translations. Only translated untensed terms,
   indexed constants and assignments are recovered by this model round trip.
6. Boolean reflection and function extensionality remain explicit fields
   of the source model. No new global axiom is declared. A `Print
   Assumptions` result of closed does not remove these theorem inputs.
7. Free-variable assignments are arbitrary, not selected examples.
   `canonical_environments_match` constructs a matching target environment
   for every source environment, so the preservation premise is not vacuous.
8. `Derivation` has only axiom and single-occurrence replacement constructors.
   Semantic truth is not a constructor argument. The proof calculus has no
   local hypothesis rule; adding one without binding restrictions would not
   preserve pointwise consequence under the unrestricted replacement rule.
   A checked Boolean counterexample explains this distinction.

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
term. Checkpoint 1 established consequence over the source model class and
its constructed image. Checkpoint 2 extends this to all independent
temporally coherent valuations on declared PTQ frames, and proves
satisfiability correspondence too. The target admissibility condition is
the nine postulate families expressed and evaluated as translated target
formulas, not a field assuming that reconstruction is admissible.
Checkpoint 3 expresses those postulates in minimal syntax and proves the
same correspondence for actual minimal target formulas. The elimination
theorem itself applies to arbitrary standard target models, without
temporal coherence; coherence is needed when connecting back to tensed PTQ.

Checkpoint 4 proves the untensed standard-semantic correspondence over
arbitrary inhabited internal entity and index types. Its theories are
arbitrary predicates on formulas, including infinite theories. The
independent `ieval` is connected to the existing PTQ evaluator by
`ptq_untensed_interpretation`, and its target is the existing compiler
followed by minimal-syntax elimination. No source grammar or PTQ audit is
changed, and this does not remove the conditions on the full tensed result.

Checkpoint 5 adds source-mapped Ty2 axioms, typed substitution and R, explicit
derivation trees and their standard-model soundness. Relative consistency
retains BooleanTruth and FunExt as inputs. Derived equality reasoning and
an explicit proof of a translated IL formula use only the two derivation
constructors. No completeness or proof-system equivalence follows.

`ModelExamples.missing_temporal_coherence_changes_prediction` gives a
standard target model whose future relation is reflexive. A translated
future tautology is true there but false in the paired one-moment PTQ
frame. The missing coherence assumption therefore cannot be discarded.

Theorem 8.2's standard-semantic correspondences now have machine-checked
counterparts for the implemented untensed IL and target signature. These
use full internal Rocq function spaces, not a theorem identifying all
external set-theoretic models with Rocq types. A reverse syntax translation,
the proof-system correspondence of Theorem 8.3, description principles,
general/Henkin models and completeness remain unimplemented. Arbitrary
index isomorphisms for the full tensed PTQ comparison also remain separate.
