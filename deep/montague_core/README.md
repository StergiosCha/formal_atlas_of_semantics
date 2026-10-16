# Montague proof-theory workbench: C, Ty2 and world-only IL

Update, 10 October 2026: the separately authorized
[source-first PTQ reconstruction](../montague_ptq/README.md) now targets
the original paper. Read its [review addendum](../montague_ptq/REVIEW_ADDENDUM.md)
before treating this workbench or the legacy correspondence as evidence of
whole-paper fidelity. This branch's mathematical checkpoint is unchanged.

Current status: checkpoint 7 is frozen for scientific review. Start with the
[two-page review brief for Robin and Rasmus](REVIEW_BRIEF.md); the longer report
is supporting evidence. The research sequence below is deferred, not required
before review. No reviewer approval or published release is claimed.

For a code-led explanation, [WALKTHROUGH.md](WALKTHROUGH.md) is the source
template for a 20-chapter companion with exact excerpts and the complete
checked source appendix. `render_walkthrough.py` expands it from the frozen
review packet, checks the copied proofs and captures the interactive session
before producing Word/PDF and a shareable archive. This is documentation of
checkpoint 7, not a further mathematical checkpoint.

For the combined review handoff, [reading instructions](REVIEW_START_HERE.md),
the [blank response form](REVIEW_RESPONSE.md) and the
[covering email draft](REVIEW_EMAIL.md) are maintained here.
`prepare_review_dispatch.py` combines the two existing hash-pinned export
packets into a new directory and ZIP, checks source identity and reruns both
proof checkers. The reading-instructions links target the assembled packet.
Assembly does not send email or imply reviewer approval.

Checkpoint 6 added the [actual legacy IL bridge](../montague_legacy/README.md)
as a separately audited companion: 40 statements cover every old IL constructor
using a Prop-valued explicit world/time target. The closed core described below
retains its checkpoint-5 code and 173 statements. Checkpoint 7 adds 36 closed-global-context
statements on [guarded Prop/Boolean observations](../montague_legacy/OBSERVATION_SPEC.md).
The combined development has 249 statements in 26 files, with distinct
global-assumption boundaries, not 249 axiom-free proofs.

This workbench begins the programme discussed with Robin Cooper and Rasmus
Blanck: keep the object language, proof calculus, interpretation and
linguistic observations separate, then prove the bridges. It is an additive
research checkpoint, not a replacement for `deep/PTQ_deep2.v` or
`atlas/montague/PTQ.v`, and not an assessment of the full source theory.

The new model milestone adds a two-valued interpretation, full internal
function domains, executable finite models, a classical soundness bridge
and the source's defined Leibniz equality. See [Model contract](MODEL_SPEC.md)
for the exact premises and the distinction from full external set models
and Henkin semantics.

Checkpoint 4 adds a distinct world type, full internal constant-domain models,
soundness for a C-style Ty2 calculus, and interpretation preservation from the
extensional Boolean core. Two-world countermodels check necessity and rigid
versus varying concepts. See [World-sensitive contract](INTENSIONALITY_SPEC.md)
for the exact scope and the audit of the older IL implementation.

Checkpoint 5 implements a specified world-only IL fragment and proves that
its translation into explicit-world Ty2 preserves interpretation, including
open terms, higher-order quantification, intension/extension and necessity.
See [IL translation contract](IL_SPEC.md). This is not yet a theorem about
the complete legacy IL or Gallin equivalence. There are now 173 named proved
statements in 20 files.

## Source and representation choices

Primary consultation: Chatzikyriakidis and Luo (2020), *Formal Semantics in
Modern Type Theories*, section 1.3.1, printed pp. 6-9; Appendix A1, pp. 175-176.
The presentation attributes the natural-deduction system C to Luo and
Soloviev (2017), *Dependent Event Types*. The latter paper has not received
a separate source audit here. [Book DOI](https://doi.org/10.1002/9781119489252).

Local consulted PDF SHA256:
`a23b5aae6bb2d65767b4d8b7b1b087cc5b13dcc2000c441798fbe65ad9adbf19`.
The PDF is not distributed. This is assistant source consultation, not an
independent human review or a change to the existing corpus artifact pins.

For the world layer, the additional directly consulted passages are the book's
pp. 9-10 and Hahn-Richter (2015), Definitions 1-2, pp. 516-518. The complete
Hahn-Richter language and Gallin's IL/Ty2 equivalence are not claimed here.

The detailed reviewer document is
[Technical report for Robin Cooper and Rasmus Blanck](TECHNICAL_REPORT.md).
`render_report.py --output-dir PATH` exports Word and PDF copies using
pandoc, python-docx and LibreOffice; it does not run or replace the Coq checks.

| Source feature | Representation here | Remaining fidelity obligation |
| --- | --- | --- |
| `e`, `t`, function types | `ty`; intrinsically typed `tm` | Relate intrinsic typing to the source's explicit typing derivations. |
| Contexts interleaving `x:A` and `P true` | Independently defined intrinsic interleaved calculus, proved equivalent to the split-context judgments | Named-source/intrinsic typing adequacy and source review remain. The theorem preserves judgments, not literal context identity. |
| Abstraction, application | Typed de Bruijn binders | Renaming/substitution now preserve terms, beta conversion and whole derivations; semantic interpretation lemmas retain their explicit premises. |
| Implication and universal quantification | `Imp`, `All`; introduction and elimination in `derives` | Conversion and eigenvariable conditions must remain explicit. |
| Beta conversion | Syntactic congruence and beta equivalence | No eta, functional-extensionality or arbitrary semantic-equality rule added to C. |
| Other logical operators | Appendix A1.2's encodings using implication and quantification over `t` | Includes Leibniz equality, whose Boolean reflection is proved with explicit denotation-equality decisions; the finite construction supplies those decisions. |
| Classical principles | Separately indexed extension with double-negation elimination | The appendix does not list that rule; it is our explicit extension, not an attribution to its base presentation. |

The code is therefore a source-informed C calculus with a selected world-typed
extension, not a completed
source-to-code adequacy theorem. Logical constants cannot be supplied by
arbitrary Coq denotations as a substitute for object derivations.

## What is implemented

1. [Syntax.v](Syntax.v): entity/truth/function types, typed lexical symbols,
   typed terms, capture-avoiding renaming/substitution, syntactic beta
   conversion and the selected encoded logical operators.
2. [Algebra.v](Algebra.v): pointwise renaming/substitution algebra, including
   composition, identities and compatibility with weakening and instantiation.
3. [Models.v](Models.v): explicit nonempty entity domain and lexical assignment;
   interpretation, renaming/substitution lemmas, beta-conversion soundness,
   meanings of the encoded logical operators, and consequence quantified
   over all models and assignments of this declared interpretation.
4. [Calculus.v](Calculus.v): constructive derivability and a separately indexed
   classical extension, hypothesis weakening, admissible cut, embedding of
   constructive derivations into the extension, soundness and a
   countermodel-to-nonderivability theorem.
5. [Structural.v](Structural.v): beta conversion and whole derivations are
   preserved by renaming and simultaneous substitution, with variable
   weakening and head-instantiation corollaries. These require no semantic premises.
6. [Contexts.v](Contexts.v): independent interleaved contexts, lookup and
   inference rules; proofs in both directions to the split calculus;
   canonical repacking preserves derivability, not declaration placement.
7. [Examples.v](Examples.v): object derivations of universal instantiation,
   a syllogism, existential introduction, beta conversion and classical
   double-negation elimination. Concrete countermodels block existential
   import and generalization from one named individual. Another fixture
   checks capture avoidance; two lexical models disagree about the same atom.
8. [StructuralExamples.v](StructuralExamples.v): ten regression proofs exercise
   binder-sensitive transformations, the classical mode and the context bridge.
9. [BooleanModels.v](BooleanModels.v): literal Boolean truth, full internal
   function spaces, quantifier reflection, binding/conversion lemmas and
   soundness for both modes. An optional explicit ClassicalDecision premise
   constructs quantifiers for arbitrary inhabited entity domains.
10. [BooleanFinite.v](BooleanFinite.v): executable finite quantifiers at every
    simple type, with proved enumeration of all functions at arrow types.
11. [BooleanEquality.v](BooleanEquality.v): source-defined Leibniz equality,
    its predicate meaning and its reflection to denotational equality.
12. [BooleanExamples.v](BooleanExamples.v): concrete finite models,
    countermodels for both modes, semantic consequences of the old derivations,
    higher-order quantification and equality tests.
13. [Ty2Syntax.v](Ty2Syntax.v): separate entity/truth/world types, typed syntax,
    capture-avoiding operations, beta conversion and defined absolute necessity.
14. [Ty2Models.v](Ty2Models.v): constant-domain world models, interpretation,
    binding/conversion proofs and finite or explicitly conditional arbitrary
    entity/world-domain constructions.
15. [Ty2Calculus.v](Ty2Calculus.v): C-style rules including world quantification,
    mode-indexed classical reasoning, soundness and countermodel exclusion.
16. [Ty2Embedding.v](Ty2Embedding.v): explicit domain conversions, a core model
    reduct, term-interpretation preservation and semantic transfer of existing
    extensional derivations. Not a legacy IL translation or conservativity proof.
17. [Ty2Examples.v](Ty2Examples.v): two-world truth, necessity, actual coextension,
    rigidity, freezing, beta/capture tests and reuse of the original core proofs.
18. [ILSyntax.v](ILSyntax.v): world-only IL types and terms, typed variable maps
    and a binding-sensitive explicit-world translation.
19. [ILTranslation.v](ILTranslation.v): independent implicit-index evaluation,
    general interpretation preservation, truth/counterexample corollaries,
    cancellation and index-rigidity results.
20. [ILExamples.v](ILExamples.v): 16 regressions for source and target evaluation,
    binder preservation, unsafe substitution, reverse cancellation and quantifiers.

The cut result is admissibility by implication introduction/elimination,
not a cut-elimination or normalization theorem. Checkpoint 2 added 43 structural
lemmas and regressions; checkpoint 3 adds 38 model/equality statements and
regressions. Checkpoint 4 adds 32 world-layer and bridge statements;
checkpoint 5 adds 28 IL translation statements and regressions. None of
these counts is a count of new linguistic results.

For example, a derivation of `forall y. man(x)` from `man(x)` can now be
transformed into a derivation of `forall y. man(John)` from `man(John)` by
the general substitution theorem. The replacement affects the free x,
not the bound y, and transforms the assumptions as well as the conclusion.

## Exactly which models and assumptions?

The original `model` supplies a nonempty individual domain and an interpretation of the
chosen typed lexical signature. Function types are interpreted as Coq function
spaces; **truth is interpreted as Coq `Prop`**. This is not yet a model class
with a literal two-element truth carrier, a Henkin subdomain construction or
a proved representation of all Montague set-theoretic models. There are no
worlds or times in this original extensional core. The new `wmodel` in
`Ty2Models.v` supplies a separate world domain and constant entity domains;
world dependence is explicit in function types. It has no tense.

The new `bmodel` is separate: truth is exactly `bool`, and implication is the
Boolean truth table. It includes total quantifiers with proofs that they
range over their whole domains. `finite_model` constructs them by enumeration,
including all functions at arrow types, with FunExt as an explicit premise.
`decision_model` handles arbitrary inhabited entity domains conditional on
`ClassicalDecision`, a data-valued decision for every proposition.

`classical_boolean_sound` needs FunExt and a model satisfying that contract,
but no additional ClassicalTruth premise. Boolean double negation is proved
by Boolean reasoning. This does not remove the quantifier construction
obligation or prove arbitrary Coq propositions decidable. No equivalence
between the old and new model classes is claimed. See [MODEL_SPEC.md](MODEL_SPEC.md).

`consequence H p` quantifies over all such models and variable assignments,
requiring the assumptions in `H` before asserting `p`. No meaning postulates
are silently installed. Lexical meaning postulates can be explicit premises;
a source-specific admissibility class remains later work.

In the original Prop-valued interpretation, general constructive soundness
has an explicit `FunExt` premise. General classical soundness additionally
has `ClassicalTruth` (excluded middle for
the interpretation's propositions). Function extensionality is used to prove
equality of denotations through binders. It is **not** an object-calculus rule.
No functional extensionality, excluded middle, UIP or proof irrelevance axiom
is imported or globally postulated.

Consequently, `Print Assumptions` reports closed global contexts, but this
does **not** mean the soundness statements are assumption-free: the named
premises appear in their types. The original concrete example derivations
and Prop-valued countermodels do not require those premises. The new finite
Boolean model construction does take FunExt. Nonderivability inferred via
the general soundness theorem is conditional on `FunExt`.

The classical-only constructor is tested; a strict non-derivability theorem
for double-negation elimination in the entire constructive calculus is NOT
yet established. Neither soundness theorem establishes completeness.

## Reproduce and inspect

Requires Coq 8.20.1 and Python 3, with no provider credentials or source PDFs.
From the repository root:

```sh
python3 deep/montague_core/check.py --check
```

The checker builds fresh copies in a temporary directory, runs `coqchk`,
queries every named proved statement, checks the soundness theorem types,
rejects twenty-three deliberately invalid fixtures, and compares source hashes and
results with [verification.json](verification.json). Temporary copies are
removed automatically. It does not update atlas records or grades.

For intentional reviewed changes, regenerate with `--record`, then inspect
the checkpoint diff. To work interactively, open the local `_CoqProject`, or
compile in place:

```sh
cd deep/montague_core
coqc -Q . MontagueProof Syntax.v
coqc -Q . MontagueProof Algebra.v
coqc -Q . MontagueProof Models.v
coqc -Q . MontagueProof Calculus.v
coqc -Q . MontagueProof Structural.v
coqc -Q . MontagueProof Contexts.v
coqc -Q . MontagueProof Examples.v
coqc -Q . MontagueProof StructuralExamples.v
coqc -Q . MontagueProof BooleanModels.v
coqc -Q . MontagueProof BooleanFinite.v
coqc -Q . MontagueProof BooleanEquality.v
coqc -Q . MontagueProof BooleanExamples.v
coqc -Q . MontagueProof Ty2Syntax.v
coqc -Q . MontagueProof Ty2Models.v
coqc -Q . MontagueProof Ty2Calculus.v
coqc -Q . MontagueProof Ty2Embedding.v
coqc -Q . MontagueProof Ty2Examples.v
coqc -Q . MontagueProof ILSyntax.v
coqc -Q . MontagueProof ILTranslation.v
coqc -Q . MontagueProof ILExamples.v
```

Then:

```sh
coqtop -Q . MontagueProof
```

```coq
From MontagueProof Require Import Syntax Models Calculus Structural Contexts Examples.
From MontagueProof Require Import BooleanModels BooleanFinite BooleanEquality BooleanExamples.
From MontagueProof Require Import Ty2Syntax Ty2Models Ty2Calculus Ty2Embedding Ty2Examples.
From MontagueProof Require Import ILSyntax ILTranslation ILExamples.
Print derivation_substitution.
Print mixed_split_equivalence.
Print constructive_sound.
Print classical_sound.
Print Assumptions constructive_sound.
Print Assumptions existential_derivation.
Print classical_boolean_sound.
Print finite_model.
Print finite_leibniz_equality.
Print Assumptions classical_boolean_sound.
Print world_derivation_sound.
Print embedding_interpretation.
Print core_derivation_world_sound.
Print no_necessitation_from_actual_assumption.
Print explicit_world_preservation.
Print Assumptions explicit_world_preservation.
Print up_down_for_rigid_intensions.
Print unsafe_index_substitution_changes_denotation.
```

The workbench has its own CI check. It is deliberately not in the published
atlas index or the root corpus `_CoqProject` yet. That preserves the existing
230-source/87-file baseline and avoids treating new infrastructure as a
source-level assessment. No site or live-worker deployment is part of this
checkpoint.

## Research sequence after this checkpoint

1. Review the source rule mapping and the now-proved intrinsic context bridge
   with the authors. Named-source typing adequacy is still distinct from this
   bridge. Renaming, variable weakening and derivation substitution are proved.
2. Review the now-explicit Boolean model/equality contract. The first Boolean
   soundness bridge is proved. External set-model adequacy and a comparison
   with the Prop-valued model class remain separate obligations.
3. The actual legacy IL now has an interpretation-preserving translation into
   a parallel Prop-valued world/time target; see `../montague_legacy/LEGACY_SPEC.md`.
   Checkpoint 7 proves a guarded logical relation between the Boolean and Prop
   target evaluators, with nine synthetic observation cases. Composing it with
   selected actual legacy terms and source-reviewed readings remains to be done.
   General Prop/predicate quantification and equality are not covered.
4. Develop the selected classical Henkin model/proof correspondence. Full
   higher-order validity is not a target for an effective complete calculus.
5. Curate 25-30 inference cases with Robin and Rasmus from FraCaS and
   Hahn-Richter. Separate agreed readings, lexical assumptions, countermodels,
   disputed cases, out-of-scope cases and proof-search failures.
6. Mechanize the stated C-to-dependent-event extension conservativity result
   (book section 7.2, p. 162), then build source-grounded comparison bridges.

The book's pp. 19-22 explicitly describe MTT semantics as both model-theoretic
and proof-theoretic, including signatures for incomplete worlds. Do not
reintroduce the erroneous blanket claim that MTT has no model-theoretic aspect.
That terminology still does not identify its signatures with Cooper's TTR
models or Montague's set-theoretic models.
