# PTQ to Gallin-style explicit-index type theory

The Gallin development connects the actual source-first PTQ
implementation to a typed, explicit-index target. It is based directly on
Gallin (1975), section 8, especially the translation on p. 61 and the
interpretation lemma on p. 62.

The general preservation proof covers all 18 PTQ term constructors,
including arbitrary bound and free variables, index-dependent constants,
higher-order equality and quantification, intension, extension, necessity,
and the declared PTQ tense extension. It composes with the existing
English analysis-tree translation and transports the admissible
temperature countermodel.

Checkpoint 2 adds independently specified standard target models and
reconstructs PTQ models from every target valuation satisfying explicit
temporal conditions. The nine meaning-postulate families are stated as
translated target formulas. Admissibility, consequence and satisfiability
agree in both directions for these model classes.

Checkpoint 3 eliminates every extra connective and quantifier constructor
into Gallin's minimal lambda/application/equality syntax. An independently
written minimal evaluator agrees with the richer evaluator for every
term. The PTQ, English-tree and admissible-model results compose with this
elimination, including the temperature countermodel.

Checkpoint 4 adds untensed IL over arbitrary inhabited entity and index
types. Its translation into minimal syntax preserves standard validity,
consequence and satisfiability for arbitrary predicate-defined theories,
over every standard model of the implemented target signature. No temporal
coherence or PTQ meaning postulate is required for this untensed result.

Checkpoint 5 adds a typed theorem calculus for Gallin's Ty2 axioms and
replacement rule, with capture-avoiding substitution, explicit derivation
trees and standard-model soundness. A proof of a translated IL formula
now implies its IL semantic validity. This is not completeness or an
IL-to-Ty2 proof translation.

Checkpoint 6 adds the source IL calculus using Gallin's alternative
AS4.1-AS4.7 and R1-R8 presentation, with standard-model soundness and
finite implication-chain discharge of assumptions. An explicit restricted
proof compiler translates reflexivity, AS4.2 and R1-R3/R6-R8 into actual
Ty2 proof trees. The other axiom families and R4-R5 are not yet compiled.

Verification: 183 kernel-checked statements across twenty-one modules, with
44 rejected invalid regression fixtures. No admitted proofs or additional
global axioms. The model fields still carry the stated logical assumptions.

## Reproduce

With Coq 8.20.1 installed, from the repository root:

```sh
python3 deep/montague_gallin/check.py --check
```

The checker builds in a fresh temporary directory, rechecks proof objects
with `coqchk`, audits global dependencies, checks exact theorem signatures,
and rejects invalid regression fixtures. No private PDF, LLM service,
API key, or pre-existing compiled file is required.

`--record` is an explicit checkpoint update after source review. It is
not used to make a failing `--check` pass automatically.

## Read the code

| File | Purpose |
|---|---|
| `Types.v` | Target types e, t, s, arrows; source-type injection and inverse value transports. |
| `Target.v` | Explicit target syntax, independent interpretation, renaming and weakening. |
| `Translation.v` | Source-backed translation, general interpretation proof, matching environments, truth and counterexample preservation. |
| `Examples.v` | Composition with English trees, transported temperature countermodel, model-image consequence, constant and binder regression checks. |
| `Independent.v` | Independent standard models, temporal-coherence conditions, reconstruction and interpretation-preserving model round trips. |
| `Correspondence.v` | Translated postulates characterize admissibility; entailment and satisfiability agree across the two model classes. |
| `ModelExamples.v` | Nonvacuity, the admissible temperature countermodel, and a counterexample when temporal coherence is dropped. |
| `Minimal.v` | Minimal syntax and evaluator, Gallin's logical abbreviations, capture-avoiding weakening and general elimination preservation. |
| `MinimalCorrespondence.v` | PTQ and English preservation, postulates, entailment, satisfiability and the countermodel in minimal target syntax. |
| `MINIMAL_SYNTAX.md` | Step-by-step account of the completed connective elimination and its assumptions. |
| `Untensed.v` | Explicit untensed syntax embedded into PTQ, arbitrary-index models and an independent evaluator. |
| `UntensedTranslation.v` | All-open-term preservation using the existing compiler; compatibility with the actual PTQ evaluator. |
| `UntensedModels.v` | Unrestricted standard-model reconstruction, arbitrary-theory consequence and satisfiability in minimal syntax. |
| `UntensedExamples.v` | Bare Boolean indices, varying constants, cross-index necessity, unused temporal symbols and exact round-trip limits. |
| `UNTENSED_MODELS.md` | Step-by-step explanation of the completed arbitrary-index correspondence. |
| `Substitution.v` | Typed substitution, its semantic lemma, one-hole contexts and replacement under binders. |
| `Calculus.v` | Source-mapped A1-A3, AS4 and R; derivation datatype, soundness and derived equality reasoning. |
| `CalculusConnections.v` | Explicit derivation of a translated IL formula and the derivation-to-IL-validity theorem. |
| `CalculusExamples.v` | Proof trees, relative consistency and counterexamples to capture and pointwise replacement. |
| `CALCULUS.md` | Step-by-step account of the proof calculus, its semantics and scope. |
| `ILCore.v` | Primitive source IL, logical macros, typed renaming and syntactic modal closure with its index-independence theorem. |
| `ILCalculus.v` | Source axiom schemas and R1-R8, all-derivations soundness and finite implication-chain discharge. |
| `ILCalculusExamples.v` | Source proof trees, semantic connection to Ty2, and countermodels to missing modal side conditions. |
| `ILProofTranslation.v` | Explicit restricted source proof datatype and its proof-to-proof compiler into the actual Ty2 calculus. |
| `IL_CALCULUS.md` | Step-by-step source-calculus guide, counterexamples and exact proof-compiler coverage. |
| `MODEL_CORRESPONDENCE.md` | Explanation of the new model classes, reconstruction proof and exact scope. |
| `SOURCE_MAP.md` | Page references, PDF fingerprint, encoding choices, and exact claim boundary. |
| `verification.json` | Reproducible source hashes, dependency pins and machine-check results. |

Start with `compile`, then `interpretation_preservation`, then
`english_interpretation_preserved`. The target has no built-in modal or
tense operator: these become ordinary quantification and applications of
named index relations.

## Exact claim

Every translated PTQ term preserves its interpretation. More strongly,
every independently chosen target valuation on a declared PTQ world-time
frame, satisfying the two temporal-coherence laws, reconstructs a PTQ
model. The target round trip preserves every expression in the implemented
signature, including expressions outside the translation's syntactic image.

Entailment and satisfiability agree between admissible PTQ models and all
such target models satisfying the translated meaning postulates. This
extends checkpoint 1's result over a constructed image to an independently
specified target model class.

For untensed IL, checkpoint 4 covers every standard model of the implemented
signature over arbitrary inhabited entity and index carriers, with
arbitrary theories rather than finite lists only. This is the standard
semantic correspondence of the kind stated in Gallin's Theorem 8.2,
formalized with internal Rocq function spaces.

This does not identify full tensed PTQ with every Ty2 or Henkin model.
Arbitrary temporal relations need not match PTQ, as the checked
counterexample demonstrates. Boolean reflection and function
extensionality remain explicit model assumptions. The final target now
has Gallin's minimal primitive syntax. The richer intermediate target is
retained for readability, with a proved interpretation-preserving elimination.

No independent human source review is claimed. Source consultation and
proof engineering were AI-assisted; the proof assistant checks the
consequences of the definitions, not their fidelity to the book.

## Isolation and next step

This development is on `codex/gallin`. The published atlas and its
Montague research checkpoint remain unchanged. No P/F grade, outcome,
comparison edge, live-Coq library, or published PTQ verification record
has been modified.

Next: extend the proof compiler to lambda/Up congruence and the remaining
source axioms. The source calculus and its standard soundness are in place.
Description principles, proof-system correspondence and Henkin completeness
are separate milestones. No colleague discussion or
email approval is a prerequisite to implementation.

Checkpoints 1-5 are preserved in commits `fb4d9db`, `f8543aa`, `f26c278`,
`503e035` and `67faced`; the current verification record is checkpoint 6. No earlier PTQ checkpoint
was modified.
