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

Verification: 101 kernel-checked statements across nine modules, with
20 rejected invalid regression fixtures. No admitted proofs or additional
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

This is a model-correspondence result for the stated classes, not full
equivalence of PTQ and every Ty2 or Henkin model. Unrestricted standard
models are defined, but their arbitrary temporal relations need not match
PTQ. A checked counterexample demonstrates the difference. Boolean reflection and function
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

Next: address the untensed comparison over arbitrary index carriers.
Gallin's axiomatic calculus and Henkin
completeness are separate later milestones. No colleague discussion or
email approval is a prerequisite to implementation.

Checkpoints 1 and 2 are preserved in commits `fb4d9db` and `f8543aa`;
the current verification record is checkpoint 3. No earlier PTQ checkpoint
was modified.
