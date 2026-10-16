# PTQ to Gallin-style explicit-index type theory

The first Gallin checkpoint connects the actual source-first PTQ
implementation to a typed, explicit-index target. It is based directly on
Gallin (1975), section 8, especially the translation on p. 61 and the
interpretation lemma on p. 62.

The general preservation proof covers all 18 PTQ term constructors,
including arbitrary bound and free variables, index-dependent constants,
higher-order equality and quantification, intension, extension, necessity,
and the declared PTQ tense extension. It composes with the existing
English analysis-tree translation and transports the admissible
temperature countermodel.

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
| `SOURCE_MAP.md` | Page references, PDF fingerprint, encoding choices, and exact claim boundary. |
| `verification.json` | Reproducible source hashes, dependency pins and machine-check results. |

Start with `compile`, then `interpretation_preservation`, then
`english_interpretation_preserved`. The target has no built-in modal or
tense operator: these become ordinary quantification and applications of
named index relations.

## Exact claim

In the constructed target interpretation, every translated PTQ term has
the same value as the source term, up to the explicit type transport.
Truth and countermodels therefore survive. Entailment agrees over the
same source model class and its constructed image, including the class
restricted by PTQ's meaning postulates.

This is an interpretation-preservation result, not full equivalence of
PTQ and every Ty2 or Henkin model. Boolean reflection and function
extensionality remain explicit model assumptions. The target currently
retains connective constructors instead of eliminating them into Gallin's
minimal lambda/application/equality syntax.

No independent human source review is claimed. Source consultation and
proof engineering were AI-assisted; the proof assistant checks the
consequences of the definitions, not their fidelity to the book.

## Isolation and next step

This development is on `codex/gallin`. The published atlas and its
Montague research checkpoint remain unchanged. No P/F grade, outcome,
comparison edge, live-Coq library, or published PTQ verification record
has been modified.

Next: independent target models and a model-correspondence theorem,
followed by the stronger source-backed inference comparison that those
models support. Gallin's axiomatic calculus and Henkin completeness are
separate later milestones. Discussion or email approval from colleagues
is not a prerequisite to continuing implementation.
