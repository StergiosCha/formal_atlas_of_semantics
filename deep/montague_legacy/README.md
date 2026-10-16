# Legacy IL and guarded observations: checkpoint 7

Update, 10 October 2026: the [source-first PTQ branch](../montague_ptq/README.md)
implements the primary paper's types and all-index necessity. This legacy
bridge intentionally preserves the older encoding's different choices.
See the [review addendum](../montague_ptq/REVIEW_ADDENDUM.md); mathematical
preservation here is not a source-fidelity certificate for PTQ.

The new `observation_preservation` theorem relates the existing Boolean Ty2
evaluator to the existing Prop explicit-index evaluator on a certified,
base-quantified fragment. It preserves truth, refutation and pointwise
inferences under related lexical meanings and assignments, without FunExt
in that theorem. A separate witness result preserves the same entity witness.
Nine synthetic cases exercise valid inferences, countermodels and boundaries.
Read [OBSERVATION_SPEC.md](OBSERVATION_SPEC.md) for the precise contract.

The theorem `legacy_open_preservation` now connects the actual datatype and
evaluator in `deep/PTQ_deep2.v` to a separately defined explicit-index target.
It covers every legacy IL constructor and every legacy assignment, including
time, higher-order quantifiers, primitive equality, all 25 named constants,
and the unusual `var_s` constructor that weakens an arbitrary term.

This companion has 76 proved statements in six files: 40 from the actual
legacy bridge and 36 from the observation extension. Together with the
unchanged 173-statement core, there are 249 statements in 26 new Coq files.
The two branches keep separate assumption audits. The actual legacy proofs
retain the old file's domain, lexical and time-order parameters; their
general preservation explicitly takes `FunExt`. All 36 observation proofs
have closed global contexts, but finite-model construction and derivation
transfer still take explicit `FunExt`. No excluded-middle,
propositional-extensionality, proof-irrelevance or other added logical axiom
appears in the new proofs' dependency audits.

The actual legacy contract is [LEGACY_SPEC.md](LEGACY_SPEC.md). The cumulative
[reviewer report](../montague_core/TECHNICAL_REPORT.md), sections 16-17, explains
both steps. No independent semantic-review endorsement is claimed.

## What the result means

Old evaluation takes a term, assignment and implicit `World * Time` index.
New evaluation takes a target term and assignment, with the index represented
explicitly inside the term. Their values agree, after transport along a proved
equality of their corresponding carriers.

Truth remains Coq `Prop`. The target has entity, truth, world, time and index
sorts, arrows, typed lambda/application, logical primitives, index pairing and
projections, and a time-order primitive. It is not the previous Boolean Ty2
target. Checkpoint 7 now compares the two target evaluators on certified
world-only observations. It does not identify their full model classes,
compare tense, or compose with every legacy term. No Gallin equivalence
is established.

Necessity changes the world while retaining time. Future/past change time
while retaining the world, respecting the original direction of `time_lt`.
Intension abstracts over both components. No time-independence assumption
or fixed-time restriction is imposed to make the theorem work.

This is code-to-code interpretation preservation. It does not validate the
old lexical analyses against Montague's text, prove the English grammar
adequate, establish a target proof calculus, or prove Henkin completeness.
It preserves the legacy evaluator as implemented, including its limitations.

## Files and reproduction

| File | Statements | Purpose |
| --- | ---: | --- |
| IndexSyntax.v | 1 | Typed explicit-index target, de Bruijn binders and renaming |
| IndexModels.v | 9 | Independent Prop interpretation, weakening and carrier-transport laws |
| LegacyTranslation.v | 15 | Direct translation, carrier equalities, assignment witnesses and preservation |
| LegacyExamples.v | 15 | Time, necessity, order, equality, higher-order and binding regressions |
| ObservationBridge.v | 18 | Guarded logical relation, observation/witness agreement and boundary theorems |
| ObservationExamples.v | 18 | Paired models, object derivations and the nine-case observation suite |

Requires Coq 8.20.1 and Python 3. From the repository root:

```sh
python3 deep/montague_core/check.py --check
python3 deep/montague_legacy/check.py --check
```

The legacy checker uses fresh temporary copies, compiles the actual old file
unchanged, kernel-rechecks it and the bridge, audits each new proved statement,
checks theorem signatures and rejects fourteen invalid fixtures. It pins the
legacy source hash and records all per-statement global dependencies. It
neither updates nor relaxes the separate closed-core checker. CI runs both.
The core has 23 additional rejected fixtures, making 37 across the two checks.

For interactive inspection without overwriting the original corpus's compiled
module under a different namespace:

```sh
python3 deep/montague_legacy/check.py --check --inspect
```

Then, in Coq:

```coq
Print legacy_interpretation_preservation.
Print legacy_open_preservation.
Print Assumptions legacy_open_preservation.
Print canonical_assignments_match.
Print legacy_carrier.
Print legacy_equality.
Print no_tense_still_allows_time_dependence.
Print necessity_is_not_all_index_quantification.
Print observable.
Print observation_relation.
Check observation_preservation.
Print Assumptions observation_preservation.
Check observable_derivation_prop_sound.
Print paired_entity_witness_agreement.
Print total_truth_reflection_implies_classical_truth.
```

Quit with Ctrl-D. This inspection build is temporary. Edit the repository
sources in your editor and rerun the checker to retain changes. Do not compile
the original corpus file in place under `LegacyPTQ` and then reuse that `.vo`
for the root corpus namespace. The checker avoids that collision by isolation.

For reviewed proof changes, run `--record` and inspect `verification.json`.
If the legacy source itself changes, the explicit source pin must first be
reviewed with the translation. `--record` cannot silently accept source drift.

## Next mathematical work

Review the nine synthetic cases with Robin and Rasmus and select source-backed
readings. Then select actual legacy terms whose translations can be related
to the certified observation image and prove a composed correspondence,
including lexical, assignment and any time conditions. This composition is
not yet provided. General truth/predicate quantification and unrestricted
equality remain outside the observation guard. Do not advertise arbitrary
higher-order Prop domains as two-element truth.

Alternatively, add a source-grounded object calculus for the explicit-index
target and prove its soundness, or a rigidity-aware source substitution
theorem. Neither follows from the present evaluator correspondence.

Existing corpus source files, atlas grades, LaTeX draft, frontend and live
worker are unchanged. The new branch is not yet published in the atlas index.
