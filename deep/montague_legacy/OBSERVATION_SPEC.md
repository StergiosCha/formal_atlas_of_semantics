# Prop/Boolean observational correspondence: checkpoint 7

## Claim and scope

`observation_preservation` relates the existing Boolean `Ty2Models.weval`
to the existing Prop-valued `IndexModels.peval`. It is not a comparison of
two newly invented evaluators. An embedding sends actual world-typed Ty2
terms to the world-only part of the explicit-index Prop target.

For a certified term, related lexical interpretations and related assignments,
the two values satisfy a type-indexed logical relation. At truth type:

```text
peval lex before (observation_term constants p) rho
  <-> weval M p sigma = true
```

This holds for every pair satisfying those premises. It is pointwise model
and assignment agreement, not equivalence of the unrestricted Prop and
Boolean model classes. It does not yet compose with every actual legacy IL
translation, compare tense, prove Gallin equivalence, or establish independent
source fidelity. The actual legacy bridge in `LEGACY_SPEC.md` remains a
separate theorem with a different domain and assumption boundary.

## The guarded language

`observation_type` maps entity, truth and world types to the corresponding
Prop-target types and maps arrows recursively. `observation_term` maps
variables, constants, lambda, application, implication and universal
quantification to their existing target constructors. The syntactic
translation is total on Ty2 terms. The semantic theorem is deliberately
restricted by the inductive certificate `observable`.

Certified terms contain:

- variables and constants of any represented type;
- lambda and application, provided their subterms are certified;
- implication between certified formulas;
- universal quantification over entities or worlds, with certified bodies;
- the particular encoded falsity `forall X:t. X`.

The last case is individually justified by its false interpretation on both
sides. It is not permission for arbitrary quantification over propositions.
Negation, defined using implication and this falsity, and absolute necessity,
defined by universal world quantification, are certified by proved lemmas.
Renaming and weakening preserve certification.

Call this a base-quantified observable fragment. It can contain higher-order
lambda, application and lexical values, but their interpretations must obey
the logical relation. Do not call it strictly first-order or claim that all
higher-order functions are covered. General truth-type or predicate-type
quantification is excluded. So is unrestricted Leibniz equality, whose
encoding quantifies over predicates. No primitive equality constructor is
added to Ty2. The translation does not use the target's time, index-pair,
projection or temporal-order constructs.

## Values and assignments

The paired interpretations have the same entity and world carriers. Their
truth carriers differ: `Prop` versus `bool`. At each type the relation is:

| Type | Required relationship |
| --- | --- |
| Entity | The values are equal in the common entity carrier. |
| World | The values are equal in the common world carrier. |
| Truth | The proposition holds if and only if the Boolean is true. |
| Arrow a b | Related inputs at a produce related outputs at b. |

The arrow clause does not equate functions with different codomains. It is
also not a surjectivity assertion: no theorem says every Prop-valued function
has a related Boolean-valued function. The lexical premise requires a proof
of this relation for each constant. The assignment premise requires it for
each typed variable. Related environments remain related when extended with
related values; this is the binder invariant used in the induction.

The Boolean model carries the existing total-quantifier reflection contract.
In particular, a quantifier is true exactly when all elements of its domain
satisfy its Boolean predicate. The observation theorem does not construct
that model. The Prop interpreter also takes a time type and time-order
relation, but translated observation terms do not inspect them.

## Preservation and inference

The proof is induction on the certification, not an unchecked assertion that
all syntax works. Variables use the assignment premise; constants use the
lexical premise. Lambda uses related environment extension, application uses
the arrow relation, and implication uses Boolean implication reflection.
For entity/world quantification the carriers coincide, so each quantified
value can be related to itself by reflexivity. Quantifier reflection then
supplies both directions. Encoded falsity is handled separately.

Neither `observation_preservation` nor its truth, refutation, decidability,
inference-agreement or counterexample-agreement corollaries takes `FunExt`.
Pointwise relations at arrow types remove the need to equate interpreted
lambda functions. The checker tests this exact theorem signature.

`observation_inference_agreement` compares satisfaction of a finite list of
certified premises and a certified conclusion at a related model/assignment
pair. `observation_counterexample_agreement` transfers a true premise and
false conclusion. Neither alone proves equality of validity over unrestricted
model classes: coverage of those classes by the relation would be another
theorem, and total coverage at truth type has the boundary below.

`observable_derivation_prop_sound` additionally takes an actual `wderives`
derivation in either constructive or classical mode. Existing Boolean
soundness and observation agreement transfer its consequence to the related
Prop interpretation. This theorem DOES take `FunExt`, inherited from
`world_derivation_sound`. Premises and conclusion must be certified; there
is no additional certification requirement on intermediate derivation terms.
This is semantic consequence transfer, not translation into a new Prop-target
object calculus or proof of equivalence between the two logical modes.

## Witness observations

Entity witnesshood is a metalinguistic observation on a certified predicate
body with one free entity variable. `observation_entity_witnesses` proves
that an entity satisfying the translated Prop body exists exactly when an
entity making the Boolean body true exists. Both directions retain the same
entity as witness. This is not a new object-language existential constructor
and not the double-negation encoding of existence used elsewhere in C.

`observation_finite_witnesses` connects that existential observation to
`existsb` over a complete finite entity enumeration. It needs completeness
of the enumeration, not a sample of likely entities. It does not introduce
a general witness-extraction function from arbitrary Coq propositions.

## Concrete paired models and nine cases

`ObservationExamples.v` uses entities and worlds both carried by `bool`,
while keeping their syntactic sorts distinct. It uses the existing full
finite Boolean world-model constructor. The Prop lexicon interprets the
same predicate tables by equality to `true`; names and entity concepts have
the same carrier values. Time is `unit`. The lexical and assignment relation
premises are proved for these instances, rather than left as assumptions.

The finite Boolean model constructor takes explicit `FunExt`. Thus the
paired examples are conditional on that premise even though the generic
preservation theorem does not need it. Empty noun extensions do not mean
an empty entity domain. John denotes `true`, the actual world is `true` and
the alternative world is `false` in the synthetic fixtures.

`OBSERVATION_SUITE.json` records these cases and their exact proved names:

| ID | Observation | Checked outcome |
| --- | --- | --- |
| O01 | Every man walks; John is a man; therefore John walks. | Object derivation and both semantic consequences for every paired lexical table. |
| O02 | Every man walks; every walker moves; therefore every man moves. | Object derivation and both semantic consequences for every paired lexical table. |
| O03 | John is a man; therefore a man exists. | The same named entity supplies an actual witness on both sides. |
| O04 | Weather holds necessarily; therefore it holds at the actual world. | Object derivation and both semantic consequences. |
| O05 | Every man walks; therefore a man exists. | Counterexample with an empty man extension in a nonempty domain. |
| O06 | Weather holds at the actual world; therefore necessarily. | Counterexample with different weather at the alternative world. |
| O07 | Concepts agree actually; substitute them under necessity. | Counterexample: actual agreement does not preserve necessary predication. |
| O08 | Double negation of the reflected weather observation. | Equivalence with the original observation, not unrestricted Prop double-negation elimination. |
| O09 | Compare different lexical interpretations of the same atom. | Different answers, illustrating a missing relation precondition. |

These are familiar synthetic validity and countermodel patterns. They are
not independently source-reviewed linguistic benchmarks or new discoveries
about Montague. The suite explicitly records that no independent semantic
review has occurred. No atlas outcomes or human labels are changed.

## Boundary theorems

`reflected_proposition_is_decidable` derives `P or not P` from a reflecting
Boolean for P. `total_truth_reflection_implies_classical_truth` shows that
requiring a reflecting Boolean for EVERY Coq proposition entails excluded
middle for all propositions. Neither theorem supplies that total-reflection
premise or imports excluded middle. This explains why the scoped relation
does not establish a constructive identification of all Prop with bool.

`common_truth_value_gives_equivalence` derives logical equivalence when two
propositions reflect the same Boolean. It does not derive their identity.
`truth_equality_bridge_requires_propositional_extensionality` shows that total
reflection together with a bridge identifying proposition equality with
Boolean equality would imply propositional extensionality. This is another
conditional boundary theorem, not an impossibility or independence proof.

## Reproduction and extension

Run `python3 deep/montague_legacy/check.py --check`. It compiles both new
modules in isolation with their dependencies, kernel-rechecks them, requires
all 36 new named proofs to have closed global contexts and checks the
no-FunExt preservation signature. Seven additional invalid fixtures reject
unguarded quantification, mismatched lexicons, proposition identity inferred
from equivalence, omitted certification, existential import and local
necessitation. Rejected proof attempts are regression tests, not independent
metatheorems that those claims can never be proved.

Run with `--inspect` to open a temporary Coq session. Inspect the actual
certificate, relation, theorem types and `Print Assumptions` output before
the examples. Use `--record` only after reviewing deliberate source changes.
The nine suite IDs must be unique and link to compiled named proofs.

Next, choose source-reviewed readings with Robin and Rasmus. A conservative
implementation extension would select actual legacy terms whose translated
forms are in, or provably equivalent to terms in, this observation image,
prove the required lexical and assignment relationships, and compose the
two existing preservation theorems. Time independence cannot be inferred
merely from the absence of tense syntax. Unrestricted equality, arbitrary
Prop/predicate quantification, Henkin models and source adequacy remain
separate obligations.
