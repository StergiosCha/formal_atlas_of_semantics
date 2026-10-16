# Model contract: checkpoint 3

This document specifies the extensional layer retained from checkpoint 3.
Checkpoint 4 adds a separate world-typed layer; its current contract and
Boolean-layer obligations are in [INTENSIONALITY_SPEC.md](INTENSIONALITY_SPEC.md).
Checkpoint 6 separately proves actual legacy IL preservation into a Prop-valued
world/time target; see `../montague_legacy/LEGACY_SPEC.md`. It does not establish
equivalence to this Boolean model class. Checkpoint 7 adds a guarded
[target observation relation](../montague_legacy/OBSERVATION_SPEC.md), not
unrestricted model-class equivalence or a bridge for every legacy term.

## Claim and source boundary

This checkpoint interprets the implemented extensional C calculus in a
two-valued, full internal function-space model class. It proves soundness
for that class and constructs executable finite instances. It does not
implement possible worlds, the full PTQ lexicon, Henkin models, a completeness
theorem or an equivalence with the earlier `Prop`-valued interpretation.

The rule source remains Chatzikyriakidis and Luo (2020), section 1.3.1,
printed pp. 6-9 and Appendix A1, pp. 175-176. Appendix A1.2 is also the source
for the defined Leibniz equality added here. C is explicitly presented as
the extensional core, not the whole of Montague's intensional logic.

The model distinction is grounded in Hahn and Richter (2015), *Henkin
semantics for reasoning with natural language*, Definitions 4-5 and the
discussion on printed pp. 518-520, DOI
<https://doi.org/10.15398/jlm.v3i2.113>. Those passages were read directly
for this milestone. Consulted PDF SHA256:
`d80700107e1aa69a00421524fc42c749078c9073578ef5d77cc8aded47b05ec9`.

Their language is richer than the present C fragment: it includes a world
sort and selected logical constants, including equality and choice in the
unrestricted language. Their Definition 4 allows restricted frames; their
general-model condition requires every term of the selected language to
denote in its assigned domain. Our implementation must not be described as
an implementation of their entire language or their translation theorem.
Source consultation is AI-assisted, not independent reviewer approval.

## The three structures must remain distinct

| Structure | Truth domain | Function domains | Status |
| --- | --- | --- | --- |
| Earlier interpretation | Coq `Prop` | Full Coq function spaces | Implemented in `Models.v`; conditional constructive/classical soundness retained unchanged. |
| New Boolean interpretation | Exactly `bool` | Full Coq function spaces at every arrow type | Implemented in `BooleanModels.v`; actual finite instances in `BooleanFinite.v` and `BooleanExamples.v`. |
| Intended Henkin interpretation | Classical truth values | Selected admissible functions, with closure for every represented term | Not yet implemented. Requires its own domain/closure design and theorem statements. |

Fullness here means all functions in the specified Coq function type, not
an unproved identification with all functions in an external set-theoretic
universe. The representation is many-sorted through type indices; it is not
a literal family of mutually disjoint sets as in the source's presentation.
Establishing that external representation bridge remains separate work.

The source's inclusion of full models among general models gives a direction
of validity preservation from all general models to all full models. It
does not give equivalence of the two validity notions. No such model-inclusion
or separation theorem has been mechanized in this workbench yet.

## Exact Boolean model data

The domain interpretation is:

```text
bdomain E entity       = E
bdomain E truth        = bool
bdomain E (arrow a b)  = bdomain E a -> bdomain E b
```

A `bmodel` supplies an inhabited E, a typed lexical interpretation and total
Boolean universal quantifiers. The quantifier specification is exact:

```coq
bforall a p = true <-> forall x : bdomain E a, p x = true
```

Thus a constant-true quantifier, a bounded sample of an infinite domain, or
an incomplete list of higher-order predicates does not satisfy the contract.
The field is a visible proof obligation, not a license to claim all model
construction is assumption-free. Two construction routes discharge it below.

Variables use typed assignments. Lambdas denote functions, application uses
function application, implication is `orb (negb p) q`, and universal
quantification uses the specified quantifier at the bound variable's type.
Truth of an interpreted formula means that its Boolean value equals `true`.

`bconsequence H p` quantifies over every model of this declared class and
every assignment satisfying H. A computation in one finite model is not
itself a proof of consequence across the class. The soundness theorem is
what supplies that general conclusion from a derivation.

## Construction route A: finite domains, executable quantification

`finite A` contains a default element, a list of values, decidable equality
and a proof that every A-value occurs in the list. Concrete instances for
`unit` and `bool` are provided.

For function types, `tables` enumerates functions by assigning an output
to each input in the complete input list. `tables_cover_points` proves
that any function agrees with some enumerated table on all listed inputs.
The completeness of the input list and an explicit `FunExt` premise then
prove `tables_complete`: every function belongs to the enumeration, in the
sense of Coq equality. Enumeration is not restricted to syntactically
definable lambda terms or selected lexical predicates.

`function_eq` decides equality by checking all input values. `finite_domain`
recursively supplies finite data at every simple type. `finite_quantifiers`
uses `forallb` over the complete enumeration, and `finite_forall_spec`
proves its reflection property.

The finite model construction needs FunExt for its function-space proofs.
It uses no `ClassicalTruth`, `ClassicalDecision`, choice operator, global
axiom import or unfinished proof. The example computations reduce even
with FunExt left as a variable: it is used in proof fields, not as an oracle
choosing Boolean answers.

With two individuals, the checked enumerations have four tables of type
`entity -> truth` and sixteen of type `(entity -> truth) -> truth`.
These small examples establish that the implementation actually handles
higher-order domains. Enumeration grows exponentially, then repeatedly
exponentially with type structure. This is a reference implementation for
small models, not a scalable general higher-order model finder.

## Construction route B: arbitrary inhabited domains, explicit decision data

For arbitrary domains, the optional premise is:

```coq
ClassicalDecision := forall P : Prop, {P} + {~ P}
```

`decision_quantifiers` decides the proposition `forall x, p x = true` and
returns the corresponding Boolean. Its reflection law is proved by cases
on that supplied decision. `decision_model` combines it with any inhabited
entity domain and typed lexicon. `natural_number_model` gives a named
infinite-domain instance conditional on ClassicalDecision.

This is data-valued excluded middle, not merely a proof of `P \/ ~ P` in
Coq's `Prop`. The development proves that ClassicalDecision implies
ClassicalTruth. It does not prove the converse here, assert either globally,
or provide an executable decision procedure for arbitrary propositions.
No theorem says finite examples eliminate this obligation for infinite
domains. No Hilbert choice operator is present in the object language.

## Soundness and its assumptions

`beval_rename`, `beval_substitution`, `beval_instantiate` and
`beta_boolean_sound` prove the binding and conversion properties of the
new interpretation. These use FunExt when equality of denoting functions
is needed. The earlier structural results about syntax and derivations
remain independent of these semantic premises.

`derivation_boolean_sound` proves soundness for either logical mode.
Universal introduction and elimination use quantifier reflection;
conversion uses beta soundness. Encoded falsity denotes `false`, encoded
negation denotes `negb`, and double negation has the same Boolean value
as its argument. Therefore the classical rule is sound by Boolean reasoning.

`classical_boolean_sound` consequently has the shape:

```coq
FunExt -> derives classical H p -> bconsequence H p
```

It has no additional ClassicalTruth premise. This is not a proof of excluded
middle for every Coq proposition. The model already has a two-element truth
carrier and quantifiers with reflection proofs. For arbitrary entity domains,
the supplied model can be constructed through ClassicalDecision; for finite
ones, enumeration supplies those quantifiers.

This also does not prove completeness or strict constructive/classical
separation. The Boolean model class validates some principles that the
constructive calculus is not given as rules.

## Equality policy

`leibniz_equal u v` is the book's defined formula:

```text
forall P : a -> truth. P(u) implies P(v)
```

`boolean_leibniz_predicates` proves its denotation is preservation of truth
across all Boolean predicates of the full internal function domain.
If equality at the denotation type is decidable, an equality-testing
predicate separates any unequal pair. `boolean_leibniz_equality` therefore
identifies the formula's truth with Coq equality of the two denotations.

`finite_leibniz_equality` discharges the decision obligation with the finite
type construction, including at function types. `decision_leibniz_equality`
discharges it for arbitrary models using ClassicalDecision. The generic
reflection theorem does not silently assume decidable equality at every
Coq type.

No equality-elimination, eta-conversion or functional-extensionality rule
has been added to `derives` or `beta`. Semantic equality of denotations
does not automatically permit object-level conversion between arbitrary
terms. Equality of Boolean denotations is also not equality of arbitrary
Coq propositions, and no propositional-extensionality principle is imported.

## What the examples establish

- `bool_no_men`: a nonempty singleton domain, empty man predicate and true
  walk/move predicates. "Every man walks" evaluates to true; "A man walks"
  evaluates to false.
- `bool_all_men`: the same entity domain, with a different man predicate.
  This changes the truth of the same closed atomic formula.
- `bool_two_people`: John is one individual, while man holds only of that
  individual. "John is a man" is true and "Everyone is a man" is false.
- The countermodel-to-nonderivability theorem excludes the two invalid
  inference patterns in both logical modes, conditional on FunExt.
- The existing universal-instantiation, syllogism, encoded-existence and
  classical double-negation derivations yield Boolean consequence via
  the new general soundness bridge.
- Quantifying over all individual predicates does not make all of them
  hold of John. The enumeration includes falsifying predicates.
- In the two-individual model, walk and move have equal denotations;
  man and walk do not. The defined equality records this distinction.

These are mathematical regression cases, not newly discovered linguistic
generalizations. In particular, evaluating the encoded existential to a
Boolean is not by itself a general witness-extraction theorem. No generic
equivalence between this Boolean encoding and constructive existence in
arbitrary domains has been claimed.

## Acceptance and remaining work

The isolated checker compiles all modules from fresh source, runs `coqchk`,
queries every named proved statement, checks explicit theorem signatures
and rejects invalid quantifier, predicate-sampling and equality fixtures.
The current counts and source hashes are in `verification.json`.

Remaining separate milestones:

1. Review this contract against the intended linguistic baseline. The
   source's named typing adequacy remains unfinished.
2. The selected Ty2 world sort and world-sensitive denotations were added
   in checkpoint 4. Checkpoint 5 proves interpretation preservation for a
   specified world-only IL fragment; see `IL_SPEC.md`. Checkpoint 6 now maps
   every actual old IL constructor to a Prop-valued world/time target, with
   preservation. A restricted target observation relation is now available
   in checkpoint 7; full legacy-to-Boolean composition and unrestricted IL substitution
   remain unproved.
3. Specify and construct Henkin domains with the required interpretation
   closure. Do not reuse the finite full-domain result as a Henkin theorem.
4. Prove precisely stated model/translation bridges. Neither equality of
   the `Prop` and Boolean model classes nor an external set-model adequacy
   result follows from the separate soundness theorems.

No atlas grade, deployed proof-reader entry, live worker or source-level
assessment is changed by this checkpoint.
