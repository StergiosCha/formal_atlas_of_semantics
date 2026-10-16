# Actual legacy evaluator correspondence

## Source pin and target choice

Source: `deep/PTQ_deep2.v`, imported as `LegacyPTQ.PTQ_deep2`, unchanged.
SHA256: `ee13df1359e47ca5856a3a35eacb9107beba145253a2f07c8fb39894477cd926`.

Checkpoint 5 proved a world-only Boolean IL translation but did not map the
actual old datatype or its World*Time/Prop evaluator. Checkpoint 6 fills the
code-to-code gap using a parallel Prop-valued explicit-index target. It does
not fill the Prop/Boolean model-comparison gap by changing truth carriers.
Checkpoint 7 separately adds [OBSERVATION_SPEC.md](OBSERVATION_SPEC.md): a
guarded relation between the two existing target evaluators, not a theorem
for all legacy translations or equivalence of their unrestricted model classes.

The target is an intrinsically typed higher-order language, with distinct
entity, truth, world, time and index sorts and unrestricted arrow formation.
Its index carrier is the product of the world and time carriers. Pairing,
projections and a time-order predicate are explicit primitives. There is no
hidden evaluator index. All logical operators and equality denote the same
Coq operations as in the legacy interpreter.

This target is not claimed to be Gallin's complete Ty2 language or a new
axiomatization of Montague. The earlier world-only Boolean target and its
object calculus remain separate.

## Exact coverage

The translation is a total recursion on the actual `Old.IL` datatype, not a
new source copy or an embedding of only a convenient fragment. Therefore
exhaustive matching covers every currently defined constructor:

- The head variable and `var_s`, which discards the corresponding assignment
  entry while translating an arbitrary subterm, not just a variable.
- All 25 named lexical constructors, mapped to their actual old parameters.
- Lambda and application, primitive equality at every legacy type, negation,
  conjunction, disjunction, implication and biconditional.
- Universal and existential quantification at every legacy type.
- Necessity, future, past, intension and extension.

The old `c_necessarily` lexical modifier remains distinct from the `nec_`
logical constructor. No axiom identifying them is introduced. Unused old
parameters such as `pen_den` and `time_le` are not imported into the new
theorems' dependency sets merely to make an allowance broad enough.

Because the theorem covers every IL term, it also applies to terms generated
by the existing English-to-IL functions. This does not prove that those
functions give the linguistically intended readings or correctly implement
the published PTQ rules. Those are source-adequacy questions.

## Type carriers and why no propositional extensionality is needed

`legacy_type` maps e/t to the corresponding target sorts, arrows recursively
to arrows, and `ty_s a` to an arrow from the explicit index sort. For every a,
`legacy_carrier a` proves an equality of Coq types:

```text
Old.Den a = pdomain Old.Entity Old.World Old.Time (legacy_type a).
```

Base cases are reflexivity. Arrow cases transport the two induction equalities
through the ordinary function-type constructor; intension uses the same
construction with the identical World*Time domain. These are equal carriers,
not just abstractly isomorphic carriers and not an arbitrary equivalence of
logical propositions. `legacy_lift` and `legacy_lower` transport values along
this equality and its reverse.

Generic identity-elimination lemmas prove that these transports commute with
application, lambda, primitive equality, universal and existential quantifiers.
For example, the primitive-equality result is equality of the two propositions,
not only logical equivalence, and needs no propositional-extensionality axiom.
It follows by elimination of the carrier equality. This is possible precisely
because truth and the recursive domain structure have been retained.

FunExt is still explicit in the general evaluator theorem. It identifies
functions whose values agree pointwise under binders. It is not used to turn
arbitrary logically equivalent propositions into equal propositions. The
cast lemmas and canonical-assignment witness do not require FunExt.

## Translation invariant

`compile_legacy t r i` translates t using a typed tuple r of target variables
for the old context, and a target term i of index sort. The source assignment
is a nested product; the target assignment is a typed variable lookup.
`assignments_match` relates corresponding entries by `legacy_lift`.

Under lambda or a source quantifier, r gains a new target head variable,
the remaining variables shift, and i is weakened beneath the new binder.
The assigned target value is transported back to the corresponding source
carrier in the induction proof. The round-trip lemmas establish the new
assignment relation.

Under index/world/time binders there is no new source variable. All old
variable references shift, preserving their assigned values. The explicit
index term used for translating the body changes as follows:

| Legacy operator | Target binder | Body's explicit index |
| --- | --- | --- |
| `nec_ p` | Universal world w' | Pair w' with the time projected from weakened i |
| `will_ p` | Existential time t' | Pair the world projected from weakened i with t'; require current time < t' |
| `has_ p` | Existential time t' | Same pair; require t' < current time |
| `up t` | Lambda over an entire index i' | The fresh index variable i' |
| `down t` | None | Apply translated t to the current explicit index i |

In particular, `up` may vary time even in a source expression containing no
future or past operator. Quantifying over all indices is not the same as
the old necessity operator. No world accessibility relation or temporal order
laws are supplied: the old `time_lt` relation is preserved as a parameter.

## Preservation statements

`legacy_interpretation_preservation` quantifies over the actual source term,
target context, variable tuple, current-index term and related assignments.
Its conclusion is:

```text
target_eval (compile_legacy t r i) rho
  = legacy_lift a (Old.eval t env (target_eval i rho)).
```

The proof is by induction on the actual source term. Lexical cases reduce
to the mapped old parameter. Application uses transport/application
compatibility; equality uses transport/equality compatibility. Source
quantifiers use the carrier-transport laws, after the induction hypothesis
identifies their predicate functions. Necessity and tense preserve the
unchanged index component using the target weakening theorem. Intension
varies the complete index while preserving the source assignment.

`canonical_assignments_match` constructs related target assignments for every
legacy assignment. There is no hidden rigidity, time-independence or
definability restriction. `legacy_open_preservation` then packages any open
legacy term as an explicit index function, preserving values at every index.
Truth and premise-true/conclusion-false corollaries follow. These are
pointwise correspondence results for the specified shared interpretation,
not reverse syntax translation, completeness or source fidelity.

## Assumptions and models

The main theorem's global dependency set is exactly 29 old parameters:
three carriers, the time_lt relation and 25 lexical denotations. General
preservation also has the explicit FunExt argument. The checker records each
new statement's actual subset of the 29 and rejects every other dependency.
The ten generic target/transport lemmas have closed global contexts.

The old file imports classical modules, but the new bridge does not call its
classical theorems. Dependency checking found no use of excluded middle,
propositional extensionality, proof irrelevance or another additional logical
axiom. This does not justify saying that the whole old library has no such
dependencies. Import reachability and a particular proof's dependencies are
different facts.

The old parameters are retained as parameters. No concrete interpretation
of the full old lexicon is constructed. Unlike the earlier Boolean model
record, the old declarations do not require inhabited World or Time types.
The bridge does not silently add nonemptiness. Particular regression cases
take a world, times, distinctness or order edges as explicit hypotheses.
No inference from those hypotheses to a new source-level linguistic result
is claimed.

## Regression claims and remaining obligations

Fifteen proved regressions exercise actual legacy expressions and their
translations. With a time-dependent proposition intension assigned to a
variable, its extension can be true at one time and false at another even
without tense syntax. Its necessity can hold at the first time without
holding at all indices. Future/past preserve the world and opposite order
directions. Other cases cover arbitrary-term weakening, primitive equality,
higher-order quantifiers and the actual freezing/re-evaluation distinction.

Seven rejected fixtures test all-index necessity, time erasure, reversed
future order, treating Prop as bool, omission of FunExt, world/time sort
confusion and unsafe index-erasing beta conversion. These are engineering
checks of distinctions in the specification, not seven new discoveries
about Montague.

Still unproved: a full legacy-to-Boolean relation; a target object proof
calculus and its soundness; rigidity-aware source substitution; reverse
translation or conservativity; Gallin equivalence; Henkin completeness;
external set-model adequacy; and independent source/English-translation review.

The old source file and the 173-statement core are unchanged. No assessment,
frontend, live worker, LaTeX draft or public deployment is changed here.
