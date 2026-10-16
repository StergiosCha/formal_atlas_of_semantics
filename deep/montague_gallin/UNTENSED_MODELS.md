# Checkpoint 4: untensed IL over arbitrary index domains

## What is now proved

Untensed intensional logic and its minimal Ty2 translation agree on
interpretation, validity, consequence and satisfiability over all standard
models of the implemented signature, with arbitrary inhabited entity and
index carriers. Theories are arbitrary predicates on formulas, so the
result is not restricted to finite lists of premises.

This is the internal, machine-checked standard-semantics correspondence
of the kind stated by Gallin (1975), Theorem 8.2, p. 62. It uses full Rocq
function spaces, explicit Boolean reflection and function extensionality.
It is not a proof about every external set-theoretic model, an object-level
derivability correspondence, or Henkin completeness.

The existing tensed PTQ results remain intact. They answer a different
question and still require their temporal and lexical conditions.

| Comparison | Tensed PTQ, checkpoints 2-3 | Untensed IL, checkpoint 4 |
|---|---|---|
| Source syntax | All 18 implemented PTQ constructors | 16 constructors, with no `Will` or `Has` |
| Index carrier | Declared world-time product | Arbitrary inhabited type I |
| Temporal relations | Must agree with same-world strict time order | Arbitrary target values, unused by the translation |
| Meaning postulates | Nine PTQ families for admissible consequence | None imposed; assumptions may be supplied as formulas in the theory |
| Premises | Finite lists | Arbitrary predicate-defined sets |
| Final target | Minimal lambda/application/equality syntax | The same minimal target syntax |

## 1. Separate untensed syntax explicitly

`Untensed.itm` retains variables, constants, abstraction, application,
equality, Boolean connectives, quantifiers, necessity, intension and
extension. It has no tense constructor and no dummy interpretation of
tense.

`embed_il` embeds these terms into the actual `MontaguePTQ.Syntax.tm`.
`embedded_il_is_untensed` proves that the embedding contains no tense
operator, even inside another expression. The two exclusion theorems
prove that no embedded term is a `Will` or `Has` term.

The compiler is not reimplemented. Every new translation uses
`translate_intension (embed_il p)`, followed by the already checked
minimal-syntax elimination. Constants therefore retain the existing
index-dependent translation, and the established binder handling is reused.

## 2. Specify models without a time structure

`il_model` supplies:

- an inhabited entity type E and an inhabited index type I;
- Boolean truth reflection and function extensionality;
- an index-dependent value for every typed source constant.

There is no world carrier, time carrier, order, accessibility relation or
PTQ admissibility field. Type domains are defined independently by
`idomain`: e denotes E, t denotes `bool`, arrows denote full functions,
and an intension of type a denotes `I -> idomain E I a`.

`ieval` independently interprets all 16 source constructors. Necessity
quantifies over every index in I. Intension abstracts over that index;
extension applies an intension at the current index. The evaluator does
not call the target interpreter.

## 3. Relate the value domains and all open terms

`il_domain_agreement` proves, by induction on source types, that the
source domain matches the translated target domain. `il_lift` and
`il_lower` transport values along that equality; their compositions are
proved to be identities.

`untensed_interpretation_preservation` then proceeds by induction on the
source term. Its assumptions relate source constants and free-variable
values to their target counterparts. There is no assumption about the
two temporal symbols in the shared target signature.

The proof handles arbitrary bound-variable environments as well as free
assignments. Under a lambda or quantifier, it extends both environments
and uses the inverse value maps. Under intension or necessity, it inserts
an index binder and proves that source-variable references still point
to the same values. `il_canonical_environments_match` constructs the
required environment for every source environment, ruling out vacuity.

`untensed_minimal_preservation` composes this proof with the previous
elimination theorem. The resulting target has no primitive connective,
quantifier, modal or tense constructors.

## 4. Keep the connection to the PTQ formalization

`forget_ptq_time M` takes an existing PTQ model and retains its entities,
world-time pairs as indices, logical assumptions and constant values.
It forgets the temporal structure as structure. Values are transported
between the separately defined source-domain recursors.

`ptq_untensed_interpretation` proves that interpreting an `itm` term in
this model agrees with interpreting its `embed_il` image using the
existing PTQ evaluator, through those value transports. It uses the two
general preservation theorems, not just a few matching examples.

This compatibility does not manufacture a time structure for an arbitrary
IL model. The new general IL models genuinely do not require one.

## 5. Construct models in both directions

`il_target M` builds a standard target model with exactly M's entity and
index carriers. Its indexed constants receive the lifted source values.
The two unused temporal symbols are assigned false as a harmless default.

`il_reconstruct N` accepts every independent `standard_model source_symbol`.
It keeps N's carriers unchanged and lowers each indexed constant value
to the corresponding source type. No temporal-coherence proof or PTQ
meaning postulate is required. Assignments are reconstructed similarly.

The forward and backward interpretation theorems cover all open source
terms. Indexed constant values and assignments are recovered by the
appropriate round trips. `untensed_model_roundtrip` establishes recovery
of every translated untensed expression.

That last scope matters: the round trip need not recover an arbitrary
target expression containing one of the unused temporal symbols. The
regression model below makes the difference explicit.

## 6. Prove the standard-semantic correspondence

An IL theory is a predicate `Gamma : il_formula -> Prop`.
`translated_il_theory Gamma` is its image in minimal target syntax.
Both sides use one common assignment and evaluation index for all
premises and the conclusion.

The checked statements are:

```coq
untensed_standard_consequence Gamma q :
  il_standard_consequence Gamma q <->
  ty2_standard_consequence (translated_il_theory Gamma)
    (il_minimal_translate q).

untensed_standard_satisfiability Gamma :
  il_standard_satisfiable Gamma <->
  ty2_standard_satisfiable (translated_il_theory Gamma).
```

Validity follows by taking the empty theory. In each direction the proof
takes an arbitrary model, constructs its counterpart, transfers each
premise, and transfers the conclusion. Satisfiability transfers the
witnessing model instead. No enumeration or bounded search is involved.

The target representation packages Gallin's explicit index variable as
the argument of a term of type s -> t. Consequence evaluates that term at
an arbitrary i; it does not assert equality to a constant-true function
or move the premises under separate index quantifiers.

The shared target signature contains the translated source constants and
two temporal constants retained for compatibility. Those temporal values
are unrestricted here. The theorem does not depend on additional unused
constants or free variables from a larger possible signature.

## 7. Regression models and boundaries

`plain_model` has E = `bool` and I = `bool`, not a world-time product. A
sentence constant is false at one index and true at the other. The tests
prove that it can be true at the current index while its necessity is
false. Necessity has not accidentally become current-index truth.

Setting both temporal relations everywhere true or everywhere false does
not change any translated untensed term, even with open bound variables.
But after reconstruction and embedding, the everywhere-true temporal
constant becomes the chosen false default. A separate checked example
therefore refutes unrestricted target-expression round-trip preservation.

The empty theory has an explicit satisfying model on each side, under
the stated BooleanTruth and FunExt inputs. Nonempty carriers and available
assignments are not assumptions about a nonexistent model class.

## 8. What remains separate

The work includes the standard-model semantic correspondence for untensed
IL in this representation. Checkpoint 5 now supplies the separate Ty2
theorem calculus and its standard-model soundness in `CALCULUS.md`.
The semantic correspondence is not itself a translation of proofs.
Checkpoint 6 adds a source IL calculus and a restricted proof-to-proof
compiler in `IL_CALCULUS.md`. Description principles D, full proof-system
correspondence, Henkin models, completeness and a reverse syntax
translation remain separate work.

The source passages are recorded in `SOURCE_MAP.md`. Consultation and
proof engineering were AI-assisted, with no independent human review
claimed. Kernel checking verifies the consequences of the encoding,
not its fidelity to the book. The existing PTQ checkpoint, atlas records,
live Coq service and deployed site are unchanged.
