# Checkpoint 5: a Ty2 proof calculus and its soundness

This records checkpoint 5. Checkpoint 6 adds the source IL calculus and
a restricted proof-to-proof compiler in `IL_CALCULUS.md`. Checkpoint 7
completes the general forward proof compiler in `FULL_PROOF_TRANSLATION.md`.
Neither adds completeness or the full IL+D/Ty2+D result of Theorem 8.3.

## Result

The development now contains an object-language derivation datatype for
Gallin's Ty2 axiom families A1, A2, A3 and AS4, and its replacement rule R
(Gallin 1975, p. 60). Every derivation is proved sound in the existing
full-function-space Boolean interpretation, hence in every implemented
standard target model.

This adds a proof-theoretic object to the previous syntax and semantics.
A `Derivation p` is a tree built from the declared object-language rules.
It is not a synonym for `ceval p = true`, and there is no constructor
that accepts an arbitrary Rocq proof of semantic truth.

The result is soundness of a typed, locally indexed presentation. It is
not completeness, equivalence of named and indexed proof presentations,
or the IL+D to Ty2+D proof interpretation of Gallin's Theorem 8.3.

## 1. Keep three levels separate

| Level | Representation | What is checked |
|---|---|---|
| Target expressions | `ctm S P G a` | Object-language typing and binding |
| Target derivations | `Derivation p` | Construction using A1-A3, AS4 and R |
| Metatheory | Rocq proofs such as `ty2_derivations_sound` | Every such derivation has the stated semantic consequence |

The central metatheorem is:

```coq
ty2_derivations_sound :
  ... -> Derivation p -> forall rho, ceval B lex theta p rho = true.
```

The omitted parameters are the typed signatures and carriers, Boolean
reflection B, function extensionality, and constant and free-variable
assignments. The isolated checker verifies the full signature.

Everything is represented inside Rocq, including the proof trees. The
distinction is that Ty2's derivability relation now has its own explicit
rules, rather than being identified with whichever reasoning Rocq admits.
Rocq remains the metalanguage and checker of the metatheorems.

## 2. Encode the source axioms

The page image was checked directly because OCR loses equality signs and
type subscripts. The following table uses equality for Ty2 equality.
All connectives and quantifiers in these formulas expand to the minimal
lambda/application/equality syntax already checked in checkpoint 3.

| Source | Formula | Role |
|---|---|---|
| A1 | `(g T and g F) = (forall x_t. g x)` | The truth domain has the two Boolean cases. |
| A2 | `x = y implies f x = f y`, with f of type a -> t | Equality respects predicates. |
| A3 | `(forall x_a. f x = g x) = (f = g)` | Function extensionality. |
| AS4 | `(lambda x_a. A_b(x)) B_a = A_b(B_a)` | Capture-avoiding beta substitution. |

`axiom1` through `axiom4` construct these formulas. `Ty2Axiom` recognizes
their source instances. A1-A3 accept variables, represented either by
context positions or named parameters. A compound term does not become
one of those variable instances merely by being well typed. AS4 accepts
arbitrary correctly scoped bodies and arguments with the specified types.

The semantic lemmas for A1-A3 are slightly stronger: they prove the
displayed equations valid even for arbitrary well-typed argument terms.
This does not add those broader instances as primitive proof rules.

## 3. Implement substitution, including its binder case

`csubst` performs simultaneous substitution for context variables.
`csub_lift` extends a substitution under a lambda. The new innermost
variable maps to itself; every substituted outer term is weakened so its
references still reach the same outer variables. Named parameters and
constants are unchanged by this binder-substitution operation.

`subst0 p q` substitutes the argument q for the nearest variable of p.
`substitution_preserves_interpretation` proves the general environment
lemma. `beta_interpretation` then proves the semantic equation needed by
AS4 for every body, argument and environment.

For example:

```text
(lambda x. lambda y. x) z  ->  lambda y. z
```

It must not become `lambda y. y`. A syntactic test checks the de Bruijn
shift. A semantic test sets the outer z to false and applies the result
to true: the correct result is false, while the capturing version returns
true. This is a test of the encoding, not a new fact about Gallin's logic.

## 4. Represent one occurrence for rule R

`ccontext S P D a G b` is a typed one-hole context. Its hole accepts an
a-term scoped in D, and plugging it produces a b-term scoped in G.
The constructors select the function or argument of an application, the
left or right side of equality, a lambda body, or the whole term.

There is exactly one hole. Binder declarations are not term positions in
this representation, so the occurrence that Gallin excludes as
"immediately preceded by lambda" cannot be selected. Occurrences in a
lambda body can be selected.

The inference constructor has the shape:

```text
Derivation (p = q)     Derivation (plug C p)
------------------------------------------------ R
                 Derivation (plug C q)
```

The equality proof is scoped at the hole's context D. Soundness supplies
equality for every environment of D, including every value assigned to
variables bound between the outside of C and its hole.

This universal condition is essential. At an assignment where x is true,
`x = T` holds. But replacing x by T under `lambda x` would identify the
identity function with the constant-true function. They differ at false.
`pointwise_equality_cannot_justify_lambda_replacement` checks this example,
and `pointwise_true_equation_has_no_derivation` rules out the offending
equation as an unconditional theorem of the calculus.

Consequently this checkpoint implements a theorem calculus, not a rule
allowing arbitrary local hypotheses to be treated as global theorems.
There is no `ByHypothesis` constructor. Checkpoint 6 implements Gallin's
finite implication-chain definition of derivability from assumptions for
the source IL calculus. It does not add a local hypothesis constructor to R.

## 5. Prove soundness by induction on derivations

`ty2_axioms_sound` handles the four axiom families. A1 uses the two
Boolean cases, A2 equality congruence, A3 extensionality, and AS4 the
substitution theorem.

`ty2_derivations_sound` then performs induction on the derivation tree.
The axiom case invokes that lemma. For R, the first induction hypothesis
gives equality at every hole environment. The context lemma transports
that equality, including through lambda bodies. The second induction
hypothesis gives truth of the original formula, hence truth after the
replacement.

`standard_model_derivation_soundness` specializes the result to the
independent standard-model record. Boolean reflection and function
extensionality remain explicit inputs. No new global axiom is introduced.
The object-language logic is not made constructive merely because the
metatheorem is checked by Rocq's constructive kernel.

## 6. Build and check explicit proof trees

Reflexivity, symmetry, transitivity, context congruence, truth and beta
expansion are derived operations, not extra primitive constructors.
For example, AS4 proves `(lambda x. x) p = p`; one application of R to its
left side yields `p = p`.

The examples include all three variable axiom families, a named-parameter
instance of A1, and beta replacement inside a lambda body. Their values
are actual `Derivation` objects checked by Rocq's type checker.

`il_proof_formula` applies the existing minimal IL translation to an
explicit index variable. `derived_il_translation_is_valid` proves:

```coq
Derivation (il_proof_formula p) ->
il_standard_consequence (fun _ => False) p.
```

`il_constant_reflexivity_proof` is an explicit proof tree for the actual
translation of `c = c`. It uses derived reflexivity and beta expansion.
`il_reflexivity_via_object_proof` obtains IL validity through that tree
and the semantic correspondence, not by treating a semantic proof as
an object-language derivation.

This is an end-to-end connection for the encodings. This particular result
is not a translation of source proof trees. Those trees and a restricted
compiler are added separately in checkpoint 6.

## 7. Verification and remaining scope

The isolated build checks all source dependencies, recompiles the new
modules, runs `coqchk`, audits global assumptions, and checks exact
signatures and negative fixtures. Those fixtures reject host equalities
as object proofs, variable capture, pointwise replacement under binders,
broader primitive A1 instances, and the reverse of the soundness theorem.

`ty2_no_derivation_of_false` gives a relative consistency result using a
Boolean standard interpretation. It explicitly takes BooleanTruth and
FunExt; it does not construct those foundational assumptions itself.

Soundness does not provide completeness or a proof-search procedure for
standard higher-order validity. Gallin's completeness discussion uses
general/Henkin models. Those models, completeness, description principles
D and the proof interpretation of Theorem 8.3 remain separate work. The
source IL calculus is now covered by checkpoint 6. The source-mapped locally indexed presentation has not been
proved equivalent to a second implementation using Gallin's named syntax.

The prior semantics and PTQ results, atlas assessments, live Coq service
and deployed site are unchanged. Source consultation and implementation
were AI-assisted; no independent human source review is claimed.
