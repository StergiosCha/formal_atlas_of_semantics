# Checkpoint 6: source IL proofs and a first proof compiler

## Result

Gallin's source IL now has an explicit primitive syntax, a syntactic
modally-closed predicate, axiom instances, derivation trees and a proof
that every derivation is sound in the implemented standard models.
Reasoning from assumptions follows his finite implication-chain definition.

A first proof-to-proof compiler also constructs actual Ty2 derivations,
but only for the explicitly represented `ILPointwiseProof` fragment:
derived reflexivity, AS4.2, and rules R1-R3/R6-R8. Its terms may contain
any primitive IL operation. It does not translate every `ILDerivation`.

The three results have different types:

```coq
il_derivations_sound :
  ... -> ILDerivation p -> forall rho i, lval M p rho sigma i = true.

il_derivation_implies_translated_validity :
  ILDerivation p ->
  ty2_standard_consequence (translated_il_theory (fun _ => False))
    (il_minimal_translate (include_il p)).

compile_pointwise_proof :
  ILPointwiseProof p -> Derivation (il_at p).
```

The first two are semantic metatheorems. Only the third produces a target
proof tree. No converse from semantic validity to derivability is assumed.

## 1. Read the source before selecting the presentation

The source is Gallin (1975), pp. 11-16 and 19-20. The scan of p. 19 was
checked visually, particularly the hats/checks, equality signs and AS4
side conditions. The source's primary presentation uses a guarded general
beta schema and a replacement rule. Immediately afterwards, Gallin gives
alternative schemas AS4.1-AS4.7 and rules R1-R8.

This checkpoint implements that explicitly listed alternative. It does
not implement unrestricted beta substitution and hope that the model
will make it sound. It also does not claim a machine-checked equivalence
between the alternative and a second encoding of the primary presentation.

Bound variables use typed context positions. Free variables retain typed
natural-number names. These are encoding choices, not source notation.
There is no separately encoded named calculus whose equivalence has been
proved. Source consultation and implementation were AI-assisted; no
independent human source approval is claimed.

## 2. Use primitive IL syntax

`ILCore.ltm` contains variables, constants, lambda, application, equality,
intension and extension. Bound and free variables are separate constructors.
There are no primitive conjunction, quantification, necessity or tense
constructors in this datatype.

`include_il` maps it into the existing untensed syntax, and `lval` uses
the existing `ieval` through that inclusion. This is deliberately reuse
of an established interpretation, not a claim to have independently
written another evaluator. The existing compiler and semantic
correspondence therefore continue to apply to these source expressions.

`ltrue`, `lfalse`, `land`, `limp` and `lall` expand into lambda and
equality, following pp. 15-16. As in the target minimal syntax, operator
applications are represented by their beta-reduced macros. Their semantic
clauses are proved. Necessity is the source abbreviation:

```text
Box A := equality (Up A) (Up T)
```

`lval_box` proves that this means truth at every index, with the assignment
fixed. It does not introduce a primitive source modal evaluation clause.

## 3. Encode modal closure, not an informal rigidity guess

On p. 14, Gallin defines the smallest class MC containing variables and
every `Up A`, closed under application, equality and lambda abstraction.
`ModallyClosed` has exactly those generating cases, splitting bound and
free variables to match the representation.

An arbitrary constant is not in MC. Neither is `Down A` automatically
in MC when A is. A term can happen to be index-independent in a particular
model without being syntactically modally closed.

`modally_closed_is_index_independent` proves the required direction:

```text
ModallyClosed A
    implies
value(A, rho, sigma, i) = value(A, rho, sigma, j)
```

This holds for every implemented model, environment, free assignment and
pair of indices. The lambda case uses the model's function-extensionality
field. No converse is claimed.

## 4. Implement the axiom schemas

| Source | Implemented form and side condition |
|---|---|
| A1 | Boolean cases T/F exhaust a truth-type variable. |
| A2 | Equal arguments have equal values under a predicate variable. |
| A3 | Pointwise equality of function variables is function equality. |
| AS4.1 | An unused binder can be removed; its body is explicitly weakened from the outer context. |
| AS4.2 | Applying the identity lambda to B yields B. |
| AS4.3 | Application in a lambda body distributes the beta step. |
| AS4.4 | Equality in a lambda body distributes the beta step. |
| AS4.5 | A beta step crosses an inner lambda with capture-avoiding context exchange. |
| AS4.6 | A beta step crosses Down. |
| AS4.7 | A beta step crosses Up only with a `ModallyClosed` argument. |
| A5 | Necessarily equal extensions of intension variables give equal intensions. |
| AS6 | Down of Up A equals A. |

A1-A3 and A5 take `il_axiom_variable`, not arbitrary terms. The separate
semantic lemmas for A1-A3 prove a stronger validity statement, but do not
broaden the primitive rules. For A5, validity is proved for modally closed
intensions and then specialized to variables.

AS4.5 deserves a binding check. If A has context `[y; x; ...]`, the
right-hand side has a new outer y and an inner x, so A's context becomes
`[x; y; ...]`. `lswap` exchanges exactly those two references; `lweaken`
keeps B's outer variables free of the newly introduced y. The renaming
interpretation theorem checks this, and a negative fixture rejects the
capturing version.

## 5. Prove all inference rules sound

`ILDerivation` introduces axioms and the source's R1-R8:
equality elimination, application congruence in either position, lambda
congruence, Up congruence, Down congruence, and equality congruence in
either position.

Soundness is an induction on these actual proof trees. Lambda congruence
uses the induction hypothesis at every bound-variable value. Up
congruence uses it at every index. These universal conditions come from
theoremhood, not from treating a currently true hypothesis as a theorem.

All standard models here use full internal Rocq function spaces and
carry BooleanTruth and FunExt explicitly. Soundness does not remove those
foundational commitments. It does not establish general/Henkin-model
soundness, completeness, or an identification with all external
set-theoretic models.

## 6. Discharge assumptions as Gallin specifies

Page 20 defines derivability from Gamma through a finite list of its
formulas and a theorem:

```text
B0 -> (B1 -> (... -> A))
```

`ILFrom Gamma A` packages that list, its membership evidence and its
`ILDerivation`. `il_from_assumptions_sound` proves pointwise consequence
when Gamma is true at the current environment and index.

This does not add an unrestricted hypothesis constructor to
`ILDerivation`. In particular, a locally true equality cannot be used
under Up by pretending it is an unconditional theorem.

The semantic correspondence transports this consequence to the translated
target theory via `il_assumptions_imply_translated_consequence`. That
result is still semantic, not a discharged-hypothesis proof compiler.

## 7. Compile an explicit proof fragment

`il_at` is the body of the already established translation at an explicit
index variable. This is checked syntactically:

```coq
il_minimal_translate (include_il p) = CLam (il_at p).
```

`ILPointwiseProof` contains derived reflexivity, AS4.2, equality elimination,
application congruence, Down congruence and equality congruence. An erasure
function constructs an `ILDerivation`, proving that every permitted input
really is a source proof.

`compile_pointwise_proof` recursively constructs Ty2 `Derivation` objects
using target AS4 and R, including the derived congruence operations from
checkpoint 5. It takes no model, BooleanTruth, FunExt, semantic-truth
certificate or completeness theorem as an input. The output is kernel
checked as a target proof tree, rather than reported as plausible code.

The example compiles identity-beta equality on an intension-valued term,
followed by Down congruence. The terms can use intension without the
compiler yet supporting every inference about intension.

The missing coverage is explicit: source R4/R5 and the other axiom
families. In particular, a source `ILDerivation` cannot simply be supplied
where the compiler requires `ILPointwiseProof`. A negative fixture checks
that boundary. This is not Gallin's IL+D/Ty2+D interpretation theorem.

## 8. Counterexamples to the tempting incorrect rules

The test model has two indices and a sentence constant c with value i
at index i. Boolean reflection and extensionality remain parameters.

At index false:

```text
(lambda x. Up x) c     denotes    (fun j => false)
Up ((lambda x. x) c)   denotes    (fun j => j)
```

The functions disagree at true. `unrestricted_modal_beta_is_false`
checks the inequality; soundness then proves that this formula has no
`ILDerivation`. This is why the syntactic condition in AS4.7 matters.

Similarly, c equals F at index false, but Up c does not equal Up F.
`current_index_equality_cannot_be_replaced_under_up` checks both claims.

For A5, the model also has an intension constant f whose value at i is
`fun j => xorb i j`. Its diagonal extension is always false, so its
extensions agree everywhere with those of Up F. Nevertheless, at index
false its intension is the identity function, not the constant-false
function. `axiom_five_cannot_accept_arbitrary_intension_terms` rejects
the overgeneralized axiom.

These are checks of the encoding against Gallin's restrictions, not new
discoveries about his theory.

## Verification and next step

The isolated checker recompiles 21 Gallin modules and pinned PTQ
dependencies, runs `coqchk`, audits global assumptions, checks exact
signatures and rejects 44 invalid fixtures. There are 183 checked theorem,
lemma and example statements; proof-tree definitions and the compiler are
also checked and included in the declaration audit.

Next: extend proof translation beyond the pointwise fragment, starting
with binding/index-renaming lemmas needed by R4 and R5, then realize the
remaining source axiom schemas as target derivations. Description
principles and the full theorem 8.3 require separate treatment. No
completeness or full proof-system equivalence is claimed.

The frozen PTQ implementation, atlas assessments, live library and
deployment are unchanged.
