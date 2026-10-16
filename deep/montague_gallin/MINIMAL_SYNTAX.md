# Checkpoint 3: PTQ into Gallin's minimal syntax

## Result

The final target now uses only variables, constants, application, lambda
abstraction and equality. Logical connectives and quantifiers are defined
terms, following Gallin (1975), pp. 15-16 and section 8, pp. 59-60.

Eliminating the richer intermediate syntax preserves interpretation for
every typed term, including open terms, over arbitrary signatures, entity
and index carriers, and assignments. Composing that result with the PTQ
translation preserves the previous admissibility, entailment,
satisfiability and English-derived countermodel results.

This closes the extra-primitive-constructors gap. It does not remove the
temporal restrictions on the PTQ model correspondence or establish
Gallin's axiomatic calculus or Henkin completeness.

## 1. A genuinely smaller language

`Minimal.ctm` has six constructors:

```coq
CVar  (* bound variable *)
CFree (* free variable *)
CCon  (* typed constant *)
CLam  (* lambda abstraction *)
CApp  (* application *)
CEq   (* equality at any target type, returning t *)
```

Gallin's four numbered formation rules cover five forms: variables,
constants, application, abstraction and equality. The sixth constructor
here only separates bound and free variables in the encoding. There is no
primitive negation, conjunction, universal quantifier, existential
quantifier, necessity or tense operator. No logical constants are added
to the parameterized signature.

`ceval` is independently defined by recursion on these constructors. It
does not call the richer evaluator or translate back into it. The only
logical operation in its clauses is equality reflected into Boolean truth.

## 2. Definitions from the source

The table uses `=` for Gallin's extensional equality in Ty2. The variables
p and q have type t; f has type t -> t. Quantified x can have any target type.

| Defined term | Minimal expression | Checked semantics |
|---|---|---|
| T | `(lambda x_t. x) = (lambda x_t. x)` | `true` |
| F | `(lambda x_t. x) = (lambda x_t. T)` | `false` |
| not p | `F = p` | Boolean negation |
| p and q | `(lambda f. (f p = q)) = (lambda f. f T)` | Boolean conjunction |
| p implies q | `(p and q) = p` | Boolean implication |
| p or q | `(not p) implies q` | Boolean disjunction |
| p iff q | `p = q` | Boolean biconditional |
| forall x. p | `(lambda x. p) = (lambda x. T)` | Universal quantification |
| exists x. p | `not (forall x. not p)` | Existential quantification |

Gallin writes the propositional operators as lambda terms. The code uses
their beta-reduced applications as syntax macros. Biconditional uses
the existing Boolean equality; it is not an additional primitive.

Conjunction is worth reading carefully. Equality of the two functions
requires agreement for every Boolean function f. If p and q are true,
both sides agree. If either is false, the identity or constant-false
function separates the sides. `gallin_conjunction` checks all four cases.
`ceval_and` then proves that inserting the extra f binder leaves the
meanings of arbitrary p and q unchanged. That depends on the proved
renaming and weakening lemmas, not on assuming that p and q are closed.

Universal quantification works because the predicate function equals the
constant-true function exactly when every argument makes the predicate
true. The converse direction uses function extensionality. Existential
quantification uses the classical Boolean reflection already supplied by
the model. It is not justified by treating intuitionistic negation as
classical without an explicit assumption.

## 3. Eliminate the richer constructors

`eliminate` is structural recursion on `gtm`. It preserves the variable,
constant, lambda, application and equality constructors and replaces
each extra logical constructor with the corresponding macro.

The central theorem is:

```coq
elimination_preserves_interpretation :
  forall S P E I B lex free FE G a (p : gtm S P G a) rho,
    ceval B lex free (eliminate p) rho =
    geval B lex free p rho.
```

Here B is `BooleanTruth`, FE is `FunExt`, and the valuations and environment
have their corresponding typed domains. The actual signature is checked
by the isolated build. This is not a finite truth-table test of translated
examples: it covers every term by structural induction. The Boolean cases
use the abbreviation lemmas; lambda and quantifier cases handle all bound
values.

`include_core` embeds the minimal syntax back into the richer syntax.
`eliminate_core_identity` proves the exact syntactic round trip
`eliminate (include_core p) = p`. This is a retraction between the two
target presentations, not a reverse translation from Ty2 to PTQ.

## 4. Compose with the actual PTQ development

```text
English analysis tree
  -> source-first PTQ translation
  -> explicit-index rich Ty2 term
  -> minimal Ty2 term
```

`minimal_translate p` is `eliminate (translate_intension p)`.
`minimal_open_preservation` covers every PTQ term and source environment.
`minimal_english_preservation` composes the translation of every
implemented English analysis tree and category with elimination.

`elimination_in_every_standard_model` applies without temporal-coherence
conditions. `minimal_backward_preservation`, which reconnects the target
to tensed PTQ, retains the explicit coherent-model boundary.

## 5. Keep the postulates on the target side

`core_admissible N` requires the nine PTQ meaning-postulate families as
minimal target formulas, evaluated at every assignment and index.
It is not defined as admissibility of a reconstructed source model.

The proofs establish:

```coq
minimal_admissible_model_correspondence :
  core_admissible N <-> admissible (reconstruct_model N).

minimal_consequence_correspondence :
  core_consequence (map minimal_translate ps) (minimal_translate q) <->
  source_consequence admissible ps q.

minimal_satisfiability_correspondence :
  source_satisfiable ps <-> core_satisfiable (map minimal_translate ps).
```

`core_consequence` and `core_satisfiable` accept actual minimal target
formulas. Their correspondence with PTQ is proved for translated
formulas. Premise lists are finite; the quantified terms, model carriers,
constant valuations and assignments are not a bounded sample.

`minimal_temperature_countermodel` transports the existing admissible
model and English analysis trees. `minimal_temperature_inference_invalid`
establishes the resulting target non-entailment. This is the preservation
of a known linguistic example, not a new claim about temperatures.

## 6. What checking guarantees

The isolated checker recompiles every imported source and every target
module with Coq 8.20.1, runs `coqchk`, audits all recorded definitions and
theorems, and checks exact signatures and intentionally invalid claims.
The tests include rejecting a primitive rich connective as a core term,
confusing universal and existential syntax, dropping bound variables,
dropping admissibility, and claiming the false Boolean universal is true.

No admitted proof or additional global axiom is used. Boolean reflection
and function extensionality remain explicit inputs. The kernel does not
verify that the source passages were transcribed faithfully. The source
map records AI-assisted consultation; no independent human review is claimed.

## 7. Remaining work

Checkpoint 4 completes the next distinct comparison, untensed IL over
arbitrary index carriers, in `UNTENSED_MODELS.md`. A reverse translation,
an object-language proof calculus, description principles and Henkin
completeness remain separate tasks. None is required to make the present
minimal-syntax preservation theorem true.

The deployed atlas, its grades and comparisons, the live Coq service,
and the frozen source PTQ checkpoint have not been changed by this work.
