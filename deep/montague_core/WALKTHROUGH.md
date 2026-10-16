---
title: "Montague in Coq: a code-led technical walkthrough"
subtitle: "From typed expressions to derivations, models and preservation proofs"
author: "For Robin Cooper and Rasmus Blanck"
date: "9 October 2026 | Frozen mathematical checkpoint 7"
lang: en-GB
---

# 1. The positive result and the reading route

We have checked connections between separately inspectable semantic
representations: typed expressions, object derivations, model interpretations
and metatheorems about them. Soundness connects derivations to truth in the
specified interpretations. Translation theorems connect implicit evaluation
indices to explicit arguments. A logical relation connects certified
observations in the existing Boolean and Prop target evaluators.

One preservation theorem covers every expression and assignment of the actual
legacy IL datatype, including time, equality and higher-order terms. This
is a universal theorem about an implementation, not a collection of successful
examples. Its claim is nevertheless code-to-code preservation: whether the
implementation adequately represents the linguistic source is a separate
question. The usefulness of the development is that we can now ask both
questions precisely rather than treating them as interchangeable.

This document explains frozen checkpoint 7; it adds no formalization. Code
excerpts are inserted directly from the hash-checked source with original
line locations. They are excerpts of modules, not standalone programs: their
imports and section parameters come from the full files. The final source
appendix supplies all 26 modules, including every supporting and regression
proof. Schematic formulas in the explanations are mathematical paraphrases,
not additional Coq declarations or claimed compiler output.

The reader needs formal semantics but not prior fluency in dependent Coq
syntax. Read chapters 2-5 for the representation, 6-10 for interpretation and
proof theory, 11-14 for Boolean models and worlds, and 15-18 for the actual
legacy and observation bridges. Reproduction and review instructions follow.

## 1.1 Four levels of claim

| Level | Example | Evidence needed |
| --- | --- | --- |
| Expression | The chosen encoding of "every man walks" | Typing and source fidelity. |
| Object derivation | A derivation of "John walks" from two premises | A tree built from the declared inference rules. |
| Interpretation | Evaluation under a model and assignment | Explicit semantic clauses and lexical meanings. |
| Metatheorem | Every such derivation preserves truth | A proof connecting derivability and interpretation. |

A Coq proof of an interpreted implication is not automatically an object
derivation. An object derivation is not automatically a faithful English
analysis. A soundness proof connects the middle two levels; source review
must still assess the first. These distinctions explain the file structure.

## 1.2 Which bridges actually exist?

| Bridge | Endpoints | Proved relationship |
| --- | --- | --- |
| Extensional embedding | Boolean C and world-typed Boolean syntax | Interpretation preservation through a model reduct and transfer of semantic consequences. |
| World-only IL translation | Specified implicit-world IL and explicit-world Ty2 | Evaluation equality under related assignments. |
| Actual legacy translation | Existing Prop/world-time IL and Prop explicit-index syntax | Evaluation equality after carrier transport, for every legacy term and assignment. |
| Observation bridge | Boolean Ty2 and a world-only image in the Prop target | A type-indexed relation; at truth, equivalence with Boolean truth. |

The fourth bridge has not been composed with every term of the third. The
first two do not acquire tense merely because the third handles it. This
table records proved edges, not permission to claim every possible diagram
commutes. It is also not an equivalence claim about Montague, MTT and TTR.

# 2. How to read the Coq

## 2.1 Data, propositions and implicit parameters

`Type` classifies types; `Prop` classifies propositions. `bool` is a datatype
with constructors `true` and `false`. A proposition P is not a Boolean b.
The proposition `P <-> b = true` can relate them without identifying them.
The iff states a logical relationship; the equality compares Boolean values.

`Inductive` declares constructors, used here for both expressions and
derivation evidence. `Fixpoint` defines recursion whose termination Coq
checks. `Record` groups data and potentially proofs. `Definition` names a
term; some model definitions are built interactively with a proof script.
`forall G a` binds parameters. Braces make arguments implicit, not absent.
`@name` exposes the implicit arguments, while an underscore asks elaboration
to infer an argument. An unresolved hole causes checking to fail.

Section variables become parameters of the definitions that use them.
Consequently a proof with an explicit `FE : FunExt` premise can have a closed
global assumption context. Read `Check theorem_name` for its type and
`Print Assumptions theorem_name` for its external global dependencies. Neither
command alone answers every foundational question.

## 2.2 A small proof-script dictionary

| Instruction | Role in this development |
| --- | --- |
| `intros` | Introduce universally quantified variables or implication premises. |
| `induction t` | Analyze constructors, with hypotheses for recursive subobjects. |
| `apply H` | Use a theorem or constructor matching the goal's conclusion. |
| `eapply H` | Leave some arguments to be inferred from subsequent subgoals. |
| `exact t` | Supply a term already having the required type. |
| `cbn` | Reduce definitions and pattern matches by computation. |
| `change P` | Present the goal as a definitionally equal expression. |
| `rewrite H` | Replace using a proved equality or supported logical rewriting relation. |
| `reflexivity` | Close an equality whose sides reduce to the same term. |
| `f_equal`, `f_equal2` | Transport equality through one- or two-argument functions. |
| `split` | Establish both conjuncts or both directions of an iff. |
| `destruct` | Perform case analysis on data or evidence. |
| `discriminate` | Refute equality of distinct constructors, such as true and false. |
| `auto`, `tauto` | Search for proof terms in supported patterns; the kernel still checks the result. |

Bullets separate branches. In `tactic1; tactic2`, the second tactic generally
acts on all goals produced by the first. Brackets direct tactics to particular
branches. `Qed` closes an opaque theorem; `Defined` keeps a completed
definition transparent for computation.

`apply d_all_elim` constructs an object inference-rule instance. `apply FE`
uses a metatheoretical premise. Both are Coq tactics, but their mathematical
roles differ. At each proof, first identify whether its goal is a derivation,
an evaluation equation, a model field or a relation between interpretations.

# 3. Types and typed variable references

{{snippet deep/montague_core/Syntax.v ty var}}

The constructors entity, truth and arrow are codes for object types, not
their semantic carriers. A later interpreter will assign carriers to them.
This makes it possible to interpret the same syntax with Prop or with bool
at truth type.

`var G a` is a variable of type a available in context G. The head of G is
the most recently added declaration. `vz` selects it; `vs v` refers to an
older variable after a new declaration is inserted. For `[entity; truth]`,
the head can refer to the entity and a shifted head to the older truth
variable. The same notation `vz` has its indices inferred from context.
There is no untyped integer that may later fail at lookup: the reference
itself is typed. No variable can be constructed in the empty context.

## 3.1 The apparently elaborate elimination lemma

{{snippet deep/montague_core/Syntax.v var_cons_cases var_cons_cases}}

P depends on both a variable's type and the variable itself. To prove P for
all variables in a nonempty context, it suffices to handle its head and each
shifted older variable. The dependent `match ... in ... return ...` tells
Coq how the output type varies with the scrutinee's indices. The empty-context
case in the motive is True, making that motive total. The nonempty case
states the required elimination property. The vz branch uses Hz; the vs
branch applies Hs to the older reference.

This is a proof by pattern matching, not an equality axiom. It avoids an
overly strong dependent-elimination tactic and gives a reusable head/old
variable split. That split will discharge the binder cases throughout the
metatheory.

# 4. Expressions and capture-avoiding renaming

{{snippet deep/montague_core/Syntax.v tm tm}}

`tm G a` means a term of type a with free variables in G. Constants come
from a typed signature. A lambda body lives in an extended context; its
result is an arrow term in the old context. Application requires the
argument type to match the function domain. Imp takes truth terms. All
binds any represented type with a truth-valued body.

This prevents applying an entity as a function. It does not determine
whether a linguistic framework ought to encode a noun as an entity predicate.
Typing and adequacy are distinct obligations. Also note that All is
unrestricted here: the later observation certificate deliberately covers
less than the whole language can express.

{{snippet deep/montague_core/Syntax.v ren weaken}}

A renaming maps each variable in G to a same-typed variable in D. `rename`
recurses over syntax and changes only variable references. Under lambda
and All it uses a lifted map. That map sends the new head to itself and
renames and shifts every older reference. Reusing the unlifted map would
confuse a new binder with an old free variable.

`weaken` is the particular renaming mapping v to `vs v`. It extends the
variable context without changing any old reference. This differs from
adding a truth assumption to a derivation context.

Trace one reference: `Var vz` in `[entity]` becomes `Var (vs vz)` after a
new entity binder is added. In `[entity; entity]`, the new head belongs to
the binder and the old reference is one slot farther away. Replacing it
with `Var vz` would capture it. This concrete trace is the motivation for
the lifting code, not a cosmetic choice of variable notation.

# 5. Substitution and algebra before semantics

{{snippet deep/montague_core/Syntax.v sub instantiate}}

A substitution replaces variables by terms, not just by variables. Each
replacement has the same type as the variable it replaces. Under a binder,
the new head maps to `Var vz`; each old replacement is weakened to cross
the binder. Thus free variables inside replacement terms remain free.

`head_sub u` replaces the head by u and removes one shift from older
references. `instantiate u t` applies it to a body t: the output context
is G rather than `(a :: G)`. No model is involved and u is not evaluated.

{{snippet deep/montague_core/Algebra.v subst_comp subst_comp}}

Composition says that substituting theta and then r agrees with replacing
each original variable by its theta replacement with r applied inside it.
Induction on the input term handles ordinary constructors directly. At a
binder, `subst_ext` reduces the goal to pointwise agreement of substitutions.
The new head agrees immediately; older variables use `subst_weaken`.

The theorem equates resulting syntax trees, not substitution functions on
the strength of pointwise agreement alone. Accordingly it needs no FunExt.
This differs from the later equality of semantic lambda functions.

{{snippet deep/montague_core/Algebra.v subst_instantiate map_subst_weaken}}

`subst_instantiate` is needed for universal elimination when transforming
a derivation: substitute the result, or first substitute the body and
argument and then instantiate. `map_subst_weaken` gives the matching equation
for a list of assumptions under universal introduction. The latter says
that weakening then substituting with the lifted map agrees with substituting
then weakening. Transforming a conclusion without transforming its assumptions
would generally be invalid.

{{snippet deep/montague_core/Syntax.v beta beta}}

Beta is a syntactic relation: reflexivity, symmetry, transitivity, a
capture-avoiding beta step and congruence. It is not defined to mean equal
denotation. It introduces no eta or arbitrary extensional-equality rule.
Its semantic soundness must therefore be proved, rather than being true
merely by definition.

# 6. Models, assignments and evaluation

{{snippet deep/montague_core/Models.v domain model}}

Entity types denote the supplied carrier E; truth denotes Prop; arrows
denote Coq function spaces. A model chooses an entity carrier, evidence of
its nonemptiness, and an interpretation of every typed lexical symbol.
Different records may interpret the same symbol differently. Nonemptiness
does not imply that every noun predicate has a witness.

`FunExt` and `ClassicalTruth` define propositions that can be passed as
premises. Naming those propositions does not prove or globally assume them.

{{snippet deep/montague_core/Models.v env eval}}

An environment maps each typed variable to a value. Extending it stores
a new head value and delegates older references to the old assignment.
Evaluation follows the syntax: variables consult the assignment, constants
consult the lexicon, lambdas evaluate bodies under extended assignments,
application applies the resulting functions, implication becomes Prop
implication, and All quantifies over the interpreted carrier.

Evaluating a truth term produces a proposition, not automatically a decision
procedure. Quantification over an arbitrary carrier does not become an
algorithmic search just because its definition is written in Coq.

{{snippet deep/montague_core/Models.v satisfies consequence}}

Satisfaction means that every formula in the premise list holds. Consequence
quantifies over every model and every assignment of this declared
interpretation. "All models" refers to those records and clauses. It does
not automatically mean every external Montague model or every semantic
framework. Nevertheless it is genuinely a quantification over models,
not just evaluation in one fixed lexical interpretation.

# 7. Semantic substitution and beta soundness, case by case

{{snippet deep/montague_core/Models.v eval_substitution eval_instantiate}}

On the left, substitute syntax and evaluate in rho. On the right, evaluate
the original term in sigma. The premise requires each replacement's value
in rho to equal sigma's value for the replaced variable. This is a precise
assignment compatibility condition, not a claim for arbitrary assignments.

The variable case is that premise. Constants are unchanged. Application
and implication follow by rewriting the two subterm induction hypotheses.
For a lambda, the denotations are functions. FE reduces their equality to
equality at an arbitrary x. Apply the body induction hypothesis in extended
assignments: the head case is reflexive, and older variables use semantic
weakening followed by the original compatibility premise.

The universal case seeks equality of propositions, not merely an iff.
The proof constructs equality E of the predicate functions using FE and
the binder invariant, then rewrites underneath forall. This does not use
propositional extensionality to turn an arbitrary iff into equality.
`eval_instantiate` specializes the theorem to `head_sub`; its extended
assignment stores the evaluated argument as the new head value.

{{snippet deep/montague_core/Models.v beta_sound beta_sound}}

Now induction is on conversion evidence. Reflexivity, symmetry and
transitivity use the corresponding equality operations. The beta step
uses `eval_instantiate`, with symmetry to match the equation's orientation.
Lambda congruence uses FE. Application and implication use rewriting.
Universal congruence again equates predicate functions before rewriting
the quantifier. Thus each permitted conversion preserves interpretation.

The converse is not established. Equal values in one finite model do not
authorize use of the object conversion rule.

# 8. Object proof rules and the soundness induction

{{snippet deep/montague_core/Calculus.v logic derives}}

`derives L H p` is indexed by a logical mode, a list of truth assumptions
and a conclusion; its variable context is also present as an implicit
index. Evidence is a derivation tree. Derivability is not defined by
whether the interpreted conclusion happens to hold.

The assumption rule requires list membership. Implication introduction
temporarily adds a premise and then discharges it; elimination combines
an implication and its antecedent. Universal elimination uses syntactic
instantiation. Conversion requires separate beta evidence. Classical
double-negation elimination requires `L = classical`, so it cannot be used
in constructive mode merely because its constructor exists in Coq.

Universal introduction derives a body under `map weaken H`. The fresh
variable is added to the variable context, but old premises do not become
dependent on it. This is the eigenvariable discipline. A fact about John
cannot be generalized by relabelling John as an arbitrary variable.

{{snippet deep/montague_core/Calculus.v derivation_sound derivation_sound}}

The proof keeps model, assignment, mode permission and satisfaction general
while inducting over the derivation. Here is the obligation in each branch:

1. Assumption: satisfaction supplies the selected premise.
2. Implication introduction: assume the interpreted antecedent and construct
   satisfaction for the extended list; its head uses the new assumption
   and its tail uses the original satisfaction proof.
3. Implication elimination: apply the interpreted implication from one
   induction hypothesis to the antecedent supplied by the other.
4. Universal introduction: choose arbitrary x, extend the assignment, and
   apply the body induction hypothesis. Membership in the weakened list
   comes from some old premise q. `eval_weaken` preserves q's value, allowing
   the original satisfaction proof to apply.
5. Universal elimination: `eval_instantiate` identifies the conclusion
   with the body at the argument's denotation. Instantiate the universal
   truth supplied by the induction hypothesis.
6. Conversion: `beta_sound` rewrites the conclusion to the established
   premise's value.
7. Classical rule: the mode permission supplies excluded middle for the
   interpreted conclusion. If true, finish. Otherwise its negation conflicts
   with the interpreted double negation, using `neg_meaning`.

This identifies the assumption boundary. FE enters through binding and
conversion. Classical truth enters only in the classical branch of the
Prop interpretation. Neither is concealed in a tactic name.

{{snippet deep/montague_core/Calculus.v constructive_in_classical countermodel_blocks_derivation}}

The constructive embedding copies derivations into classical mode. This
proves inclusion, not strictness or equivalence. Constructive soundness
discharges the impossible classical-mode condition; classical soundness
supplies CL. The countermodel theorem contradicts a hypothetical derivation
using a model that satisfies its premises and refutes its conclusion. A
failed proof search does not supply that model.

# 9. Following a linguistic inference from syntax to semantics

{{snippet deep/montague_core/Examples.v word john_walks_derivation}}

The signature places John at entity type and man, walk and move at entity
predicate types. Helpers improve readability without changing constructors.
`every_man_walks` binds one entity and uses the same head reference in both
predicate applications.

The target is: from man(john) and every man walks, derive walk(john).
The first tactic applies implication elimination backwards with antecedent
man(john). This creates two obligations: derive man(john) implies walk(john),
and derive man(john). `change` presents the former as the instantiation of
the universal body. That presentation computes to the same syntax, so
change is legitimate. Universal elimination reduces it to the universal
premise, and assumption lookup finds it. The second obligation is another
assumption lookup. `cbn; auto` handles list membership, not an unbounded
semantic inference engine.

{{snippet deep/montague_core/Examples.v john_walks_in_all_models john_walks_in_all_models}}

The derivation has no model parameter. This corollary adds FE and applies
soundness, turning it into consequence over the declared models. The first
result answers which rules derive the conclusion; the second answers why
those rules preserve interpreted truth. Source adequacy is still a third
question.

{{snippet deep/montague_core/Examples.v syllogism_derivation syllogism_derivation}}

The syllogism begins with universal and implication introduction. There
is an arbitrary new entity and a temporary assumption that it is a man.
Instantiate every walker moves at that entity. To obtain its antecedent,
instantiate every man walks at the same entity and use the temporary
assumption. Then discharge and generalize. The context machinery keeps
the two universal premises independent of the fresh variable.

## 9.1 Encoded existence is not an unexplained primitive

{{snippet deep/montague_core/Syntax.v falsity exists_}}

Falsity is `forall X:t. X`; negation is implication to falsity. Conjunction,
disjunction and existence use impredicative continuation-style encodings,
not new rule constructors. To recover interpreted conjunction, choose the
result proposition X to be that conjunction. To recover existence, choose
X to be the corresponding existential proposition.

{{snippet deep/montague_core/Models.v exists_meaning exists_meaning}}

The auxiliary equation E shows that shifting the predicate across a new
truth variable preserves its entity argument. One direction instantiates
the continuation with the actual existential assertion; the other supplies
the given entity witness to any requested continuation. This proves the
meaning of this encoding in the Prop interpretation, with FE. It is not
automatic witness extraction for every alternative encoding.

{{snippet deep/montague_core/Examples.v no_men no_existential_import}}

The entity carrier is unit, John denotes tt, man is everywhere False and
walk is everywhere True. Thus every man walks is true but no man who walks
exists. The domain is nonempty and the noun extension is empty. The first
proof establishes those semantic facts; the next invokes soundness to rule
out the invalid constructive derivation. This does not deny that a different
analysis of natural-language universals might impose additional commitments.

# 10. Proof transformations and interleaved contexts

{{snippet deep/montague_core/Structural.v derivation_substitution derivation_instantiation}}

Every premise and the conclusion receive the same typed substitution.
Induction follows the derivation: membership maps through the premise list,
implication cases reuse their induction hypotheses, universal introduction
uses `map_subst_weaken`, universal elimination uses `subst_instantiate`, and
conversion uses `beta_substitution`. The classical mode evidence is retained.
This transforms proof trees without a model or FE premise. It is not cut
elimination or normalization.

{{snippet deep/montague_core/Contexts.v mixed lookup}}

An interleaved context adds variable declarations and truth assumptions
in sequence. Flattening weakens older assumptions when crossing a variable
declaration. `lookup_var` makes exactly the same adjustment when retrieving
an older assumption. A formula can mention only variables already in scope
when it was introduced.

{{snippet deep/montague_core/Contexts.v mixed_derives mixed_split_equivalence}}

These are independently stated rules, not an alias for split derivability.
One induction turns interleaved lookup into flattened list membership and
follows the corresponding constructors. The reverse induction quantifies
over any interleaved context whose hypotheses equal H. Introduction rules
extend that context and re-establish the flattening equation.

The resulting iff is a genuine equivalence of these two intrinsic
presentations. It does not identify contexts literally: flattening loses
declaration placement. Repacking therefore preserves derivability rather
than syntax identity. Relating the intrinsic presentations to the source's
named typing judgments remains a distinct adequacy obligation.

# 11. Boolean truth and actual finite models

{{snippet deep/montague_core/BooleanModels.v bdomain classical_decision_implies_excluded_middle}}

The Boolean interpretation changes the truth carrier, not the expression
datatype. Entity remains a supplied carrier and arrows remain internal Coq
function spaces. The quantifier record is crucial: it requires both a total
Boolean operation and proof that its answer is true exactly when every
domain element satisfies the predicate. A function returning true without
that proof is not a valid quantifier instance.

An optional constructor uses `ClassicalDecision`, a data-valued decision for
every Prop. It decides the universal assertion and returns the corresponding
Boolean. Its reflection proof follows the two decision cases. The lemma
immediately below derives Prop-valued excluded middle from that premise.
This constructor does not make the premise disappear or provide it for free.
The finite construction takes a different route and does not use it.

{{snippet deep/montague_core/BooleanModels.v bmodel beval}}

The model records its lexical interpretation and its reflected quantifiers.
Implication is the Boolean table `not p or q`. `bimp_spec` connects that
table to implication between the assertions that p and q equal true.
Evaluation's All clause calls the supplied quantifier on the evaluated
body. Thus totality and reflection are explicit model obligations rather
than hidden behavior of the evaluator.

## 11.1 Enumerating all functions, not sampling predicates

{{snippet deep/montague_core/BooleanFinite.v finite finite_unit}}

A finite carrier includes a default element, a list of values, decidable
equality, and evidence that every element occurs in the list. These fields
give an inhabited carrier, not a possibly empty finite set. The list need
not be treated as a canonical duplicate-free enumeration for the proofs
of quantification: completeness is the relevant condition.

`finite_forall_spec` unfolds list quantification. If forallb succeeds, each
carrier element succeeds because completeness places it in the list.
Conversely, if every carrier element succeeds, every listed element does.
This is the exact passage from a finite computation to the intended
universal assertion.

{{snippet deep/montague_core/BooleanFinite.v override finite_arrow}}

The empty table list contains a constant default function. To extend tables
over input x, choose each possible output y and override x in each previously
constructed table. `flat_map` enumerates these alternatives; `map` installs
the new table entry.

`tables_cover_points` inducts on the input list. For its head x choose the
actual value f(x). The induction hypothesis supplies a table agreeing on
the remaining inputs. Overriding at x agrees there by construction; at any
different listed input it retains the previous agreement. This produces a
table agreeing pointwise with an arbitrary function on every listed input.

`tables_complete` applies that result to the complete input enumeration.
Every input is listed, so the table agrees with f everywhere. FE turns
that pointwise equality into function equality, allowing the list membership
proof for the table to count as membership for f itself. This is the exact
use of FE. Without proving this coverage, an enumeration of a few convenient
predicates would not be a full function-space model.

`function_eq` compares outputs at every input. In the successful branch,
FE turns pointwise equality into equality of functions. In the failed
branch, assuming function equality would force every comparison to succeed,
contradicting the failed forallb. `finite_arrow` packages these constructions
as a finite carrier of functions.

{{snippet deep/montague_core/BooleanFinite.v finite_domain booleans_are_two_valued}}

Recursion on object types now supplies a finite carrier at every Boolean
semantic type, including nested arrows. The resulting quantifier uses
forallb over the complete enumeration. With two entities, there are four
Boolean entity predicates; predicates of those predicates have sixteen
possible tables. At still higher types, this grows rapidly. Executability
does not imply efficient exhaustive reasoning at arbitrary type depth.

These are full internal function spaces because the coverage proof ranges
over arbitrary Coq functions of the interpreted type. The result is not
an external set-model representation theorem and not a construction of
restricted Henkin domains.

## 11.2 Why classical Boolean soundness needs no extra CL argument

{{snippet deep/montague_core/BooleanModels.v bfalsity_value derivation_boolean_sound}}

If encoded falsity were true, quantifier reflection would imply that every
Boolean is true, including false. That contradiction proves its Boolean
value false. Negation then reduces to negb, and double negation reduces
to the original Boolean by involution.

The derivation induction otherwise parallels Prop soundness. Implication
uses `bimp_spec`; introduction of a universal uses quantifier reflection
and semantic weakening; elimination uses reflection at the argument value;
conversion uses Boolean beta soundness. The classical branch uses Boolean
double negation, not excluded middle for every Coq proposition.

The conclusion is soundness for either object mode in the declared Boolean
model class, given FE and the quantifier-bearing model. It does not prove
that the two modes derive the same formulas. A semantic class may validate
more principles than a particular sound proof calculus can derive.

# 12. Equality: which equality is being discussed?

{{snippet deep/montague_core/BooleanEquality.v leibniz_equal boolean_leibniz_equality}}

The object equality is a defined formula: every predicate that holds of
u holds of v. It is not a newly installed primitive equality rule. The
bound predicate occupies the head variable, so u and v are weakened beneath
its binder. Quantifier reflection and semantic weakening expose the formula's
meaning as quantification over all Boolean predicates of the carrier.

To derive equality of denotations from that condition, the proof needs a
predicate that recognizes the denotation of u. The explicit equality
decision Eq defines it: return true exactly when the argument equals u's
value. It holds of u by reflexivity. The Leibniz condition says it holds
of v, forcing Eq to choose equality. In the converse direction, equal
denotations are interchangeable for every predicate by rewriting.

The finite construction supplies Eq at every represented type. The optional
arbitrary-domain result obtains Eq from ClassicalDecision. Neither dependence
is omitted from the theorem's contract. Also distinguish three equalities:
the object formula `leibniz_equal u v`; equality of its semantic denotations;
and equality between arbitrary Coq propositions. The last is not obtained
merely by sharing a Boolean truth value.

# 13. Explicit worlds and the extensional-core connection

{{snippet deep/montague_core/Ty2Models.v wdomain wmodel}}

The world syntax adds a distinct world type, ws, alongside entity and truth.
`wdomain E W ws` is W; an intension of a proposition has type `ws -> wt`
and denotes a function from W to bool. The model fixes nonempty entity
and world carriers, a typed lexicon and reflected quantifiers. Entity
domains are constant across worlds in this construction.

The evaluator has no implicit current-world argument. A world occurs as
an explicit term or as an argument of a denoted function. A constant can
denote a world-varying function even though evaluating the constant itself
does not consult an implicit world. This distinction between a fixed
function value and its varying outputs recurs in the IL translation.

{{snippet deep/montague_core/Ty2Syntax.v necessarily at_world}}

World application is ordinary typed application. Necessity is universal
world quantification applied to the weakened proposition intension. The
definition quantifies over all worlds; it does not add a Kratzer modal base
or accessibility relation. Those would require their own explicit structure.

{{snippet deep/montague_core/Ty2Models.v necessity_meaning intension_application_beta}}

Quantifier reflection gives truth at every world. Semantic weakening removes
the newly inserted variable from the interpretation of the original intension.
The result establishes the intended meaning of this definition of necessity.
It does not license inferring necessity from an assumption true only at one
world. The two-world fixtures in the full source exhibit the failure.

## 13.1 A model reduct is an actual construction

{{snippet deep/montague_core/Ty2Embedding.v value_maps lift_lower}}

The C types and their embedded world types are interpreted by different
recursive functions. Explicit value maps connect their carriers. At entity
and truth they are identities. At arrows they translate inputs in the
reverse direction and outputs in the forward direction. This is the familiar
variance of a function-space map, made executable in the code.

Round trips are proved by induction on type, using FE at arrows. These
proofs justify transporting quantifiers and lexical meanings, instead of
assuming the recursive domain interpretations are definitionally identical.

{{snippet deep/montague_core/Ty2Embedding.v reduct_quantifiers embedding_interpretation}}

Given a world model, the reduct inherits its entity carrier and interprets
core constants by lowering the corresponding world values. Its quantifier
maps arguments through lower_value. Reflection in the reverse direction
uses a lifted arbitrary core value and the lower/lift round-trip equation.

The interpretation theorem inducts over core syntax. The assignment premise
relates corresponding variables. The constant case uses the round trip;
lambda uses FE and related extended assignments; application uses both
induction hypotheses followed by cancellation of lower and lift; quantification
uses equality of the transported predicate functions.

The later consequence theorem applies this interpretation result and existing
Boolean soundness to an original core derivation. It transfers semantic
consequences. It does not itself construct a syntactic world-calculus
derivation or prove conservativity in the reverse direction.

# 14. Implicit-world IL: translation and the two binder cases

{{snippet deep/montague_core/ILSyntax.v ity itm}}

This specified source language distinguishes extension types from intension
types. Its intens a maps to a world-to-a arrow in the target. The constructors
include ordinary lambda/application, implication, universal quantification,
intension, extension and necessity. It excludes time and primitive equality.
It is therefore not introduced as a rebranding of the actual old datatype.

{{snippet deep/montague_core/ILTranslation.v idomain ieval}}

The source evaluation is defined independently of the translation. It takes
an assignment and a current world. Variables and constants return fixed
values from the assignment and lexicon. Lambda extends the assignment but
retains the world; application evaluates both sides at the same world.
`IUp t` ignores its outer evaluation world and returns a function evaluating
t at a new world. `IDown t` evaluates t at the current world and applies
the resulting intension to that world. `IBox p` evaluates p at all worlds.

The source shares the target's declared value domains and reflected
quantifiers. This makes the domain correspondence explicit, but means the
theorem is not independently establishing equivalence of arbitrary model
classes.

{{snippet deep/montague_core/ILSyntax.v ivmap translate_intension}}

The translation carries a map of source variables and a typed term for
the current world. It does not reserve an untyped variable name such as w.
There are two genuinely different binder cases:

| Binder crossed | Variable map | Current-world term |
| --- | --- | --- |
| Source lambda or All | Lift the map, giving the new source variable the new target head. | Weaken the old world term so it still denotes the old world. |
| Intension or necessity | Shift old source variables past the newly inserted world binder. | Use the new head world variable as the evaluation world. |

For Down, translate the intension under the current environment and apply
it to the same explicit world term. For Up, abstract over a new world and
translate the body at that world, without rebinding source variables. These
operations encode the difference between evaluation index and assignment.

{{snippet deep/montague_core/ILTranslation.v explicit_world_preservation explicit_world_preservation}}

The theorem quantifies over every source term, destination context, variable
map, world term and compatible pair of assignments. Its target value equals
source evaluation at the denotation of that world term.

Variable and constant cases use compatibility and reflexivity. Lambda
uses FE, the lifted map, a weakened world term and the assignment-extension
invariant. The quantifier case has the same binder invariant, applied to
the predicate supplied to the reflected quantifier. Application and
implication transport equalities through their operations. Up uses FE
over the fresh world and shifts the variable map. Down applies the
intension equality at the current world. Box again reasons pointwise over
the world binder. Each case follows one actual translation clause.

## 14.1 Why unrestricted substitution under intension is unsafe

{{snippet deep/montague_core/ILExamples.v il_weather il_nonrigid_intension}}

In the frozen expression, evaluate a world-sensitive entity at the current
world and pass that entity into a lambda. Inside the lambda, Up packages
the assigned entity into a world function. Changing the world later does
not change that assigned entity. In the recomputed expression, Up contains
the original world-sensitive expression and re-evaluates it at each world.

{{snippet deep/montague_core/ILExamples.v unsafe_index_substitution_changes_denotation source_freezing_and_recomputation_are_distinct}}

At the actual world true, the concept's value is true. The frozen intension
still returns true at the alternative world false; the recomputed intension
returns false there. The source beta-like replacement that forgets the
evaluation-world dependence would equate these different values. The
target's ordinary beta rule remains safe because its substituted argument
contains the explicit actual-world term.

{{snippet deep/montague_core/ILTranslation.v down_up_cancellation implicit_necessity_meaning}}

Down after Up cancels definitionally. The reverse direction requires index
rigidity of the intension-valued expression. This concerns whether evaluating
the expression at different outer indices yields the same function. It does
not require that function to be constant in its own world argument. A
lexical intension may be a fixed function with varying outputs. Keep these
two meanings of rigidity separate when reading the theorem's premise.

# 15. The actual legacy IL: worlds, time and equality retained

The previous chapter was not a proof about the old implementation. This
chapter is. `LegacyTranslation.v` imports the unchanged `PTQ_deep2.v` under
a separate namespace and translates its actual constructors. The new target
has entity, truth, world, time and world/time-index sorts, arrows, logical
primitives, pairing, projections and temporal order. Its truth carrier
remains Prop.

{{snippet deep/montague_legacy/IndexModels.v pdomain peval}}

The target evaluator takes no implicit index. A pair term provides the
index explicitly. PWorld and PTime project its components; PBefore uses
the supplied time-order relation. Other clauses independently interpret
the typed syntax, including native Prop equality and quantification. This
is not defined by calling the old evaluator on a reverse translation.

## 15.1 Why carrier transport is justified

{{snippet deep/montague_legacy/IndexModels.v carrier_cast cast_exists}}

`carrier_cast p x` transports x along an equality p of carrier types.
The proof is equality elimination: when p is reflexivity, transport is
identity. The generic round-trip, application, lambda, equality and
quantification lemmas are proved by eliminating the carrier equalities
and then using reflexivity. They are not arbitrary conversions between
isomorphic domains.

{{snippet deep/montague_legacy/LegacyTranslation.v legacy_type legacy_exists}}

Legacy intension becomes an arrow from the entire index pair. Recursion
proves equality between the old denotation carrier and the new target
carrier for each old type. Entity and truth cases are reflexivity; arrows
use the carrier constructor. The lift and lower maps are those justified
casts.

The equality lemma can consequently state equality between the propositions
expressing equality of transported and original values. It does not obtain
proposition identity from an arbitrary iff. That is why no propositional
extensionality premise is needed here. This carrier-equality argument must
not be reused when the truth carrier changes from Prop to bool: those
carriers do not come with such an equality.

## 15.2 Every lexical constructor is accounted for

{{snippet deep/montague_legacy/LegacyTranslation.v legacy_word named}}

The target lexicon explicitly maps all 25 legacy constants to their old
values through the carrier lift. Names are not matched by text fragments,
and no unspecified default handles missing constructors. Each fixed
constructor has a typed branch. This preserves the implemented meanings;
it does not prove that those old lexical meanings are faithful to all
of Montague's linguistic examples.

## 15.3 The translation, including the easily mishandled cases

{{snippet deep/montague_legacy/LegacyTranslation.v legacy_vars compile_legacy}}

The old variable context is represented by a tuple-like structure, so
`legacy_vars` supplies a corresponding target variable for each source slot.
Shifting inserts a target binder without adding a source variable. Lifting
adds both the new source head and its target reference.

The old `var_s` constructor weakens an arbitrary term, not only a variable.
Its translation recursively handles that term with the tail variable map.
Replacing it with a target variable successor would silently omit a real
part of the source language. Lambda and source quantifiers lift the map
and weaken the old explicit index term.

The modal and temporal cases rebuild an index pair deliberately:

| Source operation | New quantified value | World used in the body | Time used in the body |
| --- | --- | --- | --- |
| Necessity | A world w | Fresh w | Original time |
| Future | A time t' later than the original time | Original world | Fresh t' |
| Past | A time t' earlier than the original time | Original world | Fresh t' |
| Intension | An index pair i' | World of i' | Time of i' |

Future tests original-time-before-t'; past tests t'-before-original-time.
Reversing that order changes the implemented meaning. Necessity is not
quantification over every world/time pair: its time component is fixed.
Up abstracts over the entire pair. Down applies an intension to the current
explicit pair. Omitting tense syntax alone does not prove that an assigned
intension is independent of time.

## 15.4 The assignment premise is satisfiable for every old assignment

{{snippet deep/montague_legacy/LegacyTranslation.v assignments_match target_eval}}

For each source slot, the target assignment at its mapped reference must
equal the lift of the source value. The empty context has no obligations.
`assignments_shift` preserves compatibility under an extra target binder;
`assignments_lift` additionally extends the source environment with the
lowered target head value. The lift/lower round trip proves the new head
condition.

Canonical maps and assignments are then constructed from every old context
and assignment. `canonical_assignments_match` proves their compatibility
by induction. This matters: a general conditional theorem with an impossible
assignment premise would tell us little. Here a compatibility witness is
provided for each actual old assignment.

## 15.5 The preservation proof, without skipping the difficult branches

{{snippet deep/montague_legacy/LegacyTranslation.v legacy_interpretation_preservation legacy_interpretation_preservation}}

The induction is on the actual old syntax. The initial computation leaves
the carrier lifts and target evaluator controlled, rather than expanding
everything into an unreadable recursive expression. `try reflexivity`
closes the fixed-constant branches whose clauses agree by construction.
`expose_target` merely uses `change` to display a definitionally equal
left-hand side; it is not an equality axiom.

For var_z, take the head equality in the assignment premise. For var_s,
use the recursive hypothesis with its tail. For lambda, rewrite the lifted
function through `legacy_lambda`, apply FE at arbitrary target x, and use
the body hypothesis with the source value lowered from x. Compatibility
is `assignments_lift`; semantic weakening preserves the old index.

For application, use the two induction hypotheses to replace function and
argument values, then apply `legacy_application`. For equality, do the same
under the equality constructor and then use `legacy_equality`. Propositional
connectives use congruence through the corresponding Prop operation.

For each source quantifier, first compare body predicates pointwise using
FE, compatible extended assignments and index weakening. Then the carrier
quantifier law changes quantification over lowered target values into
quantification over source values. This explicitly handles higher-order
carriers; the proof is not limited to entity quantification.

For necessity, equate predicates of worlds pointwise. The body induction
hypothesis receives the fresh world paired with the original time and an
assignment shifted past the target-only binder. For future and past, equate
predicates of times. One conjunct preserves the temporal-order test by
weakening; the other invokes the body hypothesis at the original world
paired with the new time. The order direction stays different in the two
branches.

For Up, `legacy_intension` exposes a function of the complete index. Apply
FE, introduce an arbitrary pair, and use assignment shifting. For Down,
apply the intension equality at the current index and simplify the lifted
intension. No time coordinate is discarded in any of these steps.

{{snippet deep/montague_legacy/LegacyTranslation.v legacy_open_preservation legacy_counterexample_preservation}}

The general theorem is specialized to the canonical assignment and an
explicit index-function abstraction. The remaining compatibility premise
is discharged by the canonical witness. The truth and counterexample
corollaries follow by rewriting. This is the strongest immediate legacy
claim: for every implemented old expression and assignment, the translated
evaluation agrees after justified transport.

The proof retains the old Entity, World and Time parameters, temporal
relation and 25 lexical values: 29 global parameters in the main theorem's
audit. It uses explicit FE but adds no new global logical axiom dependency.
The old source may contain other proofs with classical dependencies; an
audit of this preservation proof is not an assertion about every old theorem.

# 16. Prop/Boolean comparison: certify a fragment and relate values

{{snippet deep/montague_legacy/ObservationBridge.v observation_type observable}}

The syntax embedding maps actual Ty2 terms into the world-only part of
the existing Prop target. It is defined on the whole Ty2 syntax. The
preservation theorem is guarded by the inductive proposition observable.
This distinction between a total syntax map and a restricted theorem is
essential when assessing coverage.

Variables and constants are certified. Lambda, application and implication
inherit certificates from their subterms. General quantification is
certified only over entities or worlds. A separate constructor certifies
the particular encoded falsity `forall X:t. X`, which is false on both
sides. That exception is not permission for arbitrary truth quantification.
Negation and necessity receive certificates through supporting lemmas.

The fragment is not strictly first-order: higher-order composition and
lexical values are allowed, subject to the semantic relation. But arbitrary
quantification over propositions or predicates and unrestricted equality
are outside its current guard. Failure to have a certificate under these
constructors is a limit of this theorem, not a proof that every excluded
formula could never admit a different comparison proof.

## 16.1 The logical relation is the substantive comparison contract

{{snippet deep/montague_legacy/ObservationBridge.v observation_relation observation_envs_extend}}

The entity and world carriers are shared, and their values must be equal.
At truth, the Prop value must hold exactly when the Boolean value is true.
At arrows, related arguments must produce related results. Thus a Prop
entity predicate and a Boolean entity predicate are related pointwise,
without pretending they have the same codomain or are equal functions.

There is no premise that every Prop-valued function has a Boolean partner.
The lexical relation instead requires a witness of relatedness for each
constant actually supplied, and the environment relation requires one
for each corresponding variable. Higher-order constants are therefore
constrained, not admitted with arbitrary meanings on either side.

Environment extension uses the newly supplied value relation at the head
and the old assignment relation at shifted references. This is the binder
invariant for the fundamental theorem.

## 16.2 The fundamental theorem, constructor by constructor

{{snippet deep/montague_legacy/ObservationBridge.v observation_preservation observation_preservation}}

Induction is on the certificate, not unrestricted syntax. The distinction
ensures that each universal case carries evidence of an allowed carrier.

The variable case reads the assignment relation and the constant case reads
the lexical relation. For lambda, introduce arbitrary related arguments,
extend the environments with them, and apply the body's induction hypothesis.
The goal is a relation on functions, not identity of functions, so FE is
unnecessary. For application, the related function values take the related
argument values to related results by the arrow clause itself.

For implication, the two induction hypotheses relate antecedent and
consequent truth. `bimp_spec` expresses the Boolean implication in terms
of its truth assertions; propositional reasoning combines these equivalences.
This is not treating an arbitrary unreflected Prop as decidable. The
reflection premises for the participating expressions are already present.

For universal quantification, destruct the sort certificate. There are
only entity and world cases. Both sides quantify over the same carrier,
so relate each value to itself by equality, extend the assignments and
use the body's relation. Boolean quantifier reflection supplies the
universal truth assertion needed on that side. An arbitrary predicate or
truth carrier would not have this immediate shared-carrier argument.

For encoded falsity, the Prop side is `forall P:Prop, P`; instantiate with
False to refute it. The Boolean side evaluates to false by the existing
falsity lemma. Both directions of the iff then follow. This exceptional
case does not assume a Boolean representation for every Prop.

The theorem needs no FE. It does need the certificate, model with its
reflected quantifiers, related lexical meanings and related assignments.
A theorem being closed under the global context does not erase those
arguments.

{{snippet deep/montague_legacy/ObservationBridge.v observation_truth observable_derivation_prop_sound}}

Truth specializes the relation at truth type. Refutation follows because
a Boolean that is not true must be false. Decidability for each certified
interpreted formula follows by case analysis on its related Boolean.

Inference agreement relates satisfaction of a certified premise list and
certified conclusion at a related model/assignment pair. It holds for
every pair satisfying the premises, not just the later examples. But
equality of validity over unrestricted model classes would additionally
require coverage of those classes by related pairs. No such surjectivity
or coverage theorem is asserted.

The final theorem transfers the semantic consequence of an actual Ty2
derivation. Its endpoints must be certified; intermediate formulas need
not be certified because Boolean soundness handles the derivation before
endpoint agreement is used. This theorem DOES take FE, inherited from
Boolean soundness. It does not produce a new derivation in a Prop-target
object calculus, because no such calculus has been added here.

# 17. Witnesses, paired models and concrete comparisons

{{snippet deep/montague_legacy/ObservationBridge.v observation_entity_witnesses observation_finite_witnesses}}

Witnesshood is a separately chosen observation on a certified predicate
body with a free entity variable. It is not a newly added existential
constructor or a covert double-negation encoding. The first theorem takes
an existing witness x on either side, extends both assignments with the
same x, and applies truth correspondence. It therefore preserves entity
identity, not just the proposition that something exists.

The finite theorem connects that actual existential observation to existsb
over a complete entity enumeration. In one direction completeness ensures
the given witness is searched; in the other, a successful listed witness
is a genuine entity. This iff is not an implemented generic extractor from
arbitrary Prop proofs into computational data. It also does not compare
dependent pairs or proof objects from MTT or TTR.

## 17.1 The relation premises are actually inhabited

{{snippet deep/montague_legacy/ObservationExamples.v observed_word paired_formula_agreement}}

Entities and worlds both use bool in these small fixtures, but the object
sorts remain distinct. The shared table record supplies noun, verb,
weather and concept values. The Boolean model uses the already constructed
full finite model. The Prop lexicon interprets a predicate table at x as
the proposition that its entry at x equals true. Names and entity concepts
retain their values. The unused time carrier is unit.

The lexical-relation proof examines every constant. For names it uses
equality. For predicates and concepts it introduces related inputs,
substitutes their equality, and finishes by reflexivity. Empty assignments
are related because no variables are available. `paired_formula_agreement`
therefore applies the fundamental theorem with proved compatibility,
not with a hypothetical uninhabited lexical premise.

The paired model uses FE for finite function-domain construction. Thus
its instances retain FE even though the generic relational preservation
proof does not. Inspect theorem types before inferring assumption-freedom
from short computational proofs.

{{snippet deep/montague_legacy/ObservationExamples.v observed_instantiation_derivation instantiation_agrees_for_all_tables}}

The example provides actual object derivations and applies them to every
choice of paired tables. On the Prop side, consequence is transferred
through the observation theorem; on the Boolean side, it follows directly
from world soundness. This proves the general inference for this family,
not merely one successful table lookup.

## 17.2 Empty noun extension and a real witness

{{snippet deep/montague_legacy/ObservationExamples.v empty_people_tables named_individual_supplies_a_witness}}

The empty fixture makes man false at both entities. Its universal statement
is true, but existsb finds no witness. The Prop interpretation agrees.
The second result uses John directly as the witness when man(John) is given.
The comparison is about actual entity witnesses, with no inference from
the mere nonemptiness of the entire domain to nonemptiness of a noun.

## 17.3 Actual truth, necessity and substitution

{{snippet deep/montague_legacy/ObservationExamples.v actual_truth_does_not_license_necessity mismatched_lexicons_can_change_the_answer}}

In the varying fixture, weather is true at the actual world and false at
the alternative. Consequently actual weather is true but necessity is
false. Both interpretations agree. This refutes local necessitation from
an arbitrary actual-world fact; it does not refute a rule whose premise
is an appropriately assumption-free theorem.

The next counterexample checks equality of actual entity values for a
rigid and a varying concept, in both interpretations. Their actual
predications also agree. But the rigid concept always denotes John,
whereas the varying concept denotes another entity elsewhere, where man
is false. Necessary predication therefore differs. Agreement at one
world does not license replacement inside arbitrary intensional contexts.

Double negation agrees for the reflected observation. This is consistent
with Coq remaining constructive: the particular proposition has a Boolean
reflection witness. The final diagnostic deliberately changes the lexical
interpretation and obtains a different answer for the same atom. It
illustrates why the lexical-relation premise is substantive, not optional.

# 18. The foundational boundary, proved as implications

{{snippet deep/montague_legacy/ObservationBridge.v reflected_proposition_is_decidable truth_equality_bridge_requires_propositional_extensionality}}

The first proof splits on a supplied reflecting Boolean. If true, its
reflection implies P; if false, reflection rules out P. This establishes
excluded middle for that particular reflected proposition.

The second theorem supposes every Coq proposition has some reflecting
Boolean. Apply the first result to the witness for arbitrary P. That gives
ClassicalTruth. The witness is existential evidence in Prop, not a supplied
global computational function deciding every proposition. The result
proves a conditional cost of total reflection; it neither supplies that
premise nor proves an impossibility theorem about all possible bridges.

The third proof obtains logical equivalence between propositions reflecting
the same Boolean. The fourth adds two hypotheses: total reflection and
a bridge identifying equality of propositions with equality of their
reflecting Booleans. For logically equivalent P and Q, choose reflected
values b and c. Opposite Boolean values contradict the equivalence and
reflection. Their equality then gives P = Q through the additional bridge.
That is propositional extensionality. Again the theorem exposes what a
stronger comparison would require; it does not install the hypotheses.

## 18.1 Answers to the recurring foundational questions

We are still inside Coq: its kernel checks the metatheory. A deep embedding
does not change that. What it does change is the object of reasoning.
Derivations are explicit mathematical data, so we can prove soundness,
substitution preservation and relationships between presentations rather
than only proving isolated interpreted propositions.

The host is constructive, but object rules need not be exclusively
constructive. Classical rules can be encoded as constructors; their
soundness requirements are then made explicit. Soundness into Boolean
models does not prove strict separation of constructive and classical
derivability, nor their equivalence.

There are models: parameterized Prop interpretations and executable finite
Boolean instances, with explicit world structure where provided. The
model-theoretic commitment is not erased by implementing it in type theory.
However, no theorem here identifies internal function spaces with an
external set-theoretic universe or supplies Henkin admissible domains.

Finally, an observation preserving a shared entity witness is not already
a comparison with MTT or TTR. Those frameworks may require native typing,
signature, inhabitance or record information that a shared truth observation
does not express. The present technique gives a precise style of question
to ask, not a blanket conclusion about those frameworks.

# 19. Reproduce and inspect the results

The accompanying `proofs/` directory contains the frozen source, both
checkers and the declaration parser they use. Coq 8.20.1 and Python 3 are
required. From that directory:

```sh
python3 deep/montague_core/check.py --check
python3 deep/montague_legacy/check.py --check
```

These build fresh temporary copies and perform kernel rechecks. Stale local
compiled files cannot make the check pass. The core requires closed global
contexts for its 173 named proofs. The companion separately audits 76,
allowing only the specified legacy parameters where appropriate. The 36
observation proofs have closed global contexts. Explicit theorem premises
are still part of the contract.

There are 37 negative fixtures across the checks. Each must fail with its
expected diagnostic category. They test boundary enforcement, including
capture, mode conditions, incomplete quantifiers, index erasure, omitted
certificates and false concrete consequences. Their failure is not a
standalone theorem that every attempted proposition is unprovable in every
possible system. Actual countermodels and soundness supply the stronger
mathematical nonderivability results where stated.

## 19.1 A short interactive inspection session

Start the companion's isolated interactive mode:

```sh
python3 deep/montague_legacy/check.py --check --inspect
```

It loads the existing modules after checking them. The accompanying
`WALKTHROUGH_SESSION.txt` contains the commands below. The FE variable is
local to a temporary Section, not a new global axiom or a change to the
frozen library.

{{session}}

The evaluation commands compute true for actual weather, false for necessary
weather, true for the empty-noun universal, and false for its witness search.
The packet contains a captured session log, so these are reproducible
computations rather than invented screenshots. Read the printed theorem
types as well as their assumption reports. In particular, compare the lack
of FE in generic observation preservation with its presence in derivation
transfer. The legacy preservation assumption report retains the old parameters.

Do not compile the old corpus file in place under the companion namespace
and then reuse that compiled artifact under the original corpus namespace.
The isolated checker avoids this collision. Quit inspection with Ctrl-D
or Quit. Changes to temporary files are not changes to the repository.

# 20. What a reviewer should decide, and where we stop

The primary calculus source is Chatzikyriakidis and Luo (2020), section
1.3.1, pp. 6-10, and Appendix A1, pp. 175-176, following Luo and Soloviev.
The classical rule is an explicitly stated extension of the implemented
base presentation. Hahn and Richter's discussion motivates the distinction
between full and Henkin interpretations; it is not a license to call the
present full internal models a Henkin completeness construction.

For source fidelity, compare the actual rules, typing discipline, lexical
types and index behavior with the source passages. For mathematical
correctness of the represented claims, inspect the theorem types and
reproduce the kernel checks. For significance, decide whether the explicit
preservation and observation relationships address the linguistic question
of interest. These are complementary reviews, not interchangeable approvals.

The nine observation cases are synthetic regressions. Their familiar
inferences and countermodels are not advertised as newly discovered
linguistic facts. The contribution is the audited connection between
representations, the explicit premises under which it works, and the
ability to inspect both successful consequences and counterexamples.

AI assistance can propose code, explanations and proof scripts. A proposal
becomes a formal theorem only after the checker accepts its proof term.
But a checked theorem can still formalize the wrong source reading, or
a statement weaker than the prose suggests. Exact source excerpts, premise
audits, negative tests and independent semantic review address different
parts of that risk. No AI-generated confidence score substitutes for them.

The positive paper claim is therefore: machine-checked soundness and
interpretation-preservation results for specified Montague-style fragments,
including a direct bridge for the actual legacy evaluator, plus a guarded
observational correspondence between its target's Prop semantics and
Boolean Ty2 semantics. This is a substantial bounded artifact. It does
not require completing every stronger equivalence claim before review.

Implementation remains frozen. Reviewers should identify specific defects
or source mismatches and distinguish them from requests for stronger future
theorems. Correct accepted defects, repeat the checks, and seek explicit
approval before publishing a tagged snapshot. This document records no
reviewer endorsement, publication or new mathematical checkpoint.

# Appendix A. Complete checked source and per-file proof inventory

The following files are copied verbatim from the frozen source snapshot.
Each entry lists its SHA256 and all named proved statements recorded by
the corresponding audit. The prose above explains the central proofs;
these complete modules expose their supporting algebra, contexts, examples
and exact section parameters. They are not a replacement for the audit
of explicit premises or for source-fidelity review.

{{all_sources}}
