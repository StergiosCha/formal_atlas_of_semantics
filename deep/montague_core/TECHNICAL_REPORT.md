---
title: "An Explicit Proof Calculus for the Montague Branch"
subtitle: "Checkpoint 7: object calculi, legacy IL and guarded Prop/Boolean observations"
author: "Formal Atlas project | Technical review document for Robin Cooper and Rasmus Blanck"
date: "8 October 2026"
lang: en-GB
---

# 1. Purpose and status

This report describes the seventh implemented checkpoint of the proof-theory
programme discussed with Robin Cooper and Rasmus Blanck. The question is not
simply whether Coq can prove formulas that resemble linguistic inferences.
It is whether we can make the semantic representation, object-level rules of
inference, model interpretation and metatheoretical arguments separately
inspectable, and establish their connections by checked proofs.

The checkpoint implements a source-informed version of the extensional
calculus C presented in Chatzikyriakidis and Luo (2020), section 1.3.1 and
Appendix A1, following Luo and Soloviev (2017). It supplies typed syntax,
capture-avoiding substitution, syntactic beta conversion, constructive
derivability, an explicit classical extension, a declared interpretation and
soundness theorems. It also supplies object-language derivations of elementary
linguistic inferences and concrete countermodels for two invalid inference
patterns. Checkpoint 2 adds syntactic renaming/substitution algebra,
preservation of beta conversion and entire derivations under those operations,
and an independently defined interleaved-context calculus proved equivalent
to the split-context calculus. Sections 5.5 and 7.4-7.6 explain those additions.
Checkpoint 3 adds a separate Boolean interpretation, executable finite full
internal function-space models, soundness for both modes in that model class
and the book's defined Leibniz equality. Section 13 explains this model bridge;
`MODEL_SPEC.md` records its exact source and assumption contract.

Checkpoint 4 adds distinct world types, constant-domain Boolean world models,
a C-style calculus over the selected Ty2 fragment and its soundness theorem.
A further theorem preserves interpretation from the extensional Boolean core
and transports semantic consequences of its existing derivations. Two-world
fixtures distinguish actual truth, necessity and rigid/varying concepts.
Section 14 and `INTENSIONALITY_SPEC.md` explain the result and the audit
that preceded the later bridge to the older world/time-indexed IL implementation.

Checkpoint 5 defines a specified world-only IL fragment with an independent
implicit-index evaluator and a typed translation into explicit-world Ty2.
The interpretation-preservation theorem covers every term of that fragment,
including open terms, higher-order quantification, intension, extension and
absolute necessity. Rigidity and cancellation lemmas, with two-world
regressions, expose the side conditions that unsafe index-sensitive
substitution would lose. Section 15 and `IL_SPEC.md` explain this addition.

Checkpoint 6 directly translates every constructor of the actual legacy IL
into a parallel Prop-valued explicit-index target, preserving time, equality
and all assignments. Section 16 explains the theorem and its separate audit.

Checkpoint 7 relates the existing Boolean world evaluator to the existing
Prop explicit-index evaluator on a certified base-quantified fragment. It
proves truth, refutation, pointwise inference and entity-witness agreement
under related lexical meanings and assignments. Higher-order lambda and
application are allowed under the logical relation; arbitrary quantification
over propositions or predicates and unrestricted equality are not. Nine
synthetic cases demonstrate agreement and its boundaries. Section 17 and
`../montague_legacy/OBSERVATION_SPEC.md` give the full contract. This is not
yet a composed theorem for every actual legacy expression.

The closed core consists of 20 Coq files. All 20 compile with Coq 8.20.1
and pass a separate `coqchk` kernel recheck. All 173 named proved
statements have closed global assumption contexts. Twenty-three deliberately invalid
regression fixtures are rejected. The machine-readable checkpoint is
`verification.json`; the reproducible checker is `check.py`.

The `deep/montague_legacy/` companion contains 76 proved statements in six
files and fourteen rejected fixtures, with a separate checker and checkpoint.
Its original 40 statements retain their checkpoint-6 scope; 36 new observation
statements have closed global contexts. The combined development has 249
statements in 26 new files and 37 rejected fixtures. These are not 249 globally
axiom-free proofs: the actual legacy bridge retains old semantic parameters,
recorded per statement. No new global logical axiom dependency is added.
Legacy preservation explicitly takes FunExt. Generic observation preservation
does not, but derivation transfer and the finite paired examples do.

The qualification on those results is essential. General soundness is
conditional on an explicit function-extensionality premise. Classical
soundness for the original Prop-valued interpretation additionally assumes
excluded middle for the interpreting propositions. The new Boolean soundness
theorem instead uses its model's total-quantifier reflection contract and
Boolean double negation. Finite models discharge that contract by enumeration;
an optional arbitrary-domain construction uses explicit ClassicalDecision.
None of these premises is installed as a global axiom. A closed global
assumption report therefore does not mean that the theorem's type has no
premises.

This is not yet a full formalization of Montague's PTQ, Gallin's IL/Ty2
equivalence, a source-level adequacy theorem, a Henkin completeness proof or
a formal comparison with MTT or TTR. The new IL result is a forward
interpretation theorem for the explicitly specified fragment and shared domains.
The original core has Prop-valued and Boolean interpretations. Checkpoints
4-5 use Boolean worlds without tense. The checkpoint-6 legacy target retains
Prop, world/time indices and tense. Checkpoint 7 now proves guarded observational
correspondence between the two target evaluators. Their unrestricted model
classes have not been proved equivalent or identified with an external
set-model universe.
These are the boundaries
of this checkpoint, not claims that intensionality or the other model classes
cannot be mechanized.

The files are kept in `deep/montague_core/` and `deep/montague_legacy/`, with
separate build, assumption and CI checks. Existing implementations, assessments, source grades
and comparison profiles are unchanged. The new files have not been published
in the deployed proof reader or live worker. This report is for review, not
evidence that the intended reviewers have already approved the encoding.

# 2. Why an object calculus is needed

## 2.1 The earlier architecture

The project already contains shallow Montague-style denotations and a deep
IL syntax with an interpretation into Coq. Those developments can establish
equalities or implications between interpreted expressions. That is useful,
but it does not by itself define a derivation system for the object language.

For example, a Coq proof of `P -> Q` after unfolding the interpretations of
two sentences establishes a property in the host logic. Unless an object
derivability relation is separately defined, it does not establish that a
particular Montague proof calculus derives Q from P.

The old `deep/PTQ_deep2.v` includes a theorem named `beta_sound`. Its statement
is an evaluation equation for application of a lambda, using an extended
environment. That statement is narrower than a theorem about a separately
implemented syntactic substitution operation. The new workbench includes
that operation and proves its interpretation property before proving
soundness of syntactic beta conversion.

## 2.2 Four distinct levels

The present architecture separates the following levels:

| Level | Object of study | What the checker can establish |
| --- | --- | --- |
| Linguistic representation | A chosen reading represented by a typed expression | The representation is well-typed; its linguistic adequacy still needs source review. |
| Object proof theory | A derivation built from the declared rules | The conclusion follows by those rules from those assumptions. |
| Interpretation | A model, assignment and interpretation function | The expression has the specified denotation in this encoding. |
| Metatheory | Relations between syntax, derivations and interpretations | Renaming, substitution, conversion and soundness properties hold under their stated premises. |

Coq checks the entire construction from outside. It does not become the
object calculus merely because it is the implementation language. Conversely,
writing the calculus as data does not remove Coq from the metatheory.

## 2.3 A calculus is not automatically a theory of meaning

Three claims should not be conflated:

1. A semantic representation language has a proof calculus.
2. The calculus is sound for a specified interpretation or model class.
3. The meanings of natural-language expressions are constituted by their
   inferential roles.

The workbench addresses the first claim and a bounded, explicitly qualified
version of the second. It does not establish the third. The distinction
also appears in Chatzikyriakidis and Luo (2020), p. 19, notes 32 and 33:
possessing inference rules is not sufficient to establish a proof-theoretic
meaning theory, and interpreting natural language in a proof-theoretically
specified foundational language is not the same as giving natural-language
expressions their meanings directly through introduction and elimination
rules.

# 3. Source basis and translation decisions

## 3.1 Consulted passages

The primary source consulted for the implemented calculus was:

Chatzikyriakidis, S. and Luo, Z. (2020), *Formal Semantics in Modern Type
Theories*, section 1.3.1, printed pp. 6-9, and Appendix A1, pp. 175-176.
The book DOI is <https://doi.org/10.1002/9781119489252>.

The SHA256 of the local PDF actually consulted is:

```text
a23b5aae6bb2d65767b4d8b7b1b087cc5b13dcc2000c441798fbe65ad9adbf19
```

This is an artifact identifier, not a copyright licence, a reviewer signature
or a replacement for the corpus registry's existing artifact pins. The PDF
is not included in this workbench. The consultation was performed with AI
assistance and is not independent human semantic review.

The book attributes its presentation of C to Luo and Soloviev (2017),
*Dependent Event Types*. That paper is the cited antecedent, but a separate
direct audit of the paper has not been completed for this checkpoint. We
therefore ground the immediate rule mapping in the book's explicit rules,
rather than claiming that every detail has been compared against both sources.

The discussion of possible extensions also uses the book's pp. 19-22 on
MTT semantics and signatures, and section 7.2, p. 162, on conservativity of
the dependent-event extension. Those later features are not implemented here.

## 3.2 What is represented directly

The base calculus includes entity and truth types, function types, typed
variables, abstraction, application, implication, universal quantification
and beta conversion. Other selected logical operators are defined using
implication and quantification over truth-type variables, following Appendix
A1.2. A separately declared typed lexical signature supplies the
non-logical vocabulary.

The logical constructors are not arbitrary lexical meanings. In particular,
the model is not allowed to reinterpret the built-in implication or
quantifier constructors as whichever operations make an example work.

## 3.3 What has been re-encoded

The source gives explicit judgments for valid contexts, types, typed terms
and true formulas. The implementation uses intrinsic typing for terms.
Consequently, well-formedness of a typed term is enforced when the term is
constructed, rather than by a separate proof of a typing judgment.

The source interleaves assumptions `x:A` and `P true` in a single context.
The primary implementation separates a typed variable context G from a list
H of assumed-true formulas. It uses de Bruijn variables rather than variable
names. Checkpoint 2 adds an interleaved presentation with its own lookup and
inference rules, also using intrinsic typing and de Bruijn indices. The
correspondence between these two implemented presentations is now proved.
This is a substantive bridge rather than a definition equating the judgments.
It does not yet relate the book's named terms, explicit typing judgments and
freshness conventions to intrinsic syntax. That remaining source-fidelity
obligation must not be replaced by the claim that all context presentations
are automatically equivalent.

The implementation also adds a mode-indexed classical extension using
double-negation elimination. That rule is an explicit project extension;
it is not silently attributed to the rules printed in Appendix A1. We do
not infer classical strength merely from calling the source language
Church's type theory.

# 4. Step one: typed syntax

## 4.1 Types and typed variables

The type syntax in `Syntax.v` is:

```coq
Inductive ty : Type :=
  entity | truth | arrow (a b : ty).
```

A variable is indexed both by its context and by its type:

```coq
var G a
```

The constructor `vz` denotes the most recently introduced variable. The
constructor `vs` refers to a variable one position further out. If the
context begins with a variable of type a, `vz` has type a. `vs` preserves
the referenced variable's type while extending the context.

There is no need to test at run time whether a variable lookup has the
right type. A malformed lookup is not constructible as a value of the
indexed datatype.

## 4.2 Terms

Terms have the type:

```coq
tm symbol G a
```

Here `symbol : ty -> Type` is the typed lexical signature, G is the
variable context and a is the result type. The constructors are `Var`,
`Const`, `Lam`, `App`, `Imp` and `All`.

Application requires an expression of type `arrow a b` and an argument of
type a. Abstraction consumes a body in context `a :: G`. Universal
quantification consumes a truth-valued body in that extended context and
returns a truth-valued expression in G. Implication takes two truth-valued
expressions.

This separates three notions that are easily blurred in shallow code:

- `truth` is an object-language type code.
- `tm symbol G truth` is the type of object-language formulas.
- A proof that a formula is derivable is a separate Coq object inhabiting
  the relation defined in `Calculus.v`.

## 4.3 Scope of the syntax

The syntax can express higher-order functions and quantification at all
represented types. The current example lexicon is deliberately tiny:
John, man, walk and move. That lexicon is a fixture, not a restriction
imposed by the syntax.

This original core syntax has no world type. The separate `Ty2Syntax.v`
extension now adds one, while still omitting time, primitive IL intension and
extension operators, a choice operator and primitive extensional equality.
World abstraction/application are explicit lambda/application constructs.
Appendix A1.2's Leibniz equality has been defined for the core at the term
level in `BooleanEquality.v`, with explicit conditions for reflection to
denotational equality. No equality or eta rule is thereby added to the
object calculus; see section 13.6.

# 5. Step two: renaming, substitution and beta conversion

## 5.1 Renaming

A renaming maps each typed variable in G to a variable of the same type
in another context D. `rename` extends that operation structurally to terms.

Under a binder the renaming must be lifted. The newly bound variable is
mapped to the newly bound variable, while the old variables are renamed
and shifted outwards. The helper `lift_ren` performs precisely this step.
`weaken` is the particular renaming that shifts all existing variables
when one fresh variable is added to the context.

The interpretation lemma `eval_rename` says that evaluating a renamed
term agrees with evaluating the original term under a correspondingly
related assignment. It is not merely a theorem that renaming preserves
typing; typing preservation is already enforced by the return type.

## 5.2 Simultaneous substitution

A substitution maps each typed variable in G to a term of the same type
in D. The recursive function `subst` replaces variables and traverses the
other constructors.

Again, binders require special treatment. `lift_sub` maps the fresh variable
to itself and weakens each replacement for an older variable. Without this
weakening, a free variable inside a replacement could accidentally become
bound by the traversed binder. This is variable capture, not a harmless
change of notation.

The function `instantiate u t` substitutes u for the head variable in t.
It is used both by the beta-conversion rule and by universal elimination
in the proof calculus.

The regression `substitution_avoids_capture` checks a case with an outer
free variable and an inner lambda. Substitution must preserve the reference
to the outer variable rather than changing it into a reference to the inner
bound variable. The negative fixture `capture_is_not_substitution` deliberately
asserts the incorrect result and must be rejected by Coq.

## 5.3 The substitution theorem

The central semantic statement is `eval_substitution`. In mathematical
notation, if s substitutes terms for variables and the assignments satisfy

$$
\llbracket s(v)\rrbracket_{M,\rho}=\sigma(v)
$$

for every typed variable v, then

$$
\llbracket \operatorname{subst}(t,s)\rrbracket_{M,\rho}
=\llbracket t\rrbracket_{M,\sigma}.
$$

The proof is by induction on the typed term. The variable case is the
assignment hypothesis. Constants are unchanged. Application and implication
use the induction hypotheses. Under abstraction and quantification, the
assignments are extended by the same value for the fresh variable. The
lifted substitution property then follows from the weakening lemma.

`eval_instantiate` specializes this theorem to substitution for the head
variable. This is the connection needed by the inference rules; it is not
an informal appeal to substitution being obvious.

These results concern substitution of terms and their interpretations.
The additional theorem that an arbitrary substitution transforms an entire
derivation is now proved in `Structural.v`. It is a different statement:
it needs syntactic composition and conversion-compatibility lemmas, not a
semantic soundness premise. Its proof is explained in section 7.4.

## 5.4 Syntactic beta conversion

`beta` is an inductively defined relation on typed terms. It includes the
beta step

$$
(\lambda x.t)u\equiv_\beta \operatorname{instantiate}(u,t),
$$

reflexivity, symmetry, transitivity and congruence under all the implemented
term constructors. It does not include arbitrary equality of denotations,
eta conversion or a functional-extensionality rule.

`beta_sound` proves that beta-related terms have equal denotations in every
model and assignment of the declared interpretation, conditional on the
explicit function-extensionality premise. Its beta-step case uses
`eval_instantiate`; its congruence cases proceed structurally.

This is a meaningful advance over a single evaluation equation for a lambda
application: there is now a syntactic relation whose semantic correctness
is proved. It is nevertheless an extensional result. The interaction between
substitution and IL intension operators requires its own analysis when
those operators are introduced.

## 5.5 Syntactic algebra, without semantic premises

`Algebra.v` contains 16 lemmas about the recursive operations themselves.
They do not inspect models, invoke soundness or assume function extensionality.
This matters because the semantic substitution theorem alone cannot tell us
how to transform a derivation tree.

The first pair, `rename_ext` and `subst_ext`, says that pointwise-equal
variable mappings act identically on a term. They do not assert that the
mapping functions are equal. Induction on the finite term structure suffices.
In the binder cases, `var_cons_cases` distinguishes the newly introduced
variable from an older one. The former is fixed; the latter is handled by
the given pointwise equality. No dependent-equality axiom is needed.

The identity and composition laws then establish the following relationships:

| Checked relationship | Main lemma |
| --- | --- |
| Identity renaming or substitution leaves a term unchanged | `rename_id`, `subst_id` |
| Two successive renamings are their pointwise composition | `rename_comp` |
| Renaming before substitution composes the variable mappings | `subst_after_rename` |
| Renaming after substitution renames every replacement term | `rename_after_subst` |
| Successive substitutions substitute into each replacement term | `subst_comp` |
| Substitution by variable terms is renaming | `subst_renaming` |

The remaining laws address binders. `rename_weaken` and `subst_weaken`
show that a lifted mapping commutes with adding a fresh variable.
`instantiate_weaken` says that instantiating a newly added variable has
no effect on a term that did not depend on it. The formula-list versions
`map_rename_weaken` and `map_subst_weaken` transport these facts to the
assumption lists used by universal introduction.

The two key equations for universal elimination and beta conversion are:

```coq
rename (instantiate u t) r =
  instantiate (rename u r) (rename t (lift_ren r))

subst (instantiate u t) s =
  instantiate (subst u s) (subst t (lift_sub s))
```

The second equation, `subst_instantiate`, is especially important. Applying
a substitution after removing the head binder agrees with first applying
its lifted form to the body, then instantiating with the substituted argument.
Its proof uses substitution composition and the fact that head instantiation
undoes an irrelevant weakening. This is the precise compatibility needed
when a transformed derivation ends in universal elimination or beta conversion.

# 6. Step three: the original Prop-valued interpretation

## 6.1 Domain interpretation

`Models.v` defines a recursive interpretation of type codes:

$$
D_e=E,\qquad D_t=\mathrm{Prop},\qquad
D_{a\to b}=D_a\to D_b.
$$

Here E is a Coq type supplied by the model. The arrows on the right are
Coq function spaces. `Prop` is Coq's sort of propositions.

This equation is a declaration of the implemented semantics. It should not
be read as an already established correspondence with the two-element
truth domain of an external set-theoretic interpretation. Nor does using
Coq functions establish correspondence with all externally intended
set-theoretic functions. Such correspondence is a further mathematical
claim and would need a separately specified representation relation.

## 6.2 Model data

A model contains:

- `individuals`: the individual domain E;
- `individuals_nonempty`: a witness that E is inhabited;
- `lexical`: an interpretation of every typed lexical symbol in its
  corresponding denotation domain.

The nonemptiness requirement concerns the individual domain. It does not
force the extension of each common noun to be inhabited. An empty man
predicate over a nonempty individual domain is a legitimate model and is
used in the existential-import counterexample.

The general development has no global declarations of a particular John,
man predicate or walk predicate. A model supplies them through its lexical
interpretation. The concrete fixture models instantiate every symbol in
their finite signature; they do not leave lexical behavior as undischarged
hypotheses.

No linguistic meaning postulates are silently installed. For this checkpoint,
such postulates can be supplied among the explicit premises. A dedicated
source-specific admissibility predicate, for example for a richer PTQ
lexicon, remains future work.

## 6.3 Assignments and evaluation

An assignment maps a typed variable to a member of the appropriate domain.
`extend rho x` assigns x to the newly bound variable and delegates older
variables to rho.

The interpretation function follows the syntax. Variables use the assignment;
constants use the model's lexical interpretation; lambdas produce functions;
applications apply those functions. Implication is interpreted as Coq
implication. Universal quantification ranges over the denotation domain
of the bound variable's type.

There is no world or time argument in this original interpretation. This is
the extensional core. The absence of those arguments must remain explicit when
presenting the result to linguists who associate Montague semantics with
possible-world interpretation.

## 6.4 Encoded connectives

The source defines additional logical operators impredicatively using
implication and quantification over t. The workbench follows that route
for falsity, negation, conjunction, disjunction and existence.

For example:

$$
\bot=\forall X:t.\,X
$$

and

$$
P\land Q=\forall X:t.\,(P\Rightarrow Q\Rightarrow X)\Rightarrow X.
$$

The existential encoding is:

$$
\exists x:a.\,P(x)
=\forall X:t.\,(\forall x:a.\,P(x)\Rightarrow X)\Rightarrow X.
$$

The lemmas `falsity_meaning`, `neg_meaning`, `conj_meaning`, `disj_meaning`
and `exists_meaning` establish the intended relationships with the
corresponding Coq propositions under this interpretation. The latter three
use the explicit function-extensionality premise through the renaming or
weakening lemmas.

These are semantic properties of the encodings. In particular, the
existential interpretation theorem is not a program extracting a computational
witness from every object derivation. The distinction between a proposition
of existence and a data-bearing dependent pair remains relevant to later MTT
and TTR comparisons.

## 6.5 Consequence across models

The predicate `satisfies M rho H` means that every member of H evaluates to
a proposition that holds. Consequence is then defined by:

$$
H\models p
\quad\text{iff}\quad
\forall M,\rho.\; M,\rho\models H\Rightarrow M,\rho\models p.
$$

This explicitly ranges over every model and assignment of the declared
interpretation. It is not truth in one frozen lexical interpretation.
`lexical_model_variation` exhibits two models that disagree about the same
closed atomic formula.

The qualifier "of the declared interpretation" is crucial. This quantifier
does not range over all Montague models by an established representation
theorem, and it does not range over Henkin subdomain models. Those classes
have not yet been implemented.

## 6.6 The new, separate Boolean interpretation

Checkpoint 3 adds a distinct interpretation in `BooleanModels.v`, whose
truth carrier is literally `bool`. Its model includes total universal
quantifiers with reflection proofs; actual finite instances are constructed
and checked. The domain of every function type is still a full Coq function
space. Section 13 explains the new interpretation, the finite construction
and the soundness bridge. The statements in sections 6.1-6.5 describe the
original Prop-valued interpretation and remain unchanged as mathematics.
The two interpretations must not be silently identified.

# 7. Step four: constructive and classical object derivations

## 7.1 The judgment

The central object judgment is:

```coq
derives L H p
```

The variable context G and the lexical signature are carried by the types
of H and p. L is either `constructive` or `classical`.

A value of this inductive relation is an object derivation. It is not merely
an arbitrary Coq proof of the interpretation of p. The constructors state
which inference steps are permitted.

## 7.2 The seven rule constructors

`d_assume` concludes p when p occurs in H.

`d_imp_intro` derives an implication from a derivation of its consequent
under the additional antecedent assumption.

`d_imp_elim` is modus ponens.

`d_all_intro` derives a universal formula from a derivation of its body
in an extended variable context. Every old hypothesis is weakened into
that extended context. This is the implementation of the eigenvariable
discipline: the newly introduced variable must not acquire an accidental
dependency in an old hypothesis.

`d_all_elim` instantiates the body of a universal formula with a well-typed
term. Its conclusion uses the actual `instantiate` function.

`d_conversion` permits a formula to be replaced by a syntactically
beta-equivalent formula. The premise is a `beta` derivation, not equality
of denotations assumed without proof.

`d_double_negation` permits double-negation elimination only with a proof
that the mode is `classical`.

The last rule is present in the shared datatype but cannot be selected
in constructive mode by supplying reflexivity: `constructive = classical`
has no such proof. A regression deliberately attempts that misuse and
checks that Coq rejects it. This establishes the constructor boundary;
it is not a proof that double-negation elimination is underivable by every
possible combination of the remaining rules.

## 7.3 Structural results already proved

`assumption_weakening` shows that a derivation remains valid when its
true-formula assumption list is enlarged by inclusion. Under universal
introduction, inclusion is transported through the weakening map.

`cut` shows that, given a derivation of p from H and a derivation of q
from p together with H, q is derivable from H. The proof uses implication
introduction followed by elimination. This is admissibility of this cut
principle, not a cut-elimination procedure and not a normalization theorem.

`constructive_in_classical` translates a constructive derivation into a
classical derivation by induction on the derivation. The double-negation
case is impossible at constructive mode. This proves an inclusion, not
strictness of that inclusion.

Checkpoint 2 also establishes variable-context weakening and arbitrary
simultaneous term substitution of derivations, described next. Normalization,
cut elimination and a full separation theorem between the two calculi
remain outstanding.

## 7.4 Transforming complete derivations

`Structural.v` first proves `beta_renaming` and `beta_substitution` by
induction on the beta-conversion derivation. Reflexivity, symmetry,
transitivity and congruence are preserved directly. In the actual beta-step
case, the instantiation equations from section 5.5 identify the transformed
right-hand term with the result of the transformed redex. A new beta-step
derivation therefore has exactly the required endpoints.

Only after proving those compatibility results do we transform whole
logical derivations. The central theorem types are:

```coq
derives L H p ->
  derives L (map (fun q => rename q r) H) (rename p r)

derives L H p ->
  derives L (map (fun q => subst q s) H) (subst p s)
```

The first is `derivation_renaming`; the second is
`derivation_substitution`. The displayed mappings are typed between a source
variable context G and a target context D. They need not be bijections.
Uniform replacement can identify two variables or replace a variable by
a compound term of the appropriate type. The lexical signature is unchanged:
this is variable substitution, not replacement of lexical constants or
arbitrary replacement of formulas by derivations.

Both the assumptions and conclusion are transformed. A theorem that only
replaced the conclusion would be false in general. The mode L is unchanged
as well. Transforming a constructive derivation cannot introduce permission
to use the classical rule.

The proof follows all seven derivation constructors:

1. An assumption remains in the mapped assumption list. This uses list
   membership, not a semantic truth test.
2. Implication introduction maps both the temporarily added antecedent
   and the existing assumptions, then invokes the induction hypothesis.
3. Implication elimination transforms its two premise derivations and
   rebuilds the same elimination rule.
4. Universal introduction invokes the induction hypothesis with the lifted
   mapping. The map/weakening lemma identifies the resulting assumption
   list with the one required by the target universal-introduction rule.
5. Universal elimination uses `rename_instantiate` or `subst_instantiate`
   to identify the transformed conclusion with the target rule's conclusion.
6. Conversion transforms the premise derivation and uses `beta_renaming`
   or `beta_substitution` to transform its conversion evidence.
7. Double-negation elimination preserves the existing proof that L is
   classical. Renaming/substitution commute with the encoded negation.

`derivation_weakening` specializes renaming to shifting every old variable
past one fresh variable. It differs from `assumption_weakening`, which
enlarges the formula list without changing the variable context.
`derivation_instantiation` specializes simultaneous substitution to
replacing the head variable by one term. These are derived operations on
proofs, not extra inference-rule constructors.

None of these theorems requires FunExt or ClassicalTruth. Their statements
preserve object derivability even in classical mode without appealing to
the interpretation of the classical rule. This distinction is directly
relevant to Robin's question about the constructive host: the metatheory
can reason structurally about an explicitly classical object system.

## 7.5 Interleaved contexts and a proved bridge

`Contexts.v` supplies the indexed datatype `mixed symbol G`. Its constructors
correspond to an empty context, a new typed variable, and a new true-formula
assumption. The formula in `context_true C p` must be well-typed using the
variables already available in C. It cannot refer to a future declaration.

For example, the source-style sequence

```text
x : e, man(x) true, y : e
```

is represented by adding x, assuming `man(x)`, then adding y. Adding y
changes the de Bruijn reference to x from `vz` to `vs vz`. The reference
must not suddenly denote y merely because y is now the newest variable.

The recursive function `hypotheses` flattens this context. It keeps the
typed variable context in the index and computes the formula list as follows:

- The empty context has no formulas.
- A true-formula declaration prepends that formula.
- A variable declaration weakens every previously available formula.

The independent `lookup` judgment follows the same declaration discipline:
the most recent formula can be selected; an intervening formula can be
skipped; crossing a variable declaration shifts the selected formula.
`lookup_flatten` proves that this judgment is equivalent to membership in
the flattened list. Both directions are proved, including recovery of the
earlier formula from membership in a mapped list.

The independent relation `mixed_derives` has its own seven rule
constructors. Implication introduction extends the interleaved context by
a formula declaration. Universal introduction extends it by a variable
declaration. The other rules mirror the selected calculus, including the
same beta relation and the explicit classical-mode test. This relation is
not defined as an abbreviation for split-context derivability.

`mixed_to_split` proves that each interleaved derivation gives a split
derivation by induction on the interleaved proof. `split_to_mixed` proves
the reverse for any interleaved context whose flattened hypotheses are the
given split assumption list. This stronger induction statement is needed
under implication and universal introduction: the target context must be
extended appropriately before applying the induction hypothesis.

Their combination is the checked equivalence:

```coq
mixed_derives L C p <-> derives L (hypotheses C) p
```

`variables_only` constructs the variable declarations for a given typed
context. `add_hypotheses` then appends formula declarations in the order
needed to reconstruct a given assumption list. Together they define
`pack`. The theorem `pack_flatten` proves that every split assumption list
is recovered by flattening this canonical interleaved context.
`packed_derivation` and `context_round_trip` state the resulting preservation
of derivability.

The round trip is deliberately not stated as equality of interleaved
contexts. For a closed P, the contexts "P true, x:e" and "x:e, P true"
are different declaration histories with the same flattened assumptions.
The regressions `same_flattening` and `different_interleavings` prove both
facts for a concrete P; `round_trip_preserves_judgment` proves the exact
derivability equivalence. Flattening loses declaration placement while
preserving the represented judgments of this calculus.

This bridge is specific to the implemented simple types and formulas.
It is not a generic theorem allowing arbitrary context rearrangement in
dependent type theories. Nor does it complete named-source adequacy:
both sides of this bridge already use intrinsic typing and de Bruijn
indices. Source names, explicit typing derivations and the correspondence
of their equality/freshness rules remain to be treated or explicitly
delimited by the authors' review.

## 7.6 Regression walkthrough: free variables remain free

`StructuralExamples.v` contains ten proved regression statements. A useful
sequence begins with the interleaved assumption context "x:e, man(x) true".
Adding a fresh y and looking up the older assumption derives `man(x)`, not
`man(y)`. Universal introduction therefore derives `forall y. man(x)`.

`interleaved_fresh_variable` constructs that proof with the interleaved
rules. `split_fresh_variable` obtains its split counterpart through the
general bridge, not by writing a second bespoke proof.
`substitute_beneath_generalization` then instantiates the free x by John
using the general derivation-substitution theorem. The result is a derivation
of `forall y. man(John)` from `man(John)`. The inner y remains bound and
the original assumption is transformed along with the conclusion.

`weaken_open_derivation` inserts a fresh truth-type variable into the
context. The type difference helps expose indexing mistakes: every older
individual reference must shift appropriately. The remaining fixtures
exercise substitution through an actual conversion derivation, preservation
of the classical-only rule, beta conversion beneath a lambda, and the
distinction between context identity and derivability equivalence.

The deliberately incorrect counterparts in `check.py` try to select the
new variable instead of the older one, equate different interleavings,
leave a weakened conclusion unshifted, or use an unrelated assumption after
substitution. Coq must reject these attempts. As elsewhere, rejection of
one proof script tests a boundary; it is not a general non-derivability theorem.

# 8. Step five: soundness and the exact assumption boundary

## 8.1 Explicit premises

This section first describes the original Prop-valued interpretation's
assumption boundary. The Boolean model bridge is added in section 8.5.
The original interpretation development declares:

```coq
Definition FunExt : Prop :=
  forall (A B : Type) (f g : A -> B),
    (forall x, f x = g x) -> f = g.

Definition ClassicalTruth : Prop :=
  forall P : Prop, P \/ ~ P.
```

These are definitions of propositions. They do not assert that either
proposition holds. A theorem that requires one receives it as an argument.

Function extensionality is used when pointwise equality of denotations under
a binder must yield equality of the resulting functions. It is a premise
of the present metatheoretical proof technique. It is not an inference rule
of the object calculus. This checkpoint does not establish that every
alternative semantics or every soundness proof must require it.

The general permission condition is:

```coq
permits_classical L := L = classical -> ClassicalTruth
```

In constructive mode this condition is vacuous. In classical mode it
requires excluded middle for the propositions used by the interpretation.
It is not a separate property checked individually for each lexical model:
the truth domain is Coq `Prop`, so the condition is stated globally over
that domain of interpreting propositions.

## 8.2 General soundness

`derivation_sound` has the following content:

Given FunExt, an object derivation of p from H, a model M, an assignment
rho, permission for the chosen logical mode and satisfaction of H, the
interpretation of p holds.

The proof is by induction on the object derivation:

1. Assumptions are supplied by satisfaction of H.
2. Implication introduction extends semantic satisfaction by the antecedent.
3. Implication elimination applies the interpreted implication.
4. Universal introduction evaluates the body at an arbitrary new domain
   element. `eval_weaken` proves that the old hypotheses retain their values.
5. Universal elimination uses `eval_instantiate` to connect syntactic
   substitution with the extended assignment.
6. Conversion uses `beta_sound`.
7. Double-negation elimination uses the permitted classical principle.

This proof does not inspect only the example derivations. It quantifies
over all derivations constructible from the implemented rules.

## 8.3 Specialized statements

`constructive_sound` states, under FunExt:

$$
H\vdash_{\mathrm C}p\quad\Longrightarrow\quad H\models p.
$$

`classical_sound` states the corresponding implication for the classical
extension, under FunExt and ClassicalTruth.

Both quantify over every model and assignment through the definition of
consequence. Neither theorem establishes the reverse implication.

| Result family | Explicit logical premises |
| --- | --- |
| Concrete example derivations | None beyond their displayed object assumptions |
| Concrete countermodels | None |
| Hypothesis weakening, cut, constructive inclusion | None beyond the displayed derivations |
| Syntactic algebra, beta preservation and whole-derivation transformations | None beyond their displayed syntactic premises |
| Interleaved/split correspondence and judgment round trips | None beyond their displayed syntactic premises |
| General renaming, substitution and beta interpretation | FunExt |
| General constructive soundness | FunExt |
| General classical soundness | FunExt and ClassicalTruth |
| Nonderivability inferred from the general soundness theorem | FunExt, plus the mode permission where applicable |

## 8.4 What "closed under the global context" means here

Coq's assumption audit reports that the 173 closed-core proved statements have no
global axiom dependencies. It does not erase arguments from theorem types.
For example, a theorem of type `FunExt -> R` can have a closed global
context without the development having proved FunExt.

During construction, a convenience tactic for dependent case analysis
introduced an unwanted `Eqdep.Eq_rect_eq.eq_rect_eq` dependency. The audit
detected it. The tactic was removed and replaced with the explicit
`var_cons_cases` eliminator. The final artifact has no such dependency.
This is a development correction, not a result about the source calculus.

The checker also compiles explicit expected types for the constructive and
classical soundness theorems. This prevents a change in their premise
boundary from being concealed by a reassuring but incomplete summary of
the assumption audit. It also compiles expected signatures for renaming,
substitution, beta preservation and the context equivalence, confirming
that these structural results do not acquire semantic premises.

## 8.5 The Boolean soundness boundary

`classical_boolean_sound` has an explicit FunExt premise but no extra
ClassicalTruth argument. Its consequence predicate quantifies over Boolean
models that already include correctly reflected total quantifiers.
Double negation is Boolean double negation. This differs from interpreting
truth as arbitrary Coq propositions and assuming their excluded middle.

That distinction does not make arbitrary model construction automatic.
The finite construction proves the quantifier contract with FunExt and
complete finite-domain data. The optional arbitrary-domain construction
uses `ClassicalDecision`, which returns data-valued decisions for all Coq
propositions. Neither theorem proves that arbitrary quantifiers are
computable or eliminates the distinction between Prop and Boolean truth.

The original soundness theorems retain their original types. There is no
new theorem identifying the two notions of semantic consequence. Section
13 and `MODEL_SPEC.md` give the detailed dependency account.

# 9. Step six: linguistic derivations and countermodels

## 9.1 Universal instantiation

The first fixture represents:

> John is a man. Every man walks. Therefore, John walks.

The object derivation first instantiates the universal premise at John,
obtaining an implication from John's being a man to John's walking. It
then applies implication elimination to the other premise.

The named result is `john_walks_derivation`. A separate theorem,
`john_walks_in_all_models`, obtains semantic consequence by applying
constructive soundness. The distinction between the two results makes
the derivation/interpretation connection visible.

## 9.2 A syllogism

The next fixture represents:

> Every man walks. Every walker moves. Therefore, every man moves.

The proof introduces an arbitrary individual and assumes that the
individual is a man. Each universal premise is instantiated at that
individual. Two implication eliminations establish movement. The man
assumption is discharged, then the fresh individual is universally
generalized.

The formal premises, not general world knowledge, supply the connection
between walking and moving. The fixture does not install a lexical
entailment for the verb walk across all models.

The object and semantic results are `syllogism_derivation` and
`syllogism_in_all_models`.

## 9.3 Existential introduction

The third fixture represents:

> John is a man. John walks. Therefore, a man walks.

Because the calculus follows Appendix A1.2, existence is not introduced
by an extra primitive existential rule. The proof works with the encoded
existential formula. It introduces an arbitrary result proposition X,
assumes that each walking man would establish X, instantiates that
assumption at John and constructs the encoded conjunction from the two
premises. This supplies X and completes the encoding's introductions.

The named results are `existential_derivation` and
`existential_in_all_models`. These are ordinary known logical inferences,
used to exercise the encoding and the general soundness theorem. No
linguistic or logical priority claim is attached to them.

## 9.4 Conversion and classical reasoning

`beta_conversion_derivation` transports a walking premise along the
syntactic beta equivalence between John and application of the identity
lambda to John. The conversion step is part of the object derivation.

`classical_double_negation_derivation` derives the atomic proposition
that John is a man from its double negation using the classical-only rule.
Constructing that object derivation does not itself require excluded
middle in Coq. Proving that the added rule is sound under the declared
interpretation requires ClassicalTruth. This is a concrete example of
the difference between representing a classical calculus and assuming
classical reasoning in the metatheory.

## 9.5 Countermodel to existential import

The model `no_men` has the nonempty individual domain `unit`. John denotes
its sole individual. The man predicate is always false, while walk and
move are always true.

In this model, every man walks but a man walks is false. The result
`no_men_countermodel` proves both statements directly for the concrete
interpretation. It does not rely on a hypothesized countermodel whose
existence has never been established.

`no_existential_import` then invokes the general soundness theorem to
exclude a constructive derivation of the existential conclusion from the
universal premise, conditional on FunExt. The nonempty individual domain
is important: the counterexample depends on an empty noun extension,
not on an empty universe of individuals.

## 9.6 Countermodel to generalizing from one name

The model `two_people` has the Boolean individual domain. John denotes
true; the man predicate holds exactly of true. John is therefore a man,
but not every individual is a man.

`generalization_countermodel` checks this interpretation directly.
`no_generalization_from_one_name` uses it and soundness to exclude the
corresponding constructive derivation, again conditional on FunExt.

The negative regression for universal introduction additionally attempts
to generalize from the named premise by an invalid proof script. Its
failure is a regression check, not the justification for non-derivability.
The justification is the explicit countermodel plus soundness.

# 10. Mechanical checking and reproducibility

## 10.1 The checked inventory

The 173 named proved statements in the closed core are distributed as follows:

| File | Named proved statements | Main role |
| --- | ---: | --- |
| Syntax.v | 1 | Axiom-free indexed-variable case analysis |
| Algebra.v | 16 | Syntactic renaming/substitution equations |
| Models.v | 10 | Interpretation, substitution, conversion and encoded connectives |
| Calculus.v | 7 | Structural properties and conditional soundness |
| Structural.v | 6 | Conversion and whole-derivation preservation |
| Contexts.v | 11 | Independent interleaved calculus and correspondence |
| Examples.v | 14 | Derivations, interpretation consequences and countermodels |
| StructuralExamples.v | 10 | Binder-sensitive and context-bridge regressions |
| BooleanModels.v | 14 | Two-valued interpretation, binding/conversion and soundness |
| BooleanFinite.v | 5 | Complete function tables and finite quantifier reflection |
| BooleanEquality.v | 4 | Defined Leibniz equality and denotation reflection |
| BooleanExamples.v | 15 | Actual models, consequences, countermodels and higher-order tests |
| Ty2Syntax.v | 1 | Indexed world-variable case analysis for the new typed syntax |
| Ty2Models.v | 9 | World interpretation, binding, conversion and necessity meaning |
| Ty2Calculus.v | 2 | Soundness and countermodel exclusion for the world calculus |
| Ty2Embedding.v | 6 | Domain round trips, core interpretation and consequence transfer |
| Ty2Examples.v | 14 | Two-world distinctions, proof reuse and binding regressions |
| ILSyntax.v | 1 | Indexed source-variable case analysis for the IL translation |
| ILTranslation.v | 11 | Interpretation preservation, cancellation, rigidity and necessity |
| ILExamples.v | 16 | Source/target evaluation, binding and substitution regressions |

These are engineering and mathematical declarations, not 173 independent
linguistic discoveries. The full names and source hashes are recorded in
`verification.json` and listed in Appendix A of this report.

The separately audited legacy companion adds one statement in IndexSyntax.v,
nine in IndexModels.v, fifteen in LegacyTranslation.v and fifteen in
LegacyExamples.v. Checkpoint 7 adds eighteen in ObservationBridge.v and
eighteen in ObservationExamples.v. The complete 76-statement companion
inventory is in Appendix B. Its nine-case observation registry links each
case to an actually compiled proved declaration.

## 10.2 Fresh build and kernel recheck

From the repository root, run:

```sh
python3 deep/montague_core/check.py --check
python3 deep/montague_legacy/check.py --check
```

The checker requires Coq 8.20.1. It copies only the 20 source files into
a fresh temporary directory and compiles them in dependency order. Existing
local `.vo` files cannot make this check pass for stale source. It then
kernel-rechecks all 20 modules with `coqchk`.

The checker queries every named proof with `Print Assumptions` and fails
if a global axiom dependency or an unresolved query appears. It rejects
unfinished proof declarations and selected unsafe shortcuts. It also checks
the expected signatures of the two soundness theorems and the main new
structural theorems, Boolean soundness and finite/arbitrary model construction.

Finally, it compiles twenty-three invalid fixtures and requires both failure and
the expected class of diagnostic. The invalid fixtures concern the logical
mode boundary, capture avoidance, generalization from a name, and omission
of the classical-soundness premise, incorrect lookup through a new variable,
false equality of interleavings, unshifted weakening and substitution with
the wrong assumptions. Five new fixtures test an invalid constant-true
quantifier, incomplete higher-order sampling, a false existential conclusion,
false equality of predicates and omission of ClassicalDecision from its
construction. Each has a corresponding positive checked example or construction.
The six world-layer regressions reject world/entity type confusion,
necessity inferred from actual truth, unrestricted necessitation from a local
assumption, concept identity inferred from actual agreement, conflating a
frozen value with re-evaluation, and captured world substitution.
Four IL fixtures additionally reject captured assignment variables,
index-sensitive substitution treated as unconditional beta, unconditional
reverse intension cancellation and a world abstraction that changes an
assigned variable's value. Signature checks retain the FunExt premise of
preservation and the index-rigidity premise of reverse cancellation.

The deterministic checkpoint includes the Coq version, source hashes,
declaration inventory, kernel-check status, explicit soundness premises
and negative-fixture names. A changed source hash or inventory requires
an intentional checkpoint update using `--record`. Such an update records
a mechanical result; it is not a substitute for reviewing the change.

The legacy checker independently compiles the hash-pinned old source and
six companion modules, kernel-rechecks them, checks theorem signatures and
records every new statement's global dependencies. The legacy modules may
use only the recorded old parameters. The two observation modules must have
closed global contexts, and the main preservation signature must not require
FunExt. Seven original companion invalid
fixtures concern index quantification, time erasure, temporal order, truth
carriers, FunExt, world/time sorts and unsafe source beta conversion. Seven
new fixtures reject unguarded truth/predicate quantification, unmatched
lexicons, proposition identity inferred from equivalence, omitted
certification, existential import and local necessitation. These failures
are regression checks, not standalone independence proofs. Both checkers
are mandatory in CI; neither updates atlas records.

## 10.3 Interactive inspection

After compiling the 20 files with their local `_CoqProject`, start:

```sh
coqtop -Q deep/montague_core MontagueProof
```

Useful commands include:

```coq
From MontagueProof Require Import Syntax Algebra Models Calculus Structural
  Contexts Examples StructuralExamples.
From MontagueProof Require Import BooleanModels BooleanFinite BooleanEquality BooleanExamples.
From MontagueProof Require Import Ty2Syntax Ty2Models Ty2Calculus Ty2Embedding Ty2Examples.
From MontagueProof Require Import ILSyntax ILTranslation ILExamples.
Print explicit_world_preservation.
Print Assumptions explicit_world_preservation.
Print up_down_for_rigid_intensions.
Print derives.
Print derivation_substitution.
Print beta_substitution.
Print mixed_derives.
Print mixed_split_equivalence.
Print eval_substitution.
Print constructive_sound.
Print classical_sound.
Print no_existential_import.
Print Assumptions constructive_sound.
Print Assumptions existential_derivation.
Print Assumptions derivation_substitution.
Print Assumptions mixed_split_equivalence.
Print classical_boolean_sound.
Print finite_model.
Print finite_leibniz_equality.
Print Assumptions classical_boolean_sound.
Print world_derivation_sound.
Print embedding_interpretation.
Print core_derivation_world_sound.
Print no_necessitation_from_actual_assumption.
```

Reading the theorem type and the assumption report together is the intended
review procedure. An assumption report alone is insufficient to assess
the strength of the statement.

## 10.4 What mechanical checking does not establish

The checker does not validate the linguistic readings, establish the
source-to-encoding correspondence, demonstrate historical novelty or
certify the physical compiler binary. Kernel rechecking provides another
check of the proof artifact within the Coq toolchain; it is not an
independent semantic review or a foundation-independent proof.

The workbench uses no external LLM calls or Jev calls at execution time.
AI assisted development and source consultation. Neither an LLM nor Jev
is used to certify a theorem or decide its source fidelity. In particular,
no classifier output is substituted for the object derivations or the
model proofs described above.

# 11. Responses to the foundational questions

## 11.1 Are we still inside Coq?

Yes. The syntax, derivations, interpretations and metatheorems are all
represented in Coq. This is not hidden or treated as a defect that a deep
embedding somehow removes.

The advantage is separation and inspectability. We can identify an object
inference rule, ask whether it is permitted in a particular mode, and prove
that its interpretation preserves truth under explicit premises. We can
also inspect which assumptions are required by the metatheory.

A further implementation in Lean would be valuable as an independent
engineering check, but would not by itself establish independence from
dependent-type-theoretic foundations. No Lean counterpart to this new
checkpoint is claimed.

## 11.2 Is constructive reasoning necessarily always there?

The host has Coq's underlying constructive type theory. The object calculus
need not have only constructive rules. A classical rule can be represented
as a constructor without globally asserting the truth of its semantic
interpretation.

This checkpoint does precisely that. The distinction appears in the types
of `constructive_sound` and `classical_sound`, not merely in a descriptive
label attached to a file. It does not yet prove a general strict separation
between the two object calculi.

Checkpoint 7 additionally proves that selected, reflected observations in a
Prop interpretation agree with Boolean observations, including a double-negation
example. This does not make every Coq proposition decidable. A separate
conditional theorem shows that extending Boolean reflection to every
proposition would entail unrestricted excluded middle. The relation's
premises and coverage, rather than the use of Coq alone, determine this
boundary. Nor does shared Boolean validity prove that constructive and
classical object derivability coincide.

## 11.3 What would count as faithfulness to Montague?

At least four additional obligations remain beyond the present checking:

1. A source-level account of the represented fragment, lexical analyses and
   structural rules. The intrinsic interleaved/split bridge is now proved;
   relating it to the source's named typing judgments remains separate.
2. Review of the now-specified internal Boolean model class, truth domain,
   equality and explicit assumptions, together with the still-unimplemented
   Henkin and source-specific lexical admissibility conditions.
3. A representation theorem relating those structures to the implemented
   interpretation, not merely a list of similar-looking clauses.
4. The actual legacy code now has an interpretation-preserving translation
   into an explicit-index Prop target with World*Time structure retained.
   The two target evaluators now have a guarded observational bridge, but
   composing it with selected actual legacy translations and establishing
   published-source or English-analysis adequacy remain separate obligations.

The present soundness theorem is a foundation for these obligations, not
their replacement. It can be correct even if the chosen representation
turns out not to match some intended source phenomenon.

## 11.4 What does Henkin semantics contribute?

Hahn and Richter (2015) distinguish full higher-order semantics from
Henkin semantics and prove a translation result relative to a specified
Henkin interpretation and axiom set. That work motivates a useful next
branch: an explicit Ty2 calculus, model interface and verified translation.

It does not license replacing full models by Henkin models without saying
so. Henkin models may restrict higher-order domains, and their logical
validities need not coincide with full-model validities. A countermodel
for a weakened first-order translation is especially not automatically
a countermodel for the stronger original semantics.

No Henkin model is constructed by this checkpoint. The current recursive
domain interpretation uses Coq function spaces and has no separate
admissible-function subdomain or lambda-closure component. Those pieces
must be designed, implemented and related to the proof system explicitly.

## 11.5 How should MTT enter the comparison?

The blanket statement that MTT semantics has no model-theoretic aspect
must not be used. Chatzikyriakidis and Luo (2020), pp. 19-22, explicitly
argue otherwise: types supply denotations and represent collections, while
signatures can describe incomplete possible worlds. This is not merely
the observation that type theory can itself receive an external
set-theoretic model.

It does not follow that MTT signatures, Cooper's TTR models and Montague
models are identical structures. A comparison must respect their distinct
roles. A useful first comparison concerns a specified linguistic reading
and its consequences, represented natively in each framework. A stronger
comparison requires a bridge that accounts for typing, inhabitants,
judgments and any model or signature assumptions.

For example, agreement on an existential inference need not preserve the
identity of a witness or the structure of a dependent pair. Conversely,
failure to derive a formula in a constructive calculus is not evidence
that the corresponding classical interpretation is false. Both the
observation and the direction of the proposed bridge must be stated.

# 12. Extension plan and review questions

## 12.1 First review: source calculus and structural metatheory

The first review should decide whether C, in precisely the source
presentation used here, is the appropriate initial object calculus. It
should check the split-context discipline, treatment of constants and
conversion relation. The structural milestone requested after checkpoint 1
is now implemented: syntactic algebra, conversion preservation, whole-proof
renaming/substitution and the intrinsic interleaved-context correspondence.
Review should focus on the actual types of those theorems and on the
remaining distinction from named-source typing adequacy. Normalization,
cut elimination and full constructive/classical separation are not included.

## 12.2 Second review: the implemented Boolean model contract

The first model milestone is now implemented and described in section 13:
a two-valued full internal function-space interpretation, actual finite
instances, soundness and a defined-equality reflection result. Review should
check `MODEL_SPEC.md`, especially the explicit quantifier contract, the finite
construction's use of FunExt and the optional arbitrary-domain construction's
use of ClassicalDecision.

The external set-model adequacy question, unrestricted comparison with the
Prop-valued model class and a Henkin interpretation with admissible higher-order domains
remain separate. These should be stated as additional mathematical problems,
not treated as already settled by Boolean soundness.

## 12.3 Intensional extension

The world type, Boolean models, core bridge and world-only IL translation
are implemented. Checkpoint 6 also proves correspondence for the actual old
IL, including its World*Time index, Prop truth, equality and all constructors.
It retains these features in a parallel target. Checkpoint 7 specifies and
proves a scoped relation between the target evaluators, with explicit
conditions on higher-order values. Its connection to selected actual legacy
terms still requires a composition theorem, not just juxtaposed results.

The new fixtures address a key constraint on substitution through intensional structure. A
term that varies with the evaluation index cannot automatically be
substituted as if it denoted an index-independent value in every context.
The extensional beta theorem should not be renamed or advertised as
settling that question. The present code deliberately has no unrestricted
IL beta rule; a rigidity-aware substitution calculus would be a further result.

## 12.4 Shared linguistic inference suite

There is now a nine-case synthetic seed suite in `OBSERVATION_SUITE.json`,
covering quantification, witnesses, necessity and a lexical precondition
diagnostic. Each case names a compiled proof; none is labelled independently
source-reviewed. Section 17 explains what these cases actually establish.

Robin and Rasmus should help choose an initial 25-30 cases from FraCaS,
Hahn-Richter and the frameworks' own motivating examples. Each case should
record the source, reading, premises, lexical assumptions, implemented
fragment and observation being compared.

The outcome vocabulary should distinguish entailment, contradiction,
contingency, disputed analysis, out-of-scope representation and unresolved
proof search. For non-entailment, an admissible countermodel or another
appropriate metatheoretical argument is required. A timeout is not such
an argument. In dynamic theories, the observation may need to include
accessibility or update behavior rather than truth alone.

## 12.5 Dependent events and conservativity

Theorem 7.2 of Chatzikyriakidis and Luo (2020), p. 162, states conservativity
of the dependent-event extension Ce over C. This is an attractive later
case study because it names a precise relationship, not a scalar
similarity score.

Mechanizing it requires the actual extended syntax, typing and subtyping
rules, a translation back to C, derivation preservation and the identity
property on the original language. The erasure of added type distinctions
must be reviewed for exactly what it preserves. None of those Ce results
is claimed by the present checkpoint.

## 12.6 Questions for Robin and Rasmus

1. Is the source presentation of C the right initial comparison object, or
   should a particular classical Ty2 calculus be the primary baseline?
2. Which structural and equality principles should be explicit in that
   baseline, and which should be separate extensions?
3. Which model class is required for the first paper claim: the implemented
   internal Boolean class, a source-grounded class with an external adequacy
   theorem, or Henkin models with their own construction and bridge?
4. Which linguistic readings and assumptions should be frozen in the first
   shared inference suite?
5. For comparisons with MTT and TTR, which observations must preserve
   witnesses, typing or signature/model structure rather than truth alone?

The intended contribution is not that these familiar inferences have
just been discovered. It is the auditable connection between a source
presentation, an explicit calculus, a declared interpretation and checked
claims about their relationship.

# 13. Step seven: a two-valued model soundness bridge

## 13.1 The precise advance

Checkpoint 3 takes the next step proposed after the structural milestone:
it defines a separate classical, two-valued interpretation and proves the
implemented calculus sound for that declared model class. It constructs
actual finite models, including complete domains of higher-order functions,
and checks the book's defined equality against equality of denotations.

The source contract is in `MODEL_SPEC.md`. Its full/general model distinction
comes from Hahn and Richter (2015), Definitions 4-5 and printed pp. 518-520.
Those passages explicitly distinguish arbitrary full function domains from
general domains that must provide interpretations for all represented terms.
The implementation here selects the full internal function-space case for
the extensional fragment. It does not implement their complete Ty2 language,
choice operator, Henkin semantics or translation theorem.

The adjective "internal" is substantive. The function spaces are Coq
function types. No theorem identifies their entire universe with an external
set-theoretic universe. The sorts are distinguished by type indices, not
represented as a literal family of mutually disjoint sets. The result is a
proved soundness bridge to this specified encoding, not a completed external
Montague adequacy theorem.

## 13.2 Boolean domains and the quantifier obligation

The type interpreter in `BooleanModels.v` is:

```text
bdomain E entity       = E
bdomain E truth        = bool
bdomain E (arrow a b)  = bdomain E a -> bdomain E b
```

Truth has exactly two values. Function domains are unrestricted within
the corresponding Coq function spaces. A `bmodel` supplies an inhabited
entity type, a typed lexical assignment and a `BooleanQuantifiers` record.
The latter includes both a total Boolean operation at each type and its
reflection proof:

```coq
bforall a p = true <-> forall x : bdomain E a, p x = true
```

This law is the critical obligation. Merely defining truth as `bool` does
not supply an algorithm for quantifying over an arbitrary domain. The model
must provide the operation and prove that it quantifies over the entire
domain. A constant-true quantifier fails this law; so does a finite sample
that omits a falsifying value. The checker includes negative fixtures for
these boundaries.

The recursive interpreter `beval` uses typed environments and their
extensions, just as the Prop interpreter does. Lambdas denote functions,
applications apply them, implication denotes `orb (negb p) q`, and `All`
uses the model's reflected quantifier. `bsatisfies` requires each assumption
to evaluate to `true`. `bconsequence` quantifies over every model of this
class and every satisfying assignment.

## 13.3 Constructing all finite higher-order domains

`BooleanFinite.v` implements the quantifiers without a global excluded-middle
oracle. A `finite A` packages an A-value, a finite list, decidable equality
and a proof that every A-value occurs in the list. The supplied base instances
are `unit` and `bool`.

The main issue is function types. Listing only the lexical predicates or
the functions denoted by the current examples would not construct a full
function domain. Instead, `tables` enumerates every assignment of a listed
output value to every listed input value. An empty input list starts with
the constant default function. Adding an input x extends every previous
table once for each possible output y by overriding its value at x.

`tables_cover_points` proves by induction on the input list that every
function agrees with an enumerated table on all those inputs. In the
inductive case, select the desired function's value at the new input and
reuse the previously agreeing table elsewhere. Decidable input equality
controls the override. This proof is pointwise and needs no FunExt.

`tables_complete` then uses completeness of the input enumeration to obtain
pointwise agreement everywhere. FunExt converts that agreement into equality
of functions, proving that the original function itself belongs to the
enumeration. This is the explicit place where enumeration of function
objects requires the extensionality premise in the chosen representation.

`function_eq` compares two functions at all enumerated inputs. If every
output comparison succeeds, FunExt proves equality. If one fails, equality
of the functions would contradict that comparison. This supplies the
decidable equality needed when those functions are themselves inputs to
a higher-order function.

`finite_domain` recurses over every simple type using these constructions.
`finite_quantifiers` evaluates `forallb` over the resulting list, and
`finite_forall_spec` proves reflection from complete membership. The
resulting `finite_model` has actual quantifier data and proved laws, rather
than an uninstantiated quantifier assumption.

Two regressions check enumeration sizes: four tables of type `e -> t`
over two individuals, and sixteen tables of type `(e -> t) -> t`.
The interpretation of "every predicate holds of John" computes to false:
the domain includes falsifying predicates. These tests exercise higher-order
quantification rather than only first-order cases.

The construction is a small-model reference implementation. Enumeration
grows rapidly with type structure; no claim of efficient general proof
search or scalable model finding follows. Completeness of each finite
type enumeration is not completeness of the logical calculus.

## 13.4 Optional arbitrary-domain construction

For arbitrary inhabited entity domains, `decision_quantifiers` has an
explicit input:

```coq
ClassicalDecision := forall P : Prop, {P} + {~ P}
```

It asks that input to decide `forall x, p x = true`, returning the
corresponding Boolean. Reflection follows by the two decision cases.
`decision_model` packages the result with the entity domain and lexicon.
The example `natural_number_model` instantiates this route at the infinite
domain of natural numbers.

ClassicalDecision is not silently imported or proved. It is data-valued
excluded middle, rather than just a disjunction in Prop. A lemma proves
that it implies ClassicalTruth; no converse is established in this
development. The construction is therefore conditional and is not presented
as an executable decision procedure for arbitrary mathematical propositions.

The finite route does not take ClassicalDecision. Its computation reduces
with FunExt left as a variable because FunExt is used in proof fields,
not to choose the resulting truth values. No Hilbert choice operator or
generic witness-selection mechanism has been added to C.

## 13.5 Binding, conversion and classical soundness

The new interpretation receives its own renaming and substitution proofs.
`beval_rename` relates changed variables to related environments;
`beval_weaken` specializes it to environment extension;
`beval_substitution` interprets simultaneous substitution; and
`beval_instantiate` handles replacement of the head variable.

Their term-induction arguments follow the earlier Prop-valued proofs.
In a lambda case, use FunExt to compare denoting functions. In a universal
case, pointwise equal Boolean predicate functions are equal under FunExt
and therefore have the same value under the supplied quantifier. These
lemmas do not depend on a particular finite enumeration.

`beta_boolean_sound` then follows by induction on the beta derivation.
The beta-step case uses the instantiation lemma, and the congruence cases
use the induction hypotheses. This connects the actual syntactic conversion
relation to equality of Boolean-model denotations.

The logical proof `derivation_boolean_sound` follows all seven inference
constructors. Assumptions use Boolean satisfaction. Implication uses the
proved truth-table specification. Universal introduction and elimination
use the quantifier-reflection law and the binding lemmas. Conversion uses
beta soundness.

For the final classical rule, `bfalsity_value` first proves that the encoded
falsity is false: if `forall X:t. X` were true, its instance at Boolean
false would be true. `bneg_value` identifies encoded negation with `negb`.
`bdouble_negation_value` then follows from Boolean involution. The classical
rule therefore preserves truth without invoking excluded middle over
arbitrary Coq propositions.

The specialized bridge is:

```coq
FunExt -> derives classical H p -> bconsequence H p
```

The quantifier obligation remains visible inside each model quantified by
the conclusion. There is no extra ClassicalTruth argument, but there is
also no claim that an arbitrary unreflected Boolean function is a valid
quantifier. The finite and arbitrary-domain construction routes show
exactly how that obligation is discharged and what each route assumes.

The same interpretation validates constructive derivations. This supplies
another soundness theorem, not completeness or a strict separation result.
In particular, Boolean validity of a principle does not by itself construct
an object proof in the constructive mode.

## 13.6 Defined equality and the role of full predicates

Appendix A1.2 defines equality by:

```text
u = v  :=  forall P : a -> t. P(u) implies P(v)
```

`BooleanEquality.v` implements this as `leibniz_equal`, shifting u and v
under the new predicate binder. `boolean_leibniz_predicates` uses quantifier
reflection and the weakening lemma to show that its truth means preservation
of truth from u's denotation to v's across all Boolean predicates.

To conclude that the denotations themselves are equal, the general theorem
takes a decision for equality at their domain. The predicate that tests
equality to u's denotation is then available in the full function space.
It holds of u, so the assumed Leibniz condition forces it to hold of v.
The reverse direction follows by substituting equal denotations.

This argument exposes both requirements: the separating predicate belongs
to the full domain, and its equality test can be defined. The finite
construction supplies the equality decision at every type, including
function types, yielding `finite_leibniz_equality`. For arbitrary models,
`decision_leibniz_equality` explicitly supplies ClassicalDecision instead.

No primitive equality rule or arbitrary semantic conversion rule has been
added to the object calculus. The beta relation is unchanged. Nor is the
reflection theorem a claim that equality of arbitrary Coq propositions
follows from logical equivalence; the truth carrier here is Boolean.
One cannot automatically transfer the separating-predicate argument to
an as-yet-unspecified restricted Henkin predicate domain.

## 13.7 Concrete models and the current research boundary

Three finite models parallel the earlier Prop-valued examples:

- `bool_no_men` has a nonempty singleton entity domain and an empty noun
  predicate. The universal premise is true and the encoded existential
  conclusion is false by computation.
- `bool_all_men` changes the noun predicate over that same entity domain.
  The same atomic sentence now has the opposite truth value.
- `bool_two_people` makes John a man but leaves another individual outside
  the noun extension. Generalization from the named individual is false.

`boolean_countermodel_blocks_derivation` combines a genuine false conclusion,
true premises and soundness to exclude a derivation. The example theorems
exclude existential import and generalization from one name in either mode,
conditional on FunExt. Rejection is justified by a countermodel and a theorem,
not by a failed tactic search.

The already implemented instantiation, syllogism, existential and classical
double-negation derivations produce Boolean semantic consequences through
the new bridge. They are reused rather than replaced with only concrete
truth-table computations. In the two-individual model, walk and move also
pass the defined equality test, while man and walk do not.

These results settle the first model milestone, not the entire Montague
programme. The explicit world sort and selected world-sensitive interpretation
are now added in checkpoint 4, described next. Henkin domains, external set-model adequacy,
and unrestricted equivalence between the Prop and Boolean model classes
remain separate proof obligations. Section 17 adds only a guarded target
observation relation. The finite models also do not establish a general
constructive witness-extraction theorem for the encoded existential.

# 14. Step eight: explicit worlds and an interpretation-preserving core embedding

## 14.1 Source and scope of the world extension

The new source consultation covers Chatzikyriakidis and Luo (2020), pp. 9-10,
including footnote 11, and Hahn and Richter (2015), Definitions 1-2,
pp. 516-518. These passages introduce the separate world type s and
represent intensions by functions from worlds. The source's claim of equal
expressive power with the IL approach is not treated as a theorem already
established by our implementation.

`Ty2Syntax.v` adds separate entity, truth and world types, function types,
intrinsically typed variables and the selected C-style term constructors.
It has its own capture-avoiding renaming/substitution operations and beta
relation. This preserves the previous checkpoints without changing the
original `Syntax.ty` datatype or silently modifying its proved statements.

The world fragment does not implement the entire Hahn-Richter language:
there is no primitive equality, choice operator, tense or complete PTQ
lexical translation. Necessity is defined by quantification, not introduced
as an unconstrained lexical constant. The treatment is constant-domain and
world-only. Its precise contract is in `INTENSIONALITY_SPEC.md`.

## 14.2 Models with explicit world dependence

A `wmodel` supplies inhabited entity and world domains, typed lexical
interpretations and reflected Boolean quantifiers at every represented type.
The interpretation of `s -> t` is a function from W to Boolean truth;
the interpretation of `s -> e` is an individual concept. The interpretation
of `s -> (e -> t)` can vary a predicate extension across worlds.

There is no hidden current-world argument to `weval`. Applying an intension
to a world is ordinary typed application. A lexical constant of type `s -> e`
denotes a fixed function, but that function can return different individuals
at different worlds. A constant of type e is not silently promoted to that
varying behavior.

`world_finite_domain` reuses the already proved finite function-table
construction, now starting from finite E and W. `world_finite_model` packages
the result. A test enumerates sixteen functions of type `s -> (e -> t)`
when E and W each have two elements. The model genuinely includes all such
internal functions, not only the example lexicon.

An optional `world_decision_model` handles arbitrary inhabited entity and
world domains using the explicit ClassicalDecision premise. Finite model
construction instead takes FunExt and finite-domain data. In both cases the
model includes proofs of quantifier reflection. There is no imported global
classical oracle, hidden choice principle or claim of external set-model adequacy.

## 14.3 Binding, beta and soundness at world types

`weval_rename`, `weval_weaken`, `weval_substitution` and `weval_instantiate`
repeat the checked binding argument for the new typed language. These are
not merely renamed claims: they are compiled proofs over the new syntax
and interpretation. The binder cases extend both environments by the same
value and use the lifting discipline. FunExt remains explicit where equality
of denoting functions is required.

`wbeta_sound` proves interpretation preservation for every constructor of
the new syntactic beta relation. In particular, applying an abstraction over
a world to an explicit world term agrees with its actual capture-avoiding
instantiation. `intension_application_beta` records this specialization.

`Ty2Calculus.v` supplies a separate `wderives` relation with the seven C-style
rules. Universal introduction can bind any represented type, including s;
its old hypotheses must still be weakened correctly. The classical-only
rule retains its mode check. `world_derivation_sound` proves all these rules
sound in the declared Boolean world models, with FunExt and the model's
reflected quantifiers. `world_countermodel_blocks_derivation` derives
non-derivability from an actual countermodel.

The checkpoint-2 structural results for `derives` are not silently asserted
for `wderives`. Whole-Ty2-derivation substitution, for example, is not separately
proved in this milestone. The term-level semantic substitution proof and
soundness for all declared world-calculus constructors are established.

## 14.4 Necessity and local assumptions

The defined `necessarily p` universally quantifies over all W and applies
the proposition intension p at each world. `necessity_meaning` proves this
equivalence between the defined term and its intended quantification.
There is no accessibility relation in this definition. It should not be
advertised as a model of every possible modal logic or varying-domain policy.

`necessity_elimination_derivation` constructs an object proof from a necessary
proposition to its truth at the named actual world, by universal elimination.
A separate theorem obtains its consequence in every model through soundness.

The converse fails in the actual finite example: Weather is true at Actual
and false at Alternative, so it is not necessary. The theorem
`no_necessitation_from_actual_assumption` excludes that derivation in either
mode using the countermodel and soundness. Rejecting a deliberately invalid
proof script is an additional regression test, not the basis of the exclusion.

This concerns necessitation from a local assumption. It does not deny the
usual necessitation of theorems in an appropriately specified modal system.
No complete S5 axiomatization or completeness theorem is claimed here.

## 14.5 The exact connection to the earlier extensional core

`Ty2Embedding.v` translates every old core type, typed variable and term.
The type map sends e and t to their corresponding new types and preserves
arrows. A typed map of lexical constants is an explicit parameter of the
term translation.

The two recursive domain interpretations are not definitionally the same
function. `value_maps` therefore constructs forward/backward value conversions
by recursion on core types. At base types they are identities. At arrow types,
they convert the argument in the opposite direction and the result in the
forward direction. `value_round_trips` proves both composites are identities;
its function cases use FunExt. This avoids concealing a dependent cast or
importing equality-proof irrelevance.

`core_reduct` constructs an extensional Boolean model from each world model.
Its lexical values are projected through those conversions. Its quantifier
applies the world model's quantifier at the translated type to a predicate
composed with the backward conversion. Reflection follows from the round-trip
identities and the original reflected quantifier law.

The theorem `embedding_interpretation` is proved by induction on the source
term under related environments. Variables use the environment relation;
constants use the value round trip; application composes related function
and argument values; and lambdas and quantifiers extend related environments.
The formula specialization equates the literal Boolean interpretations.

`core_derivation_world_sound` combines that theorem with the already checked
Boolean soundness theorem. It transports semantic consequences of all existing
core derivations, not only selected examples. The instantiation and syllogism
fixtures reuse their original proofs through this bridge.

Three qualifications must remain explicit. First, this embeds the world-free
core into the world-free part of the new language. It does not automatically
reinterpret an old `e -> t` lexical item as a world-varying `s -> (e -> t)`
item. Second, this is interpretation and semantic-consequence preservation,
not a separately proved syntactic translation between the two derivability
relations or a conservativity theorem. Third, it is not a translation of
the old IL syntax with primitive `up` and `down` operators.

## 14.6 Actual agreement, rigidity and freezing

The concrete model uses two individuals and two worlds. PersonConcept picks
John at Actual and the other individual at Alternative. The rigid concept
picks John at both. A simple predicate distinguishes John from the other
individual.

`concepts_agree_actually` checks agreement at Actual;
`concepts_disagree_elsewhere` checks disagreement at Alternative.
`actual_agreement_does_not_preserve_necessity` then shows that the predicate
holds necessarily of the rigid concept but not of the varying one. This is
a known distinction between actual coextension and intensional agreement,
not a new claim about Montague's theory.

`frozen_concept` first evaluates PersonConcept at Actual and passes that
individual to a lambda that abstracts over a world without changing the
individual. At Alternative this frozen concept still returns John, while
PersonConcept re-evaluated there returns the other individual.

This is not failure of ordinary Ty2 beta conversion. The expressions have
different world-binding and evaluation structure. The proved beta theorem
preserves the structure of each well-typed term. One cannot use it alone
to justify a proposed substitution rule for implicit-index IL expressions
that has not yet been defined and related to this language.

## 14.7 What the legacy-code audit establishes

The old `deep/PTQ_deep2.v` was read through its types, environments and
complete interpreter. Its consulted source hash is recorded in
`INTENSIONALITY_SPEC.md`. It remains unchanged. Its domains and lexicon
include global parameters and it imports classical logic; importing that
file into the new workbench would alter the assumption boundary rather
than prove the desired translation.

The old implementation evaluates terms at `Index = World * Time` and uses
Coq Prop for truth. Its `up` clause abstracts over a fresh index while keeping
the assignment fixed, `down` applies an intension to the current index, and
`nec_` quantifies over worlds while holding time fixed. The new layer has
explicit world arguments, Boolean truth and no time sort. Its ordinary
lambda/application clauses therefore suggest a translation route but do
not themselves establish one.

The world-only IL translation in section 15 uses Boolean truth and excludes
primitive equality. Section 16 now proves a separate actual legacy translation
preserving Prop, equality and the complete world/time index. Section 17 now
adds a guarded Prop/Boolean target bridge without a theorem for the full
legacy language or tense. Henkin
closure/completeness, external set-model adequacy, source fidelity and the
relation to MTT/TTR remain separate obligations.

# 15. Step nine: translating implicit-index IL into explicit-world Ty2

## 15.1 What the new theorem establishes

The new theorem is `explicit_world_preservation` in `ILTranslation.v`.
For every well-typed term of the declared source fragment, every typed
source-to-target variable map, related assignments and a target term
denoting the current world, evaluating the translated term yields the same
value as the independently defined source evaluator at that world.

This matters because the source and target handle worlds differently.
The source term does not mention a current-world variable; its evaluator
receives a world parameter. The target evaluator receives no such parameter;
all world dependence must be expressed by typed terms. The theorem proves
that changing this representation preserves denotation, including under
binders. It is not merely a comparison of closed example truth values.

The statement is forward interpretation preservation, not an equivalence of
the complete languages. There is no reverse translation, source IL proof
calculus, proof-theoretic conservativity theorem or Henkin completeness
result in this addition. Gallin's theorem is not claimed. Nor does the new
source syntax become the actual legacy syntax by being named IL.

## 15.2 The declared source language

`ILSyntax.v` introduces a separate source type datatype:

```coq
Inductive ity := ie | it | iarr (a b : ity) | intens (a : ity).
```

There is no standalone source world sort. Worlds enter through the
intension constructor and the evaluator parameter. The map `world_type`
sends entity and truth to their Ty2 counterparts, sends arrows recursively
to arrows, and sends `intens a` to `warr ws (world_type a)`.

The source terms are intrinsically typed variables, constants, lambda,
application, implication, universal quantification, `IUp`, `IDown` and
`IBox`. Universal quantification is available at every source type, not
only over individuals. No tense, primitive equality or choice is included.
There is deliberately no unrestricted IL beta relation or substitution
operation. Adding one requires specifying its admissibility conditions.

Source constants denote fixed values at their assigned types. A constant
of type `intens ie` may denote a nonconstant function from worlds to
individuals. Its value as a function is fixed, while its extension at a
world can vary. Therefore a world-dependent individual expression is
represented by `IDown` of an individual-concept constant, not by silently
making every e-typed constant depend on the evaluator's current world.
The same pattern represents a world-dependent predicate using a constant
of type `intens (iarr ie it)`.

This policy is explicit in the specification rather than an inference
about which linguistic names are rigid. Source lexical choices would
still require linguistic review and their own source-linked signatures.

## 15.3 Independent evaluation with a shared semantic domain contract

`ieval` is defined by structural recursion directly on source terms. It
does not evaluate a translated target term. Its arguments are a source
term, a typed assignment and a current world. Its output type is the
carrier of the translated source type in a supplied `wmodel`.

The source and target thus share internal carriers, reflected quantifiers
and a typed lexical-constant map. This is a conscious representation
choice, not a newly proved model isomorphism. In particular, truth is
`bool` on both sides, and functions inhabit the same full internal Coq
function spaces. Interpretation preservation is substantive because the
two evaluators traverse different syntax and handle world binding
differently. It is not substantive evidence for an equivalence with an
independently specified Prop-valued or external set-theoretic model class.

Let $I(t,\rho,w)$ abbreviate source evaluation. The central clauses are:

| Source form | Independent evaluation clause |
| --- | --- |
| Variable x | The fixed assigned value of x in rho, independent of w |
| Constant c | The fixed value supplied by the typed lexical map |
| Lambda x.t | The function taking a to the value of t under the extended assignment, at the same w |
| Application f u | Evaluate f and u at the same current w, then apply the resulting function to the resulting value |
| Universal x.p | Quantify over all values of x's source type, evaluating p at the same w |
| `IUp t` | The function taking a new world w' to the value of t under the unchanged assignment at w' |
| `IDown t` | Evaluate the intension expression t at w, then apply that function to w |
| `IBox p` | Quantify over all worlds w', evaluating p under the unchanged assignment at w' |

Implication is the Boolean truth table. Source quantifiers use the target
model's quantifier at the corresponding type. Necessity uses the quantifier
at `ws`, with no accessibility relation. Reflection establishes that it
is true exactly when the proposition is true at every world.

The assignment discipline deserves special attention. Changing the world
parameter does not re-evaluate a variable's assigned value. A variable can
be assigned a function, including an intension, but the same function stays
assigned when the current world changes. Application of that assigned
function is distinct from changing the assignment itself.

## 15.4 Two kinds of binders in the translation

`explicit_world constants t r w` translates t using a typed variable map
r and an arbitrary target term w of world type. Keeping w as a term, rather
than a specially named variable, makes the construction work under binders
and at constants or computed world expressions.

Under a source lambda or universal binder, a new source variable and a
corresponding target variable are introduced. `ilift r` maps the new
variable to the new target head and shifts every previous mapping. The
current-world term is also weakened because it is now under an extra
target binder. Failing to shift it would change the world being used.

Under `IUp` or `IBox`, a fresh target world variable is introduced, but
there is no new source variable. `ishift r` moves every old variable past
the fresh world binder. The new target variable becomes the current-world
term for translating the body. `IUp` translates to target lambda and
`IBox` to target universal quantification. `IDown t` translates to applying
the translation of t to the current-world term.

The small source expression `lambda x. up x` therefore translates to:

```coq
WLam (WLam (WVar (wvs wz)))
```

The inner body refers past the world binder to x. Replacing it by `WVar wz`
would return the world variable instead. In the entity-typed regression,
the target's type system rejects this attempted capture before a proof
can even begin: a world is not an individual.

`translate_intension` packages the construction by introducing an explicit
outer world lambda over the translated source context. A source term of
type a then becomes a target term of type `s -> world_type(a)`. If a is
already an intension type, the result has two world arguments with distinct
roles: an evaluation world for the source expression and a world at which
its denoted intension is applied. These arguments must not be conflated.

## 15.5 The proof, case by case

The general preservation theorem assumes a pointwise environment relation:
the value assigned to r(v) in the target equals the value assigned to v
in the source. It concludes equality between target evaluation of the
translation and source evaluation at the interpreted target world term.

The proof is by induction on the source term. Variable and constant cases
use the environment premise and shared lexical map respectively. The
application and implication cases combine the induction hypotheses for
their immediate subterms. In the extension case, the induction hypothesis
identifies the denoted intension functions; applying equal functions to
the same current world yields the required equality.

In the lambda case, function extensionality reduces equality of denotations
to equality at an arbitrary argument value. The induction hypothesis is
instantiated with the lifted variable map and extended assignments. The
fresh-variable case of the environment premise is reflexivity; old
variables use the original environment premise. `weval_weaken` proves that
weakening the world term did not change its denotation. Universal
quantification uses the same argument to equate its predicate functions.

The intension case also uses function extensionality, now at an arbitrary
new world. It applies the induction hypothesis with all source variables
shifted under that world binder but the source assignment unchanged. The
fresh world variable evaluates to the chosen new world. Necessity uses
the same construction under a universal world quantifier.

The result takes `FunExt` explicitly. It introduces no global extensionality
or classical axiom. The model still carries reflected quantifiers; the
preservation proof uses the fact that source and target call the same
quantifier operations on equal predicates. It is not a new construction
of arbitrary-domain quantifiers, and it does not discharge the independent
model-construction obligations described in sections 13 and 14.

The packaged theorem `intension_translation_preservation` specializes the
variable map to the canonical embedding of source variables. Its corollaries
relate truth values and premise-true/conclusion-false counterexamples at
every supplied world. They use a source environment projected from a
target environment. These pointwise equivalences must not be advertised
as a reverse syntax translation or a whole-model-class equivalence.

## 15.6 Cancellation and two meanings of rigidity

The semantic identity `down(up t) = t` follows directly from the evaluator
and is proved without FunExt. `IUp` builds the world-indexed function from
t, and the outer `IDown` applies it at the original evaluation world.

The reverse direction needs care. `index_rigid t` means that, for any
fixed assignment, evaluating t at two different worlds yields the same
denoted value. Variables, constants, `IUp` terms and `IBox` terms satisfy
this property. For index-rigid intension expressions, the theorem
`up_down_for_rigid_intensions` proves the reverse identity, using FunExt.
Rigidity is a sufficient condition here; no theorem claims it is necessary.

Index rigidity of an intension expression is not constancy of its value
as a world-to-value function. A concept constant c can denote the fixed
function that selects John at one world and Mary at another. The expression
c is index-rigid: its assigned function does not change with the current
evaluation world. The expression `down c` need not be index-rigid.

The regression with a nested concept shows why unrestricted reverse
cancellation fails. The finite model uses Boolean carriers for both
individuals and worlds, while their object types remain distinct. Let N
map a world to the constant individual concept returning the correspondingly
coded individual. At an evaluation world w, `down N` denotes that constant
concept. But `up(down(down N))` selects the individual corresponding to each
newly supplied world. At the actual world, applying the two functions to
the other world yields different answers. Both the unequal values and the
failure of index rigidity are proved in the finite model.

This is a familiar distinction about evaluation indices, not a discovery
that the source theory is inconsistent. The purpose of the fixture is to
prevent an implementation from installing an invalid unconditional inverse.

## 15.7 Why unrestricted source substitution is not supplied

Let c be an individual concept that denotes different individuals at the
two worlds. Compare these closed source terms at the actual world:

```text
(lambda x. up x) (down c)
up (down c)
```

The first evaluates `down c` at the actual world, assigns that individual
to x, and returns the intension that keeps returning x's assigned value.
The second builds an intension that evaluates `down c` at each newly
supplied world. They agree when subsequently applied to the actual world,
but can disagree at the alternative world. `ILExamples.v` proves this
disagreement in both source and translated target evaluations.

The first term's target translation makes the binding visible:

```text
(lambda x. lambda v. x) (c actual)
```

Ordinary target beta reduction gives `lambda v. c actual`, not
`lambda v. c v`. The actual-world argument stays explicit. The target
beta step is itself checked by `target_beta_keeps_the_evaluation_world`.
Thus the counterexample concerns an unsafe proposed source substitution
that forgets an implicit evaluation index, not a failure of target beta.

A future source calculus should specify which substitutions are admissible,
possibly using a syntactic class of index-rigid terms with a proved semantic
rigidity lemma. It should then prove a substitution theorem and only the
beta conversions justified by it. This checkpoint does not label the
absence of that calculus as a proof of impossibility.

## 15.8 What checkpoint 5 left open about the actual legacy implementation

The new source evaluator was informed by the previously inspected legacy
clauses, but no legacy file was imported or modified. Four gaps remain.

First, old intensions are functions on `World * Time`. Legacy `up` varies
the entire pair; legacy necessity changes only the world, holding time
fixed. Removing `will_` and `has_` does not make arbitrary intension values
or variable assignments time-independent. A fixed-time bridge must supply
and preserve appropriate restrictions, or the target should explicitly
represent both world and time. A single undifferentiated index sort would
also need to reproduce the fixed-time necessity policy.

Second, legacy truth is Coq Prop and its equality constructor denotes Coq
equality. The new source uses Boolean truth and excludes primitive equality.
A direct bridge requires a justified semantic relation or a parallel
Prop-valued target. A Boolean theorem cannot silently rewrite that boundary.

Third, legacy `var_s` shifts an arbitrary term, whereas the new `ivs`
shifts only a variable. A syntax inclusion must handle the old general
weakening constructor. Fourth, the old fixed lexical constructors and
English/PTQ grammar have not been mapped into the parameterized new signature.

Section 16 now proves an evaluator diagram for every actual legacy term
by retaining its old index and truth carrier in a parallel target. It does
not itself assert a Boolean relation. The scoped target relation in section
17 must still be composed with selected legacy translations. Direct source review and comparison with the
published rules remain needed: kernel checking establishes the diagram for
the specified definitions, not the correctness of every source interpretation.

## 15.9 Reproduction and review order

The three new modules add one indexed-variable lemma, eleven interpretation,
rigidity and cancellation statements, and sixteen regression statements.
The checkpoint-5 core has 173 proved declarations, all kernel-rechecked.
The checker tests the full preservation signature and the rigidity premise
of reverse cancellation, and rejects four new invalid fixtures.

Review `IL_SPEC.md`, then compare `ieval` and `explicit_world` clause by
clause. Read the general preservation type before the proof. Trace the
lambda and intension cases, then inspect the two counterexample families
before proposing any source conversion rule. Finally, inspect the explicit
legacy gaps instead of assuming that a shared name establishes identity.

No existing corpus Coq files, assessments, LaTeX draft, comparison profiles,
frontend or live worker were changed. These are local workbench artifacts.
Publishing them as new atlas evidence remains a separate reviewed action.

# 16. Step ten: a direct bridge to the actual legacy evaluator

## 16.1 Source pin and target choice

Source: `deep/PTQ_deep2.v`, imported as `LegacyPTQ.PTQ_deep2`, unchanged.
SHA256: `ee13df1359e47ca5856a3a35eacb9107beba145253a2f07c8fb39894477cd926`.

Checkpoint 5 proved a world-only Boolean IL translation but did not map the
actual old datatype or its World*Time/Prop evaluator. Checkpoint 6 fills the
code-to-code gap using a parallel Prop-valued explicit-index target. It does
not fill the Prop/Boolean model-comparison gap by changing truth carriers.

The target is an intrinsically typed higher-order language, with distinct
entity, truth, world, time and index sorts and unrestricted arrow formation.
Its index carrier is the product of the world and time carriers. Pairing,
projections and a time-order predicate are explicit primitives. There is no
hidden evaluator index. All logical operators and equality denote the same
Coq operations as in the legacy interpreter.

This target is not claimed to be Gallin's complete Ty2 language or a new
axiomatization of Montague. The earlier world-only Boolean target and its
object calculus remain separate.

## 16.2 Exact coverage

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

## 16.3 Type carriers and why no propositional extensionality is needed

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

## 16.4 Translation invariant

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

## 16.5 Preservation statements

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

## 16.6 Assumptions and models

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

## 16.7 Regression claims and remaining obligations

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

Section 17 now provides a guarded relation between the two target evaluators.
Still unproved: its composition with the full legacy language; a target object proof
calculus and its soundness; rigidity-aware source substitution; reverse
translation or conservativity; Gallin equivalence; Henkin completeness;
external set-model adequacy; and independent source/English-translation review.

The old source file and the 173-statement core are unchanged. No assessment,
frontend, live worker, LaTeX draft or public deployment is changed here.

Interactive inspection uses the isolated build, avoiding a namespace collision
with the original corpus's compiled module:

```sh
python3 deep/montague_legacy/check.py --check --inspect
```

Inspect `legacy_carrier`, `canonical_assignments_match`, the preservation
theorems and their `Print Assumptions` outputs. Quit with Ctrl-D. This
inspection build is temporary; retain source edits in the repository.

# 17. Step eleven: comparing Prop and Boolean observations

## 17.1 The question and the exact advance

The previous steps left two kinds of semantics side by side. The world-only
Ty2 branch returns Boolean truth; the actual legacy translation returns
Coq propositions in an explicit world/time target. Having two sound or
interpretation-preserving developments does not itself connect their answers.
Checkpoint 7 supplies a first connection with an explicit scope.

The main theorem uses the existing `Ty2Models.weval` and `IndexModels.peval`.
It does not define a replacement evaluator whose agreement with itself would
make the comparison vacuous. A syntax embedding translates actual Ty2 terms
into the world-only part of the Prop target. For certified terms, it relates
the two evaluations under related lexicons and assignments. The truth case
is logical equivalence with a Boolean truth assertion, not equality of
truth carriers:

```text
Prop interpretation of translated p <-> Boolean interpretation of p = true.
```

At this stage the direction of syntactic translation is Boolean Ty2 to the
Prop target. The semantic relation is symmetric at truth in the sense of
an iff, but the whole construction is not an inverse translation or an
equivalence of theories. It is also not yet a theorem taking arbitrary actual
legacy syntax as input. Section 16 and this section share a target evaluator;
that common target makes future composition possible, not automatic.

## 17.2 A total syntax embedding and a guarded theorem

`observation_type` maps `we` to `pe`, `wt` to `pt` and `ws` to `pw`; arrows
map recursively. Thus world and entity sorts remain syntactically different
even when a concrete example chooses the same carrier type for both.
`observation_var` maps a de Bruijn variable to the corresponding variable in
the mapped context. `observation_term` maps the six Ty2 constructors to
their existing Prop-target counterparts: variable, constant, lambda,
application, implication and universal quantification. A parameter
`constants` states which target constant represents each source constant.

The embedding is defined on all Ty2 terms, but the preservation theorem
requires `observable t`. This is an inductive certificate on the actual
source term, not an informal promise in documentation. Variables and constants
are certified; lambda, application and implication inherit certification
from their subterms. A universal quantifier is certified only if its bound
type has a proof of `observation_sort`, whose two constructors are entity
and world. One additional constructor certifies the particular encoded
falsity `forall X:t. X`.

That special case matters. Both interpretations make this exact expression
false, constructively: on the Prop side instantiate it with False; on the
Boolean side instantiate it with false. It does not license arbitrary
quantification over truth values. Since negation is implication to that
falsity, `observable_negation` certifies negation of a certified formula.
Since necessity quantifies over worlds, `observable_necessity` certifies
necessity of a certified world predicate. Renaming and weakening preserve
the guard by induction on its constructors.

This is a base-quantified fragment, not a strictly first-order syntax.
Higher-order lambda and application are present, and constants may have
higher-order types. Their meanings must satisfy the relation defined next.
General proposition or predicate quantification is outside the guard, as is
unrestricted Leibniz equality, which uses predicate quantification. No new
primitive equality is added. Time, pairs of world/time indices and temporal
order are not used by this embedding.

## 17.3 Relate meanings rather than identify domains

The relation `observation_relation a` is recursive on the source type a:

| Source type | Prop-side and Boolean-side values are related when |
| --- | --- |
| Entity | They are equal in the shared entity carrier. |
| World | They are equal in the shared world carrier. |
| Truth | The proposition holds exactly when the Boolean is true. |
| Arrow a b | Every pair of related inputs at a yields related outputs at b. |

At `e -> t`, for example, the relation says that P(x) holds exactly when
the Boolean predicate B(x) is true, for each entity x. It does not equate
P and B: their codomains are different. At higher arrows the relation is
defined on related arguments, not on arbitrary interchangeable values.
There is no theorem here that every Prop-valued function has a related
Boolean function, or that every value in either full higher-order domain
is covered by a corresponding value on the other side.

The model data and lexicon must therefore carry real information. For each
constant c, `lexical_relation` relates its Prop interpretation to the Boolean
model's interpretation. `observation_envs rho sigma` requires the same for
each corresponding variable. A model can satisfy the syntactic interface
without satisfying these semantic premises. Calling two constants "man"
does not prove their predicates agree.

The Boolean model still supplies the full reflected-quantifier contract
from section 14. The theorem uses this contract; it does not construct
decisions for arbitrary domains. The Prop evaluator takes an arbitrary time
type and order relation as well, but the image terms never inspect time.
This last fact is about these image terms, not about all legacy terms with
no explicit tense operator.

## 17.4 The fundamental proof, case by case

First, `observation_envs_extend` proves that extending related assignments
with related values preserves their relationship. The newly bound variable
uses the new value relation; every older variable uses the original
assignment premise. This is the binder invariant.

`observation_preservation` proceeds by induction on the certification.
Its variable case is the assignment relation. Its constant case is the
lexical relation. In the lambda case, introduce arbitrary related arguments,
extend both environments, and apply the induction hypothesis to the body.
The required conclusion is a pointwise arrow relation, so no equality between
lambda functions is needed. In application, the related function meanings
take the related argument meanings to related results directly.

For implication, the two induction hypotheses equate the truth assertions
for the antecedent and consequent. Boolean implication reflection then
matches the Prop implication. For a universal entity or world quantifier,
both models quantify over the same carrier. Relate each value to itself by
reflexivity, extend the assignments, and apply the body induction hypothesis.
The Boolean quantifier's reflection law supplies both directions. The
remaining encoded-falsity constructor uses the separate falsehood argument
above, not a general truth-domain correspondence.

The resulting theorem takes no `FunExt` premise. This is a deliberate
difference from preservation proofs that demand literal equality between
interpreted functions. Its proof has a closed global context, and the
checker compiles a signature fixture requiring preservation without FunExt.
The semantic model, lexical relation, assignments and certificate are still
explicit arguments. "No FunExt" does not mean "no assumptions".

## 17.5 Truth, counterexamples and inference agreement

`observation_truth` specializes the fundamental theorem to truth type.
`observation_refutation` derives that failure of the Prop formula is
equivalent to the Boolean value being false. `certified_observation_is_decidable`
uses a case split on that Boolean to derive P or not P for this interpreted
certified formula. It does not quantify over every proposition in Coq.

`observation_inference_agreement` takes a list of certified premise formulas
and a certified conclusion. At related assignments in a related model pair,
the implication from satisfaction of all premises to satisfaction of the
conclusion holds on one side exactly when it holds on the other. The proof
first relates satisfaction of the premise list, then applies the conclusion
correspondence. `observation_counterexample_agreement` similarly transfers
a true premise with a false conclusion.

The parameters are universal, so these results apply to every pair satisfying
the relationship, not just one example. Nevertheless, pointwise agreement
is not equality of validity over the unrestricted model classes. Such a
claim would also require enough related models and assignments to cover
each class. No coverage or surjectivity theorem is proved. This distinction
is particularly important for a theory-comparison interface: a proved
agreement under declared models should not become an unqualified badge
of theoretical equivalence.

## 17.6 Transfer actual derivations, with their soundness premise

`observable_derivation_prop_sound` takes an existing `wderives` derivation
in either the constructive or classical mode. Its premises and conclusion
must be certified. Existing Boolean soundness supplies Boolean semantic
consequence, and the inference-agreement theorem transfers that consequence
to the related Prop interpretation. Intermediate derivation formulas are
not separately required to be certified; the Boolean soundness theorem
handles the derivation, and observation correspondence handles its endpoints.

This result DOES take `FunExt`, because `world_derivation_sound` takes it.
The source theorem's assumption is not erased merely because the final
observation relation itself needs less. The result is also not a new
derivation in a Prop-target object calculus: none has been defined. It is
a semantic consequence theorem about the existing interpretation.

The examples include actual constructive object derivations for universal
instantiation, syllogism and necessity elimination. Their paired semantic
consequences are proved for every choice of the example's lexical tables,
using these derivations and soundness. They are not just successful
evaluations of one hand-picked table.

## 17.7 Witnesses are a distinct observation

The observation suite also asks whether an entity satisfying a predicate
exists. This is deliberately not the C encoding of existential quantification
by truth-type quantification, and it is not a newly added syntax constructor.
It is a metalinguistic observation on a certified formula body with a free
entity variable.

`observation_entity_witnesses` states that an x satisfying the Prop evaluation
of that body exists exactly when an x makes the Boolean evaluation true.
In each direction the proof takes the witness already supplied, extends
the assignments with that same x, and uses truth correspondence. Thus the
theorem preserves the entity witness, not only the truth of a sentence.
It does not compare proof objects or dependent-pair structures from MTT/TTR.

`observation_finite_witnesses` then relates this existential assertion to
an executable `existsb` search over a complete finite entity enumeration.
Completeness ensures that no possible entity is omitted. The result is an
iff about existence, not an implemented general extractor from arbitrary
Prop proofs into computational witness data. This precision will matter
when comparing the native witness structures of other semantic frameworks.

## 17.8 Construct the paired models before comparing them

`ObservationExamples.v` has a shared table record for men, walkers, movers,
weather by world, and an entity concept by world. Entity and world carriers
are both `bool`, with their language sorts kept distinct. The Boolean side
is constructed with the existing full finite `world_finite_model`. On the
Prop side a predicate table is interpreted by the proposition that its
Boolean entry equals true; names and concept values are retained directly.
The target time carrier is unit and its unused order relation is false.

`paired_lexical_relation` proves the required relation for each constant.
`paired_empty_assignments` proves it for the closed-term assignments.
`paired_formula_agreement` applies the generic theorem with those proofs.
These are concrete witnesses that the comparison premises can be met, not
an assumption that suitably related lexicons exist.

The finite Boolean constructor uses explicit FunExt, so the paired-model
results retain that premise even where evaluation reduces computationally.
The domain has two entities; an empty extension of "man" does not make
the whole domain empty. John denotes true, the actual world is true and
the alternative world is false. These codes are a small test model, not
linguistic claims about the identity of entities and worlds.

## 17.9 Nine linked observations and what they show

`OBSERVATION_SUITE.json` supplies unique case IDs, exact proved names and
an explicit negative independent-review status. The checker verifies that
each named proof exists in the compiled inventory. The suite is a synthetic
seed for later source-reviewed cases, not calibrated empirical evidence.

| Case | Pattern | Checked result |
| --- | --- | --- |
| O01 | Every man walks; John is a man; John walks. | Constructive derivation and paired consequences. |
| O02 | Every man walks; every walker moves; every man moves. | Constructive derivation and paired consequences. |
| O03 | John is a man; some man exists. | The named entity supplies the same actual witness. |
| O04 | Necessary weather; actual weather. | Constructive derivation and paired consequences. |
| O05 | Every man walks; some man exists. | Counterexample: empty noun extension, nonempty domain. |
| O06 | Actual weather; necessary weather. | Counterexample: different weather at the other world. |
| O07 | Actual concept agreement; substitution under necessity. | Counterexample: necessary predication differs. |
| O08 | Double negation of the reflected weather observation. | Equivalent to that observation within the paired interpretation. |
| O09 | Same atom with unmatched lexicons. | Different answers; relation premise cannot be dropped. |

O05 demonstrates vacuous universal truth with no man witness on either
side. O06 is a counterexample to inferring necessity from a local fact, not
a rejection of a suitably restricted necessitation rule. O07 compares a
rigid John concept with a world-varying concept: their actual predications
agree, but their necessary predications differ. The fixture explicitly checks
equality of their actual entity values in both interpretations, the Boolean
actual predications and both necessity values; the general theorem
also gives the corresponding Prop observations.

O08 does not show that the constructive and classical object calculi are
equivalent. Both may have sound interpretations in models that validate
classical principles, while differing in what they derive. O09 is a
precondition diagnostic rather than a non-entailment between shared readings:
the lexical meanings have deliberately been changed. None of these familiar
patterns is advertised as a newly discovered fact about Montague.

## 17.10 Why the unrestricted extension has a cost

Four named boundary statements record what extra demands would imply.
First, a proposition with a reflecting Boolean satisfies P or not P.
Second, `total_truth_reflection_implies_classical_truth` proves:

```text
(for every P:Prop, some b:bool satisfies P iff b=true)
  implies ClassicalTruth.
```

This is a conditional implication. It neither supplies the premise nor
assumes classical logic globally. It explains why the coverage requirement
for arbitrary propositions cannot be silently folded into a claim that
the present bridge has no additional foundational commitments. The theorem
uses propositional existence of a Boolean, not a choice function computing
one for every proposition.

Third, propositions reflecting the same Boolean are logically equivalent.
That still does not make them identical Coq propositions. Fourth,
`truth_equality_bridge_requires_propositional_extensionality` shows that
total reflection together with a bridge equating proposition identity with
Boolean identity would entail propositional extensionality. Again, it is
a conditional theorem, not a proof that no bridge is possible under suitable
additional axioms. It is not a metatheoretic independence proof.

These results sharpen the discussion with Robin and Rasmus. Coq remains the
constructive host. We can nevertheless define a classical object calculus,
give it Boolean semantics and relate selected Prop-valued observations to
that semantics. What cannot be claimed from those steps is that all host
propositions are two-valued, that Prop identity is logical equivalence, or
that constructive and classical object proof theories have been identified.

## 17.11 Checking, review and the next composition theorem

The extension adds 18 named statements in `ObservationBridge.v` and 18 in
`ObservationExamples.v`. All have closed global contexts. The companion
checker fresh-builds and kernel-rechecks them, checks the key signatures,
records source hashes and tests seven additional rejected fixtures. These
fixtures try arbitrary truth/predicate quantification, unmatched lexicons,
proposition equality from equivalence, missing certification, existential
import and local necessitation. Failed proof scripts test enforcement of
the intended interface; they are not proofs of general unprovability.

For inspection, run the isolated companion checker with `--inspect`, then:

```coq
Print observable.
Print observation_relation.
Check observation_preservation.
Print Assumptions observation_preservation.
Check observable_derivation_prop_sound.
Print observation_entity_witnesses.
Print paired_lexical_relation.
Print total_truth_reflection_implies_classical_truth.
```

Read the statement types as well as the assumption report. A closed global
context does not remove arguments such as the quantifier-bearing model,
lexical relation, certification, or explicit FunExt in other theorems.

The next useful mathematical step is a source-scoped composition. Choose
actual legacy expressions whose Prop translations lie in, or are provably
equivalent to terms in, the certified observation image. Prove the lexical
and assignment relationships, preserve any time dependence, then compose
legacy preservation with observation correspondence. Absence of tense
syntax alone is not a time-independence proof, as section 16 already shows.
This composition is not implemented at checkpoint 7.

In parallel with that mathematical design, Robin and Rasmus should review
the readings and observations, replacing or supplementing the synthetic seed
with source-backed cases. General higher-order truth domains, equality,
Henkin completeness, external model adequacy and comparisons with MTT/TTR
remain separately stated work. No atlas assessment, frontend or live-worker
publication follows automatically from this local checked extension.

# Appendix A. Complete inventory of the 173 closed-core proved statements

Names below omit the common `MontagueProof` prefix. The file hashes in
`verification.json` identify the checked source versions.
Items 1-32 retain the numbering of checkpoint 1. Items 33-75 were added in
checkpoint 2; items 76-113 were added in checkpoint 3; items 114-145 in
checkpoint 4; items 146-173 in checkpoint 5. This review order
is not the dependency order of compilation.

## Syntax

1. `Syntax.var_cons_cases`: indexed case analysis without a global equality axiom.

## Models

2. `Models.eval_rename`: interpretation respects typed renaming, given FunExt.
3. `Models.eval_weaken`: weakening preserves interpretation under assignment extension, given FunExt.
4. `Models.eval_substitution`: simultaneous substitution interpretation, given FunExt.
5. `Models.eval_instantiate`: head-variable instantiation interpretation, given FunExt.
6. `Models.beta_sound`: syntactic beta conversion preserves denotation, given FunExt.
7. `Models.falsity_meaning`: the encoded falsity denotes falsity.
8. `Models.neg_meaning`: encoded negation has the expected interpretation.
9. `Models.conj_meaning`: encoded conjunction has the expected interpretation, given FunExt.
10. `Models.disj_meaning`: encoded disjunction has the expected interpretation, given FunExt.
11. `Models.exists_meaning`: encoded existence has the expected interpretation, given FunExt.

## Calculus

12. `Calculus.assumption_weakening`: enlarge the true-formula assumption list.
13. `Calculus.cut`: admissibility via implication introduction and elimination.
14. `Calculus.derivation_sound`: general soundness with FunExt and mode permission.
15. `Calculus.constructive_in_classical`: inclusion of constructive derivations.
16. `Calculus.constructive_sound`: constructive consequence, given FunExt.
17. `Calculus.classical_sound`: classical consequence, given FunExt and ClassicalTruth.
18. `Calculus.countermodel_blocks_derivation`: actual countermodels exclude derivations under the soundness premises.

## Examples

19. `Examples.john_walks_derivation`: universal instantiation and modus ponens.
20. `Examples.syllogism_derivation`: two universal premises yield their syllogistic consequence.
21. `Examples.existential_derivation`: encoded existential introduction from a named witness.
22. `Examples.classical_double_negation_derivation`: use of the classical-only rule.
23. `Examples.beta_conversion_derivation`: object-level use of beta conversion.
24. `Examples.substitution_avoids_capture`: an outer variable remains free under substitution.
25. `Examples.no_men_countermodel`: a nonempty individual domain with an empty noun extension.
26. `Examples.no_existential_import`: the corresponding constructive non-derivability, given FunExt.
27. `Examples.john_walks_in_all_models`: semantic consequence via soundness, given FunExt.
28. `Examples.syllogism_in_all_models`: semantic consequence via soundness, given FunExt.
29. `Examples.existential_in_all_models`: semantic consequence via soundness, given FunExt.
30. `Examples.lexical_model_variation`: two models disagree about a closed atom.
31. `Examples.generalization_countermodel`: one named individual's property is not universal.
32. `Examples.no_generalization_from_one_name`: the corresponding constructive non-derivability, given FunExt.

## Algebra: added in checkpoint 2

33. `Algebra.rename_ext`: pointwise equal renamings act identically on terms.
34. `Algebra.subst_ext`: pointwise equal substitutions act identically on terms.
35. `Algebra.rename_id`: identity renaming leaves a term unchanged.
36. `Algebra.rename_comp`: composition of renamings.
37. `Algebra.rename_weaken`: lifted renaming commutes with weakening.
38. `Algebra.subst_after_rename`: substitution following renaming.
39. `Algebra.rename_after_subst`: rename each replacement after substitution.
40. `Algebra.subst_weaken`: lifted substitution commutes with weakening.
41. `Algebra.subst_comp`: composition of simultaneous substitutions.
42. `Algebra.subst_renaming`: substitution by variables equals renaming.
43. `Algebra.subst_id`: identity substitution leaves a term unchanged.
44. `Algebra.instantiate_weaken`: instantiate a variable on which a weakened term does not depend.
45. `Algebra.rename_instantiate`: renaming commutes with head instantiation.
46. `Algebra.subst_instantiate`: substitution commutes with head instantiation.
47. `Algebra.map_rename_weaken`: renaming/weakening compatibility for hypothesis lists.
48. `Algebra.map_subst_weaken`: substitution/weakening compatibility for hypothesis lists.

## Structural: added in checkpoint 2

49. `Structural.beta_renaming`: renaming preserves beta conversion.
50. `Structural.beta_substitution`: substitution preserves beta conversion.
51. `Structural.derivation_renaming`: transform a whole derivation by typed renaming.
52. `Structural.derivation_weakening`: add a fresh typed variable to a derivation.
53. `Structural.derivation_substitution`: transform a whole derivation by simultaneous substitution.
54. `Structural.derivation_instantiation`: specialize a derivation at a head-variable replacement.

## Contexts: added in checkpoint 2

55. `Contexts.lookup_in`: interleaved lookup gives flattened-list membership.
56. `Contexts.in_lookup`: recover interleaved lookup from flattened-list membership.
57. `Contexts.lookup_flatten`: the lookup/membership equivalence.
58. `Contexts.mixed_to_split`: translate an interleaved derivation to the split calculus.
59. `Contexts.split_to_mixed`: recover a derivation for any matching interleaved context.
60. `Contexts.mixed_split_equivalence`: equivalence of the implemented derivability judgments.
61. `Contexts.variables_only_empty`: variable declarations alone contribute no formula hypotheses.
62. `Contexts.add_hypotheses_flatten`: formula declarations have the expected flattened list.
63. `Contexts.pack_flatten`: every split assumption list has a canonical interleaved presentation.
64. `Contexts.packed_derivation`: the canonical presentation preserves derivability.
65. `Contexts.context_round_trip`: repacking preserves judgments, not declaration placement.

## StructuralExamples: added in checkpoint 2

66. `StructuralExamples.interleaved_fresh_variable`: generalization keeps an older variable reference.
67. `StructuralExamples.split_fresh_variable`: obtain its split proof through the general bridge.
68. `StructuralExamples.substitute_beneath_generalization`: instantiate the older free variable by John.
69. `StructuralExamples.weaken_open_derivation`: shift references past a new truth-type variable.
70. `StructuralExamples.substitute_conversion_derivation`: transform a proof containing beta conversion.
71. `StructuralExamples.classical_rule_survives_substitution`: preserve an explicitly classical step.
72. `StructuralExamples.beta_substitution_beneath_binder`: substitution preserves a beta proof beneath a lambda.
73. `StructuralExamples.same_flattening`: different declaration orders can have identical flattened hypotheses.
74. `StructuralExamples.different_interleavings`: those contexts are not literally equal.
75. `StructuralExamples.round_trip_preserves_judgment`: the concrete contexts derive the same formulas.

## BooleanModels: added in checkpoint 3

76. `BooleanModels.classical_decision_implies_excluded_middle`: data-valued decisions imply Prop-valued excluded middle.
77. `BooleanModels.bimp_spec`: the Boolean implication truth table reflects implication between truth assertions.
78. `BooleanModels.beval_rename`: Boolean interpretation of renaming, given FunExt.
79. `BooleanModels.beval_weaken`: Boolean interpretation under environment extension, given FunExt.
80. `BooleanModels.beval_substitution`: Boolean interpretation of simultaneous substitution, given FunExt.
81. `BooleanModels.beval_instantiate`: Boolean interpretation of head instantiation, given FunExt.
82. `BooleanModels.beta_boolean_sound`: beta conversion preserves Boolean-model denotation, given FunExt.
83. `BooleanModels.bfalsity_value`: encoded falsity denotes false.
84. `BooleanModels.bneg_value`: encoded negation denotes Boolean negation.
85. `BooleanModels.bdouble_negation_value`: encoded double negation preserves the Boolean value.
86. `BooleanModels.derivation_boolean_sound`: soundness in either mode, with FunExt and reflected model quantifiers.
87. `BooleanModels.classical_boolean_sound`: the classical Boolean consequence bridge, given FunExt.
88. `BooleanModels.constructive_boolean_sound`: the constructive Boolean consequence bridge, given FunExt.
89. `BooleanModels.boolean_countermodel_blocks_derivation`: false-in-model conclusions exclude derivations, given FunExt.

## BooleanFinite: added in checkpoint 3

90. `BooleanFinite.finite_forall_spec`: complete finite enumeration reflects universal quantification.
91. `BooleanFinite.tables_cover_points`: enumerated function tables cover every behavior on the listed inputs.
92. `BooleanFinite.tables_complete`: every function belongs to the complete table enumeration, given FunExt.
93. `BooleanFinite.finite_quantification_complete`: the recursively constructed quantifiers satisfy their exact contract.
94. `BooleanFinite.booleans_are_two_valued`: every Boolean is true or false.

## BooleanEquality: added in checkpoint 3

95. `BooleanEquality.boolean_leibniz_predicates`: the defined equality quantifies over all Boolean predicates, given FunExt.
96. `BooleanEquality.boolean_leibniz_equality`: reflection to denotation equality with explicit equality decisions and FunExt.
97. `BooleanEquality.finite_leibniz_equality`: the finite construction discharges equality decisions, given FunExt.
98. `BooleanEquality.decision_leibniz_equality`: ClassicalDecision discharges equality decisions in arbitrary models, given FunExt.

## BooleanExamples: added in checkpoint 3

99. `BooleanExamples.boolean_no_men_countermodel`: compute the Boolean empty-noun countermodel, given FunExt for construction.
100. `BooleanExamples.boolean_generalization_countermodel`: compute the Boolean two-individual countermodel, given FunExt for construction.
101. `BooleanExamples.boolean_lexical_variation`: changing lexical interpretation changes an atom's Boolean truth.
102. `BooleanExamples.boolean_no_existential_import`: neither mode derives the invalid existential inference, given FunExt.
103. `BooleanExamples.boolean_no_generalization_from_one_name`: neither mode derives the invalid generalization, given FunExt.
104. `BooleanExamples.boolean_john_walks_consequence`: reuse the instantiation derivation through Boolean soundness.
105. `BooleanExamples.boolean_syllogism_consequence`: reuse the syllogism derivation through Boolean soundness.
106. `BooleanExamples.boolean_existential_consequence`: reuse the encoded-existence derivation through Boolean soundness.
107. `BooleanExamples.boolean_double_negation_consequence`: reuse the classical derivation through Boolean soundness.
108. `BooleanExamples.four_individual_predicates`: four function tables over two individuals and two truth values.
109. `BooleanExamples.sixteen_predicates_of_predicates`: sixteen tables at the next predicate level.
110. `BooleanExamples.higher_order_quantification_checks_all_functions`: full quantification includes predicates false of John.
111. `BooleanExamples.finite_function_equality_reflects_denotation`: equal lexical functions satisfy the defined equality.
112. `BooleanExamples.distinct_predicates_are_not_equal`: different lexical predicates fail that equality.
113. `BooleanExamples.decision_model_quantifier_correct`: the infinite-domain example's quantifier reflects universality under ClassicalDecision.

## Ty2Syntax: added in checkpoint 4

114. `Ty2Syntax.wvar_cons_cases`: indexed variable case analysis for the world-typed syntax without equality axioms.

## Ty2Models: added in checkpoint 4

115. `Ty2Models.weval_rename`: world-model interpretation of renaming, given FunExt.
116. `Ty2Models.weval_weaken`: interpretation under environment extension, given FunExt.
117. `Ty2Models.weval_substitution`: simultaneous substitution interpretation, given FunExt.
118. `Ty2Models.weval_instantiate`: head-variable instantiation interpretation, given FunExt.
119. `Ty2Models.wbeta_sound`: syntactic beta conversion preserves world-model denotation, given FunExt.
120. `Ty2Models.wfalsity_value`: encoded falsity is false in world models.
121. `Ty2Models.wneg_value`: encoded negation is Boolean negation.
122. `Ty2Models.necessity_meaning`: defined absolute necessity is truth at every world, given FunExt.
123. `Ty2Models.intension_application_beta`: world abstraction/application respects actual instantiation, given FunExt.

## Ty2Calculus: added in checkpoint 4

124. `Ty2Calculus.world_derivation_sound`: soundness for both modes over the declared world model class, given FunExt.
125. `Ty2Calculus.world_countermodel_blocks_derivation`: actual world countermodels exclude derivations, given FunExt.

## Ty2Embedding: added in checkpoint 4

126. `Ty2Embedding.value_round_trips`: both domain-conversion composites are identities, given FunExt.
127. `Ty2Embedding.lower_lift`: recover an original core value after conversion, given FunExt.
128. `Ty2Embedding.lift_lower`: recover a target value at a translated core type, given FunExt.
129. `Ty2Embedding.embedding_interpretation`: translated core terms preserve interpretation under related environments, given FunExt.
130. `Ty2Embedding.embedded_formula_interpretation`: translated formulas have the same Boolean truth in the reduct, given FunExt.
131. `Ty2Embedding.core_derivation_world_sound`: semantic consequences of core derivations transfer to translated formulas, given FunExt.

## Ty2Examples: added in checkpoint 4

132. `Ty2Examples.world_sensitive_truth`: one proposition has different truth values at two worlds.
133. `Ty2Examples.actual_truth_is_not_necessity`: actual truth and false necessity in the concrete model.
134. `Ty2Examples.necessity_elimination_derivation`: an object derivation by universal elimination.
135. `Ty2Examples.necessity_elimination_in_models`: its general semantic consequence, given FunExt.
136. `Ty2Examples.no_necessitation_from_actual_assumption`: neither mode licenses the invalid local-to-necessary inference, given FunExt.
137. `Ty2Examples.concepts_agree_actually`: the rigid and varying concepts agree at Actual.
138. `Ty2Examples.concepts_disagree_elsewhere`: those concepts disagree at Alternative.
139. `Ty2Examples.actual_agreement_does_not_preserve_necessity`: a predicate distinguishes the concepts under necessity.
140. `Ty2Examples.freezing_is_not_worldwise_re_evaluation`: freezing an actual value differs from re-evaluating the concept.
141. `Ty2Examples.explicit_world_beta_conversion`: a genuine world beta step.
142. `Ty2Examples.typed_world_substitution_avoids_capture`: an older world variable remains free beneath a binder.
143. `Ty2Examples.old_instantiation_in_world_models`: reuse the original core instantiation derivation through the bridge.
144. `Ty2Examples.old_syllogism_in_world_models`: reuse the original core syllogism derivation through the bridge.
145. `Ty2Examples.sixteen_world_dependent_predicates`: sixteen full function tables of type `s -> (e -> t)` in the finite model.

## ILSyntax: added in checkpoint 5

146. `ILSyntax.ivar_cons_cases`: axiom-free case analysis for source variables under a binder.

## ILTranslation: added in checkpoint 5

147. `ILTranslation.explicit_world_preservation`: all typed source terms preserve interpretation under related assignments and an explicit current-world term, given FunExt.
148. `ILTranslation.intension_translation_preservation`: the world-function packaging preserves evaluation at every world, given FunExt.
149. `ILTranslation.translated_truth_iff`: source and target agree on truth at a supplied world and projected assignment, given FunExt.
150. `ILTranslation.translated_counterexample_iff`: premise-true/conclusion-false pairs are preserved and reflected pointwise, given FunExt.
151. `ILTranslation.down_up_cancellation`: extension immediately after intension preserves evaluation, without FunExt.
152. `ILTranslation.variables_are_index_rigid`: a fixed assignment does not change when the evaluation world changes.
153. `ILTranslation.constants_are_index_rigid`: typed constants have fixed denoted values.
154. `ILTranslation.up_is_index_rigid`: an intension abstraction denotes the same function at each evaluation world.
155. `ILTranslation.box_is_index_rigid`: absolute necessity is independent of the current evaluation world.
156. `ILTranslation.up_down_for_rigid_intensions`: reverse cancellation under index rigidity, given FunExt.
157. `ILTranslation.implicit_necessity_meaning`: source necessity means truth at every world.

## ILExamples: added in checkpoint 5

158. `ILExamples.source_world_sensitive_truth`: a source proposition has different values at two worlds.
159. `ILExamples.source_actual_truth_not_necessity`: actual truth does not entail source necessity.
160. `ILExamples.assigned_variable_survives_world_shift`: abstraction changes the index, not an assigned individual's value.
161. `ILExamples.il_binder_translation_is_capture_free`: an assigned entity remains past the new world binder.
162. `ILExamples.down_translation_uses_current_world`: extension translates to application at the supplied world.
163. `ILExamples.up_rebinds_world_but_not_assignment`: the complete freezing term has the required target binding structure.
164. `ILExamples.unsafe_index_substitution_changes_denotation`: freezing and re-evaluation compute different values.
165. `ILExamples.source_freezing_and_recomputation_are_distinct`: the source-denoted functions are unequal.
166. `ILExamples.target_preserves_freezing_counterexample`: target computations retain that counterexample.
167. `ILExamples.up_down_requires_a_side_condition`: a nested intension refutes unconditional reverse cancellation.
168. `ILExamples.nested_extension_is_not_index_rigid`: the nested extension violates the rigidity premise.
169. `ILExamples.quantification_survives_world_abstraction`: entity quantification through up/down computes identically in both evaluators.
170. `ILExamples.higher_order_quantification_is_not_a_sample`: full predicate quantification includes the falsifying predicate in both evaluators.
171. `ILExamples.implication_translation_regression`: a translated implication with necessity computes as specified.
172. `ILExamples.target_beta_keeps_the_evaluation_world`: target beta retains the explicit world in the substituted argument.
173. `ILExamples.preservation_applies_to_open_intensional_terms`: an open-term instance of the general preservation theorem.

# Appendix B. Complete inventory of the 76 companion statements

Names omit `MontagueLegacy`. The number of retained legacy global parameters
is given for each statement. This is not its number of explicit premises:
FunExt and other theorem hypotheses remain visible in its type. The exact
dependency names and source hashes are in `deep/montague_legacy/verification.json`.
Items 174-213 are the checkpoint-6 legacy companion. Items 214-249 are
checkpoint-7 observations; all of the latter have closed global contexts.

## IndexSyntax.v

174. `IndexSyntax.pvar_cons_cases`: closed global context.

## IndexModels.v

175. `IndexModels.peval_rename`: closed global context.
176. `IndexModels.peval_weaken`: closed global context.
177. `IndexModels.cast_back`: closed global context.
178. `IndexModels.cast_forward`: closed global context.
179. `IndexModels.cast_application`: closed global context.
180. `IndexModels.cast_lambda`: closed global context.
181. `IndexModels.cast_equality`: closed global context.
182. `IndexModels.cast_forall`: closed global context.
183. `IndexModels.cast_exists`: closed global context.

## LegacyTranslation.v

184. `LegacyTranslation.legacy_lower_lift`: 3 retained legacy parameters.
185. `LegacyTranslation.legacy_lift_lower`: 3 retained legacy parameters.
186. `LegacyTranslation.legacy_application`: 3 retained legacy parameters.
187. `LegacyTranslation.legacy_lambda`: 3 retained legacy parameters.
188. `LegacyTranslation.legacy_intension`: 3 retained legacy parameters.
189. `LegacyTranslation.legacy_equality`: 3 retained legacy parameters.
190. `LegacyTranslation.legacy_forall`: 3 retained legacy parameters.
191. `LegacyTranslation.legacy_exists`: 3 retained legacy parameters.
192. `LegacyTranslation.assignments_shift`: 3 retained legacy parameters.
193. `LegacyTranslation.assignments_lift`: 3 retained legacy parameters.
194. `LegacyTranslation.canonical_assignments_match`: 3 retained legacy parameters.
195. `LegacyTranslation.legacy_interpretation_preservation`: 29 retained legacy parameters.
196. `LegacyTranslation.legacy_open_preservation`: 29 retained legacy parameters.
197. `LegacyTranslation.legacy_truth_preservation`: 29 retained legacy parameters.
198. `LegacyTranslation.legacy_counterexample_preservation`: 29 retained legacy parameters.

## LegacyExamples.v

199. `LegacyExamples.no_tense_still_allows_time_dependence`: 29 retained legacy parameters.
200. `LegacyExamples.legacy_necessity_holds_time_fixed`: 29 retained legacy parameters.
201. `LegacyExamples.necessity_is_not_all_index_quantification`: 29 retained legacy parameters.
202. `LegacyExamples.translated_necessity_keeps_time`: 29 retained legacy parameters.
203. `LegacyExamples.translated_atom_retains_time_dependence`: 29 retained legacy parameters.
204. `LegacyExamples.intension_abstracts_over_time_too`: 29 retained legacy parameters.
205. `LegacyExamples.future_keeps_world_and_order`: 29 retained legacy parameters.
206. `LegacyExamples.past_keeps_world_and_order`: 29 retained legacy parameters.
207. `LegacyExamples.reversing_future_order_changes_predictions`: 29 retained legacy parameters.
208. `LegacyExamples.translated_future_and_past`: 29 retained legacy parameters.
209. `LegacyExamples.weakening_shifts_a_whole_term_not_only_a_variable`: closed global context.
210. `LegacyExamples.translated_primitive_equality`: 29 retained legacy parameters.
211. `LegacyExamples.translated_higher_order_quantifiers`: 29 retained legacy parameters.
212. `LegacyExamples.actual_legacy_freezing_distinction`: 3 retained legacy parameters.
213. `LegacyExamples.translated_legacy_freezing_distinction`: 29 retained legacy parameters.

## ObservationBridge.v: added in checkpoint 7

214. `ObservationBridge.observable_renaming`: renaming preserves the observation certificate.
215. `ObservationBridge.observable_weakening`: variable-context extension preserves certification.
216. `ObservationBridge.observable_negation`: certified formulas have certified encoded negations.
217. `ObservationBridge.observable_necessity`: certified world predicates have certified necessity formulas.
218. `ObservationBridge.observation_envs_extend`: related values extend related assignments.
219. `ObservationBridge.observation_preservation`: related values for every certified term, without FunExt.
220. `ObservationBridge.observation_truth`: truth correspondence under the lexical and assignment relations.
221. `ObservationBridge.observation_refutation`: Prop refutation corresponds to Boolean false.
222. `ObservationBridge.certified_observation_is_decidable`: an interpreted certified formula satisfies excluded middle under the relation premises.
223. `ObservationBridge.observation_inference_agreement`: pointwise agreement on certified premises and conclusion.
224. `ObservationBridge.observation_counterexample_agreement`: a true premise and false conclusion transfer between related interpretations.
225. `ObservationBridge.observable_derivation_prop_sound`: actual Ty2 derivations transfer semantic consequences to Prop, given FunExt and certified endpoints.
226. `ObservationBridge.observation_entity_witnesses`: the same entity supplies a witness on either side.
227. `ObservationBridge.observation_finite_witnesses`: actual existential observation agrees with search over a complete finite entity enumeration.
228. `ObservationBridge.reflected_proposition_is_decidable`: a reflecting Boolean implies excluded middle for that proposition.
229. `ObservationBridge.total_truth_reflection_implies_classical_truth`: reflection coverage of all Prop would imply unrestricted excluded middle.
230. `ObservationBridge.common_truth_value_gives_equivalence`: sharing a reflecting Boolean gives equivalence, not proposition identity.
231. `ObservationBridge.truth_equality_bridge_requires_propositional_extensionality`: total reflection plus the stated truth-equality bridge would imply propositional extensionality.

## ObservationExamples.v: added in checkpoint 7

The paired Boolean model takes explicit FunExt for construction. That
premise remains distinct from these proofs' closed global contexts.

232. `ObservationExamples.paired_lexical_relation`: the concrete paired lexicons satisfy the logical relation.
233. `ObservationExamples.paired_empty_assignments`: the closed-term assignments satisfy the assignment relation.
234. `ObservationExamples.paired_formula_agreement`: certified formulas agree in the paired models.
235. `ObservationExamples.inference_suite_is_certified`: the suite's principal formulas satisfy the observation guard.
236. `ObservationExamples.observed_instantiation_derivation`: constructive object derivation of universal instantiation with a named individual.
237. `ObservationExamples.observed_syllogism_derivation`: constructive object derivation of the syllogism.
238. `ObservationExamples.observed_necessity_elimination_derivation`: constructive object derivation from necessity to actual truth.
239. `ObservationExamples.paired_derivation_transfer`: derivations yield paired Prop consequences under certified endpoints and FunExt.
240. `ObservationExamples.instantiation_agrees_for_all_tables`: both interpretations validate the instantiation inference for every paired table.
241. `ObservationExamples.syllogism_agrees_for_all_tables`: both interpretations validate the syllogism for every paired table.
242. `ObservationExamples.necessity_elimination_agrees_for_all_tables`: both interpretations validate necessity elimination for every paired table.
243. `ObservationExamples.paired_entity_witness_agreement`: existence of a man agrees with finite Boolean witness search.
244. `ObservationExamples.universal_has_no_existential_import`: paired counterexample with an empty noun extension.
245. `ObservationExamples.named_individual_supplies_a_witness`: the named entity is an actual witness in each interpretation.
246. `ObservationExamples.actual_truth_does_not_license_necessity`: paired two-world counterexample to local necessitation.
247. `ObservationExamples.actual_agreement_does_not_license_necessary_substitution`: actual agreement fails to preserve necessary predication.
248. `ObservationExamples.double_negation_agrees_on_reflected_observations`: double negation holds for the selected reflected observation, not arbitrary Prop.
249. `ObservationExamples.mismatched_lexicons_can_change_the_answer`: differing lexical meanings change the same atom's truth.

# Appendix C. Reading and evidence order

For a short technical review, start with the definition of `derives` in
`Calculus.v`, then inspect `model`, `domain` and `consequence` in `Models.v`.
Read the types of the two specialized soundness theorems before their
proof scripts. Inspect `eval_substitution` and `beta_sound` next, then the
example derivations and concrete model definitions. Finally, run the fresh
checker and compare its output with `verification.json`.

For the new structural milestone, begin with `derivation_substitution` in
`Structural.v`. Read its universal-introduction, universal-elimination and
conversion cases alongside their algebra lemmas. Then compare the
constructors of `mixed_derives` and `derives`, read both directions of the
context bridge, and follow the first three examples in
`StructuralExamples.v`. This order exposes the binding discipline before
the supporting algebra in full detail.

For the model milestone, read `MODEL_SPEC.md` first. Inspect `bmodel`,
`bforall_spec` and the type of `classical_boolean_sound`. Then read
`tables_cover_points`, `tables_complete` and `finite_quantifiers` to verify
that actual finite models discharge the quantifier obligation. Inspect
`boolean_leibniz_equality` with its equality-decision premise, and finally
the concrete computations and consequences in `BooleanExamples.v`.

For the world milestone, read `INTENSIONALITY_SPEC.md`, then the definitions
of `wty`, `wmodel`, `weval`, `necessarily` and `wderives`. Inspect the type of
`world_derivation_sound` before its proof. Next inspect `value_round_trips`,
`core_reduct` and `embedding_interpretation`, followed by the two-world
countermodels. Keep the core bridge distinct from the actual legacy-to-Prop
translation added in section 16 and from the guarded target observation
relation in section 17.

For the implemented world-only IL milestone, read `IL_SPEC.md`, then the
types, `ieval` and `explicit_world` side by side. Inspect the assignment
premise of `explicit_world_preservation`, its two different binder cases,
and the freezing/reverse-cancellation counterexamples. The legacy
World*Time and Prop obligations are separate from that Boolean result.

For the actual legacy bridge, read `../montague_legacy/LEGACY_SPEC.md`, then
the carrier equality and transport laws, `compile_legacy` against the old
`eval`, and the canonical-assignment witness. Inspect the main theorem and
its nonempty global audit before interpreting the time and freezing examples.
Keep the unrestricted Prop/Boolean model comparison and full legacy
composition open.

For the observation milestone, read `../montague_legacy/OBSERVATION_SPEC.md`,
then `observable`, `observation_relation` and `observation_envs`. Read the
full type and induction cases of `observation_preservation` before its
inference corollaries. Distinguish its lack of FunExt from the explicit
FunExt in derivation transfer and paired finite-model construction. Inspect
the witness theorems, the actual lexical-relation proof and the nine suite
cases. Finish with the two conditional boundary theorems about unrestricted
reflection and truth equality. Do not infer coverage of all Prop-valued
models from pointwise agreement on related interpretations.

For a source-fidelity review, reverse the initial emphasis: read the cited
book rules first, record any differences in judgments or structural rules,
and only then inspect the encoding. Mechanical success should not settle
a disagreement about the source reading.

# References and consultation status

- Chatzikyriakidis, S. and Luo, Z. (2020). *Formal Semantics in Modern Type
  Theories*. ISTE/Wiley. DOI: <https://doi.org/10.1002/9781119489252>.
  Directly consulted for the implemented rules and the contextual discussion.
- Luo, Z. and Soloviev, S. (2017). *Dependent Event Types*. WoLLIC 2017.
  DOI: <https://doi.org/10.1007/978-3-662-55386-2_15>. Source antecedent
  identified through the book; no separate direct rule audit claimed here.
- Luo, Z. (2014). *Formal Semantics in Modern Type Theories: Is It
  Model-Theoretic, Proof-Theoretic, or Both?* LACL 2014.
  DOI: <https://doi.org/10.1007/978-3-662-43742-1_14>. The position is
  discussed through the directly consulted book; this report does not claim
  a separate full reading of the original paper.
- Hahn, M. and Richter, F. (2015). *Henkin semantics for reasoning with
  natural language*. Journal of Language Modelling 3(2), 513-568.
  DOI: <https://doi.org/10.15398/jlm.v3i2.113>. Relevant definitions,
  translation statements and evaluation discussion were directly consulted
  in preparation for this programme; their translation is not implemented here.
- Gallin, D. (1975). *Intensional and Higher-Order Modal Logic*.
  North-Holland. Ty2 background cited through the book and Hahn-Richter;
  no independent audit of the monograph is claimed.
- Montague, R. (1973). *The Proper Treatment of Quantification in Ordinary
  English*. Historical source of the branch. The immediate rule source for
  this new checkpoint is the explicit C presentation listed above, not a
  claim of a fresh complete audit of PTQ.

The proposed review by Robin Cooper and Rasmus Blanck has not yet occurred.
No statement in this report should be treated as their endorsement.
