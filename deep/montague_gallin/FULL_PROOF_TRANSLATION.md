# Checkpoint 7: every implemented IL proof compiles to a Ty2 proof

## Completed result

The public compiler now has this type:

```coq
compile_il_proof :
  forall G (p : ltm G t), ILDerivation p -> Derivation (il_at p).
```

There is no pointwise-fragment restriction. Every constructor of the
existing source `ILAxiom` and `ILDerivation` datatypes is covered. The
result is a proof object in the existing Ty2 `Derivation` datatype,
using its original axiom and replacement constructors.

Neither proof calculus was changed to obtain this result. The translation
`il_at` is also unchanged. The baseline definitions are those of commit
`30a4a28`, which contains checkpoint 6.

Proofs from assumptions translate as well:

```coq
compile_il_from :
  forall G (Gamma : ltm G t -> Prop) p,
  ILFrom Gamma p -> Ty2From (compiled_premises Gamma) (il_at p).
```

The source's finite premise list is translated, not discarded, and the
compiled theorem has the corresponding nested implications. No local
hypothesis constructor is added to either theorem calculus.

These are forward proof-translation results for the implemented,
locally indexed, primitive IL calculus. They are not a reverse proof
translation, completeness theorem, description-principle extension, or
equivalence with a separate named-syntax implementation.

## 1. Prove substitution laws as syntactic equalities

`SyntaxAlgebra.v` proves the needed renaming and substitution laws on
minimal Ty2 terms. These are equalities between syntax trees, not merely
equal denotations. They include:

- pointwise agreement of renamings and substitutions;
- identity and composition of renamings;
- renaming before and after substitution;
- substitution under a binder preserving weakening;
- substituting into a weakened term leaving that term unchanged.

No model, Boolean reflection, function extensionality or completeness
assumption is used. The proofs are structural inductions; the functions
representing variable maps are compared pointwise rather than by an
extensionality axiom.

## 2. Generalize the compiler without changing its public result

`ILCompileSyntax.lcompile` temporarily allows each source context variable
to map to a target term rather than only a target variable. This makes
the substitution lemma expressible: substituting in the target can turn
a variable's image into a compound expression.

The implementation follows the existing clauses:

```text
constant c      -> c applied to the current index
lambda x. A    -> lambda x. compile A with lifted variable mapping
Up A           -> lambda index. compile A at that fresh index
Down A         -> compile A applied to the current index
```

`lcompile_agrees_with_existing` proves syntactic equality with the existing
compiler followed by minimal-syntax elimination, for variable mappings
and an explicit index variable. That is exactly the interface used by
`il_at`. This is not a newly chosen translation with only semantic
agreement to the old one.

The central substitution equation is:

```text
substitute (compile A r i) s
  = compile A (substitute each image of r using s) (substitute i using s)
```

From it, `lcompile_beta` handles substitution for an ordinary source
binder and `lcompile_index_beta` handles substitution for the index binder
introduced by Up. The source-renaming lemma handles the exchange required
by AS4.5.

## 3. Construct a target proof for every source axiom

`compile_all_axioms` returns an actual target proof for any `ILAxiom`.
It does not assert that a valid axiom must have some proof.

| Source axiom | Target proof construction |
|---|---|
| A1 | Target A1 after the logical abbreviations are matched syntactically. |
| A2 | Target A2, with the translated variables. |
| A3 | Target A3 at the translated argument/result types. |
| AS4.1 | Target beta plus removal of the unused source binder. |
| AS4.2 | Target beta for the identity lambda. |
| AS4.3 | Target beta on both sides, application congruence, symmetry and transitivity. |
| AS4.4 | Target beta on both sides and equality congruence. |
| AS4.5 | Target beta under lambda with the proved capture-avoiding variable exchange. |
| AS4.6 | Target beta and application congruence for Down. |
| AS4.7 | Target beta under the index lambda, using the source MC evidence. |
| A5 | Target function extensionality A3 with argument type s. |
| AS6 | Target beta for the index abstraction introduced by Up. |

The modal condition in AS4.7 is substantive. Moving the beta argument
under an index lambda changes the index used to translate it. The lemma
`lcompile_modal_closed` proves that a syntactically modally closed term's
translation is independent of the current-index argument, for a fixed
variable mapping. This is the exact equality needed in that proof case.
It is not assumed for arbitrary constants or terms.

A5 illustrates what explicit indices buy. The source says that intension
variables are equal exactly when their extensions agree at every index.
After translation, this is target function extensionality at type s.
The proof uses the existing Ty2 A3 rule, not a new semantic axiom.

## 4. Translate every inference rule

`compile_il_general` is an induction on `ILDerivation`. It is generalized
over the target context, source-to-target variable map and current-index
term. All eight rule cases are covered:

| Source rule | Target construction |
|---|---|
| R1, equality elimination | Replacement at the whole formula. |
| R2/R3, application congruence | Derived target application congruence. |
| R4, lambda congruence | Recurse with a lifted mapping and weakened index, then target lambda congruence. |
| R5, Up congruence | Recurse with shifted variable images and a fresh index variable, then target lambda congruence. |
| R6, Down congruence | Application congruence with the same index argument. |
| R7/R8, equality congruence | Derived target equality congruence. |

The public `compile_il_proof` specializes that induction to the canonical
variable mapping and the leading index variable, and uses the syntactic
agreement theorem to return `Derivation (il_at p)`.

The compiler has no model or semantic-truth argument. It does not invoke
either calculus's soundness theorem, a completeness theorem, or an LLM.
Its output is checked directly by the target proof datatype and Rocq's
kernel. Rocq remains the metalanguage in which this metatheory is proved.

## 5. Preserve reasoning from assumptions

`ProofDischarge.v` gives Ty2 the same finite implication-chain packaging
already used for source assumptions. This is a definition around existing
theorems, not a new inference rule.

`compile_implication_chain` proves that translating a source chain yields
the corresponding target chain syntactically. `compile_il_from` retains
the source premise list, maps it through `il_at`, maps its membership
evidence into `compiled_premises Gamma`, and compiles the source theorem.

The separate `ty2_from_assumptions_sound` theorem checks the semantic
interpretation of that packaging. Its BooleanTruth/FunExt parameters are
not parameters of the proof compiler.

## 6. Regression and independent checks

`FullCompilerExamples.v` supplies concrete proof objects for:

- nested lambda and Up congruence around Down/Up cancellation;
- AS4.5 with a reference crossing the exchanged binders;
- guarded modal beta with an intension-valued argument;
- A5 compiled to target extensionality;
- an empty-premise discharged proof bundle.

`il_at_interpretation` cross-checks the explicit-index body against the
previous standard-model correspondence. This semantic result is used to
check the output interface, not to construct the proof objects.

The existing two-index countermodel still refutes the unguarded modal
beta formula. `forbidden_modal_beta_has_no_target_derivation` now also
rules out a target proof of its actual translation, conditional on the
same explicit foundational model inputs. Completing the compiler has not
made the invalid source formula acceptable.

The isolated verifier checks 225 theorem/lemma/example statements across
26 Gallin modules, rechecks proof objects with `coqchk`, audits definitions
including both compilers, checks exact public signatures, and rejects
52 negative fixtures. The new fixtures reject missing source proofs,
semantic truth supplied as a proof, erased hypotheses, an unguarded modal
beta instance, and a claimed reverse proof translation.

## Completed scope and separate future work

The requested general forward proof translation is complete for every
implemented `ILDerivation` and `ILFrom`. No source rule or axiom case in
those datatypes remains outside the compiler.

The source calculus is Gallin's printed alternative AS4.1-AS4.7/R1-R8
presentation, encoded with typed local binders and the documented logical
macros. A formal comparison with separately implemented named syntax or
the primary AS4/R presentation remains a different task.

Description principles D, the full IL+D/Ty2+D result of Theorem 8.3,
reverse interpretations, general/Henkin models and completeness are not
claimed. They are not hidden prerequisites in this forward compiler.

The source PTQ checkpoint, atlas assessments, proof library served by the
app and deployment remain unchanged. This checkpoint is local until a
separate push/deployment step is requested.
