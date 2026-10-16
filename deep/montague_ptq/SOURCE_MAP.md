# Source-first PTQ specification and correspondence

10 October 2026. This is a new reconstruction, not a modification of the
frozen checkpoint-7 sources or their preservation theorems.

## What counts as formalizing PTQ

The target is the specified English fragment in Montague (1973), not merely
a typed logic with familiar examples. Completion requires its categories,
lexicon and syntactic operations; its intensional language and model clauses;
its compositional translation relation; its admissible-model conditions; and
the claimed readings, truth conditions and inference/non-inference examples.
Representation choices and corrections must be distinguished from changes to
the semantic analysis. Kernel acceptance cannot establish source fidelity by itself.

Gallin equivalence, Henkin completeness and equivalence with another semantic
theory are additional research questions. They are not requirements imposed
by PTQ's own specification and must not distract from finishing that specification.

## Primary source

Richard Montague (1973), *The Proper Treatment of Quantification in Ordinary
English*. Originally in *Approaches to Natural Language*, pp. 221-242.
The consulted copy is an 18-page reprint, printed pp. 17-34, including
Richmond Thomason's editorial notes 9, 10 and 12. All page citations below
refer to that reprint, not the original proceedings pagination.

PDF SHA256:
`45ec6a0fa9bdac5c4fe92baf839aa90f60001a99a769a64fa7fa5c13f290b2e8`.

Local source: `/Users/graogro/Dropbox/formalizing_formal_semantics/montague73.pdf`.
The PDF is not redistributed. The text of the paper was consulted; the
formulas on printed pp. 26 and 28, the surface rules on p. 19, and the
coordination examples on p. 32 were also
checked against rendered page images. This is AI-assisted source consultation,
not independent human approval.

We use the corrected interpretation clauses in note 10. We retain PTQ's
all-world/all-time necessity (clause 8, note 9), and implement the capture
avoidance required by note 12 using fresh de Bruijn binders. `FreshNames.v`
now implements the exact least-even source-index algorithm, checks bound
and free occurrences, proves literal replacement, and proves agreement
with the intrinsic relative-clause operation.

## Source-to-code map

| Source | Code | Status and representation choice |
| --- | --- | --- |
| Categories, p. 18 | `Syntax.cat` | Both slash categories retained, syntactically distinct. |
| Type assignment, p. 25 | `Syntax.category_type` | Recursive map; IV and CN have type `intens e -> t`, not `intens e -> intens t`. |
| Lexicon, p. 19; lexical injection g, pp. 25-26 | `Grammar.lexeme`, `lexical_code`, `lexical_map_injective` | All listed basic words, plus exceptional names, pronouns, be and necessarily. The map into typed numbered constants is proved injective. |
| S1-S17, pp. 19-22 | `Grammar.tree` | All rule families as intrinsically category-correct candidate analysis trees. Surface success is checked separately. |
| F0-F15, pp. 19-21 | `Surface.realize`, `surface`; `SurfaceInvariant`; `VacuousInsertion` | Missing first-occurrence targets return None. No-op handling has a truth-changing countermodel. An unbounded invariant proves that the literal rules cannot generate two printed coordination examples. |
| Declared S4 surface amendment, not a printed source rule | `SurfaceAmendment`; `SurfaceAmendmentSafety` | Present attachment inflects coordinated IV heads without entering control complements. The literal policy is preserved for all trees. Only verb forms change; realization failure is preserved. S17 is unchanged. |
| IL types and constructors, p. 23 | `Syntax.ty`, `tm`; `Named.ntm`, `embed_named` | All declared forms; countably many constants and variables at every type. Named-to-intrinsic interpretation preservation proved. A general syntax alpha-round-trip is not claimed. |
| Denotation domains, p. 24 | `Models.domain` | Entity carrier, literal `bool` truth, full internal Coq function spaces, intensions over World x Time. |
| Interpretations, p. 24 | `Models.frame`, `model` | Inhabited carriers and a reflexive, transitive, antisymmetric, total time order. Constants have index-dependent values. |
| Clauses 1-10, pp. 24-25; note 10 | `Models.eval` | Independent structural recursion over IL. Equality and quantification use explicit Boolean reflection; connectives use Boolean operations. |
| Necessity and tense, clause 8; note 9 | `necessity_clause`, `future_clause`, `past_clause` | Necessity ranges over all world/time pairs. Tense preserves the world and uses strict comparison derived from linear time. |
| T1(b-e), p. 26 | `translate_be`, `translate_necessarily`, `translate_name`; pronoun case | Defined IL terms, not unexplained lexical parameters. Proper-name rigidity is not forced into constant evaluation. |
| T2, p. 26 | `translate_determiner` | Every, the and a/an quantify over individual concepts, with the source's uniqueness condition for the. |
| T3, p. 26; note 12, p. 33 | `FreshNames.editorial_relative`, `editorial_rule_uses_literal_replacement`, `editorial_intrinsic_relative_agree` | Exact least-even source index, including bound-occurrence freshness, literal renaming, and interpretation correspondence. The noun's pre-existing free pronouns remain free. |
| T4-T10, p. 26 | Seven distinct cases of `translate` | Typed functional application to the intension of the argument. |
| T11-T13, p. 27 | `translate` s11-s13 cases | Sentence/IV conjunction-disjunction and term disjunction, at their source types. |
| T14-T16, p. 27 | `translate` s14-s16 cases | Quantifying into sentences, common nouns and IVs; assignment update is explicit. |
| T17, p. 27 | `sign`, `translate` s17 case | All five tense/sign forms. |
| Interpretation induced by translation, p. 27 | `Meaning.denote`, `translation_interpretation` | Independent tree interpreter; equality with evaluated translation proved for every tree under related assignments. |
| Meaning postulates (1)-(9), p. 28 | `Postulates.mp1` through `mp9`; `PostulateFormulas.formula1` through `formula9` | All nine formula families, with universal closure of open formulas 2 and 9. `compiled_postulates_exact` proves satisfaction iff `admissible`, at every model, assignment and index. Not globally asserted axioms. |
| Logical truth/consequence, p. 28 | `logically_true`, `english_consequence`, `compiled_english_consequence` | Restricted to admissible models, all assignments and indices in the declared internal semantics. |
| First-order reductions, p. 29 | `Postulates` and `Reductions` | All first five examples reduced; ordinary determiners quantify over entities using noun rigidity. Lexical star extensions are definitions. IV/TV extensionality retains the lexical postulate and subclass restrictions. |
| Extensionality of be, p. 29; identity/predication, p. 30 | `be_extensional_without_postulates`, `identity_source_reduction`, `predication_source_reduction` | Be has equality as its relation without assuming lexical MP4. Identity and predication are consequences of the same translated be term. Ordinary predication uses MP2. |
| Seeking a unicorn, pp. 22 and 30 | `seeks_unicorn_dicto`, `seeks_unicorn_re`, `unicorn_readings_separated` | Two distinct analyses; an admissible model separates their truth values and contains no unicorns. Exhaustiveness over all trees for the surface sentence is not proved. |
| Temperature argument, pp. 30-31 | Three English trees; `temperature_countermodel`, `temperature_inference_invalid` | A supplied admissible model satisfies both translated premises and falsifies the translated conclusion. Not just hypothetical countermodel assumptions. |
| Seek/try paraphrase, p. 30 | `seeking_trying_dicto_equal`, `seeking_trying_re_equal` | Both corresponding analyses have equal truth values in admissible models, using MP9. |
| Section-4 example strings, pp. 29-32 | `Catalogue.catalogue`; `SurfaceInvariant.section4_generation_claim_refuted` | 18 strings matched by 24 analyses. Two further printed strings have no analysis under the literal rules, proved for all trees. The blanket generation claim is refuted, not pending a longer search. |
| Registered section-4 strings under the declared amendment | `amended_printed_examples_covered`, `amended_catalogue_source_formulas` | All 20 strings have witnesses; all 26 registered analyses have the existing IL formula certificates in every admissible model. This supplies coverage, not exhaustive reading classification. |
| Displayed section-4 IL readings | `ReadingForms.reading_pairs`, `all_listed_compiled_formulas` | All 26 listed candidate analysis/formula pairs checked. Starred vocabulary consists of defined IL terms. This includes formulas for the two canonical trees that fail to realize their printed strings. |
| Quantifier-scope pair, p. 31 | `Scope.surface_scope_source_reduction`, `inverse_scope_source_reduction`, `quantifier_readings_separated` | Both entity-level formulas and an admissible separating model are proved. |
| Nonreferential readings, pp. 30-31 | `five_nonreferential_witnesses` | Seek, try, about, wish with coordinated IV, and belief with pronouns are true without unicorns in a supplied admissible model; corresponding referential analyses are false. |
| Referential cases, p. 32 | `referential_analyses_have_witnesses` | Eight listed referential analyses require a unicorn witness, including three p. 32 candidates. This does not prove that every analysis of the printed string is referential. |
| A price rises, p. 31 | `price_concept_truth_condition` | The source concept-quantifying truth condition, with no ordinary-noun simplification imposed on price. The illustrative number vocabulary is not in the declared p. 19 lexicon. |

## Model and foundation choices

Coq is still the host. The object truth domain is `bool`, not `Prop`. The
model carries a `BooleanTruth` operation with the specification that a
reflected proposition returns true exactly when that proposition holds.
`reflection_requires_classical_truth` proves that this operation entails
excluded middle. `decision_truth` constructs it from the explicit
`ClassicalDecision` premise. This is not a terminating algorithm deciding
arbitrary propositions or higher-order validity.

Function extensionality is also an explicit model field. This supports the
usual equality of functions and the induction proof under binders. No
classical or extensionality axiom is installed globally. The compiled theorem
types retain these assumptions through their model arguments.

`sample_model` has two entities, one world and two linearly ordered times.
It supplies a complete typed interpretation of every numbered constant, not
just the words used in a single example. `sample_model_admissible` verifies
all nine postulate families. Its empty ordinary noun extensions are a valid
test model, not an empirical lexical claim. Its temperature concept varies
across times. Seek, try, wish, about and the attitude verbs are permissive in
this deliberately simple countermodel, while in retains MP8's extensional
condition. This gives the five nonreferential witnesses. No empirical lexical
plausibility is inferred. The construction needs the foundational inputs above.

Internal full function spaces are the declared representation of the
set-theoretic domains. No equivalence with an independently formalized
external set universe or with all Henkin models is claimed.

## Defects in earlier encodings, not limitations of Montague

The existing source audit `atlas_data/records/deep__PTQ_deep2.json` had
already identified the wrong IV/CN result type, fixed-time necessity and
unfinished English translation. Direct consultation now confirms them.
They are encoding errors or omissions, not evidence that PTQ cannot be
formalized without changing its analysis.

The checkpoint-7 legacy theorem remains valid: it preserves the old
evaluator, including those choices. It is therefore not a source-adequacy
certificate for PTQ. Similarly, the older proof calculus follows the later
C presentation, not a calculus extracted from PTQ. Neither old branch is
silently retagged as this reconstruction.

## Completion ledger

The current checkpoint contains 443 proved statements in 27 modules, with
49 negative fixtures. The exact editorial T3 procedure, all 26 original listed
analysis/formula correspondences and the quantifier-scope countermodel are
completed. All earlier compiler, model, postulate and countermodel results
remain checked.

The remaining blanket positive source-coverage claim is **refuted** under
the literal grammar. `printed_try_wish_has_no_analysis` and
`printed_wish_try_has_no_analysis` quantify over every candidate tree;
`section4_generation_claim_refuted` records the consequence for the whole
listed example-generation claim. This is not just absence of an implementation
or an incomplete finite search.

Consequently, a positive full-paper adequacy certificate for those unchanged
rules cannot be supplied. A separately named present-inflection amendment
is now implemented and proved to restore all 20 registered strings with their
26 analysis/formula certificates. General proofs show that it changes only
verb forms and preserves realization failure. The original policy and all
17 earlier Coq modules are unchanged. The current work does not certify
exhaustive readings under either policy. Independent source review remains
separate from kernel checking.
The illustrative noun number is still outside the printed basic lexicon.

The subsequent [reading audit](READING_CLASSIFICATION.md) refutes the original
two-candidate belief list under both surface policies. The revised registry
adds the external-conjunction reading and has 27 analysis/formula certificates;
all candidates within each sentence are pairwise inequivalent. Coq classifies
every one of 2,073 discovered trees into this registry in all admissible models.
`RenamingNormalization.v` now eliminates redundant bare-pronoun wrappers for
all successful trees while preserving both surface policies and all supplied
model interpretations. `SurfaceInverse.v` proves local F10 inversion and
freshening, including S3's separate binder. `SearchRank.v` proves the measure
well founded and the F10 inverse-body steps strictly decreasing. These are
implementation metatheorems, not additional claims attributed to Montague.
The complete parser/certificate coverage bridge remains unproved.
The unrestricted theorem connecting every successful grammar tree to that
finite set is still missing. This is not an exhaustive-reading certificate.

See `SOURCE_DISCREPANCY.md` for the all-tree proof, the no-op insertion
countermodel, the precise qualifications, and the difference between
reproduced source semantics and newly checked source-audit results.
See `SURFACE_AMENDMENT.md` for the implemented correction, its all-tree safety
proofs, and the distinction between registered coverage and all readings.
