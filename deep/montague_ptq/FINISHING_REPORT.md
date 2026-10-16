# Source-first PTQ: implementation and review handoff

10 October 2026. For Robin Cooper and Rasmus Blanck.

## Outcome

The source-first branch now contains 27 Coq modules and 443 proved statements.
Its checker compiles every module, rechecks their proof objects with `coqchk`,
audits all parsed definitions and theorems, and rejects 49 deliberately invalid
fixtures. The checkpoint is `verification.json`. There are no admitted proofs
or global axiom dependencies in this branch. The model nevertheless has
explicit, substantive classical and extensionality premises.

A [separately labelled present-inflection amendment](SURFACE_AMENDMENT.md)
now restores the two printed coordination strings and supplies coverage/formula certificates
for all 20 registered strings and 26 analyses. For every tree, the original
policy is proved equivalent to the literal implementation, and the amended
policy is proved to change only verb forms while preserving realization
failure. The compiler, semantics and all 17 earlier Coq modules are unchanged.

The subsequent [reading-classification audit](READING_CLASSIFICATION.md)
proves the original two-candidate belief entry incomplete and supplies a third
reading with conjunction outside belief. The revised registry has 27 certified
analysis/formula pairs. Within each sentence these candidates are pairwise
inequivalent. Coq has also classified all 2,073 inverse-search witnesses into
the revised registry in every admissible model. The unrestricted proof that
the search omits no different reading is still missing; this task is not
mathematically complete.

The blanket claim that all registered printed examples are generated remains
**refuted under the literal S4/S12 rules**, by an invariant over every analysis
tree. Two printed coordination strings have no analysis under that policy.
The original result and the amended coverage theorem concern different
specifications. See [the source-discrepancy proof](SOURCE_DISCREPANCY.md).

This does **not** certify full PTQ adequacy: that positive claim cannot hold
for the unchanged literal rules. Exhaustive reading classification is not
certified under either policy. A finite example catalogue is not an
unbounded reading-exhaustiveness theorem.

The primary source is Montague's 1973 PTQ paper, consulted in the reprint
with printed pages 17-34 and Thomason's editorial corrections. Page references,
the PDF hash and the definition-level correspondence are in `SOURCE_MAP.md`.
The implementation and this report are AI-assisted; they have not received
independent semantic-review approval.

## What is now connected

```text
English candidate analysis tree     Named IL expression
          | T1-T17                         | capture-safe conversion
          v                               v
              Intrinsically typed IL
                         |
                Boolean interpretation
                         |
             truth at a world/time index
```

There are three distinct correspondence results, not just agreement between
different names for the same evaluator:

1. `Meaning.translation_interpretation` relates the compiled tree to an
   independently recursive tree interpreter. It quantifies over every typed
   tree, model, context and related assignment.
2. `Named.named_interpretation` relates the named IL evaluator, which updates
   typed variable names, to the intrinsic evaluator, which uses de Bruijn
   variables. Local shadowing and different-type same-name cases are tested.
3. `FreshNames.editorial_intrinsic_relative_agree` connects the editor's
   exact least-even fresh-name T3 procedure to intrinsic binding. The search
   includes bound occurrences, and renaming is proved equal to literal
   replacement at a fresh name.

These theorems do not prove that a mistranscribed source definition is correct.
They establish the implementation correspondence once those independently
written definitions are accepted. Comparing both to the primary source is
therefore still an essential review task.

## Meaning postulates are formulas, not unexplained assumptions

`PostulateFormulas.v` contains all nine postulate families as named IL terms.
Open formulas 2 and 9 are universally closed. The lexical restrictions on
ordinary nouns, ordinary IVs and extensional versus intensional TVs are
retained; price and temperature are not silently treated like man and woman.
Curried relation arguments use subject-first coordinates consistently.

Each formula has a satisfaction lemma. The aggregate theorem is:

```coq
Theorem compiled_postulates_exact M sigma i :
  postulate_family
    (fun p => eval M (embed_named p) (empty_env M) sigma i = true)
  <-> admissible M.
```

Thus the model restrictions are neither a stronger unexplained surrogate
nor a weaker unchecked subset of the encoded formulas. The equivalence
holds at every assignment and index. `sample_model_admissible` separately
establishes that all nine conditions can hold together under the explicit
foundational inputs.

## Source claims reproduced

These are mechanized instances of Montague's analyses, not newly discovered
linguistic generalizations:

| Source claim | Checked implementation result |
| --- | --- |
| Ordinary extensional examples have the expected entity-level truth conditions, p. 29 | All first five examples reduced, using defined lexical star extensions and the necessary postulate restrictions. |
| Be covers identity and predication, p. 30 | `identity_source_reduction` and `predication_source_reduction` use the same translated term. |
| Extensionality of be need not be assumed separately, p. 29 | `be_extensional_without_postulates` supplies equality as its relation without an admissibility premise. |
| Seek is try to find under postulate 9, p. 30 | Both corresponding dicto and re analyses have equal truth values in admissible models. |
| Nonreferential readings need not imply unicorn existence, pp. 30-31 | Five explicitly listed dicto analyses are true in an admissible model with no unicorns; their re counterparts are false there. |
| The temperature argument is invalid, pp. 30-31 | An admissible model makes the two actual compiled premises true and the compiled conclusion false. |
| A price rises quantifies over individual concepts, p. 31 | Its compiled truth condition is proved without imposing ordinary-noun rigidity on price. |
| The two quantifier scopes have different truth conditions, p. 31 | Both object-language formulas are proved equivalent to their compiled analyses and separated in an admissible model. |
| The listed analysis/formula pairs have the stated meanings | `all_listed_compiled_formulas` checks all 26 pairs as actual IL terms. This does not assert that both p. 32 strings are generated. |

The five nonreferential cases are seek, try to find, talk about, wish to find
and eat, and believe that John finds and eats. The wish case quantifies into
a coordinated IV; the belief case uses sentence coordination and pronouns.
They are different analyses with different scopes, not renamed copies of
the seeking example.

`referential_analyses_have_witnesses` proves that eight listed referential
analyses require a unicorn witness. This includes the three canonical p. 32
candidates. It does not prove Montague's stronger assertion that these
printed sentences have only referential readings.

The sample model is deliberately simple: two entities, one world, two ordered
times, empty ordinary noun extensions, a varying temperature concept, and
permissive intensional predicates. It witnesses logical possibility under
the postulates, not a realistic lexical or psychological model. Boolean
reflection means it is not an executable higher-order truth decider.

## Surface realization and two source questions

`Surface.v` implements F0-F15 using typed tokens. This separates lexical
identity from inflected spelling. The tables include irregular forms, bare
versus object pronouns, gendered residual pronouns, and all five tense/sign
variants. Every noun in the declared basic lexicon takes the indefinite
article a, including unicorn. The code does not invent an extended lexicon.

`Catalogue.v` checks 18 section-4 surface strings against 24 candidate
analyses. It also checks the full relative-clause derivation on p. 21. Two
additional section-4 candidates are recorded separately because literal S4
does not produce their printed inflection.

### First-occurrence replacement

F10, p. 20, instructs us to replace the first indexed pronoun by the inserted
term and replace later occurrences by gendered pronouns. The rule's displayed
antecedent does not explicitly require that such an occurrence exist.

The implementation returns `None` when a non-bare-pronoun insertion has no
target. For example, inserting a unicorn at index 9 into Bill walks fails.
This makes an operational precondition explicit; it is a declared convention
requiring source review, not a theorem extracted from the displayed antecedent.
The bare-pronoun renaming case can legitimately leave an absent name unchanged.

A category-correct candidate tree may therefore have a translation but no
successful surface realization. Such a tree must not be advertised as a
reading of an English sentence. Treating failed insertion as a no-op would
need a separate semantic justification, since quantifying-in still changes
the interpreted term. `VacuousInsertion.v` now supplies that diagnostic:
an admissible model makes Bill walks true and an unused a unicorn insertion
false, although the no-op display would leave Bill walks unchanged.

### Coordinated inflection

S4 on p. 19 says to replace the **first verb** by its third-person singular
present. S12 on p. 20 concatenates two IVs with and/or. For the canonical
shared-subject analyses used here:

| Literal S4/S12 result | Printed p. 32 example |
| --- | --- |
| John tries to find a unicorn and wish to eat it | John tries to find a unicorn and wishes to eat it |
| John wishes to find a unicorn and try to eat it | John wishes to find a unicorn and tries to eat it |

Both mismatches are checked computations. `SurfaceInvariant.v` now proves
the stronger result: no analysis tree can produce either printed string
under the literal rules. The proof covers all S1-S17 constructors, including
quantifying-in and pronoun replacement, and transfers its token invariant
to rendered words. No unannounced inflection repair has been added.

`SurfaceAmendment.v` implements the repair separately. At S4 it inflects the
heads of coordinated IVs, passing through adverb modification and quantifying-in
but not into infinitival control complements. S17 tense/sign is unchanged.
`SurfaceAmendmentSafety.v` proves for all trees that lexical identity, token
order, pronoun indices and success/failure are preserved. Its guide explains
the positive registered-coverage theorem and its distinct quantifier scope.

The nearby illustration every price is a number uses number, which is absent
from the declared p. 19 lexicon. That illustration is not evidence that the
implementation forgot one of the listed lexical entries. Testing the entire
price/number argument requires an explicitly declared lexical extension.

## What Coq does and does not settle

Cooper's point is correct: a deep embedding does not leave Coq. What it does
is make object syntax and semantics explicit enough to quantify over terms,
assignments and models and prove metatheorems about them. The host and object
logics must not be conflated.

Here object truth values are `bool`. `BooleanTruth` reflects propositions
into those truth values, and `reflection_requires_classical_truth` proves
that this field entails excluded middle. `FunExt` supplies extensional
function equality. A constructive Coq kernel checks theorems conditional on
these explicit classical mathematical inputs. It does not force Montague's
object semantics to become intuitionistic, nor make those premises disappear.

The full function spaces are internal Coq function spaces. There is no theorem
here identifying all these models with an independently formalized external
set universe, all Henkin models, or the models of another semantic theory.
This branch reconstructs PTQ's syntax and model semantics. It does not invent
a proof calculus and attribute it to Montague, and does not establish Gallin,
MTT or TTR equivalence.

## Safeguards and reproducibility

Run from the repository root with Coq 8.20.1 and Python 3:

```sh
python3 deep/montague_ptq/check.py --check
```

No source PDF, network access, model key or AI service is needed to check the
proofs. The checker uses temporary copies, so normal verification does not
overwrite source files or the frozen earlier checkpoints. Intentional changes
require review and then `--record`; `--check` rejects checkpoint drift.

The 49 negative fixtures include wrong IV types, fixed-time necessity,
incorrect variable capture, hidden model assumptions, silent missing-target
substitution, incorrect coordinated inflection and unjustified extension of
referential/ordinary-noun results, finite control complements, duplicated
negation, conflation of amended and literal policies, mistaking coverage for
exhaustiveness, erasing the new belief scope, unsafe renaming, and extending
extensional-object lifting to seek. They supplement,
not replace, kernel checks
and human source review. No LLM or Jev response is used as proof evidence.

The final regression run also checked the two existing Montague branches,
without changing their mathematical sources or checkpoints:

| Check | Result |
| --- | --- |
| Source-first PTQ, isolated `--check` | 443 proved statements; 49 invalid fixtures rejected |
| Existing proof-theory core, isolated `--check` | 173 proved statements; 23 invalid fixtures rejected |
| Existing legacy companion, isolated `--check` | 76 proved statements; 14 invalid fixtures rejected |
| Verification-workflow unit tests | 24 passed |
| Reading-exploration unit tests | 11 passed |
| Isolated reading-certificate reproduction | 2,073 checked trees, 27 sentence-scoped classes |
| Tracked-diff whitespace check | Passed |

All three branch checkers completed their kernel rechecks. These totals are
verification results for the respective branches, not a count of independent
linguistic discoveries or a full-paper adequacy measure.

## Boundary after the additional proofs

The listed formula correspondences, the quantifier-scope separation and the
exact editorial T3 procedure are completed. The literal-rule generation
claim is refuted, not an outstanding theorem awaiting another proof attempt.

A positive coverage result for the registered examples is now proved for
the explicitly amended surface specification, with a source-formula certificate
for every registered analysis. This is not reading exhaustiveness. Classification
of every possible reading is not claimed by this checkpoint. Independent
source review remains necessary for publication;
machine checking does not manufacture reviewer approval.

The latest three modules discharge the redundant-renaming normalization
obligation for every successful grammar tree, with equivalence under both
surface policies and every supplied model. They also prove capture-safe
freshening for quantifying-in and relative clauses, soundness/completeness of
finite local F10 inverses, well-foundedness of the inverse-search measure, and
strict decrease of both F10 inverse-body operations. Genuine index merges are
retained rather than erased. The detailed statements, case distinctions and
capture regressions are in `READING_CLASSIFICATION.md`.

These results still need a whole-search coverage bridge connecting all grammar
branches and tokenization to the actual finite certificate. Neither a local
inverse theorem nor a terminating measure supplies that bridge on its own.

The old checkpoint-7 sources and distributed review documents remain unchanged.
This report and `REVIEW_ADDENDUM.md` supersede any implication that their old
preservation result certified the original PTQ specification. This work has
not been pushed, deployed, promoted in the atlas assessments, or emailed.
