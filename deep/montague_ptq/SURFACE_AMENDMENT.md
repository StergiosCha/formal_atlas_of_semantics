# PTQ surface amendment: coordinated present heads

10 October 2026. Implementation and proof guide for Robin Cooper and Rasmus
Blanck. This is a declared amendment, not a new linguistic generalization
or independent source-review approval.

## Outcome

The separately labelled `coordinated_present` policy generates all 20
registered section-4 strings with the 26 existing candidate analyses. Each
analysis retains its proved correspondence to an actual IL formula in every
admissible model. The compiler, models, meaning postulates and all 17 previously
recorded Coq modules are unchanged.

Two general safety results accompany the finite catalogue checks:

- Selecting `first_verb_only` reproduces the original realizer for every tree.
- The amendment differs only in verb-form fields for every tree. It preserves
  lexical identity, token order, pronoun indices, token count, and whether
  realization succeeds or fails.

The amendment-only checkpoint had 19 modules, 266 proved statements and 29
rejected negative fixtures. The later [reading audit](READING_CLASSIFICATION.md)
records the current 348-statement checkpoint and its remaining obligation.
No proof is admitted. The new surface proofs have no classical or
extensionality premises; semantic certificates retain the existing explicit
model premises.

## Two distinct specifications

| Specification | Registered strings with witnesses | Two printed control-coordination strings |
| --- | --- | --- |
| Literal `Surface.surface` | 18, with 24 analyses | No tree generates them, by the existing invariant proof |
| Amended `amended_surface` | 20, with 26 analyses | Both canonical trees now generate the printed strings |

The literal policy produces "John tries to find a unicorn and wish to eat it".
The amended policy produces "John tries to find a unicorn and wishes to eat it".
The literal refutation remains true: it concerns a different, explicitly
named rendering function. The amendment does not replace the source file.

## 1. A structurally scoped change

In `SurfaceAmendment.v`, a `surface_plan` stores two optional token sequences:

- `plain_tokens`: realization in the current syntactic category.
- `present_tokens`: realization when S4 requests present subject attachment.

For S12, present attachment requests present forms from both IV conjuncts.
The request also passes through S10 adverb modification and S16 quantifying-in
to the relevant IV. At a control verb it stops: the control head is inflected,
while its IV complement uses its plain realization. Compare:

```text
John tries to find a unicorn and wishes to eat it
John wishes to find a unicorn and eat it
```

The second must not become "wishes to find ... and eats ...".
`control_complement_stays_infinitival` covers an arbitrary IV complement;
the catalogue also checks both dicto and re analyses of this sentence.

S17 is unchanged. We do not distribute negation, future or perfect over
coordinated IVs: that could change scope and truth conditions.
`amendment_keeps_tense_sign` records the unchanged outer S17 operation for
every tense/sign constructor. F10 likewise retains its explicit failure
on a missing non-pronominal insertion target.

## 2. Proving the literal policy is unchanged

`first_policy_plan_exact` is a structural induction over all S1-S17 trees.
It proves equality of plain realization with `Surface.realize`, together
with equality of the present form with literal first-verb inflection.
Its rendered-word corollary is:

```coq
forall A (u : tree A),
  policy_surface first_verb_only u = surface u
```

This rules out an unnoticed change elsewhere in the duplicated recursive
renderer. It is stronger than checking the existing examples alone.

## 3. Proving that only inflection changes

In `SurfaceAmendmentSafety.v`, `erase_verb_form` replaces each verb token's
form by `infinitive`, retaining its lexical identity. Other tokens are
unchanged. `erase_result` applies this to successful results and preserves
`None`.

`all_tree_amendment_erasure` proves equality of the erased literal and amended
plans. It covers pronoun replacement, relative clauses, quantifying-in,
coordination and subject attachment. The existing IV-head invariant supplies
the fact that successful IVs have an inflectable verb. Two corollaries are:

```coq
forall A (u : tree A),
  erase_result (amended_tokens u) = erase_result (realize u)

forall A (u : tree A),
  amended_surface u = None <-> surface u = None
```

Thus the change neither deletes or inserts lexical material nor repairs
an invalid insertion. `amendment_preserves_token_identity` also states
equality of the erased token lists and their lengths explicitly. This is
a token-level result, not a claim that arbitrary inflection changes in
natural language preserve meaning.

## 4. Connecting repaired strings to the existing semantics

`amended_catalogue` adds the two printed strings and their canonical trees
to the existing catalogue. No translation rule is introduced.
`amended_registry_matches` checks that its 26 trees are exactly those in
`ReadingForms.reading_pairs`. `amended_catalogue_source_formulas` certifies
every registered analysis: it generates the registered string and has a
listed IL formula agreeing with its compiled translation in every admissible
model, at every assignment and index.

The combined theorem `amended_printed_examples_covered` says:

```text
For every registered printed string,
  there exist an analysis tree and a registered IL formula such that
    the amended realization is that string, and
    in every admissible model, at every assignment and index,
      the compiled tree and the formula have equal truth values.
```

This closes the missing surface link for the registered examples. Existing
semantic proofs are reused for the same trees, not replaced by an
interpretation tailored to the corrected words.

## 5. Completion boundary

Completed here: the explicit present-inflection amendment, literal-policy
equivalence, all-tree inflection-only and failure-preservation proofs, and
coverage/formula certificates for all 20 registered strings and 26 analyses.

Not claimed: that these are all possible readings of each string. Coverage
supplies witnesses; it does not universally classify every tree realizing
a string. The stronger source assertions about "only referential" readings
still need exhaustive classification. The illustrative noun number remains
outside the declared basic lexicon.

Review of the transcription, the F10 occurrence convention and this declared
surface amendment remains separate from kernel checking.

## Reproduce

From the repository root with Coq 8.20.1 and Python 3:

```sh
python3 deep/montague_ptq/check.py --check
```

The checker compiles temporary copies, rechecks proof objects, audits
assumptions, checks theorem signatures, rejects 38 negative fixtures and
checks the recorded hashes. No PDF, network, key or AI service is needed.
Negative fixtures reject finite control complements, distributed negation,
a missing-target no-op, conflating erasure with identical strings, and
dropping admissibility from the formula certificate.

See `FINISHING_REPORT.md` and `SOURCE_MAP.md` for the complete reconstruction;
see `SOURCE_DISCREPANCY.md` for the unchanged literal obstruction. This work
has not been pushed, deployed or emailed.
