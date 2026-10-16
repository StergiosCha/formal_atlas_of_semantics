# A checked obstacle to unchanged PTQ example coverage

10 October 2026. This is an implementation/source audit result, not a new
linguistic claim attributed to Montague and not independent reviewer approval.

## Result

Under the literal S4/S12 surface rules implemented from PTQ, **no analysis
tree generates either of the following printed p. 32 examples**:

- John tries to find a unicorn and wishes to eat it.
- John wishes to find a unicorn and tries to eat it.

This is proved in Coq for every tree, without a depth bound or a finite
enumeration assumption. It is stronger than the earlier observation that
two particular canonical trees had different outputs.

The source was checked against rendered pp. 19 and 32 of the reprint whose
hash is in `SOURCE_MAP.md`. S4 inflects the **first verb**. S12 concatenates
two IVs with a coordinator. Literal application gives wish/try, not the
second finite wishes/tries, for the canonical analyses.

The precise qualification is essential: the result is about the formalized
literal surface rules and must be reviewed against the source. It is not a
claim that Montague's model-theoretic semantics is inconsistent or cannot
be formalized.

A separately labelled amendment has since been implemented and proved to
restore the registered examples. The literal result below is unchanged.
See [the amendment and its safety proofs](SURFACE_AMENDMENT.md).

## Why the proof covers all trees

`SurfaceInvariant.v` proves the following chain:

1. `realized_sequence_invariant` is by induction on the full `Grammar.tree`
   datatype. It covers every S1-S17 family, including pronoun renaming,
   quantifying-in, relative clauses, conjunction and tense/sign.
2. Every realized token sequence has a nonfinite initial token, a valid
   coordinator/finite-verb scan, and an ending that is not a coordinator.
   An IV starts with an infinitive verb before subject attachment.
3. `insert_flags` proves that first-occurrence substitution by a valid NP
   preserves the scan. It replaces later indexed pronouns by gendered
   pronouns without introducing a hidden finite verb after a coordinator.
4. `realized_tokens_allowed` restricts literal tokens to the actual lexicon
   and operation vocabulary. This prevents an arbitrary literal token from
   smuggling in a word such as wishes.
5. `allowed_fragment` and `rendered_scan` transfer the token invariant to
   the displayed words, including all lexical and inflected verb forms.
6. Both printed strings fail that word-level scan at and wishes / and tries.

The final theorems are:

```coq
Theorem printed_try_wish_has_no_analysis :
  forall u : tree ct, surface u <> Some printed_try_wish.

Theorem printed_wish_try_has_no_analysis :
  forall u : tree ct, surface u <> Some printed_wish_try.

Theorem section4_generation_claim_refuted :
  ~ section4_generation_claim.
```

`section4_generation_claim` says that every sentence in the section-4
catalogue, including these two examples, has an analysis. Its refutation
therefore blocks a positive "all printed examples are generated" theorem.
The proofs are syntactic and do not need BooleanTruth, classical decision
or function extensionality as premises.

## The semantic formulas are not the failing part

`ReadingForms.v` supplies actual IL terms for all 26 listed candidate
analyses. Its starred lexical expressions are IL lambda terms, not new
uninterpreted constants. `all_listed_compiled_formulas` proves their
agreement with the corresponding compiled trees in every admissible model.
The registry is checked against the 24 analyses in the surface catalogue
plus the two canonical coordination analyses.

For those final two cases, the tree/formula correspondence is true, while
the claim that the tree realizes the printed words is false. These facts
must not be collapsed into a single successful example badge.

The two quantifier scopes of a woman loves every man are also reduced to
their source formulas and separated by `Scope.scope_model`, which satisfies
all nine postulate families. The exact editorial T3 fresh-name procedure
is connected to intrinsic binding by `editorial_intrinsic_relative_agree`.
The search uses the least even source index m; since x_m abbreviates raw
variable u_(2m,ic), candidate raw names are 4k. Bound occurrences are checked,
and the swap implementation is proved equal to literal replacement when
the selected name is fresh.

## A second necessary clarification: absent occurrences

The displayed F10 antecedent does not explicitly say that the indexed
pronoun occurs. `Surface.v` treats replacement of a nonexistent first
occurrence as failure. `VacuousInsertion.v` checks the alternative no-op
interpretation rather than assuming it harmless:

- In its admissible model, Bill walks is true and there are no unicorns.
- Quantifying an unused a unicorn into that tree gives a false translation.
- Displaying the failed replacement as unchanged Bill walks would therefore
  attach a different truth condition to the same words.

`vacuous_insertion_changes_truth` is the actual countermodel theorem. The
default implementation does not adopt this no-op behavior. Its explicit
occurrence precondition should be recorded as a specification clarification.

## The explicitly amended specification

`SurfaceAmendment.v` now implements present inflection of each coordinated
IV head under S4, leaving infinitival complements and S17 tense/sign alone.
This is a declared change to the printed operation, not an alternative proof
of the unchanged operation. It has not been installed as Montague's original
rule. All 20 registered strings now have witnesses with all 26 existing
analysis/formula certificates under this separately named policy.

`SurfaceAmendmentSafety.v` proves for every tree that only verb forms change,
and realization failure, lexical identity and token order are preserved.
The literal policy is also proved identical to the original realizer.

These results do not certify that the registered strings have no additional
readings. A finite coverage certificate is distinct from exhaustive reading
classification. See `SURFACE_AMENDMENT.md` for the exact theorem statements.

## Reproduce

With Coq 8.20.1 and Python 3, from the repository root:

```sh
python3 deep/montague_ptq/check.py --check
```

The current checkpoint has 24 modules, 348 proved statements and 38 rejected
negative fixtures. It includes kernel rechecking, declaration-level assumption audits,
general theorem-signature checks, and source hashes. There are no admitted
proofs. No source PDF, network access or model key is required to check it.

The previous frozen core/legacy checkpoints are unchanged. No atlas outcome
was promoted, no push or deployment was performed, and no reviewer email or
endorsement is claimed.
