# PTQ reading classification: checked results and the remaining obligation

10 October 2026. Technical update for Robin Cooper and Rasmus Blanck.

## Result and status

The original two-candidate belief entry is provably incomplete. Both surface
policies generate a third reading, and admissible models separate all three.
The revised registry contains 27 sentence-scoped readings for 20 strings.
Every registered reading has a surface certificate and an actual IL formula
with an all-admissible-model interpretation theorem. Within each sentence,
the registered readings are pairwise inequivalent.

An inverse search found 2,073 derivation trees. Coq checked every generated
surface and classified every discovered tree into the revised registry,
using equalities valid in all admissible models, not agreement in a test model.
The generated proof objects were independently rechecked with `coqchk`.

The latest update proves redundant-renaming normalization for all successful
trees, capture-safe binder freshening, local F10 inversion and inverse-body
rank decrease. The checkpoint now has 443 proved statements in 27 modules.

**The requested unrestricted exhaustiveness result is not finished.** There
is not yet a Coq theorem that the inverse search covers every successful tree
of the grammar up to meaning. Accordingly, neither the report nor the
checkpoint claims that the 27 entries exhaust the grammar's readings. This
is a missing proof, not an established counterexample to the revised list.

## What exhaustive means

`ReadingClassification.v` defines the required property explicitly:

```coq
Definition reading_equivalent (u v : tree ct) :=
  forall M, admissible M -> forall sigma i,
    eval M (translate_closed u) (empty_env M) sigma i =
    eval M (translate_closed v) (empty_env M) sigma i.

Definition reading_exhaustive render (text : list string)
  (candidates : list (tree ct)) :=
  forall u : tree ct, render u = Some text ->
    exists v, In v candidates /\ reading_equivalent u v.
```

The first quantifier in the second definition ranges over every tree, with
no depth bound. The model quantifier ranges over every admissible model,
not just the supplied examples. Equality is for all assignments and indices.
The list of candidates does not restrict the quantified input tree.

Existence of an analysis for each sentence, correctness of listed formulas,
pairwise distinctness, and exhaustiveness are four different obligations.
The first three are now checked for the revised registry. The fourth remains.

## The third belief reading

Sentence: Mary believes that John finds a unicorn and he eats it.

The earlier candidates place both finding and eating within Mary's belief.
But S11 permits sentence conjunction outside the attitude clause as well.
The actual added tree, `belief_external_conjunction`, is:

```coq
s14 some_unicorn 0
  (s14 (s1_name john) 1
    (s11 conjunction
      (s4 (s1_name mary)
        (s7 (s1_word (latt believe_that))
          (s4 (s1_pronoun 1)
            (s5 (s1_word (ltv find)) (s1_pronoun 0)))))
      (s4 (s1_pronoun 1)
        (s5 (s1_word (ltv eat)) (s1_pronoun 0)))))
```

The outer unicorn insertion links the object pronouns. The John insertion
links the two subject pronouns. The sentence conjunction joins Mary's belief
clause to an assertion that John eats the unicorn. No parser-only notation or
new grammar constructor was introduced.

Suppressing intensional type annotations, the three scopes are:

| Registered reading | Scope schematic |
| --- | --- |
| Belief dicto | Mary believes [there is a unicorn that John finds and eats]. |
| Belief re | There is a unicorn such that Mary believes [John finds and eats it]. |
| External conjunction | There is a unicorn such that [Mary believes John finds it] and [John eats it]. |

`rf_belief_external` gives the third reading as an actual named IL term.
`additional_belief_compiled_formula` proves its equality with the translated
tree in every admissible model. `additional_belief_reading_is_generated`
checks the printed string under both literal and amended realization.

The new separating model has unicorn witnesses, permissive belief, and false
ordinary finding/eating relations. It satisfies all nine meaning-postulate
families. Both old belief readings are true there; the new reading is false
because actual eating is false. The earlier no-unicorn model separately
distinguishes the old dicto and re readings.

Therefore `registered_belief_pair_not_exhaustive` refutes the old list under
both surface policies. `original_amended_registry_not_exhaustive` lifts this
to the old whole registry. `three_belief_readings_pairwise_distinct` proves
the three candidates are genuinely different meanings.

This corrects the project's candidate list. It does not establish that
Montague claimed exactly two readings of this string, and it is not presented
as a newly discovered linguistic ambiguity. Source-fidelity review is separate.

## The finite search and its checked classifications

`explore_readings.py` proposes inverse applications of S1-S17 over typed tokens.
It distinguishes subject/object pronouns, infinitival versus present heads,
both surface policies, quantifying-in, and nontrivial index-class merges.
It has no language-model dependency. A witness cap raises an error instead
of silently truncating the set.

`check_reading_exploration.py` independently emits actual Coq trees. For every
tree it proves the surface equality and equality of its real `Meaning.denote`
interpretation with its proposed group representative. It then proves each
representative equal to a registered candidate in every admissible model and
checks that this candidate belongs to the corresponding registry entry.
Python grouping is only a proposal: Coq must accept the resulting proofs.

There are 30 computational groups. Three further identifications under the
postulates reduce these to 27 registered, sentence-scoped classes. In
particular, `ReadingNormalization.extensional_object_lifting` derives
quantifier lifting from the extensional-TV postulate. Its premise excludes
seek. It does not rewrite belief, try or wish as extensional predicates.

The following counts describe the discovered set, not all grammar trees:

| Sentence | Checked trees | Registered classes reached |
| --- | ---: | ---: |
| Bill walks | 2 | 1 |
| A man walks | 2 | 1 |
| Every man walks | 2 | 1 |
| The man walks | 2 | 1 |
| John finds a unicorn | 7 | 1 |
| John seeks a unicorn | 7 | 2 |
| John tries to find a unicorn | 9 | 2 |
| John talks about a unicorn | 7 | 2 |
| Bill is Mary | 7 | 1 |
| Bill is a man | 7 | 1 |
| The temperature is ninety | 7 | 1 |
| The temperature rises | 2 | 1 |
| Ninety rises | 2 | 1 |
| A price rises | 2 | 1 |
| A woman loves every man | 7 | 2 |
| John wishes to find a unicorn and eat it | 39 | 2 |
| Mary believes that John finds a unicorn and he eats it | 1,842 | 3 |
| John seeks a unicorn and Mary seeks it | 74 | 1 |
| John tries to find a unicorn and wishes to eat it | 23 | 1 |
| John wishes to find a unicorn and tries to eat it | 23 | 1 |
| Total | 2,073 | 27 |

These counts use the explicitly amended surface policy. The last two
strings remain impossible under the literal policy by the earlier all-tree
invariant, not merely because a search returned zero. Across different
sentences, some readings can be equivalent, including the existing seek/try
paraphrase. The total 27 is not a claim of 27 globally inequivalent meanings.

## Why an unbounded proof needs more than enumeration

Bare-pronoun quantifying-in can leave a closed surface unchanged. Repeating
such a wrapper arbitrarily often yields arbitrarily long derivations with
the same words and meaning. A fixed tree-depth cutoff therefore cannot
justify the required universal theorem.

`PronounSupport.v` supplies structural proofs over all grammar trees:

1. `support` records a sufficient finite set of semantic pronoun dependencies.
   Unused bare-pronoun arguments are handled specially, rather than counted
   as genuine dependencies.
2. `support_is_visible` and `amended_support_is_visible` prove that these
   dependencies occur as indexed pronouns in successful output tokens.
3. `interpretation_depends_on_support` proves agreement on this support is
   sufficient for equal denotations. This holds in any supplied model.
4. Closed successfully realized strings are assignment-independent. Adding
   any number of unused bare-pronoun renamings preserves their literal surface
   and interpretation (`arbitrarily_many_neutral_renamings`).

`GrammarRenaming.v` also proves capture-safe injective renaming for all S1-S17
trees. `rename_tree_interpretation` relates denotation to the pulled-back
assignment. `rename_tree_surface` and `rename_tree_plan` prove commutation
with token realization under both policies. Injectivity is explicit: arbitrary
non-injective renaming can collapse binding distinctions and is not licensed
by these theorems.

### Redundant renaming normalization is now proved

`RenamingNormalization.v` supplies a structural normalizer over every S1-S17
tree. At a bare-pronoun S14/S15/S16 node with binding index `n` and argument
index `k`, it distinguishes four cases:

| Case | Operation | Justification |
| --- | --- | --- |
| `n = k` | Remove the wrapper | The assignment update is the identity. |
| `n` absent from the body's visible indices | Remove the wrapper | Visible support proves the update cannot affect the body's meaning. |
| `k` absent from the body's visible indices | Replace the wrapper by a capture-safe swap of `n` and `k` throughout the body tree | Injective renaming also changes internal binder names, preventing capture. |
| `n <> k`, both indices present | Retain the wrapper | This genuinely merges two index classes and can change meaning. |

`tree_equivalent` requires equality of both surface-plan components under
both policies and equality of denotation in every supplied model, assignment
and world/time index. It is stronger than the catalogue's reading equivalence.
No admissibility assumption is needed for this normalization theorem; model
foundations remain explicit in the model record.

`normalize_renamings_equivalent` proves equivalence for every tree, including
unsuccessful ones. `every_successful_tree_has_merge_normal_form` additionally
proves that every successfully realized tree has a no-larger equivalent tree
whose bare binders are all genuine merges. The normalizer traverses the
entire grammar, not just outer wrappers. Its result is idempotent for successful
inputs. This discharges the redundant-wrapper obligation without a depth bound.

The capture regression is concrete: removing an outer `0 -> 1` relabelling
above an internal binder named `1` swaps that internal binder to `0`. Simply
changing the free pronoun leaf would capture it. A separate example checks
that a genuine merge is retained.

### Local inverse operations and their measure are now proved

`SurfaceInverse.v` defines finite inverse operations on typed tokens:

- `restore_pronouns` enumerates which later gendered pronouns came from a
  coindexed occurrence. Replacement has both completeness and fresh-output
  soundness proofs.
- `insertion_inverses` enumerates all prefix, NP-span and suffix splits, both
  cases of the replaced first occurrence, and the possible later occurrences.
  Every successful nonbare F10 insertion appears in this list. Every listed
  candidate with a nonbare argument and fresh output index reproduces the output.
- `merge_inverses` splits occurrences of a visible index, keeping precisely
  nonempty, proper splits. Every genuine merge is covered; fresh-index
  candidates reproduce their output. Empty splits and whole-class relabellings
  are explicitly excluded.
- `canonical_binding_index` proves that choosing one plus the largest visible
  output index, or zero for no indices, preserves the binding's meaning and
  both rendering policies. `freshen_relative_equivalent` and
  `canonical_relative_index` handle S3 separately, leaving the noun's free
  indices untouched.

`SearchRank.v` formalizes the search's lexicographic triple:

```text
(token count, non-pronoun token count,
 indexed occurrence count minus distinct-index count)
```

`inverse_rank_well_founded` proves that this measure admits no infinite
strict descent. `nonbare_np_body_rank` proves decrease for the inverse body
of every successful nonbare NP insertion. `canonical_merge_inverse_rank`
proves decrease for every canonical genuine merge candidate: token count and
non-pronoun count stay fixed, while splitting one class increases the number
of distinct indices by one. These are general theorems, not tests of a finite
collection of runs.

These finite Coq operations have not yet been connected to a verified complete
parser or a closed search-chart certificate. In particular, local inversion
does not by itself certify Python's category filters, all other S1-S17 inverse
branches, mode propagation, or word tokenization.

## Precisely what remains

The remaining mathematical obligation is the whole-search coverage bridge:
any successful tree realizing a registered string must have an equivalent
representative in the finite discovered set. Redundant-wrapper normalization,
binder freshening, local F10 inverses and their body-rank decrease are now
proved. They must still be composed with coverage of every other grammar
branch, mode propagation and tokenization/morphology, then connected to the
actual finite certificate. A well-founded measure does not prove that a search
has included every branch.

Once that bridge is proved, the already checked finite classification and
pairwise-inequivalence theorem supply the requested exhaustive classification.
It would also establish the appropriately scoped only-referential results
where every resulting class requires a unicorn witness. Such unrestricted
only-referential claims are not promoted on the present evidence.

This finish line does not require Gallin equivalence, Henkin completeness,
equivalence with TTR/MTT, or an external set-theoretic adequacy theorem. It does
require the unbounded bridge. Independent source review remains a publication
safeguard after the mathematical work, not something Coq can manufacture.

## Reproduce

From the repository root, using Coq 8.20.1 and Python 3:

```sh
python3 deep/montague_ptq/check.py --check
python3 -m unittest discover -s deep/montague_ptq -p 'test_*.py'
python3 deep/montague_ptq/check_reading_exploration.py \
  --check-report deep/montague_ptq/reading_exploration.json
```

The main checkpoint has 27 modules, 443 proved statements and 49 rejected
negative fixtures. `reading_exploration.json` separately records every group,
representative tree, canonical target, generated Coq-file hash and input hash.
Its completeness flags remain false. The full certificate check builds in
temporary directories and does not use the development cache. CI requires
both checks and does not rerecord their outputs automatically.

No source PDF, network access, API key, LLM response or Jev judgment is needed
to reproduce these results. Development and documentation are AI-assisted;
the artifact does not claim independent human source-review approval.
