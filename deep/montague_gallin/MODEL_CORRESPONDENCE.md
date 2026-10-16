# Checkpoint 2: independent models and what the correspondence proves

## Result

Admissible PTQ consequence agrees with consequence in the independently
specified target model class below. Satisfiability also agrees. The
translation is the existing checkpoint-1 translation, not a new formula
mapping chosen to make the model theorem easy.

The two central results are:

```coq
admissible_consequence_correspondence ps q :
  admissible_target_consequence ps q <->
  source_consequence admissible ps q.

admissible_satisfiability_correspondence ps :
  source_satisfiable ps <-> target_satisfiable ps.
```

Here the target consequence relation quantifies over all independently
chosen target valuations satisfying the declared conditions. It is not
defined by quantifying only over images of source models. Recovering a
source model for every such target valuation is part of the proof.

## 1. Make the target independent

`Types.value_domain E I a` interprets target types with arbitrary types E
and I for entities and indices. Truth values are Boolean and arrow types
are full internal function spaces. Neither a PTQ model nor its evaluator
is an argument.

`Target.geval` is generalized to these carriers. Its syntax and evaluation
clauses are unchanged; the original preservation theorem and all its
regression examples still compile. `genv`, `gextend`, `gempty` and
`gdomain` remain compatibility names for the world-time specialization.

`Independent.standard_model` supplies inhabited E and I, Boolean
reflection, function extensionality and arbitrary values for its typed
constant signature. Free-variable assignments are separate. This record
can describe standard target models with no temporal structure at all.

This is still a formalization *inside* Rocq. Full internal function spaces
do not establish equality with all external set-theoretic models. Nor do
they provide the restricted function domains of Henkin models.

## 2. State which standard models can interpret tensed PTQ

PTQ includes `Will` and `Has`. Their translations use the designated
target constants `FutureRelation` and `PastRelation`. General Ty2 permits
arbitrary interpretations of those constants. PTQ does not.

The correspondence therefore uses `coherent_model F`, where F supplies
inhabited entity, world and time carriers and the existing linear-time
structure. Its constant valuation is independently chosen. Two laws are
required:

```text
Future(i,j) is true iff world(i) = world(j) and time(i) < time(j).
Past(i,j)   is true iff world(i) = world(j) and time(j) < time(i).
```

There is no source model in this record. It does not contain a field
asserting that a translation is faithful or that a reconstruction works.
`as_standard` embeds any coherent model into the general standard-model
record, and the interpretations agree by computation.

The frame is a declared world-time presentation. The present theorem does
not transport along an arbitrary isomorphism from a separately chosen
index type to such a product. This restriction is explicit, not hidden in
the meaning of "all models".

## 3. Construct the two directions

`embed_model M` takes a PTQ model and interprets each target constant of
type `s -> translate_type a` by the source constant's index-dependent
value. The temporal symbols receive their PTQ interpretations. Their
coherence laws follow from Boolean reflection.

`reconstruct_model N` starts with an arbitrary coherent target valuation.
For each source type a, constant number n and index i, its source constant
is obtained by applying the target indexed constant at i and transporting
the value back to the source type. Free-variable assignments are recovered
in the same way. The value transports were already proved inverse in
checkpoint 1.

No choice of arbitrary domain elements is needed for reconstruction.
The existing symbol values supply exactly the typed values required.

## 4. Check recovery, not record identity

The following are proved:

| Result | Guarantee |
|---|---|
| `target_symbols_recovered` | Reconstructing and embedding recovers every typed target constant value. |
| `target_free_values_recovered` | Every target free-variable value is recovered. |
| `source_constant_values_recovered` | The corresponding source round trip preserves constant values at every index. |
| `source_free_values_recovered` | Source assignment values are recovered. |
| `target_roundtrip_interpretation` | The target round trip preserves every target term in the signature and every environment, not just translated expressions. |
| `backward_preservation` | Evaluation in an independently chosen coherent target agrees with its reconstructed source model. |
| `forward_preservation` | Evaluation in an embedded source model agrees with the original PTQ evaluation. |

These are semantic recovery theorems. They do not assert that two records
with possibly different proof fields are equal, and they do not construct
a reverse translation from arbitrary target expressions to PTQ syntax.

## 5. Put the meaning postulates on the target side

The source development already encodes all nine PTQ meaning-postulate
families as formulas and proves that their satisfaction characterizes
`admissible M`. That source result is imported unchanged and hash-pinned.

`target_postulates_at` translates these formulas into target syntax and
evaluates them in the independently chosen target model.
`target_admissible` requires them at every assignment and index.

`translated_postulates_exact` and `admissible_model_correspondence` prove
that this independently stated target condition is equivalent to
admissibility of the reconstructed source model. It is not merely defined
as source admissibility. Conversely, `embed_preserves_admissibility`
proves that admissible source models satisfy the translated conditions.

To rule out a vacuous universal condition, the proof constructs a target
assignment from existing typed constants at an inhabited index. No global
choice axiom is silently installed. A separate example constructs an
admissible target model under the explicit BooleanTruth and FunExt inputs.

## 6. Obtain consequence and satisfiability

If an admissible PTQ consequence holds, take any admissible coherent
target model. Reconstruct an admissible source model, transfer the
premises, apply the source consequence and transfer the conclusion back.

For the converse, embed any admissible PTQ model in the target class and
apply the target consequence. The same constructions transport satisfying
models in both directions. All models, assignments and evaluation indices
in these statements are universally or existentially quantified as stated,
not a finite collection of test cases.

The consequence and satisfiability APIs use finite lists of premises.
They quantify over arbitrary formulas in those lists; the model and
assignment classes are not bounded or enumerated.

The admissible temperature countermodel is retained, and
`target_temperature_inference_invalid` proves the non-entailment in the
new independently specified target class. This transports a known source
example; it is not a new linguistic discovery.

## 7. Show why the temporal boundary matters

`reflexive_future_model` is a well-formed standard target model on one
index with a reflexive future relation. Its interpretation of the
translated sentence `Will (Eq (Con 0) (Con 0))` is true. The corresponding
one-moment PTQ model makes that formula false because there is no strictly
later time.

`missing_temporal_coherence_changes_prediction` checks both values.
`coherent_future_is_irreflexive` and the associated separation theorem show
that this unrestricted target valuation cannot be a coherent one.

The issue is a mismatch in stipulated temporal structure, not a claim
that Gallin's theory makes a linguistic mistake.

## Assumptions and remaining boundaries

Boolean reflection and function extensionality are explicit fields of
both model records. The kernel audit checks for undeclared global axioms;
it does not erase these fields or certify source fidelity.

This is a tensed, temporally restricted analogue of the standard-model
comparison motivating Gallin's section 8. It is not a reconstruction of
all of Theorem 8.2, of the Ty2 axiomatic calculus, of the description
principles D, or of Henkin completeness. Extra connective constructors
also remain in the target syntax. These are distinct next milestones,
not missing cases of the correspondence proved at this checkpoint.
