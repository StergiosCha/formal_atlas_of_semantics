# Rosch bounded implementation — design before coding

2026-09-13. Continues the frozen second-cohort protocol and Rosch inventory.
This attempt is restricted to R2-03 and R2-04, with all eight inventory targets
retained for the result report. No source grades or inventory wording change.

## Scope and representation decisions

R2-03: use a finite list of observations and Boolean event/category predicates.
Repeated observations count as repeated frequency, not duplicate set members.
Counts are exact nonnegative rationals built from unit indicators; conditioning
is the intersection count divided by the cue count. The public optional value
is absent for a zero-count cue. Raw total division is internal algebra, with
positive-denominator premises explicit in meaningful probability theorems.
This is a finite empirical-frequency restriction, not general real probability.

Prove range and category-inclusion monotonicity for positive cues. Lift the
latter to the same finite list of cues and nonnegative weights, and rule out a
strict interior maximum against a containing category under those assumptions.
The source's unweighted sum is the unit-weight case; arbitrary weights extend
the mathematics and are not claimed as Rosch's definition. Keep the actual
category-specific choice of attributes external and explicit.

Construct a tiny, clearly synthetic furniture/chair/kitchen-chair dataset to
show both fixed-cue monotonicity and an interior maximum with assigned different
cue lists. The numeric counts and feature assignments are not published data.
Check zero-frequency versus defined-zero cues, negative weights, and nonnested
categories so the boundary's premises are not silently discarded.

Also express finite event probabilities by normalizing the same counts by
sample size; prove the resulting conditional ratio equals the direct frequency
ratio on nonempty samples and positive cues. This is a narrow representation
correspondence for the same data, not independent empirical/model validation.

R2-04: separate Boolean membership from a natural-number typicality score and
its induced weak ordering. Prove best-member invariance under preservation of
that ordering, and demonstrate ordinal rescaling on one finite example. Use
robin, sparrow, penguin and a nonbird as illustrative labels: membership and
qualitative ordering are supplied constraints, numerical scores and ties are
constructed, not measured source findings. Check unequal typicality among
members, tied maxima and that ranking alone does not determine membership.
No distances, unique centroid, classifier, processing or learning model.

## Interpretation and integration boundaries

Count/probability correspondence and ordinal-order invariance are limited
encoding checks; independent semantic review remains pending. No success
percentage, efficiency comparison or causal tier result follows. R2-01, R2-02,
R2-05–08 remain uncovered except where the report identifies a narrower
representation or qualification; do not count code comments as coverage.

Fresh compilation, every-declaration assumption checks, kernel checking and
triviality/vacuity probes are required. Preserve probe flags and distinguish
definition/computation checks from substantive conditional lemmas. If integrated
into the atlas, use pilot/F3 and whole-source unassessed, never an as-is verdict.

Keep historical protocol, inventory, index and manifests unchanged. Extending
the project list and generated reporting necessarily supersedes those shared
aggregate hashes in a new result manifest; it does not rewrite the earlier
checkpoint. No commit, push, external mirror sync or deployment is requested.
