# Bounded independent-review packages — prepared, not sent or approved

These packages ask for source/code review, not an endorsement of an entire
framework. No reviewer has been contacted or recorded as consenting. The
source-outcome registry remains empty. A bounded review need not satisfy the
separate whole-source outcome policy.

## TTR and its MTT comparison

- Source: Cooper 2023, supplementary registry entry cooper-2023; exact bytes,
  passages and provenance are in the registry. Do not substitute survey
  ID50, Cooper 2005. C&L 2020 is surveyed ID40.
- Primary audit: [TTR comparison](ttr_comparison.md).
- Code: [TTR_Model.v](../../atlas/ttr/TTR_Model.v) and
  [TTR_vs_MTT.v](../../atlas/ttr/TTR_vs_MTT.v), with TTR.v as a dependency.
- Questions: Does the explicit type/model/witness distinction represent the
  cited Cooper fragment? Does the meet counterexample test the right witness
  condition? Is the fixed-model inhabitation comparison correctly scoped?
  Is non-invertibility precisely about the subject projection?
- Required exclusions: general dependent type functions, varying Type_M domains,
  stratification and unrestricted framework equivalence.

## Heim 1982

- Source: ID7, Schoubye–Glick 2011 retypesetting; use its pagination.
- Reports: [core](../campaigns/heim_1982_results.md),
  [integration](../campaigns/heim_1982_integration_results.md) and
  [policies](../campaigns/heim_1982_policy_results.md).
- Questions: Are p.234's final universal rule and nuclear existential closure
  represented correctly? Is condition B distinguished correctly from full
  assignment support? Do pp.250–251 warrant the proposed distinction between
  possible-world and assignment preservation? Are local/global repair and the
  proxy policies separated from Heim's unresolved preferences?
- Required exclusions: raw-English parsing, complete movement derivations,
  a total felicity decision procedure and a default pragmatic policy.
- Fresh reproduction: run the check_heim_1982_policies.sh script in campaigns.

## DTS

- Source: ID38, Bekki–Mineshima 2017, not Bekki 2014 or the title suggested by
  the misleading PDF filename. Ranta's edition/date remains unresolved.
- Reports: [comparison](ttr_comparison.md) and
  [typed-resolution revision](revision_2026_09_13.md).
- Code: [DTS_Resolution.v](../../atlas/mtt_ranta/DTS_Resolution.v),
  DTS.v, MTT_vs_DTS.v and Shared_Examples.v.
- Questions: Does substitution preserve the intended typing judgments?
  Are soundness and projection-context completeness correctly bounded?
  Are CN predicates, Sigma re-encoding, context passage, ambiguity and
  nonexport distinguished correctly?
- Required exclusions: unrestricted proof search/completeness and general
  equivalence of DTS, Ranta, MTT or TTR.

## Review response

Record the exact repository commit, artifact hash/edition, passages, theorem
names, scope and exclusions; identify added assumptions or competing source
interpretations. State the reviewer's identity and relationship to the work,
what was checked, and unresolved objections. Mere agreement, a compilation log
or another assistant pass is not independent human review.

Submit through the [contribution workflow](../../CONTRIBUTING.md). Use the
[source-outcome policy](../OUTCOME_POLICY.md) only if coverage and independence
requirements for that stronger outcome have genuinely been met.
