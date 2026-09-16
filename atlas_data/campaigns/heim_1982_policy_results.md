# Heim: what the accommodation policies add

2026-09-15. Step 2 compares explicit policy completions on the same inputs.
**33 new proved statements** establish different truth, accessibility and
permission consequences. No candidate is adopted as Heim's default or as a
complete theory of conversational appropriateness. This is evidence about what
additional choices do, not an accepted whole-source transfer verdict.

Implementation: [Heim1982_Policies.v](../../atlas/dynamic/Heim1982_Policies.v).
The [fixed design](heim_1982_policy_design.md) and
[machine-readable comparisons](heim_1982_policy_results.json) record exact
theorem support. The previous seven modules and their proof/assessment records
remain unchanged.

## Local versus global: more than a truth-value difference

Heim pp.244–246 gives two places to apply accommodation when evaluating a
negation. For an input file F, fresh index i, descriptive predicate P and positive
predicate Q, the checked assignment-level consequences are:

- Local: F(w,g) and **no x satisfies both P(w,x) and Q(w,x)**. The original file
  domain is retained.
- Global: F(w,g), **P(w,g(i)) and not Q(w,g(i))**. The accommodated index remains
  in the resulting domain.

The general local theorem uses the source's condition B and freshness; the
general global assignment theorem does not require those extra premises. Both
world-projection theorems use B and freshness. The selector operates on a
declared fresh-description repair request, not every utterance. No-repair then
blocks because the definite index is absent, even if the description happens
to be true somewhere in the world.

| Same input, initially fresh king index | No repair | Local repair | Global repair |
| --- | --- | --- | --- |
| No king exists | Blocked | True resulting file | False resulting file |
| A king exists; Mary had lunch with no king | Blocked | True; following use of that index unlicensed | True; following use of that index licensed |

Thus a comparison that only checks truth values misses a dynamic consequence:
two true results may provide different subsequent anaphoric possibilities.
`local_global_domain_difference` proves the general domain distinction;
`existing_king_same_truth_different_next_pronoun` checks the second row.

`selected_local_is_a_valid_run` and `selected_global_is_a_valid_run` certify the
chosen paths using the existing accommodation `Run` relation. The selector has
a unique output for a chosen site; this is not a uniqueness or completeness
theorem for every possible unrestricted accommodation search. The source's
tentative global preference at p.246 is not elevated to an unconditional rule.

## Proxy permission: distinct preservation requirements

Four candidate policies are explicit:

| Policy | Additional requirement beyond the runner's recorded precedent and fresh, distinct index |
| --- | --- |
| Deny | No proxy repair is permitted. |
| Bridge-only | The repair is the stated descriptive introduction. This is a deliberately permissive structural bound. |
| World-safe | Bridge-only, and each input-compatible world already contains a witness of the description. |
| Assignment-safe | Bridge-only, and every previously satisfying assignment remains satisfying. |

Assignment-safe implies world-safe, which implies bridge-only. Inclusion of
permissions is proved to preserve complete runs. The two latter inclusions are
strict, established through allowed and blocked complete programs, not merely
by inspecting policy names. Assignment-safe is not an empty policy: it permits
the test whose description is true of every individual.

Under condition B and freshness, `world_safe_characterizes_world_preservation`
proves that world-safe is **equivalent** to preserving possible-world content
for the given descriptive bridge. This is more precise than saying it is just
a plausible restriction. Assignment-safe preserves the full satisfying
assignment set instead, which is a stronger requirement.

The comparison uses the previous compiled-modal → proxy → ordinary-assertion
program with the same keep-all attention fixture. Referent description and
syntax are held fixed within each row.

| Same program and model | Bridge-only | World-safe | Assignment-safe |
| --- | --- | --- | --- |
| Witness exists only in desire worlds, not the actual world | Run allowed; actual world removed | Complete program blocked | Blocked by policy inclusion |
| Witness already existentially guaranteed, but not every individual fits | Allowed | Complete program allowed | Complete program blocked |
| Description true of every individual | Allowed | Allowed | Complete program allowed |

Deny blocks all three programs. Allowed entries inherited through inclusion
are distinguished from the direct run theorems in the JSON ledger.

The factive result is general: reflexive accessibility makes the modal assertion
support an actual witness, so world-safe permits the source-linked program.
The nonfactive result uses an explicit two-world countermodel. Rejection is
proved for every final state of the relevant program, not merely failure to
find one execution.

The second row sharpens the pp.250–251 clarification from the earlier review:
knowing that a suitable object exists does not make every assignment of a fresh
index point to such an object. Literal assignment preservation can therefore
reject an informationally redundant introduction. This is not an inability of
Coq to express comprehension; it is a substantive difference between candidate
requirements.

## Which commitments are theoretical?

The file representations, selector code and proof infrastructure are engineering.
The following choices affect predictions and must be recorded separately:

- Choosing local versus global repair as a general preference changes both
  truth conditions and subsequent accessibility. Heim discusses the alternatives
  and leaves the general preference hypothesis open.
- Requiring world-safe proxy repair rules out information-adding repairs. This
  is a candidate completion motivated by the source, not a claim that all
  accommodation in Heim must preserve information.
- Requiring assignment-safe repair is stronger still and excludes the checked
  guaranteed-witness case. It cannot be substituted for world safety without
  changing permitted analyses.
- Bridge-only deliberately leaves appropriateness unconstrained; its allowance
  of a damaging repair does not show that Heim predicts that repair is good.
- Keep-all attention is held fixed to isolate permission differences. It is an
  instrumentation fixture, not a recency/prominence theory.

The policies do not exhaust all possible completions, rank empirical adequacy,
or predict every pronoun contrast. Source-correspondence and the intended
assignment/world clarification still need independent review. No necessary
restructuring or whole-source outcome is inferred from these alternatives.

## Checks, integration and preservation

Coq 8.20.1 compiles all 33 new statements; every one is globally closed, with
no admissions, top-level axioms, undocumented dependencies, unresolved queries
or unsafe flags. Explicit hypotheses in theorem statements still apply.
Depth probes cover 33/33: 0 vacuity flags, 3 triviality flags, 0 bailouts. The
three retained triviality flags are `repaired_description_licensed`,
`world_safe_implies_bridge_only` and `deny_is_least_policy`; they are direct
definition/entailment checks, not independent linguistic claims.

Fresh compilation of the complete eight-module dependency closure and kernel
rechecking pass. The project make target, all 69 Python atlas tests (including
eight new policy tests), 14 CI-setup tests and three site-reporting test scripts
also pass. The previous 85 consolidated records and 1,129 locked claim entries
are unchanged; exactly 33 new claims were added. All 230 paper records preserve
their levels, grades and outcomes; only Heim's evidence-file list changes.

The full Heim collection now has 186 proved statements: 183 globally closed
and the three previously documented classical metatheorems. Counts include
helpers, source-linked formulas and new comparison diagnostics.

One historical integration regression test was made additive-campaign aware:
it now selects the exact original 82 file identities, pinned in
`heim_1982_integration_baseline_paths.json`, before comparing the original
aggregate hashes. No protected hash was changed. This retains the original
preservation check without treating an additional campaign as a modification
of the old one. Prior code, raw/mechanical/probe records, reports and manifests
remain unchanged; the new checkpoint records the test adjustment explicitly.

Reproduce from the repository root:

```sh
bash atlas_data/campaigns/check_heim_1982_policies.sh
python3 atlas_data/verify.py atlas/dynamic/Heim1982_Policies.v
python3 atlas_data/probes/run_probes.py atlas__heim1982_policies
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 atlas_data/check_checkpoint.py atlas_data/campaigns/heim_1982_policy_manifest.json
```

Rebuilding requires the external corpus directory in `ATLAS_PAPERS` when
running `consolidate.py`, followed by `build_site.py`. Heim remains P4/F3 and
`review_required`, with no default policy or accepted source outcome. The local
site is rebuilt; nothing is committed, pushed or deployed in this step.
