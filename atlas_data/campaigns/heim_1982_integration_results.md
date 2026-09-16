# Heim: binding and end-to-end integration

2026-09-15. Authorized next step 1 is implemented for a selected logical-form
analysis: automatic operator indexing/free-variable extraction and a common
runner connecting modal tests, final file updates and recorded proxy transitions.
Three new modules add **61 proved statements**, all without global axiom
dependencies or admissions. The seven-module Heim implementation now contains
153 proved statements: 150 globally closed and the three previously documented
classical metatheorems. Explicit model/policy hypotheses remain in theorem
statements; "globally closed" does not erase those conditions.

This closes specific engineering gaps in the
[previous checkpoint](heim_1982_results.md). It does not complete a raw-English
parser, choose Heim's unresolved pragmatic policies, or approve a whole-source
transfer outcome. The earlier four modules and their research records are
unchanged. See the [fixed targets](heim_1982_integration_design.md) and
[machine-readable coverage ledger](heim_1982_integration_results.json).

## What now connects

```text
Selected NP-prefixed scope tree + lexical interpretations
  → nearest-operator indexing + nuclear/text existential closure
  → indexed LF + computed free-reference requirements
  → modal truth test on current file + tagged tentative-memory trace
  → explicitly authorized fresh proxy introduction
  → ordinary final-FCS assertion about that referent
```

The runner also accepts ordinary final-FCS blocks directly. These are separate
adapters: `Core` reproduces the existing final update and felicity guard; `Read`
filters the current file by the earlier indexed satisfaction relation, after
checking computed reference availability. No theorem identifies the complete
earlier and final theories. `Then` composes these commands with `Direct` and
`Proxy` transitions while threading current file and recorded history.

## Binding is computed and checked

[Heim1982_Binding.v](../../atlas/dynamic/Heim1982_Binding.v), 25 statements:

- `free_indices` covers every indexed constructor, including both modal
  operators. `free_indices_exact` proves syntactic membership correctness.
- `satisfaction_depends_only_on_free` proves that agreement on computed free
  indices suffices for identical satisfaction, for arbitrary models. Binder
  transport uses assignment splicing, not choice or function extensionality.
- `pending_indices` passes an indefinite's index to its nearest operator.
  Pronouns do not request binding. Operator seeds preserve the indices carried
  by quantifier extraction; nuclear and text existential closure are computed.
- Compiler truth theorems recover universal donkey-pair quantification and
  nuclear existential witnesses. A separate example checks that a deictic
  pronoun remains free rather than being accidentally bound by text closure.
- `contextual_truth_computed` replaces the caller-supplied free-variable list in
  the earlier contextual-reference schema. The resolved-assignment theorem
  connects unique reference provision to satisfaction.

Source: pp.90–100, especially obligatory closure pp.90–94 and nearest-operator
selection pp.96–97; earlier satisfaction/reference clauses pp.105–111; modal
binding pp.118–120. The input tree already has a chosen NP-prefixing/scope
analysis and referential indices. Choosing movement readings and checking
original-source-order novelty, crossover and other grammar constraints remain
upstream responsibilities. This is an operator-indexing compiler, not an English
parser or automatic generator of every available reading.

## File, modality and memory stay distinct

[Heim1982_Integration.v](../../atlas/dynamic/Heim1982_Integration.v), 23 statements:

- The core and indexed adapters have exactness and file-well-formedness proofs.
  The indexed adapter uses actual world/assignment satisfaction; it does not
  erase the modal base or ordering from the truth test.
- `core_trace` records actual intermediate files, including tentative ones
  discarded from the live domain by an operator. `indexed_trace` records stages
  of satisfaction calculation and tags them with the originating indexed text.
- Modal descent resets world information in those calculation snapshots. Their
  predicates still depend on candidate worlds; they are not assertions about
  the actual world. Accessibility and ordering remain in the tagged origin and
  the modal truth test. The snapshots do not themselves encode a complete
  context-sensitive accessibility/felicity calculation.
- Trace files satisfy condition B when the input does. Attention/retention is a
  history-sensitive parameter constrained to select only indices in a file's
  domain. Remembered history does not enlarge the current domain.
- `Proxy` requires a recorded prominent precedent, a distinct fresh index and
  an explicit authorization relating the old and repaired files. It performs
  the introduction and establishes the description. A theorem connects that
  real transition to the existing `pronoun_with_proxy` licensing interface.
- Missing memory or denied permission blocks the proxy command. Remembering a
  card alone does not authorize accommodation, and direct use requires a live
  accessible index.

This runner is added infrastructure, motivated by pp.234 and 247–254. It is not
attributed to Heim as an already specified unique processing algorithm. `Read`
checks free-reference availability, not a complete modal presupposition theory.
`Core` executes licensed raw blocks; other accommodation interleavings remain
available in the earlier separate `Run` relation. The connected proxy step is
not a claim to implement every kind of repair in every syntactic position.

## End-to-end results

[Heim1982_EndToEnd.v](../../atlas/dynamic/Heim1982_EndToEnd.v), 13 statements:

`complete_modal_proxy_core_run` derives a full sequence from a compiled modal
tree, through generated memory and an authorized proxy, to a final-FCS assertion.
For predicates P (the remembered description) and Q (the subsequent assertion),
`complete_program_truth_conditions` derives:

```text
the original file is true at w
and every accessible v has some x satisfying P(v,x)
and some actual x satisfies both P(w,x) and Q(w,x).
```

The quantification is over arbitrary individual/world types. The modal example
uses a flat ordering, an explicit source-permitted modal parameter choice. It is
not a proof for every interpretation of desire, knowledge, tense or negation.

With reflexive accessibility, `factive_modal_proxy_preserves_world_content`
shows why the actual witness is already supported by the modal assertion.
The two-world `desired_witness_is_not_an_actual_witness` shows the converse
failure: a witness in desire worlds can be remembered while absent in the actual
world, and adding that description can make the actual file false. This tests
the distinction discussed at pp.251–252. Preservation here is of **world
content**, not the literal assignment-set claim qualified in the earlier report.

The keep-all attention setting in these derivations is a named instrumentation
fixture, not a proposed theory of prominence. Authorization remains a premise;
the implementation does not silently approve all remembered proxies. Further
negative tests reject direct reuse of a scoped card and a read with unresolved
deictic reference. These are pipeline checks, not a completed theory of pronoun
acceptability.

## Verification and reporting

Fresh compilation of all seven modules and kernel rechecking pass with Coq
8.20.1. Every new theorem's assumptions were queried: 61/61 globally closed,
0 admissions, 0 top-level axioms, 0 undocumented dependencies, 0 unresolved
queries and 0 unsafe flags. The project make target also passes.

All 61 Python atlas tests (including eight new integration tests), 14 CI-setup
tests and three site-reporting test scripts pass. The new tests verify that the
82 previous consolidated file records and 1,068 previous claim entries remain
unchanged, exactly 61 new claims are locked, and all 230 paper records are
unchanged apart from Heim's three additional evidence-file links.

Depth probes cover all 61 new statements: 0 vacuity flags, 11 triviality flags,
0 bailouts. The 11 flags remain in the sidecars and concern direct adapter
equations, computed example indices and simple trace facts. They are not failed
proofs or independent source-fidelity verdicts. Counts include helpers, source
examples and new conditional integration results, not 61 linguistic claims.

Reproduce from the repository root:

```sh
bash atlas_data/campaigns/check_heim_1982_integration.sh
python3 atlas_data/verify.py atlas/dynamic/Heim1982_Binding.v atlas/dynamic/Heim1982_Integration.v atlas/dynamic/Heim1982_EndToEnd.v
python3 atlas_data/probes/run_probes.py atlas__heim1982_binding atlas__heim1982_integration atlas__heim1982_endtoend
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 atlas_data/check_checkpoint.py atlas_data/campaigns/heim_1982_integration_manifest.json
```

To regenerate the local atlas, supply `ATLAS_PAPERS` to `consolidate.py` with the
external corpus directory, then run `build_site.py`. This preserves sourced
levels for unrelated papers whose PDFs live outside the repository.

The new checkpoint pins code, ledgers, tests, generated evidence and the consulted
2011 PDF hash. It supersedes shared generated-output hashes in the previous
checkpoint, without rewriting old reports, proofs, records or frozen grades.
This remains one assistant's implementation/source comparison; independent
semantic review and maintainer approval are pending. Heim remains P4/F3 and
`review_required`; the integration adds evidence, not an accepted outcome.
Nothing has been committed, pushed or deployed in this step.
