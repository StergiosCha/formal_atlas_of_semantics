# Formal Atlas of Semantics

What must be made explicit, assumed, or added to mechanize a semantic theory—and
what changes when different choices are made?

Formal Atlas connects a **230-source survey** with Coq implementations,
source-to-code audits, checked comparisons and countermodels. It records both
what an encoding establishes and which additional commitments affect its results.

[Explore the atlas](https://orange-beach-0c447e210.5.azurestaticapps.net) ·
[Read the evidence](atlas_data/ATLAS.md) ·
[Source registry](atlas_data/SOURCE_REGISTRY.md) ·
[Propose a change](CONTRIBUTING.md)

Two axes keep the survey separate from implementation progress:

- **P0–P5: intrinsic formality**, from discursive prose to a machine-checked
  source. See the [frozen rubric](atlas_data/FORMALITY_RUBRIC.md).
- **F0–F5: project evidence**, from surveyed, sourced and designed through
  piloted, formalized and verified/connected. These are pipeline labels, not
  grades of a theory's truth or importance.

Checked proofs concern explicitly scoped encodings; whole-source fidelity needs
separate review. No accepted source-level reviews are currently registered.
See [Reading the atlas responsibly](atlas_data/READING_THE_ATLAS.md).

## Selected checked results

| Case study | What the encoding establishes | Evidence |
| --- | --- | --- |
| TTR's model layer | Inhabited component types need not have an inhabited meet: their witnesses can differ. | [Countermodels and source audit](atlas_data/audits/ttr_comparison.md#what-changed-in-ttr) |
| TTR → MTT comparison | A fixed-model translation preserves the selected inhabitation reading, while its subject projection loses witness information and has no inverse. This is not framework equivalence. | [Translation](atlas/ttr/TTR_vs_MTT.v) |
| Typed DTS resolution | Substitution preserves typing; resolution has soundness and bounded completeness guarantees for the implemented projection-context fragment. | [Resolution calculus](atlas/mtt_ranta/DTS_Resolution.v), [scope and source audit](atlas_data/audits/revision_2026_09_13.md) |
| Heim's accommodation policies | Local/global repair can differ in truth conditions and subsequent anaphoric accessibility. Preserving worlds and preserving assignments impose distinct proxy permissions. No default policy is selected. | [Policy comparison](atlas_data/campaigns/heim_1982_policy_results.md) |
| Montague/Kratzer modal clauses | Particular encoded clauses agree by unfolding definitions; the deep embedding also checks T, 4 and 5 for its universal-world necessity operator. | [Shallow clauses](shallow/kratzer2.v), [deep modal proofs](deep/kratzer_deep2.v) |

The [Heim implementation](atlas_data/campaigns/heim_1982_results.md) and
[integration report](atlas_data/campaigns/heim_1982_integration_results.md)
connect file changes, operator binding, modal tests and proxy transitions.
The [claim-level comparison](atlas_data/campaigns/claim_comparison_2026_09_13.md)
separates source-linked fragments, illustrative models and uncovered claims in
the Derrida, Austin, Horn, Grice and Tarski pilots. It does not establish a
formality-tier gradient. More campaigns and correction history are indexed in
the [reading guide](atlas_data/READING_THE_ATLAS.md#campaigns-and-correction-history).

Each proof record on the site includes **Read the actual Coq source and proofs**.
Named declarations link to the full `.v` source with line navigation, recorded
assumption audits and a download. This reader works without the LLM backend;
it displays repository code, not generated proof summaries or live proof states.

Theory comparisons use [scoped evidence profiles](atlas_data/COMPARISON_METHOD.md),
not a theoretical similarity score. Each states its fragment, observations,
representation choices, named evidence and outstanding translation obligations.
The old ordinal means are retained only as history; map spacing is editorial.

## Development and review

Development is LLM-assisted. Coq checks proof artifacts; source comparisons
record passages, scope, assumptions and reviewer provenance where available.
Assistant source reading and multiple agent passes are not independent human
semantic review. The [review registry](atlas_data/paper_outcome_reviews.json)
tracks accepted source-level assessments separately from file assessments.

The [verification workflow](.github/workflows/verify.yml) compiles the project,
kernel-rechecks the atlas layer and checks recorded statements and assumptions.
Its admission-free gate applies to `atlas/`, not the entire repository: legacy
material retains admissions and parameters, visible in the records. A green
check is not maintainer approval or a certificate of source fidelity.

## Repository map

| Path | Role |
| --- | --- |
| `atlas/` | Later implementations, translations, countermodels and bounded pilots. |
| `atlas_data/` | Survey, source assessments, claim/evidence records, audits, campaigns and reporting tests. |
| `atlas_data/site/` | Site template, generated static atlas and rendering tests. |
| `shallow/`, `deep/` | Original paper's two Montague/Kratzer experiments. |
| `extras/`, `ttr_mtt/` | Earlier implementations and pilots retained as research history and reusable material. Consult their records for status. |
| `tool/` | Optional checker service and LLM workbench tooling; see its [README](tool/README.md). |
| `tools/` | Local build/watch helper scripts. |

## Reproduce the checks

The tested toolchain is **Coq 8.20.1** (the project retains Coq naming; the
proof assistant is now known as Rocq). CI uses `coqorg/coq:8.20.1`.
With that version on your path, build from the repository root:

```bash
coqc --version
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

The separate generated makefile avoids the historical machine-local
`Makefile.conf`. For just the paper experiments, use the same generated makefile
and its dependency-aware targets:

```bash
make -f Makefile.coq shallow/PTQ.vo shallow/kratzer2.vo
make -f Makefile.coq deep/kratzer_deep2.vo deep/theorems_deep_PTQ.vo
```

Reporting checks require Python 3 and Node.js, but not the source PDFs:

```bash
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 -m unittest discover -s tool/llm -p 'test_*.py'
python3 atlas_data/build_site.py
node atlas_data/site/test_landing.cjs
node atlas_data/site/test_source_registry.cjs
node atlas_data/site/test_claim_comparison.cjs
node atlas_data/site/test_rosch_campaign.cjs
node atlas_data/site/test_outcomes.cjs
node atlas_data/site/test_proofs.cjs
node atlas_data/site/test_edge_profiles.cjs
```

Both the site and consolidated evidence now rebuild without external PDFs.
The [source registry](atlas_data/SOURCE_REGISTRY.md) covers all 230 survey entries
and pins 138 artifacts. Candidate matches are distinguished from documented
identity, consultation and design links. Bibliographic metadata remains incomplete.
Published low-tier levels are explicitly retained from a historical baseline
pending migration review; 104 documented-only differences are diagnostic, not
automatic downgrades. Optional local hash checks never change those levels.
See [reproducibility limits](atlas_data/READING_THE_ATLAS.md#reproducibility-and-source-access)
and [CONTRIBUTING.md](CONTRIBUTING.md). Do not upload copyrighted source PDFs.

## Original paper companion

This repository also accompanies *Revisiting formal semantics using proof
assistants* (Stergios Chatzikyriakidis). Its case study compares shallow and
deep embeddings of Montague's Intensional Logic and Kratzer's conversational
backgrounds.

| Experiment | Files and scope |
| --- | --- |
| A — shallow | [MontagueFragment.v](shallow/MontagueFragment.v): extensional, intensional and world–time fragments. [PTQ.v](shallow/PTQ.v): analysis trees with shallow denotations. [kratzer2.v](shallow/kratzer2.v): conversational backgrounds and modal-clause comparisons. |
| B — deep | [PTQ_deep2.v](deep/PTQ_deep2.v): typed IL syntax and interpretation, including a temperature-puzzle non-entailment result under stated model hypotheses. [kratzer_deep2.v](deep/kratzer_deep2.v): modal clauses over deep IL denotations. [theorems_deep_PTQ.v](deep/theorems_deep_PTQ.v): further metatheorems. |

## Contributing

Open a Coq file in GitHub's browser editor and propose a pull request for
maintainer review. The deployed atlas is read-only; editing it does not submit
or publish a proposal. [CONTRIBUTING.md](CONTRIBUTING.md) explains browser edits,
local checks, source-review requirements and the limits of approval enforcement.

## Citation and license

Until a versioned archive is assigned, cite *Formal Atlas of Semantics*, Stergios
Chatzikyriakidis, with the [repository URL](https://github.com/StergiosCha/formal_atlas_of_semantics)
and the exact commit you used. The accompanying paper, *Revisiting formal
semantics using proof assistants*, is in progress.

[CITATION.cff](CITATION.cff) supplies machine-readable metadata.
[Release preparation](RELEASING.md) and the
[independent-review packages](atlas_data/audits/INDEPENDENT_REVIEW_PACKAGES.md)
keep an archived release, actual reviewer approval and checked code separate.

MIT, see [LICENSE](LICENSE). External source publications retain their own rights.
