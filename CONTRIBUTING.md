# Propose changes for review

The atlas site is a generated, read-only presentation. It is not a shared Coq
editor and does not currently have a submission inbox. GitHub provides the
browser-editing and pull-request workflow for proposing changes to the maintainer.

## Browser workflow

1. Sign in to GitHub and open the relevant file in
   [the repository](https://github.com/StergiosCha/formal_atlas_of_semantics).
   Implementations are in `atlas/`, `shallow/`, `deep/`, `extras/` and `ttr_mtt/`.
2. Use **Edit this file** (the pencil). If you lack write access, GitHub may offer
   to fork the repository. Otherwise create a fork first. Make a proposal branch;
   do not commit directly to `main`.
3. Commit your changes on that branch and open a pull request targeting this
   repository's `main`. Explain the source passages, encoded claims, limitations,
   and any changes to definitions or assumptions. Link related atlas records.
4. Request review from `StergiosCha` where GitHub permissions allow it. The
   maintainer can inspect the diff, discuss revisions, and approve or reject it.
   Notifications depend on their GitHub notification settings; this is not an
   automatic email attachment or a submission through the atlas webpage.
5. Wait for review and checks. Approval does not itself deploy the site: merging
   into `main` triggers Coq and reporting checks before production upload.
   Same-repository pull requests may get verified previews; fork proposals run
   checks without deployment credentials. Preview availability depends on the
   configured Azure credentials. Uploads are serialized per target.

GitHub's editor does not compile Coq. The existing `verify` workflow runs on pull
requests and checks compilation, kernel checking, mechanical records and atlas
invariants. Read its actual result; neither opening a PR nor receiving a green
build establishes source fidelity. Some contributors will need a local Coq
environment to regenerate the corresponding evidence before checks can pass.

## Approval is a policy until enforced

This guide asks contributors to use pull requests and wait for maintainer
approval. It does **not** prove that branch protection is enabled or prevent
people with sufficient permissions from pushing or merging. Requiring approval
from this specific maintainer needs repository rules/protected branches,
appropriate code-owner review settings and control of bypass permissions.
No permissions or branch rules were changed in this documentation update.

## Local checks and generated evidence

Use the Coq version required by `.github/workflows/verify.yml` for matching
mechanical records (currently 8.20.1). Build using the README instructions.
For changed Coq files, rerun the relevant mechanical verification, inspect its
assumptions and regenerate fingerprints as described in `atlas_data/verify.py`.
Do not silently accept a changed record solely to make CI green.

For reporting/UI changes:

```bash
python3 -m unittest discover -s atlas_data -p 'test_*.py'
python3 atlas_data/build_site.py
node atlas_data/site/test_landing.cjs
node atlas_data/site/test_source_registry.cjs
node atlas_data/site/test_claim_comparison.cjs
node atlas_data/site/test_rosch_campaign.cjs
node atlas_data/site/test_outcomes.cjs
git diff --check
```

If you change consolidation inputs, rebuild before running those checks:

```bash
python3 atlas_data/source_registry.py
python3 atlas_data/consolidate.py
python3 atlas_data/build_site.py
```

The [source registry](atlas_data/SOURCE_REGISTRY.md) makes these rebuilds
independent of external PDF availability. F0–F2 retain a labelled historical
baseline pending migration review; candidate matches do not certify identity.
Use `python3 atlas_data/source_registry.py --corpus /absolute/path/to/papers`
for optional local byte verification, separately from identity and consultation.
Edit `atlas_data/site/template.html`, not only generated `index.html`.

## Protect research provenance

- Keep the frozen survey, addendum and `formality.json` unchanged. Propose any
  methodological revision separately rather than silently regrading a source.
- Preserve historical records and manifests. Record changed scope and evidence
  explicitly; a bounded pilot is not an implementation of an entire book.
- Follow [the source-outcome policy](atlas_data/OUTCOME_POLICY.md) when proposing
  a paper verdict. A file opinion, edge or successful proof is not enough.
- Do not upload external source PDFs, credentials, machine-specific configuration
  or compiled Coq artifacts. Cite sources and include permitted excerpts only.

The deployment workflow requires the Coq and reporting/provenance jobs to pass
before upload. These checks cover structure and encoded claims; source fidelity
and authentic independent review remain human/research work.
