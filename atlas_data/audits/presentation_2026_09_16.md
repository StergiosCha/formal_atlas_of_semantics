# Atlas-first presentation revision — 2026-09-16

This is a documentation/reporting revision, not a source audit, new proof
campaign or accepted source outcome. It starts from the local checkout that
already contains the eight Heim modules and policy-comparison records.

## Changes

- The README now leads with the atlas's research question, survey axes and
  scoped results. The original paper remains a companion section; no
  implementation directories were moved.
- The site introduction and metadata no longer claim “every theory” or “every
  edge” is machine-checked. Featured TTR, Heim and DTS results link to their
  existing records. New rendering checks require the named proved support.
- A linked reading guide, both on the site and in the repository, explains
  scope, source outcomes, LLM assistance, missing independent review and
  remaining corpus reproducibility limits. The correction history stays linked.
- Source-review counts use the same source/outcome-matching predicate as paper
  badges, not a status label alone. Admission counts retain the atlas/legacy
  distinction. No review was added or accepted.
- README build instructions match CI's Coq 8.20.1 and separately generated
  `Makefile.coq`. The new landing-page test is listed in the contribution guide.

## Preservation and checks

Before/after SHA256 comparison confirms no changes to the atlas implementation
files, raw/mechanical/probe records, existing campaigns/audits/designs, project
inventory, consolidated evidence, frozen survey/formality inputs, claim lock,
paper-evidence links or source-review registry. In particular, all 230 sources
retain their evidence levels, intrinsic-formality grades and outcome state.

The historical Heim manifests are unchanged. Their README and generated-site
hashes describe the earlier checkpoint and are intentionally superseded by this
presentation revision; they were not rewritten to conceal later changes.

Local checks:

- 69 atlas Python tests pass.
- 14 verification-setup Python tests pass.
- Four Node rendering test scripts pass, including the new landing/reading
  routes, scoped result links and local documentation links.
- The site rebuild succeeds from the existing `atlas.json`, without running
  consolidation or consulting the external PDFs.
- The documented generated-makefile build succeeds on Coq 8.20.1; existing
  proof artifacts were up to date. This step is not a fresh kernel recheck.
- `git diff --check` passes. Existing Python resource warnings in `verify.py`
  remain; they do not fail the tests.

The rendering tests use a minimal DOM, not a browser or visual inspection.
Nothing in this step is committed, pushed, released or deployed. The next
substantive task remains the canonical corpus registry and explicit evidence
bindings, followed separately by independent review and a citable release.
