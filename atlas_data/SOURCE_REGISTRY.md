# Source registry and conservative migration

The registry covers all **230 frozen survey entries**, plus Cooper 2023 as a
separate supplementary work. It does not identify Cooper 2023 with survey ID50
(Cooper 2005), mint a new grade, approve an outcome, or claim that all
bibliographic metadata has now been verified.

## Current checkpoint

- 138 distinct SHA256-identified artifacts, referenced by corpus-relative
  paths; no source PDFs are redistributed.
- Seven surveyed sources have imported, source-specific identity evidence:
  Heim 1982, Coecke–Sadrzadeh–Clark 2010, Bekki–Mineshima 2017, C&L 2020,
  Derrida's Signature Event Context, Austin's book and Horn's taxonomy.
  Cooper 2023 has a separate documented supplementary link.
- “Documented” means that a named audit supplies the source/artifact link.
  It does not certify an independent reader, complete bibliographic metadata,
  whole-source fidelity or empirical adequacy.
- Other matches remain candidates or absent metadata. DOI/ISBN values were
  not guessed. The one imported bibliographic identifier is DisCoCat's
  explicitly documented arXiv version. An edition description may identify
  the audited local text without settling every publisher/printing detail.
- Ranta's 1994/1995 date discrepancy and Hobbs's later internal citations
  remain unresolved. Their pinned bytes are not treated as confirmed editions.

## Files and fields

| File / field | Meaning |
| --- | --- |
| [source_registry.json](source_registry.json) | Canonical source/artifact/design links, imported reading records and baseline references. |
| sources: paper_id, citation | Exact frozen survey identity, including mixed numeric and minted string IDs. |
| artifacts | SHA256-keyed objects: corpus-relative paths and supporting historical manifests, where available. |
| artifact_links: status | Candidate (not identity evidence) or documented (a hashed source-specific audit supports the link). |
| edition, identifiers | Version description and supported DOI/ISBN/arXiv values; null/empty means not documented, not nonexistent. |
| consultations | Artifact, report hash, passages and reader provenance. Assistant reading is not independent human review. |
| designs | Exact document/hash, source-specific scope and candidate/documented status. A surname mention alone is insufficient. |
| supplementary_sources | Relevant works outside the frozen survey; no P grade or F promotion. |
| [source_registry_baseline.json](source_registry_baseline.json) | Published source identities and levels at commit 91983bc; not fresh evidence of source availability. |
| [source_registry_migration.json](source_registry_migration.json) | Diagnostic comparison with documented-only low-tier evidence. No automatic grade changes. |
| [source_bindings.json](source_bindings.json) | Explicit import recipe for the audited cases, not an independent review registry. |

The validator rejects missing/duplicate survey IDs, citation substitutions,
stale evidence references, unsafe paths, unsupported documented labels, and
purported independent-review status in this imported checkpoint. Structural
validation cannot establish that an audit's interpretation is correct.

## Published versus documented-only evidence

Production consolidation no longer scans the PDF directory or searches surnames
in design text. It reads explicit source IDs from the validated registry.

For the initial migration, published F0–F2 labels are retained from the pinned
baseline and labelled as historical on the site. F3–F5 still depend on the
existing implementation/edge rules; source records cannot grant a proof tier.
The P grades, source outcomes, proofs and claim lock remain unchanged.

The documented-only comparison finds **104 unresolved low-tier labels**
(87 F1 and 17 F2). These are registration gaps, **not 104 false claims or
recommended downgrades**. Most candidate artifacts have not yet been checked
for exact identity, and candidate design references have not been adjudicated.
The comparison deliberately excludes that unconfirmed evidence.

Review candidates source by source, record exact title/edition and design
scope with provenance, then propose the migration diff for maintainer approval.
This initial loader rejects a bare switch to “approved.” A publication
transition needs a reviewed policy/change, not a boolean toggle.

## Reproduction

These commands require no external PDFs:

    python3 atlas_data/source_registry.py
    python3 atlas_data/source_registry.py --report
    python3 atlas_data/consolidate.py
    python3 atlas_data/build_site.py
    python3 -m unittest discover -s atlas_data -p 'test_*.py'
    node atlas_data/site/test_source_registry.cjs

To check a locally held corpus separately:

    python3 atlas_data/source_registry.py --corpus /absolute/path/to/papers

This reports matching, missing and mismatched bytes and exits nonzero if any
recorded artifact path does not match. It changes neither the registry nor the
published levels. Missing files do not erase historical consultation;
matching bytes do not establish citation identity or prove that anyone read them.

The one-time bootstrap retains the old heuristics **only to generate explicit
candidates**. It refuses to overwrite an existing registry. Routine rebuilds
must not rerun it. Future metadata edits should be reviewed directly, with
updated evidence hashes and a refreshed diagnostic report.

## Preservation and deployment

Historical campaign manifests retain their original hashes. The later Heim
regression tests now explicitly permit changes to the consolidation/site-builder
infrastructure; no proof, record, survey or source-audit hash was exempted.
New migration tests check byte-identical consolidated evidence at this checkpoint,
offline levels, source identity boundaries and rejected metadata mutations.

The subsequent [comparison-profile migration](COMPARISON_METHOD.md) changes
only the edge reporting schema. Its preservation test reverses that explicit
schema change before checking the complete historical atlas hash; it does not
exempt any paper, grade, proof record, original edge annotation or statistic.

Deployment now calls reusable Coq verification and requires both that job and
reporting/provenance checks. Uploads are serialized per production/preview target;
active uploads are not canceled. Stale production commits are skipped, fork
proposals do not receive deployment credentials, and the deployed footer
identifies the checked commit. Local builds say “working copy.” These are local
workflow changes until committed and pushed; branch protection and independent
review remain separate policies.
