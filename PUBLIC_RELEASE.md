# Public release hygiene

The repository publishes code, technical reports, source audits, reproducibility
records and the application. Personal correspondence, assistant handovers,
session instructions, credentials and local caches belong outside the checkout.
Ignoring a file does not untrack it and does not remove earlier Git versions.

## Check a candidate tree

```sh
python3 tools/check_public_tree.py
python3 -m unittest discover -s .github/tests -p 'test_*.py'
```

The scanner reports file locations and categories, never credential values.
It checks tracked files and non-ignored additions, including the generated site.
It does not replace specialist secret scanning or human review. Intentional
test canaries can match a credential pattern and require inspection.

Before making a previously private repository public, also run:

```sh
python3 tools/check_public_tree.py --history
```

History inspection covers objects reachable from local refs. It does not inspect
server-only pull requests, caches, forks, releases or Actions artifacts. Historical
findings need an explicit publication decision. A cleanup commit alone leaves
earlier content accessible. Rotate any actual exposed credentials before a
separately approved history rewrite or publication of a new sanitized repository.

## Documentation cleanup on 11 November 2026

Private handovers, one-off assistant prompts, session planning and personalised
correspondence were removed from the candidate tree after a private backup.
Public review materials were retained with recipient-neutral headings. The
Montague overview is now `deep/montague_ptq/OVERVIEW.md`.

Historical machine paths in records and reports were replaced with repository
relative paths or neutral `/historical-checkout/`, `external-corpus/`,
`external-source-cache/` and `external-scratch/` labels. The historical root
retains old record identity without promoting a paper's assessment merely
because a local path has been cleaned. These labels do not mean that copyrighted sources
or old scratch files are distributed. Configure `ATLAS_PAPERS`, `ATLAS_REPO`
or `ATLAS_CORPUS_ROOT` when a local operation needs an external checkout or corpus.

Scientific statements, Coq sources, proof checkpoints, grades and source-review
decisions were not revised by this cleanup. Active source-registry references
were refreshed only where path sanitization changed a referenced document's
bytes. Historical snapshot manifests retain their original scientific file
hashes. They identify their historical snapshots, not this sanitized working tree.

Tests use the exact before/after fingerprints in
`atlas_data/privacy_migration_2026_11_11.json` for the affected snapshots.
Only named scopes with the matching original digest can use a replacement.
Unlisted files still require their original hash. The consolidated atlas was
compared with the pre-cleanup version after only the documented path substitutions.
All 169 Coq files and 123 additional proof checkpoints and protected research
files were also checked for byte identity. This migration does not authorize
future changes to claims, outcomes, assumptions or evidence.

## Local history rewrite on 11 November 2026

Following explicit approval, the cleanup was committed and all locally available
branches were rewritten. Private documents and caches were removed throughout
history, and personal paths and recipient headings were redacted. A complete
Git recovery backup and bundle are retained privately outside the checkout.

The rewrite processed 74 commits. Every historical Coq source blob remained
unchanged. The main tree immediately before and after the rewrite had the same
Git tree ID, so the rewrite did not alter the already-tested cleanup result.
The full local history scan then checked 1,068 reachable file versions with no
findings. These checks are not a guarantee about remote-only refs or caches.

`HISTORY_REWRITE_2026_11_11.tsv` records the old and new commit IDs. In particular,
the previously cited revision `9c2302fe106a3104081df8751fa715d1ca68f772` maps to
`374e4a98ac106ea2bdf7f3c77d8648db6ce26703`. The original IDs and hashes inside
historical evidence manifests remain as provenance identifiers. They are not
promises that the private, pre-redaction snapshots remain publicly retrievable.

The history tool removed the local `origin` remote as a safety precaution.
No force-push was performed. GitHub still requires a separately approved update,
including checking for remote changes and arranging any necessary cache or
pull-request cleanup. Do not fetch or merge old history back into the sanitized
checkout. Collaborators should re-clone after the remote update.

No deployment, visibility change, archival DOI or independent source-review
approval is implied by the rewrite.
