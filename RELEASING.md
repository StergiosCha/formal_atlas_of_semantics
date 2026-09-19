# Preparing a citable research snapshot

[CITATION.cff](CITATION.cff) identifies the software without inventing a
release version, publication date or DOI. Until an archive is created, cite
the exact repository commit used.

Before selecting and tagging a release:

1. Review the source-registry migration status and retain its limitations.
   “230 surveyed sources” must not become “230 independently verified theories.”
2. Verify the release commit through the Coq and reporting jobs, inspect the
   deployed revision and record source-review status accurately.
3. Choose the release version and approve its scope/notes. A preliminary
   research snapshot may include pending reviews if clearly labelled;
   it must not imply those reviews have occurred.
4. Connect the owner's repository to the intended Zenodo account/community
   or supply appropriate archive authorization. Archive only redistributable
   code, records and metadata—not the external copyrighted PDF corpus.
5. Create the tag/release and archive it; only then add the assigned DOI and
   actual release metadata to CITATION.cff and the release notes.

No tag, external release or DOI is created by this preparation. External review
requires real reviewers; Zenodo publication requires an authorized account and
the owner's archival choices. These are not replaceable by generated metadata.
