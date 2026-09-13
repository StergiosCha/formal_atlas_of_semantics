# Second-cohort reading audit and post-reading qualifications

This accompanies [the inventory checkpoint](cohort2_2026_09_13.md). It does
not amend the frozen stage-A protocol. Work was performed by one assistant;
“single-researcher” in the protocol does not imply an independent human reader,
blinding, multiple graders or expert semantic review. No subagents were used.

## Reading coverage and extraction

Corpus root: `/Users/graogro/Dropbox/formalizing_formal_semantics/papers`.
All sources retain the SHA-256 identities fixed in stage A and the index.

- **Rosch:** All 25 local PDF pages, including references, via native text
  extraction. The file is a reformatted chapter, not the original pagination.
  Visually checked local pp. 5 and 16. Do not translate local pages to original
  pp. 27–48 by an offset. The PDF itself contains some typographical defects.
- **Hobbs:** All 36 local pages, including references, via fresh English OCR
  after the original text extraction proved unusable. Rendering used 170 dpi;
  Tesseract ran on all pages, with four local OCR processes (not four readers).
  Crucial formulas and source identity were visually checked on pp. 1, 21, 22,
  25 and 35. Restored negations in (41) and the non-strict comparison in (43)
  from the images. The original garbled extraction is not reading evidence.
- **Spivak:** All 46 local pages via the usable existing text layer: printed
  pp. 271–313 (essay and notes) plus appended title, copyright and contents.
  Visually checked printed pp. 276 and 308. The appended book matter identifies
  the 1988 publication. This is not a reading of later revisions or reception.

Commands used for extraction were `pdftotext -layout`, `pdftoppm`, and
`tesseract -l eng`. Scratch outputs are in
`/private/tmp/cohort2-reading.NuQO6a`; they are disposable working aids, not
tracked source editions or a redistributed corpus. The source PDFs and the
actual inventory text are the durable hashed artifacts. Bibliographic works
cited by these sources were not thereby independently read or verified.

## Qualifications discovered after stage A

1. **Hobbs version gate:** The selected file's 1985 label is not enough to
   identify its revision. It cites Hovy 1988 in the body and bibliography and
   Linde 1989 as forthcoming, and refers to a next chapter. A filename search
   in the local corpus found no second Hobbs file to compare. Exact publication
   provenance remains unverified. Keep the inventory tied to these bytes and
   resolve the version match before a paper-attributed implementation. No
   source substitution, attribution repair or regrading was performed.
2. **Rosch granularity caution:** The frozen P1 rationale says “no formal
   apparatus,” but the read chapter defines conditional-probability cue validity
   and discusses formal resemblance measures. This is a recorded tension between
   a paper-level grade/rationale and source fragments, not a silently revised
   grade. A later review could examine it explicitly; current tier comparisons
   must not suppress it.
3. **Spivak scope:** A literal inability to utter or act is not an adequate
   paraphrase of the argument about representation, agency and hearing/reading.
   Several central historical and normative claims have no defensible formal
   obligation specified here. This is not an impossibility verdict. Source
   statements quoted from interlocutors, colonial records or Guha's scheme
   must not automatically be attributed as Spivak's endorsed definitions.

There was no departure from selection/order, the full-local-text reading
commitment, preservation of earlier work, or the stop-before-Coq boundary.
The version and grade-rationale issues were discovered during reading; stage A
has not been rewritten to conceal them. Actual claim wording was selected in
stage B after reading, not preregistered before reading.

## Tool-clock ledger (UTC)

| Phase | Start | Recorded boundary | Meaning |
|---|---|---|---|
| Preparation / stage A | 14:17:58 | 14:18:20 | Metadata/hashes and protocol, before source-body reading. |
| Rosch main text pass | 14:18:20 | 14:19:53 | Full local text; later visual/re-reading checks included below. |
| Hobbs preparation / reading | 14:19:53 | 14:26:30 | Failed text extraction, rendering, OCR, full reading and visual checks. |
| Spivak reading / visual checks | 14:26:30 | 14:41:04 | Full local text and appended matter; includes automatic context summarization. |
| Inventory drafting / source rechecks | 14:41:04 | 15:08:09 | Three inventories, index and successful structural checks. |
| Overview / audit metadata | 15:08:09 | 16:36:52 | Large observed clock interval; active work versus delay was not instrumented. |

All times are on 2026-09-13, from the available UTC clock. Rosch image checks
overlapped Hobbs preparation; subsequent focused source checks occurred during
inventory construction. The final metadata/freeze timestamp is in the manifest.
These intervals include model/tool latency, context handling and other overhead;
active reading and idle time were not separately measured. They are **not human
research times**, per-paper effort estimates or a controlled efficiency result.
There was source-extraction engineering, but no Coq encoding/proof/debug effort
for this cohort in this stage. Earlier pilots lack matched effort measurements.

## Validation and interpretation limits

Before freezing, read-only checks confirmed:

- 25 unique target IDs (8 Rosch, 10 Hobbs, 7 Spivak), matching the index.
- Every target has all six required fields and source page loci: claim/type/
  centrality; cases/limits; possible obligation/limit; parameters/additions;
  input/prediction; robustness status.
- All three remain F1 with no linked Coq file and no actual determination.
  Source hashes, selection and reading order match stage A.
- Protocol SHA-256 remains
  `f38f42640ed9a543d0372ef541394d060eedf10f652d1e7e14cc43b2f45f5e2a`.
  Baseline atlas and frozen grade hashes are unchanged.
- The prior claim-comparison checkpoint still verifies all 116 hashes,
  including its external sources. No earlier tracked artifact was rewritten.

Structural checks cannot establish that the paraphrases or proposed mappings
are faithful; those remain a first-pass, source-linked interpretation requiring
independent review. No Coq compilation, proof checks, empirical replication,
alternative-encoding experiment or new site build was performed for this
inventory-only stage. The new manifest records the completed hash checks.
