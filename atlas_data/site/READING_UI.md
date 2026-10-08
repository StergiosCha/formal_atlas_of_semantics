# Discovery and proof reading

The first frontend increment adds three entry points without removing any
existing routes:

- `#/explore`: papers, proof records, the theory map and source registry.
- `#/comparison`: existing claim-level comparisons; recorded edges remain at
  `#/edges`. There is no theoretical similarity score.
- `#/experiment`: guided witness example, countermodels and the existing
  proof-drafting workflow.

`#/reading` holds methods and links to contribution and reproduction guidance.
The navigation keeps its active group across individual records and proofs.

## Guided result

`#/result/witnesses` explains the Boolean separation in
`atlas/ttr/Witness_Contract.v`. Its three evidence links are resolved from exact
names in the bundled declaration index, not hard-coded line numbers:

- `Packages.Separation.independent_inhabited`
- `Packages.Separation.shared_empty`
- `Packages.Separation.no_total_recovery`

This is curated explanatory text about project-added comparison infrastructure,
not a new source-fidelity judgment or an equivalence between TTR and MTT. It
links the existing source consultation, including the unresolved Ranta edition
discrepancy. The finite table is an illustration, not a fresh Coq execution.

To add another guided result, identify precise existing declarations, document
the construction's scope and source boundary, and add routing and tests. Do not
invent missing evidence or copy a result's recorded audit onto edited source.

## Connected reader

`#/proof/<record-key>?line=<number>` combines the record summary, the selected
theorem's recorded source claim when available, a searchable declaration index,
and the full Coq source. It retains separate compilation, assumptions and source
correspondence panels. A source-index status is not itself a kernel check.

Only an exact declaration-line selection gets a declaration-specific audit;
arbitrary body-line links do not guess which theorem was audited. The existing
assumption-audit checks remain authoritative. Missing or unresolved audits do
not receive closure claims. Audit records are not rerun on page load.

Syntax highlighting uses the existing pinned CodeMirror bundle in read-only
mode. Search works after focusing the code. Plain text and original line links
remain available through a toggle and when the enhancement bundle fails.
Downloads preserve the original source bytes. Mobile context and declaration
panels start collapsed to keep the code within easy reach.

Opening a reader does not start Coq, call an LLM or send source to a backend.
The site's existing external font request is unchanged. Live editing remains a
separate private-copy action with its existing explicit connection and checks.

## Files and checks

Edit `template.html` and `reading.css`. Rebuild `index.html` with
`python3 atlas_data/build_site.py`. Editor changes belong in
`tool/editor/editor.js`; rebuild its committed bundle using the editor README.
No Coq files, outcome labels, P/F grades or backend contracts change here.

```sh
node atlas_data/site/test_reading.cjs
node atlas_data/site/test_proofs.cjs
node atlas_data/site/test_workspace.cjs
python3 atlas_data/smoke_reading.py
```

The browser regression needs Playwright and Chromium. It serves the checkout
locally, blocks external requests, and writes desktop/mobile screenshots and
`checks.json` to a fresh temporary directory. It checks discovery, guided
navigation, syntax highlighting, read-only behaviour, search, source downloads,
editor transitions, responsive layouts and missing-bundle fallback. It makes
no live Coq requests or paid model calls and does not claim a deployment test.

This increment does not add assumptions diffs for edited copies, multi-file
editing, new comparison profiles, review submission or additional guided cases.
