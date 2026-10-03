# Atlas Coq editor

CodeMirror 6 is bundled locally, not loaded from a CDN. Exact dependency versions
and integrity hashes are in `package.json` and `package-lock.json`.

```sh
npm ci --prefix tool/editor --ignore-scripts
npm --prefix tool/editor run build
```

Commit the source, lockfile, generated `atlas_data/site/vendor/coq-editor.js`
and its license notice together. The reporting workflow rebuilds and checks for
drift. No npm installation is needed to serve an already-built site.

`editor.js` owns the Coq lexical mode, CodeMirror extensions and proof markers.
`atlas_data/site/workspace.js` owns request handling and snapshot attribution.
Highlighting, navigation and parsed goal panels are UI aids, not verification.
Coq checks the submitted source; original semantic audits never transfer to edits.

The browser test can serve the checkout against the deployed worker:

```sh
python3 tool/checker/smoke_public.py \
  --backend https://formal-atlas-coq-crete.westus2.cloudapp.azure.com
```

Add `--site <url>` to test a published site. The test makes temporary real Coq
requests but mocks model output; it does not require a model key or paid calls.
