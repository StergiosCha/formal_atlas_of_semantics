# Persistent Coq candidate validation, 2026-10-03

Status: tested candidate, not a production-deployment record.

The public site/worker were not replaced or restarted during this work. The
existing deployment remains at site commit `14b28d9` and worker image
`sha256:31a276f63ef8bb9c21d9d739632e38559a64a379f2960bcf7606b20301ddf8b6`.

## Candidate artifacts

- Coq 8.20.1, OCaml 4.13.1.
- Pinned opam package `coq-lsp.0.2.5+8.20`; runtime version `0.2.5`.
- Toolchain and complete library build: ACR run `caa`, base image
  `formalatlasacr.azurecr.io/atlas-checker@sha256:4ed67ec757301f8288150dc75b4d49895a9a48d40731c91bfb5c700c28595264`.
- Passing runtime candidate: ACR run `cac`, image
  `formalatlasacr.azurecr.io/atlas-checker@sha256:24f488c892065bfaab0b49ffd79d8e17a085cda5a7432cb49b38e7328da35495`.
- Public library fingerprint remains
  `9dfe0dbdad82d8e23445ef3c7dff79af01189558d3af10577846daab23ae1536`.

`Dockerfile.runtime` packages runtime changes over an already compiled,
digest-pinned toolchain/library. Use the main Dockerfile for source or toolchain
changes; do not assume the overlay recompiles Coq dependencies.

## Checks performed

On the approved Linux VM, the candidate ran in a separate non-root, networkless,
read-only container. It had no published ports, model credentials or host mounts.
The existing production container stayed running.

- All 23 session tests passed, including five actual sandboxed LSP tests.
- Forward, backward and edited-prefix queries retained the same process.
- Separate sessions could not see one another's definitions.
- An existing atlas module imported correctly; Greek identifiers worked.
- A known file outside the session sandbox could not be loaded.
- Invalid tactics, unfinished bullets and failed `Qed` never produced success.
- Real HTTP tests passed for opening/closing sessions, empty prefixes, Unicode,
  out-of-order requests, missing/expired tokens and no-store response headers.
- Full compilation ran independently through the existing fresh `coqc` route.
- The HTTP smoke harness was supplied to the candidate on stdin; that new test
  script is not itself present in the earlier built candidate image.

Local regression checks also passed: 94 atlas tests, 20 workflow tests, 12
provider/loop tests, 20 non-live workspace tests and eight frontend JS suites.
The seven existing local real-Coq workspace fixtures were skipped; this is not
a claim that they ran on macOS during this change.

The updated local editor passed a real-Coq replay browser regression against
the unchanged public worker. Separate browser tests exercised persistent
session lifecycle, expiry, stale results, escaped structured goals and cleanup
with mocked Coq responses. **A real browser-to-persistent-worker deployment
test remains a rollout gate.** No paid model call was made; explanation output
in browser tests was mocked.

## Corrections caught during validation

1. The base image pins ocamlfind 1.9.6; coq-lsp requires at least 1.9.8. The
   isolated build now explicitly installs 1.9.8 without changing user toolchains.
2. The executable reports `0.2.5`, not the opam package suffix `0.2.5+8.20`.
3. The documented completion variant is encoded as `["Yes"]`, not `"Yes"`.
   The first candidate rejected valid prefixes because of this mismatch. It was
   never deployed. The corrected decoder has an explicit regression test.

These checks establish runtime behavior for the tested cases, not source
fidelity or a new theory-level result. No `.v` source, assessment or outcome
label was changed.

## Rollout requirements

1. Review the change and publish the frontend through the normal CI workflow.
2. Activate the candidate worker with a recorded previous-image rollback path.
3. Run `smoke_deployed.py` and `smoke_public.py` against the actual deployment;
   both now exercise persistent sessions when the backend advertises them.
4. Confirm session cleanup and unchanged isolation/privacy controls before
   describing persistent execution as publicly available.

The in-memory registry needs one API worker process. Two sessions reserve both
Coq slots; users can release an idle one before compilation. Text-only
explanations have a separate concurrency limit. Sessions are not durable across
server restarts or page reloads; source drafts remain browser-local.
