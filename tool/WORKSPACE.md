# Live Coq workspace and explanation assistant

From an atlas proof reader, choose **Edit and run in Coq**. The new route is
`#/edit/<record-key>`, optionally with `?line=<number>`.

## What visitors can do

- Edit the actual bundled `.v`, including existing definitions and proofs.
- Connect to a matching Coq 8.20.1 backend, step forward/back, inspect a prefix's
  goals, or compile the full copy. No LLM is needed for these operations.
- Ask the selected model to explain highlighted code. GPT-6 Astra is selected
  when present in the server roster. Claude is not offered.
- Recover browser-local drafts, download a `.v`, or download a review patch.
  Submit the patch through the existing GitHub pull-request workflow. No code
  is automatically published, committed, emailed or submitted for approval.

This is single-file editing against the backend's precompiled imports. It is
not yet a multi-file project IDE. Editing an imported file does not rebuild its
dependents. Each prefix check replays in a fresh process, rather than keeping
a long-lived shared session. Large files may hit the 25-second limit.

Original assumptions audits stay in the read-only reader. The editable copy
never inherits its verified status. A prefix can have open goals, and full
compilation can accept `Admitted` or additional assumptions. Neither establishes
source fidelity. A current assumptions-diff audit is a separate future feature.

## Privacy and model boundary

Opening an editor makes no model call and sends no code. Browser storage is
keyed by file and original source hash; old-version drafts are not overwritten
by a new library snapshot. Clear browser site data to remove retained drafts.

Check sends the edited file to the displayed checker. Explain sends the edited
file, selection and question to that backend. The backend sends only the selected
text plus up to 5,000 characters on either side, with line numbers and provenance,
to the selected provider. Do not put secrets into a draft or question.

The explanation endpoint uses OpenRouter with the visitor's own API key.
Both the editor and Verifier provide a password field and Clear key button.
The app keeps the key in the current page only, not browser storage. Reloading
or navigating clears it. Clicking Explain or Draft & check sends it as an
`X-OpenRouter-Key` header to the displayed backend, which passes it directly to
OpenRouter. The visitor pays for model calls and must trust that backend.
No key is inserted into prompts, Coq processes, application logs, persistent
storage or shared environment variables. Model results are not cached across
visitors. Web requests with no key stop before a model call, even if a server
environment key exists. Coq-only requests do not send or require a key.
The selected Astra alias maps to `openai/gpt-6-astra`. Both the explanation
assistant and proof-drafting loop use this provider, with no Foundry fallback.
It has no tools, does not execute suggestions, and returns an
explicitly unverified explanation rendered as text, not model-supplied HTML.
OpenRouter and its upstream model provider receive the selected context.
No zero-retention promise is made. No prompts are written to application logs.
Requests are rate-limited and output is bounded. Questions are separate calls,
not a persistent assistant conversation.

The [official text-generation guidance](https://developers.openai.com/api/docs/guides/text)
informed separating the explanation instructions from the supplied source data.
Prompt instructions alone are not a security boundary; the endpoint has no
execution or editing capabilities.

## Runtime isolation

Linux requires **usable bubblewrap namespaces**, not merely an installed binary.
The Coq child receives no API credentials, no network, a private process namespace,
read-only Coq/runtime libraries and a writable per-request scratch directory.
CPU, memory, output/file-size and time limits bound execution. Descendants are
terminated and temporary files are removed after each request.

For local macOS development, `sandbox-exec` confines file access, writes and
network access. macOS does not use the Linux address-space limit; use the Linux
worker for production. Neither adapter has an unrestricted fallback.

The legacy `/check` and model-driven `/verify` also require this isolation when
served by the checker. The standalone research CLI retains its prior trusted-local
mode; do not expose that CLI as a public executor. The Docker build context is
allowlisted to public Coq sources, the atlas manifest and runtime code.

`GET /workspace/capabilities` reports the sandbox probe, Coq version and a hash
of every indexed source file. Checks and explanations reject a different site
snapshot with HTTP 409. Editing during a check invalidates its attribution to
the current editor. Compiled imports are assumed to have been built from the
matching immutable image; do not edit server library files after building it.

## Local setup and tests

Build the library first using the repository README. With FastAPI, Uvicorn,
Pydantic and Coq 8.20.1 installed, run from the repository root:

```sh
python3 atlas_data/build_site.py
ATLAS_REPO="$PWD" ATLAS_JSON="$PWD/atlas_data/atlas.json" \
  python3 -m uvicorn server:app --app-dir tool/checker --host 127.0.0.1 --port 8477
```

Serve `atlas_data/site` separately, open an editable proof, and set its backend
to `http://127.0.0.1:8477`. Enter your own key in the page's password field to
test real explanations. No backend environment key is required. No key is
required for Coq.

```sh
python3 tool/checker/test_workspace.py -v
python3 tool/checker/test_workspace.py --live -v
node atlas_data/site/test_workspace.cjs
python3 tool/checker/smoke_workspace.py
```

The last command requires Playwright and Chromium. It checks the actual browser
and sandboxed Coq, but deliberately mocks the explanation response. It does not
test OpenRouter availability or claim a real model response. Screenshot/log artifacts
go to a temporary directory. The real-Coq tests include a forbidden-file canary.

## Production rollout is a separate step

1. Build a checker image containing the same source snapshot as the static site.
2. Confirm that the deployment platform permits bubblewrap's user, PID and
   network namespaces. Some managed container policies prohibit them. If the
   capability probe fails, checking stays unavailable. Use a suitable isolated
   worker deployment; do not disable the sandbox to make the button work.
3. Configure additional permitted site origins using `ATLAS_WORKSPACE_ORIGINS`
   (comma-separated exact origins), if needed. Do not configure a shared model
   secret for the website; visitors supply request-scoped keys.
4. Verify real goals, an invalid proof, forbidden-file access, version/snapshot
   mismatch, and a real explanation on the target runtime before publishing.
5. Deploy the frontend and check the end-to-end public route.

Local macOS tests do not establish Linux/Container Apps compatibility. This
implementation does not itself update the existing deployed checker or site.

### Hosted preflight, 2026-10-02

Production was inspected at `atlas-checker--r5a28a88`. No image, traffic,
secret, public site or GitHub branch was changed during this preflight.

| Check | Result |
| --- | --- |
| Azure and GitHub authentication | Working |
| Production revision | Existing revision remains ready; provisioning succeeded |
| User/PID/network namespace probe | `unshare failed: Operation not permitted` |
| User namespace alone | Same rejection, under the existing `coq` uid 1000 |
| Existing dedicated worker in `formal-atlas` | None found |
| Real GPT-6 Astra explanation probe | HTTP 401 from Foundry; no explanation returned |
| Credential handling | Existing server secret used in place; no key copied or printed |

The earlier explanation probe used the then-deployed Foundry adapter. Its 401
is historical evidence, not an OpenRouter result. On the owner's correction,
the local implementation now uses OpenRouter only. All twelve roster model IDs
were checked against OpenRouter's public catalog. The existing revision has no
`OPENROUTER_API_KEY`, and its legacy secret does not have the OpenRouter prefix.
The local environment also has no OpenRouter key. Only presence/prefix booleans
were inspected; no secret was displayed or copied. No paid OpenRouter call has
been made during this provider correction.

`probe_hosted_explanation.py --revision <revision>` now refuses the legacy
adapter, rather than making another Foundry call. Once the new backend and its
secret are configured, it tests one short real-code explanation through
OpenRouter. `--local` tests this checkout with its environment key. Neither
variant exercises the new HTTP route, which needs an end-to-end test too.

The owner then clarified the intended bring-your-own-key UI. That is now
implemented for both web model actions and covered by request-isolation and
browser tests using dummy credentials. The missing server environment key is
not a deployment blocker. A real provider test still requires a user-supplied
key; no paid call is claimed from a mock.

The owner approved a dedicated Azure Linux VM for live Coq. It uses the
[dedicated worker deployment](deploy/README.md), with a non-root read-only
container, request isolation and HTTPS. Foundry authorization and a shared
OpenRouter key are not prerequisites. The old Container Apps endpoint is not
the default. Publication requires the deployed proof and isolation checks;
never disable isolation to bypass a failed probe.
