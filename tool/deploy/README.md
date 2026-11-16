# Dedicated live Coq worker

Deployment target, approved 2026-10-02:

- Azure resource group: `formal-atlas`.
- VM: `atlas-coq-worker`, Ubuntu 22.04, `Standard_B2s_v2`, 64 GB Standard SSD.
- Public endpoint: `https://formal-atlas-coq-crete.westus2.cloudapp.azure.com`.
- Public ingress: TCP 80 and 443 only. SSH and port 8477 are not public.
- Site stays on Azure Static Web Apps. The former Container Apps checker is
  retained, but is not the site's default backend.
- The VM, disk and public IP incur hosting charges. They do not scale to zero.

## Reproduction

`cloud-init.yaml` installs Docker and defines the worker services. Run
`setup-worker.sh` through Azure Run Command after provisioning to install
Caddy from its signed upstream repository and enable automatic HTTPS.
`activate-worker.py` is the historical initial-release migration and privacy
test. Do not run it on the persistent-session release. `activate-sessions.py`
migrates the replay-only worker to the tested persistent-session image, retains
a root-only configuration backup, and restores the previous worker if its live
checks fail. Caddy's runtime-log filter removes
request headers and response headers; access logging is not enabled.
The VM's system-assigned identity has `AcrPull` on `formalatlasacr` only.
Registry login material is confined to a temporary root-only directory under
`/run` and removed after the pull. No visitor OpenRouter keys are configured
as VM secrets or stored in the service environment.

Current image, active since 15 November 2026 (UTC):
`formalatlasacr.azurecr.io/atlas-checker@sha256:dbb6e5535a21197e3b10afb84acee566cb1d9e94cb3de736be4a05e241dd44ae`.
Built by ACR run `cad` from commit `c64ac19` with `tool/checker/Dockerfile`
(the full build, since the library changed). It contains Coq 8.20.1, coq-lsp
package `0.2.5+8.20` and the published 91-file library, whose fingerprint is
`2777e8513cbb5e4e75a4d93410272396e49c938cf1e62b965b85568c860f5c5f`. The
runtime code is unchanged from the persistent-session release. See
"Library release, 2026-11-15" below.

Previous image (persistent sessions, 87-file library), retained on the VM for
rollback: `formalatlasacr.azurecr.io/atlas-checker@sha256:a3a858b2e91c781dd45e07a734e1f0287901260ee5c95b6fc35577aef27e57d8`.
Built by ACR run `cac`, with the runtime implementation in commit `a5bd0ed`,
on the fully compiled toolchain/library base from run `caa`. See
`../SESSION_VALIDATION.md` for its candidate tests.

Older rollback image, also retained on the VM:
`formalatlasacr.azurecr.io/atlas-checker@sha256:31a276f63ef8bb9c21d9d739632e38559a64a379f2960bcf7606b20301ddf8b6`.
The activator prints its root-only backup directory. To roll back, restore
`atlas-pull` and `atlas-coq.service` from that exact directory to their original
paths, run `systemctl daemon-reload`, and restart `atlas-coq`. The frontend
falls back to isolated replay when the worker does not advertise sessions.

## Isolation

The outer container runs as the image's unprivileged `coq` user, with all Docker
capabilities dropped, no-new-privileges, a read-only root filesystem, a bounded
temporary filesystem, process limits, 3 GB memory and a two-CPU ceiling.
It binds its API to host loopback only. Caddy terminates HTTPS and forwards to it.

Docker's seccomp and AppArmor filters are disabled for this container because
their defaults prevent nested user namespaces. This does not grant a privileged
container or host mounts. Every submitted Coq process is additionally confined
by bubblewrap's user, PID and network namespaces, its explicit read-only library
mounts, a per-request scratch directory and resource limits. There is no
`/proc` mount inside the sandbox: Coq does not need it, and Docker rejects
mounting a nested proc filesystem from this unprivileged user namespace.
There is no unrestricted execution fallback. A host firewall rule also blocks containers
from Azure's instance-identity endpoint.

Keep a single Uvicorn API worker: the private session registry is in memory.
Two Coq slots are available, and an open session reserves one until closed or
expired. Sessions expire after five idle minutes or thirty minutes total and
do not survive a worker restart. Full-file compilation remains a separate,
fresh `coqc` process. Visitor tokens are kept in tab memory only. See
`../WORKSPACE.md` for limits and the distinction between a checked prefix and
a compiled file.

## Checks and updates

Run `python3 tool/checker/smoke_deployed.py --backend <endpoint> --site <site-url>`
after rollout. It verifies matching source fingerprints, real goals, valid and
invalid proofs, full original-file compilation, origin restrictions, and missing
user-key rejection. It makes no paid model call. A successful model explanation
requires a visitor's key and is always unverified, independently of Coq results.

Run `probe-sandbox.sh` through Azure Run Command to check filesystem isolation.
It creates a temporary Coq fixture outside the sandbox, first proves the exact
`Load` command succeeds in the outer container, then checks that the running
API rejects that command. The temporary fixture is removed afterwards.
Run `smoke_public.py --backend <endpoint> --site <site-url> --require-sessions`
to test the deployed editor in a browser with real persistent Coq and mocked
model output. It releases its own test sessions even when a check fails. Run
public API and browser tests sequentially to respect the two-slot capacity.

Inspect services using Azure Run Command; no SSH opening is necessary. Use
`systemctl status atlas-coq caddy atlas-metadata-guard` and
`journalctl -u atlas-coq` without printing request headers or environment values.

For the next source release, build the new image, update the pinned image in
both deployment files and VM service, and rerun the checks before publishing the
matching site. A static-site push alone does not update the worker's library.
The source fingerprint deliberately rejects mismatched releases.

## Hosted checks, 2026-10-03

The VM was restarted after its installed security updates. The HTTPS API passed
real prefix-goal, complete-proof, invalid-proof, original-file compilation,
source-mismatch, origin and missing-key checks against the 87-file snapshot.
The controlled filesystem canary also passed: the same existing `.v` loaded
outside the sandbox but was inaccessible through the running API. The test
removed its temporary fixture. These checks made no paid model calls.

GitHub run `37110601530` passed compilation, independent kernel checking,
mechanical audits and deployment for revision `d2f9553`. The published site's
source fingerprint matched the worker. The public-browser smoke test passed
real goals, valid and invalid proof checks, missing-key rejection, inert model
text rendering, no browser key storage, key clearing on reload, and mobile
layout. Only the model response was mocked. The browser test explicitly selects
code after filling the dummy key field, because filling another field can
collapse the textarea selection. No paid OpenRouter response is claimed.

## Persistent worker rollout, 2026-10-03

The persistent-session image above is active on the dedicated VM. Activation
passed live forward/back steps, invalid `Qed` rejection, Unicode and independent
full-file compilation. Public HTTPS API checks also passed against the existing
site's unchanged library fingerprint, including session closure, original-file
compilation, source mismatch, origin restrictions and missing-key rejection.
The previous image is retained. The activation backup is
`/var/lib/atlas-deployments/persistent-20261003-51bcl55r` on the VM.
This section records worker activation only. Confirm frontend publication from
the deployed site's revision, a successful CI run for that revision, and the
public-browser smoke test. Worker checks alone do not establish publication.

## Library release, 2026-11-15

The library grew from 87 to 91 files (`Donkey_Sums.v`, `Lambek_Count.v`,
`Lambek_Decision.v`, `DRT_to_DPL.v`), so the worker needed a new image.

1. ACR run `cad` built the image above from a clean export of commit `c64ac19`
   in 29 minutes; all 91 files compiled.
2. `test-sessions.py` pulled the candidate on the VM and ran its 23 tests in a
   separate container without network. All passed; production was unchanged.
3. `activate-release.py` moved the service to the new image. It takes the old
   and new images and library fingerprints as arguments, keeps a root-only
   configuration backup, and restores the previous worker if a check fails.
   Its in-container session test passed. The backup is
   `/var/lib/atlas-deployments/release-20261115-awhrzyvw` on the VM.
4. The public endpoint reports the new library fingerprint, which is the one
   in the site published from `c64ac19`.
5. `smoke_deployed.py` passed against the public endpoint and the published
   site: real Coq, persistent sessions, 91 sources, matching fingerprints,
   site revision `c64ac19`, no paid model call. The browser smoke test
   (`smoke_public.py`) was not run for this release.

A first activation attempt stopped at the script's argument check, before any
change, because the new image name had been passed incorrectly.

To roll back, restore `atlas-pull` and `atlas-coq.service` from the backup
directory above to their original paths, run `systemctl daemon-reload`, and
restart `atlas-coq`. The site would then again reject the worker as a
mismatched release.

## Library release, 2026-11-16

The library grew from 91 to 100 files (nine files under `atlas/mtt_ranta`,
`atlas/probabilistic`, `atlas/inquisitive` and `atlas/model_theoretic`), so
the worker needed a new image. The steps were those of the previous release.

1. ACR run `cae` built the image above from a clean export of commit `372264e`
   in 28 minutes; all 100 files compiled. Its library is that of the merge
   commit `0798ead`.
2. `test-sessions.py` ran its 23 tests on the candidate on the VM. All passed;
   production was unchanged.
3. `activate-release.py` moved the service to the new image and its
   in-container session test passed. The backup is
   `/var/lib/atlas-deployments/release-20261116-0zfkkr0u` on the VM.
4. `smoke_deployed.py` passed against the public endpoint and the published
   site: real Coq, persistent sessions, 100 sources, matching fingerprints,
   site revision `0798ead`, no paid model call. The browser smoke test
   (`smoke_public.py`) was not run for this release.

Between the site's publication and the activation, about an hour, the site
rejected the worker as a mismatched release. Rollback is as described above,
from the backup directory of this release.
