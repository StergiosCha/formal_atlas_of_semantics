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
The VM's system-assigned identity has `AcrPull` on `formalatlasacr` only.
Registry login material is confined to a temporary root-only directory under
`/run` and removed after the pull. No visitor OpenRouter keys are configured
as VM secrets or stored in the service environment.

Image: `formalatlasacr.azurecr.io/atlas-checker@sha256:92af29f43f427775b139746f1a7cb56596cd38fc21a6981efdc58b536b5d74eb`.
Built by ACR run `ca7` from application commit `2c45392`, compiling the unchanged
published 87-file library. Unpublished theory additions in the research checkout
are not part of this release.

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
There is no
unrestricted execution fallback. A host firewall rule also blocks containers
from Azure's instance-identity endpoint.

## Checks and updates

Run `python3 tool/checker/smoke_deployed.py --backend <endpoint> --site <site-url>`
after rollout. It verifies matching source fingerprints, real goals, valid and
invalid proofs, full original-file compilation, origin restrictions, and missing
user-key rejection. It makes no paid model call. A successful model explanation
requires a visitor's key and is always unverified, independently of Coq results.

Inspect services using Azure Run Command; no SSH opening is necessary. Use
`systemctl status atlas-coq caddy atlas-metadata-guard` and
`journalctl -u atlas-coq` without printing request headers or environment values.

For the next source release, build the new image, update the pinned image in
both deployment files and VM service, and rerun the checks before publishing the
matching site. A static-site push alone does not update the worker's library.
The source fingerprint deliberately rejects mismatched releases.
