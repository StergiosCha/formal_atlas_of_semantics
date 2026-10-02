# FORMAL ATLAS — hosting architecture

Current deployment: the site remains on Azure Static Web Apps; live Coq uses
the [dedicated Linux VM](../tool/deploy/README.md), approved on 2026-10-02.
The editor's OpenRouter assistant uses each visitor's request-scoped key.
The Container Apps design below is historical: its namespace policy rejected
the live workspace sandbox, so it is no longer the default execution host.

The instinct "we need an LLM and Coq, so we need a real server" is half wrong.
Three surfaces, and only one of them genuinely needs a running process.

---

## 1. The atlas + theory pages → static, free

`atlas.json`, the 64 records and the 7 edges are files. The graph view, the
theory pages, the comparison tables, the search — all of it is a static site
reading JSON. Azure Static Web Apps Free tier — no backend, no cold start,
CDN-fast, free SSL on a custom domain, and it survives us not paying a bill.

## 2. The proof reader → ALSO static (this is the trick)

The Proof-General-style stepping — locked amber region, goal pane, step
forward/back — looks like it needs a live `coqtop`. It does not, because our
twelve atlas files are **fixed and version-controlled**. The proof states are
therefore *build artifacts*, not runtime state.

In CI, after `make`, run each file through SerAPI (`sertop`) or `coq-lsp` and
dump the goal state after every sentence:

```
proofstates/atlas__rsa.json
  [ {sentence: "intros n H.", start: 4213, end: 4228,
     goals: [{hyps: [...], concl: "..."}]}, ... ]
```

Ship that JSON with the static site. Stepping becomes an array index. Zero
servers, instant response, works offline, and it can never drift from the
source because CI regenerates it on every push. This is strictly better than
jsCoq for our case: no 40MB wasm download, no version pinning, no 1900-line
file choking the browser.

The same artifact powers `Print Assumptions` badges and the theorem counts, so
it doubles as the **verifier pass** (ROADMAP A3). Build it once, use it twice.

## 3. The verifier (user-submitted Coq) + LLM → the only real backend

This is the one surface that must run a process, because the user's claim is
not known ahead of time. One stateless endpoint:

```
POST /check   { theory: "rsa", statement: "..." }  →  { verdict, output, goals }
```

It holds the LLM API key (which is the actual reason it can't be browser-side)
and shells out to `coqc` against a prebuilt atlas `.vo` set.

---

## Where to run #3

Checked 2026-09-05 against the providers' own docs.

| Option | Free allowance | Verdict |
|---|---|---|
| **Azure Container Apps** | 180,000 vCPU-s + 360,000 GiB-s + 2M requests/month, per subscription | **Chosen.** Plain Docker, scale-to-zero, no duration cap, up to 4 vCPU / 8 GiB per replica on Consumption. The grant is ~50 vCPU-hours/month ≈ 9,000 twenty-second Coq compiles. We hold Azure credits, which makes this free twice over. |
| **Vercel** (Hobby) | 2 GB / 1 vCPU, 300 s max, 5 GB bundle, non-commercial | Strong runner-up. `Dockerfile.vercel` is a first-class container target, snapshotted for fast boot, Active-CPU billed so LLM wait time is free. Would have been the pick without Azure credits. |
| **Hetzner CX22** | — €3.79/mo | 2 vCPU / 4 GB always warm, and the only option here permitting **one throwaway container per request**. Pick only if per-request container isolation becomes a hard requirement. |
| **Render** | 512 MB, spins down after 15 min, **~60 s cold start**, 750 h/month | **Rejected.** A minute of loading screen on a shared link is fatal for an academic demo. Paid Render is fine but worse value than Hetzner, and its strengths (workers, cron, disks, WebSockets) are things we don't need. |

**Decision: Azure end to end.** Azure Static Web Apps (Free tier) for the site
and the precomputed proof states, Azure Container Apps for `/check`.

### Design for the grant, not the credits

The important discipline: **architect so the thing survives the credits running
out.** Student/academic credits expire and take the subscription with them; the
180,000 vCPU-second monthly grant does not. So:

- `--min-replicas 0` — scale to zero is what keeps us inside the grant
- small replicas (0.5 vCPU / 1 GiB is enough for `coqc` on our files)
- cache identical `/check` requests so a shared link doesn't recompile

Credits are then headroom for the one thing scale-to-zero costs us: cold start.
While credits last, run `--min-replicas 1` to keep a replica warm (billed at
Azure's reduced *idle* rate, well under the active rate). Drop it back to 0
when they run out and the service keeps working, just with a few seconds of
first-request latency. Check the Azure pricing calculator for your region's
actual idle and active rates — the pricing page renders them dynamically and
they vary by region.

### Deployment recipe

Status on 2026-10-02: the current Container Apps host denies the namespaces
required by the new live workspace. The recipe below records the original
hosting setup, not an approved deployment target for arbitrary visitor code.
See [workspace preflight](../tool/WORKSPACE.md#hosted-preflight-2026-10-02).
LLM routing is now OpenRouter, independent of where the Coq worker is hosted.

```bash
az extension add --name containerapp --upgrade
az provider register -n Microsoft.App
az provider register -n Microsoft.OperationalInsights

az group create -n formal-atlas -l westeurope        # closest region to Greece
az containerapp env create -n atlas-env -g formal-atlas -l westeurope

# builds the Dockerfile in the cloud (ACR Tasks) — no local Docker needed
az containerapp up -n atlas-checker -g formal-atlas \
  --environment atlas-env --source ./tool \
  --ingress external --target-port 8080

# No shared model secret: visitors enter their own OpenRouter key in the UI.
# The backend handles it only for the individual model request.

# scale-to-zero, capped fan-out, one of the allowed cpu/memory pairs
az containerapp update -n atlas-checker -g formal-atlas \
  --min-replicas 0 --max-replicas 5 --cpu 0.5 --memory 1.0Gi
```

Consumption CPU/memory must be one of the allowed pairs — 0.25/0.5Gi,
0.5/1Gi, 0.75/1.5Gi, 1/2Gi … up to 2/4Gi (4 vCPU / 8 GiB on the larger
workload profiles). Arbitrary combinations are rejected at deploy time.

Frontend:

```bash
az staticwebapp create -n formal-atlas-site -g formal-atlas \
  -s https://github.com/StergiosCha/formal_atlas_of_semantics \
  -b main --login-with-github --app-location "site"
```

Static Web Apps Free tier includes custom domains with free SSL. Its app-size
cap is comfortable for the site plus proof-state JSON, but if the dumps grow
past it, move `proofstates/` to Azure Blob Storage with static-website hosting
and fetch them from there — they're immutable per commit, so they cache well.

The real budget line is the LLM, not the hosting. Cap it: rate-limit per IP,
cache identical statements, and use a small model for the draft with a larger
one only on retry after a compile failure.

---

## Sandboxing user Coq (non-negotiable)

Do not treat Coq as a safe text evaluator. File access, loaded native plugins,
process behavior and resource exhaustion all matter for visitor-supplied code.
A timeout, a scratch directory or an empty child environment alone does not
isolate it from the service's credentials or other requests.

The [live workspace](../tool/WORKSPACE.md) requires an OS-isolated child with
read-only library/runtime mounts, a writable per-request scratch directory,
no provider credentials, no network, process cleanup and resource limits.
The legacy public checker and draft loop use the same isolation requirement.

Linux uses bubblewrap. Confirm usable user, PID and network namespaces on the
actual deployment platform. Installing bubblewrap in an Azure Container Apps
image does not establish that the platform permits it. If the probe fails,
the new service refuses execution. Use a suitable worker deployment; never
substitute an unrestricted subprocess to make a deployment appear functional.
Local macOS tests use sandbox-exec and do not certify Linux compatibility.

---

## Deployment shape

```
Azure Static Web Apps ──── site + atlas.json + records + proofstates
   (Free tier, CDN)            │
                               └── fetch() ──→ Azure Container Apps
                                                 atlas-checker (min-replicas 0)
                                                 ├── LLM proxy (key = ACA secret)
                                                 └── coqc runner (rlimit + timeout)
```

CI (GitHub Actions) on every push: `make -k -j8` → verifier pass →
proofstate dump → publish static bundle. The backend image rebuilds only when
the atlas `.v` files change.
