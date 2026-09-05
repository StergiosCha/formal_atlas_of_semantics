# FORMAL ATLAS — hosting architecture

The instinct "we need an LLM and Coq, so we need a real server" is half wrong.
Three surfaces, and only one of them genuinely needs a running process.

---

## 1. The atlas + theory pages → static, free

`atlas.json`, the 64 records and the 7 edges are files. The graph view, the
theory pages, the comparison tables, the search — all of it is a static site
reading JSON. Cloudflare Pages or GitHub Pages, free, no backend, no cold
start, CDN-fast, and it survives us not paying a bill.

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
| **Vercel** (Hobby) | 2 GB / 1 vCPU, 300 s max duration, 5 GB bundle, free within limits, non-commercial | **Recommended.** Now a first-class container target: drop a `Dockerfile.vercel` in the repo root, it builds into Vercel Container Registry and gets snapshotted for fast boot. Scales to zero (prod idles down after 5 min). Billed on *Active CPU* — waiting on the LLM API costs nothing, which is exactly our proxy's profile. Same project as the static site, preview deploy per commit. |
| **Azure Container Apps** | 180,000 vCPU-s + 360,000 GiB-s + 2M requests/month | **Best fallback.** That grant is ~50 vCPU-hours/month = roughly 9,000 twenty-second Coq compiles, free, every month. Plain Docker, scale-to-zero, no duration cap. More ops surface than Vercel, and worth a look because university Azure credit may already be available. |
| **Hetzner CX22** | — €3.79/mo | 2 vCPU / 4 GB always warm, no cold start, and the only option here that permits **one throwaway container per request** (Docker-in-Docker). Pick this if per-request container isolation becomes a requirement. |
| **Render** | 512 MB, spins down after 15 min, **~60 s cold start**, 750 h/month | **Rejected for the free tier.** A minute of loading screen on a link someone shared is fatal for an academic demo. Render paid ($7/mo, always-on, no scale-to-zero) is fine but strictly worse value than Hetzner. Render's real strengths — workers, cron, persistent disks, unlimited WebSockets — are things we don't need. |

**Recommendation: Vercel for all three surfaces.** Static site, precomputed
proof states, and the container function in one repo, one deploy, free on
Hobby. If the Coq image proves awkward on Fluid compute or usage outgrows
Hobby, lift the same `Dockerfile` to Azure Container Apps — that migration is
a day, and nothing in the frontend changes.

The real budget line is the LLM, not the hosting. Cap it: rate-limit per IP,
cache identical statements, and use a small model for the draft with a larger
one only on retry after a compile failure.

---

## Sandboxing user Coq (non-negotiable)

`coqc` has no shell escape in a plain run, so the threat is not code execution
but **resource exhaustion**, which is one line away (`Eval compute in 2^100000`).
Required either way:

- wall-clock timeout (~20 s), enforced by the supervisor, not by Coq
- `rlimit` on address space and CPU for the `coqc` child process
- `Require` restricted to the prebuilt atlas `.vo` set — no `-I` plugin
  loading, no `Declare ML Module`, no `Extraction` to disk
- scratch files in a tmpfs, wiped per request
- rate limit per IP

**Platform caveat.** On Vercel and Azure Container Apps you get one container
and cannot spawn a throwaway container per request — isolation comes from the
platform's own invocation sandbox, and concurrent requests may share an
instance. That is acceptable for Coq specifically, because the rlimit +
timeout pair addresses the only realistic attack. If you later want true
per-request container isolation (say, to allow user-supplied `Require`), that
needs a VM with Docker — Hetzner — and is the one scenario that changes the
recommendation.

---

## Deployment shape

```
Vercel (static) ────── site + atlas.json + records + proofstates
        │
        └── fetch() ──→ /api/check  (Vercel container function)
                              ├── LLM proxy (key lives here)
                              └── coqc runner (ephemeral sandboxed container)
```

CI (GitHub Actions) on every push: `make -k -j8` → verifier pass →
proofstate dump → publish static bundle. The backend image rebuilds only when
the atlas `.v` files change.
