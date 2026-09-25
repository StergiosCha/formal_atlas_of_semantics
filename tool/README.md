# Semantics Workbench (v0 scaffold)

A tool for formal semanticists: **educational explorer + mechanical
verifier**, built on the FORMAL-ATLAS Coq library in this repository.

## Architecture (three tiers)

```
┌───────────────────────────────────────────────────────────────┐
│ frontend  — the atlas site (atlas.json + edges), grown into:  │
│   • the MAP: scoped comparison profiles with evidence,       │
│     click-through to scoped statements and actual proofs    │
│   • the PHENOMENON view: one sentence (e.g. the donkey)       │
│     side-by-side in DPL / Ranta / DTS / MTT / PTQ             │
│   • the PLAYGROUND: RSA calculator, InqB support checker      │
│     (every value backed by the exact-rational theorems)       │
├───────────────────────────────────────────────────────────────┤
│ checker   — tool/checker: FastAPI service wrapping coqc with  │
│   the atlas .vo files precompiled; POST /check returns the    │
│   compiler verdict + Print Assumptions audit for user code    │
├───────────────────────────────────────────────────────────────┤
│ llm       — tool/llm: Foundry model loop using GUIDE.md       │
│   (the reading protocol): draft Coq for a paper fragment,     │
│   check it, iterate; output the PROVED / REFUTED /            │
│   NEEDS_ASSUMPTION / NOT-STATABLE partition                   │
└───────────────────────────────────────────────────────────────┘
```

**Design rule: the LLM proposes; Coq checks the proof artifact.** Theory-level
relationships and source fidelity need separate assessment. Historical edge
annotations are not grades computed or certified by Coq.

## Quick start

```
docker compose -f tool/docker-compose.yml up --build
# POST a lemma against the atlas:
curl -s localhost:8477/check -H 'content-type: application/json' -d '{
  "imports": ["probabilistic.RSA"],
  "code": "Lemma my_check : (1#2) + (1#2) == 1. Proof. vm_compute; reflexivity. Qed."
}'
```

The checker container builds the whole `_CoqProject` once at image
build; user snippets then compile in well under a second.

## Model selection

The backend's `/models` endpoint supplies the frontend picker from
`llm/models.json`. Claude is no longer callable. Select `gpt-6-astra` for
the requested flagship; the existing default remains `gpt-5.4-mini`.
The escalation policy names Astra, but the current loop does **not** switch
models automatically: it uses your selected model for every repair round.

The roster also includes Sol, GPT-5.4/Pro, Grok, DeepSeek Flash/Pro,
Mistral Medium, MAI Thinking, Cohere Command and the retained GPT-5.5/Kimi
options. New entries use the deployment names supplied on 2026-09-19;
`gpt-5.4-pro-2` is intentional. Existing non-Claude entries are preserved,
including those not visible on that first page of Foundry deployments.
OCR, embeddings, image and video deployments are not proof drafters.
Availability of newly added deployments still needs a live smoke test.

Set `AZURE_AI_KEY` in the backend environment only. `AZURE_AI_ENDPOINT`
is the resource root (default `https://crete-xamoulis-resource.services.ai.azure.com`),
not the project endpoint or the `/openai/v1` URL. Astra and GPT-5.4 Pro use
`/openai/v1/responses`; other models retain their existing chat routes.
No key is embedded in the site. Restart/rebuild the checker to update its
roster; deploying the static site alone does not change backend model options.
The site's default backend is the deployed Azure checker. For local development,
set the Verifier's Backend field to `http://localhost:8477`; that browser override
is retained in local storage.

Compatibility reference: [official Astra migration guidance](https://developers.openai.com/api/docs/guides/latest-model/gpt-6-astra#migration-quickstart).

## Status

- [x] checker service (tool/checker/server.py, Dockerfile)
- [x] LLM loop skeleton + policy (tool/llm/loop.py, policy.md)
- [ ] frontend map/phenomenon views (extend
      ../formalizing_formal_semantics/atlas/site/template.html; the
      data — atlas.json with `files` and `edges` — is already shaped
      for it)
- [ ] jsCoq in-browser fallback for classroom mode
- [ ] referee-mode upload pipeline (paper PDF -> GUIDE partition)
