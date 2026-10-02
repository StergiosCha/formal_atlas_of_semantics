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
│ llm         tool/llm: OpenRouter model loop using GUIDE.md    │
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

All LLM requests use OpenRouter, including explanation and proof drafting.
The roster maps stable application aliases to explicit provider IDs, for example
`gpt-6-astra` to `openai/gpt-6-astra` and `gpt-5.4-pro-2` to `openai/gpt-5.4-pro`.
The frontend displays the OpenRouter IDs. Sol, GPT-5.5, GPT-5.4/Pro/Mini, Grok 4.3,
DeepSeek V4 Flash/Pro, Kimi K2.6, Mistral Medium 3 and Cohere Command A+ are included.
MAI Thinking and the old Grok fast alias are not offered: corresponding routes
were not found in OpenRouter's public catalog on 2026-10-02. No substitute is
silently selected. Catalog presence does not establish paid account access.

Visitors enter their own key in the **Your OpenRouter API key** password field
on the editor or Verifier page. Their OpenRouter account pays for model calls.
The key is held only in the current page, not local/session storage. Clear key,
reload or navigation clears it. It is sent in `X-OpenRouter-Key` to the displayed
backend only for Explain or Draft & check, never for a Coq-only request.
Only use a trusted backend. The backend forwards it as bearer authentication
to `https://openrouter.ai/api/v1/chat/completions`, without storing it in the
environment, logs or a shared cache. Web calls require the user's key and never
fall back to a server-funded key. Trusted CLI calls can still use
`OPENROUTER_API_KEY` from their own environment.
There is no Foundry route or Azure credential fallback. No key is embedded in
the published site, passed to Coq, or printed in provider errors. Redirects are refused.
Incomplete, refusal-only, tool-call and empty replies are rejected.
Restart/rebuild the checker to update its
roster; deploying the static site alone does not change backend model options.
The site's default backend is the deployed Azure checker. For local development,
set the Verifier's Backend field to `http://localhost:8477`; that browser override
is retained in local storage.

Contract reference: [OpenRouter API](https://openrouter.ai/docs/api/reference/overview).

Offline tests: `python3 tool/llm/test_providers.py -v`. An authorized single live
explanation can be tested with `python3 tool/checker/probe_hosted_explanation.py --local`
after a CLI environment key is configured. This optional diagnostic is not a
deployment requirement. The hosted variant accepts
`--revision <revision>` and refuses to call a legacy Foundry adapter.

## Status

The [live workspace](WORKSPACE.md) now adds editable copies, real Coq prefix
goals and full-copy checks, and selected-code explanations. Backend sandbox
support and a matching library image are required before production activation.
The old public checker and draft loop now also fail closed without isolation.

- [x] checker service (tool/checker/server.py, Dockerfile)
- [x] LLM loop skeleton + policy (tool/llm/loop.py, policy.md)
- [ ] frontend map/phenomenon views (extend
      ../formalizing_formal_semantics/atlas/site/template.html; the
      data — atlas.json with `files` and `edges` — is already shaped
      for it)
- [ ] jsCoq in-browser fallback for classroom mode
- [ ] referee-mode upload pipeline (paper PDF -> GUIDE partition)
