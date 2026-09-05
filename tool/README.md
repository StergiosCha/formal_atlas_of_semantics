# Semantics Workbench (v0 scaffold)

A tool for formal semanticists: **educational explorer + mechanical
verifier**, built on the FORMAL-ATLAS Coq library in this repository.

## Architecture (three tiers)

```
┌───────────────────────────────────────────────────────────────┐
│ frontend  — the atlas site (atlas.json + edges), grown into:  │
│   • the MAP: framework graph, edges colored by similarity,    │
│     click-through to per-phenomenon grades and theorems       │
│   • the PHENOMENON view: one sentence (e.g. the donkey)       │
│     side-by-side in DPL / Ranta / DTS / MTT / PTQ             │
│   • the PLAYGROUND: RSA calculator, InqB support checker      │
│     (every value backed by the exact-rational theorems)       │
├───────────────────────────────────────────────────────────────┤
│ checker   — tool/checker: FastAPI service wrapping coqc with  │
│   the atlas .vo files precompiled; POST /check returns the    │
│   compiler verdict + Print Assumptions audit for user code    │
├───────────────────────────────────────────────────────────────┤
│ llm       — tool/llm: Claude API loop implementing GUIDE.md   │
│   (the reading protocol): draft Coq for a paper fragment,     │
│   check it, iterate; output the PROVED / REFUTED /            │
│   NEEDS_ASSUMPTION / NOT-STATABLE partition                   │
└───────────────────────────────────────────────────────────────┘
```

**Design rule: the LLM never grades; Coq grades.** Every green check in
the UI is a `Qed` behind the scenes; the LLM only proposes.

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

## Status

- [x] checker service (tool/checker/server.py, Dockerfile)
- [x] LLM loop skeleton + policy (tool/llm/loop.py, policy.md)
- [ ] frontend map/phenomenon views (extend
      ../formalizing_formal_semantics/atlas/site/template.html; the
      data — atlas.json with `files` and `edges` — is already shaped
      for it)
- [ ] jsCoq in-browser fallback for classroom mode
- [ ] referee-mode upload pipeline (paper PDF -> GUIDE partition)
