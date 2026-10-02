"""Semantics Workbench — Coq checker service.

POST /check  {"code": "...", "imports": ["probabilistic.RSA", ...],
              "audit": ["my_lemma", ...]}
  -> {"ok": bool, "output": str, "audit": {name: "closed"|str}}

GET /atlas   -> the consolidated atlas.json (for the frontend)
GET /health

The atlas .vo files are precompiled at image build (see Dockerfile), so
a user snippet importing them checks in well under a second. Snippets
run under a timeout in a scratch directory; nothing the user sends can
touch the library.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import uuid

from fastapi import FastAPI, HTTPException, Request
import isolation
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

# the draft-and-check loop lives next door (baked to /srv/llm in the image,
# ../llm in a checkout)
_LLM = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "llm")
for _cand in ("/srv/llm", os.path.abspath(_LLM)):
    if os.path.isdir(_cand):
        sys.path.insert(0, _cand)
        break

REPO = os.environ.get("ATLAS_REPO", "/atlas")
ATLAS_JSON = os.environ.get(
    "ATLAS_JSON", os.path.join(REPO, "atlas_data", "atlas.json"))
os.environ.setdefault("ATLAS_REPO", REPO)
os.environ.setdefault("ATLAS_JSON", ATLAS_JSON)
COQ_FLAGS = ["-R", f"{REPO}/shallow", "", "-R", f"{REPO}/deep", "",
             "-R", f"{REPO}/extras", "", "-R", f"{REPO}/ttr_mtt", "",
             "-R", f"{REPO}/atlas", ""]
TIMEOUT_S = int(os.environ.get("CHECK_TIMEOUT", "30"))
MAX_CODE = 200_000

app = FastAPI(title="Formalizing Formal Semantics — checker")
app.add_middleware(CORSMiddleware, allow_origins=["*"],
                   allow_methods=["*"], allow_headers=["*"])

from workspace import router as workspace_router, guard as workspace_guard, user_model_key, SLOTS
app.include_router(workspace_router)
# Both legacy public entry points also execute untrusted/model-proposed Coq.
# They must not bypass the sandbox used by the new editor. The separate CLI
# remains available for trusted local research runs.
os.environ["ATLAS_REQUIRE_SANDBOX"] = "1"

# User-funded model calls are request-scoped, never cached across visitors.
_IP_HITS: dict[str, list[float]] = {}
VERIFY_LIMIT_PER_HOUR = int(os.environ.get("VERIFY_LIMIT", "20"))


class CheckRequest(BaseModel):
    code: str
    imports: list[str] = []
    audit: list[str] = []   # names to Print Assumptions on


IMPORT_RE = re.compile(r"^[A-Za-z0-9_.]+$")
NAME_RE = re.compile(r"^[A-Za-z0-9_.']+$")


@app.get("/health")
def health():
    return {"ok": True}


@app.get("/atlas")
def atlas():
    with open(ATLAS_JSON) as f:
        return json.load(f)


@app.post("/check")
def check(req: CheckRequest, request: Request):
    workspace_guard(request, "check")
    import check_local
    if not SLOTS.acquire(blocking=False):
        return {"ok": False, "output": "Coq workers are busy; try again shortly", "audit": {}}
    try:
        return check_local.check(req.code, req.imports, req.audit)
    finally:
        SLOTS.release()


class VerifyRequest(BaseModel):
    claim: str
    model: str = ""
    imports: list[str] = []
    feedback: str = "typed"      # E2 ablation arm: none | raw | typed
    rounds: int = 4


@app.get("/models")
def models():
    """The roster the frontend's model picker renders. Only deployments in
    tool/llm/models.json are callable — the list is the allowlist."""
    import providers
    return {"provider": providers.CFG["provider"],
            "models": [{"deployment": m["deployment"], "model": m["model"], "family": m["family"],
                        "role": m["role"]} for m in providers.CFG["roster"]],
            "default": providers.POLICY["first_draft"],
            "max_rounds": providers.POLICY["max_rounds"]}


@app.post("/verify")
def verify(req: VerifyRequest, request: Request):
    workspace_guard(request, "explain")
    api_key = user_model_key(request)
    if not isolation.capability(REPO)["available"]:
        raise HTTPException(503, "Live Coq is unavailable on this host. No model call was made. Selected-code explanations remain available.")
    if not SLOTS.acquire(blocking=False):
        return {"error": "Workspace is busy; try again shortly", "bucket": None}
    try:
        return _verify(req, request, api_key=api_key)
    finally:
        SLOTS.release()


def _verify(req: VerifyRequest, request: Request, *, api_key: str):
    """The full neurosymbolic loop, server-side: the chosen model drafts,
    coqc disposes, typed feedback drives repair. The reply carries the
    compiler's verdict; any model-only claim is labeled *_MODEL_CLAIMED_
    UNVERIFIED by the loop and rendered as such."""
    import loop
    import providers

    ip = (request.headers.get("x-forwarded-for") or
          (request.client.host if request.client else "?")).split(",")[0]
    now = time.time()
    hits = [t for t in _IP_HITS.get(ip, []) if now - t < 3600]
    if len(hits) >= VERIFY_LIMIT_PER_HOUR:
        return {"error": f"rate limit: {VERIFY_LIMIT_PER_HOUR}/hour", "bucket": None}
    _IP_HITS[ip] = hits + [now]

    model = req.model or providers.POLICY["first_draft"]
    if model not in providers.ROSTER:
        return {"error": f"unknown model {model}", "bucket": None}
    if len(req.claim) > 4000:
        return {"error": "claim too long", "bucket": None}
    arm = req.feedback if req.feedback in ("none", "raw", "typed") else "typed"
    rounds = max(1, min(req.rounds, 6))

    turns = []
    def log(rnd, draft, check_res, state):
        turns.append({"round": rnd,
                      "signals": (check_res or {}).get("signals", []),
                      "ok": (check_res or {}).get("ok")})
    try:
        state = loop.one_run(req.claim, model, arm, rounds,
                             req.imports, None, log, api_key=api_key)
    except Exception as e:  # a dead model must not 500 the service
        return {"error": f"loop failed: {type(e).__name__}; no verified result", "bucket": None}
    out = {"bucket": state.get("bucket"), "model": model, "arm": arm,
           "rounds": state.get("rounds"), "audit": state.get("audit", {}),
           "code": state.get("code"), "notes": state.get("notes"),
           "error": state.get("error"), "turns": turns}
    return out
