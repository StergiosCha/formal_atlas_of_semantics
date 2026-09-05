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

from fastapi import FastAPI, Request
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
    "ATLAS_JSON", os.path.join(REPO, "atlas.json"))
COQ_FLAGS = ["-R", f"{REPO}/shallow", "", "-R", f"{REPO}/deep", "",
             "-R", f"{REPO}/extras", "", "-R", f"{REPO}/ttr_mtt", "",
             "-R", f"{REPO}/atlas", ""]
TIMEOUT_S = int(os.environ.get("CHECK_TIMEOUT", "30"))
MAX_CODE = 200_000

app = FastAPI(title="Formalizing Formal Semantics — checker")
app.add_middleware(CORSMiddleware, allow_origins=["*"],
                   allow_methods=["*"], allow_headers=["*"])

# The LLM is the budget line (HOSTING.md): cache identical requests, cap
# per-IP fan-out. In-memory is fine for a single scale-to-zero replica.
_VERIFY_CACHE: dict[str, dict] = {}
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
def check(req: CheckRequest):
    if len(req.code) > MAX_CODE:
        return {"ok": False, "output": "snippet too large", "audit": {}}
    for imp in req.imports:
        if not IMPORT_RE.match(imp):
            return {"ok": False, "output": f"bad import: {imp}", "audit": {}}
    for name in req.audit:
        if not NAME_RE.match(name):
            return {"ok": False, "output": f"bad name: {name}", "audit": {}}

    header = "".join(f"Require Import {imp}.\n" for imp in req.imports)
    footer = "".join(f"Print Assumptions {n}.\n" for n in req.audit)
    body = header + req.code + "\n" + footer

    with tempfile.TemporaryDirectory() as tmp:
        # coqc requires a valid module name
        vname = os.path.join(tmp, "Check_" + uuid.uuid4().hex[:8] + ".v")
        with open(vname, "w") as f:
            f.write(body)
        try:
            proc = subprocess.run(
                ["coqc", *COQ_FLAGS, "-R", tmp, "", vname],
                capture_output=True, text=True, timeout=TIMEOUT_S,
                cwd=tmp)
        except subprocess.TimeoutExpired:
            return {"ok": False, "output": f"timeout after {TIMEOUT_S}s",
                    "audit": {}}

    ok = proc.returncode == 0
    output = (proc.stdout or "") + (proc.stderr or "")
    import check_local
    audit = check_local.parse_audit(output, req.audit) if ok else {}
    return {"ok": ok, "output": output[-20_000:], "audit": audit}


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
    return {"models": [{"deployment": m["deployment"], "family": m["family"],
                        "role": m["role"]} for m in providers.CFG["roster"]],
            "default": providers.POLICY["first_draft"],
            "max_rounds": providers.POLICY["max_rounds"]}


@app.post("/verify")
def verify(req: VerifyRequest, request: Request):
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

    ck = hashlib.sha256(
        f"{req.claim}|{model}|{sorted(req.imports)}|{arm}|{rounds}".encode()
    ).hexdigest()
    if ck in _VERIFY_CACHE:
        return {**_VERIFY_CACHE[ck], "cached": True}

    turns = []
    def log(rnd, draft, check_res, state):
        turns.append({"round": rnd,
                      "signals": (check_res or {}).get("signals", []),
                      "ok": (check_res or {}).get("ok")})
    try:
        state = loop.one_run(req.claim, model, arm, rounds,
                             req.imports, None, log)
    except Exception as e:  # a dead model must not 500 the service
        return {"error": f"loop failed: {type(e).__name__}: {e}", "bucket": None}
    out = {"bucket": state.get("bucket"), "model": model, "arm": arm,
           "rounds": state.get("rounds"), "audit": state.get("audit", {}),
           "code": state.get("code"), "notes": state.get("notes"),
           "error": state.get("error"), "turns": turns}
    if out["bucket"] and not out.get("error"):
        _VERIFY_CACHE[ck] = out
    return out
