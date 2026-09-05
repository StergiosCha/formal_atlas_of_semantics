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
import json
import os
import re
import subprocess
import tempfile
import uuid

from fastapi import FastAPI
from pydantic import BaseModel

REPO = os.environ.get("ATLAS_REPO", "/atlas")
ATLAS_JSON = os.environ.get(
    "ATLAS_JSON", os.path.join(REPO, "atlas.json"))
COQ_FLAGS = ["-R", f"{REPO}/shallow", "", "-R", f"{REPO}/deep", "",
             "-R", f"{REPO}/extras", "", "-R", f"{REPO}/ttr_mtt", "",
             "-R", f"{REPO}/atlas", ""]
TIMEOUT_S = int(os.environ.get("CHECK_TIMEOUT", "30"))
MAX_CODE = 200_000

app = FastAPI(title="Semantics Workbench checker")


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

    audit: dict[str, str] = {}
    if ok and req.audit:
        # Print Assumptions blocks appear in stdout in order
        chunks = output.split("Axioms:")
        closed = output.count("Closed under the global context")
        for i, name in enumerate(req.audit):
            if i < closed and len(chunks) == 1:
                audit[name] = "closed"
            else:
                audit[name] = "see output"  # conservative: report raw
        if closed == len(req.audit) and "Axioms:" not in output:
            audit = {n: "closed" for n in req.audit}
    return {"ok": ok, "output": output[-20_000:], "audit": audit}
