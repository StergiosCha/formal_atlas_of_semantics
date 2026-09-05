"""Local checker — the POST /check contract without the server.

Same request/response shape as tool/checker/server.py, but shells out to
coqc against this repository directly, so the loop runs today with no
Docker and no deployment. The .vo files are already in-tree; a snippet
importing them checks in well under a second.
"""
import os
import re
import subprocess
import tempfile
import uuid

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get("ATLAS_REPO",
                      os.path.dirname(os.path.dirname(HERE)))
COQ_FLAGS = []
for root in ("shallow", "deep", "extras", "ttr_mtt", "atlas"):
    COQ_FLAGS += ["-R", os.path.join(REPO, root), ""]
TIMEOUT_S = int(os.environ.get("CHECK_TIMEOUT", "30"))
IMPORT_RE = re.compile(r"^[A-Za-z0-9_.]+$")
NAME_RE = re.compile(r"^[A-Za-z0-9_.']+$")


def check(code: str, imports: list[str] | None = None,
          audit: list[str] | None = None) -> dict:
    imports, audit = imports or [], audit or []
    if len(code) > 200_000:
        return {"ok": False, "output": "snippet too large", "audit": {}}
    for imp in imports:
        if not IMPORT_RE.match(imp):
            return {"ok": False, "output": f"bad import: {imp}", "audit": {}}
    for name in audit:
        if not NAME_RE.match(name):
            return {"ok": False, "output": f"bad name: {name}", "audit": {}}

    header = "".join(f"Require Import {imp}.\n" for imp in imports)
    footer = "".join(f"Print Assumptions {n}.\n" for n in audit)
    body = header + code + "\n" + footer

    tmpbase = os.path.join(os.environ.get("TMPDIR", "/tmp"), "wb-check")
    os.makedirs(tmpbase, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=tmpbase) as tmp:
        vname = os.path.join(tmp, "Check_" + uuid.uuid4().hex[:8] + ".v")
        with open(vname, "w") as f:
            f.write(body)
        try:
            proc = subprocess.run(
                ["coqc", *COQ_FLAGS, "-R", tmp, "", vname],
                capture_output=True, text=True, timeout=TIMEOUT_S, cwd=tmp)
        except subprocess.TimeoutExpired:
            return {"ok": False, "output": f"timeout after {TIMEOUT_S}s",
                    "audit": {}}

    ok = proc.returncode == 0
    output = (proc.stdout or "") + (proc.stderr or "")
    return {"ok": ok, "output": output[-20_000:],
            "audit": parse_audit(output, audit) if ok else {}}


def parse_audit(output: str, names: list[str]) -> dict[str, str]:
    """The Print Assumptions blocks appear in stdout in request order: each
    is either the closed marker or an `Axioms:` block. Zip them positionally
    and, for dirty ones, name the axioms."""
    marks = []
    for m in re.finditer(
            r"Closed under the global context|Axioms:\n((?:.+\n?)*?)(?=\nClosed|\nAxioms:|\Z)",
            output):
        if m.group(0).startswith("Closed"):
            marks.append("closed")
        else:
            axs = re.findall(r"^([\w.']+)\s*:", m.group(1) or "", re.M)
            marks.append("axioms: " + ", ".join(sorted(set(axs))[:6]))
    return {n: (marks[i] if i < len(marks) else "no audit output")
            for i, n in enumerate(names)}


if __name__ == "__main__":
    import json, sys
    r = check(sys.stdin.read(),
              imports=[a for a in sys.argv[1:]])
    print(json.dumps(r, indent=1)[:3000])
