"""Bundle real Coq source and navigation, never model-written proof excerpts.

Declaration positions reuse the verifier's lexical index, not a Coq evaluator.
The mechanical sidecars are explicitly labelled recorded audits. Source hashes
identify downloaded bytes; they do not assert that a stored audit was rerun.
"""
import hashlib
import json
from pathlib import Path

from verify import ROOTS, parse


def bundle_sources(records, repo):
    repo = Path(repo).resolve()
    sources = {}
    for record in records:
        key = record.get("key", record.get("_key"))
        original = record["file"]
        # Historical records include the author's absolute checkout path.
        relative = original.split("/revisiting-formal-semantics/", 1)[-1]
        path = (repo / relative).resolve()
        if not path.is_relative_to(repo) or path.suffix != ".v":
            raise ValueError(f"Unsafe proof source path: {original}")
        relative = path.relative_to(repo).as_posix()
        if relative.split("/")[0] not in ROOTS:
            raise ValueError(f"Proof source outside Coq roots: {relative}")
        raw = path.read_bytes()  # Missing sources fail the build, not a broken link.
        text = raw.decode("utf-8")
        declarations, warnings = parse(str(path))
        module = relative.split("/", 1)[1][:-2].replace("/", ".")
        audit_path = repo / "atlas_data" / "records" / f"{key}.mech.json"
        audit = json.loads(audit_path.read_text()) if audit_path.exists() else None
        if audit and audit.get("file") != relative:
            raise ValueError(f"Audit/source mismatch: {key}")
        entries = []
        for d in declarations:
            name = ".".join(d["modpath"] + [d["name"]])
            qualified = module + "." + name
            entries.append({"name": name, "qualified": qualified,
                            "line": d["line"], "kind": d["kind"],
                            "status": d["status"], "keyword": d["kw"]})
        sources[key] = {"path": relative, "text": text,
                        "sha256": hashlib.sha256(raw).hexdigest(),
                        "declarations": entries, "index_warnings": warnings,
                        "audit": ({"coq_version": audit.get("coq_version"),
                                   "compile": audit.get("compile"),
                                   "assumptions": audit.get("assumptions"),
                                   "statements": audit.get("statements", {})}
                                  if audit else None)}
    return sources
