"""Bundle real Coq source and navigation, never model-written proof excerpts.

Declaration positions reuse the verifier's lexical index, not a Coq evaluator.
The mechanical sidecars are explicitly labelled recorded audits. Source hashes
identify downloaded bytes; they do not assert that a stored audit was rerun.
"""
import hashlib
import json
import subprocess
from pathlib import Path

from verify import ROOTS, parse


def library_fingerprint(sources):
    manifest = {source["path"]: source["sha256"] for source in sources.values()}
    return hashlib.sha256(json.dumps(manifest, sort_keys=True,
                                     separators=(",", ":")).encode()).hexdigest()


def indexed_source(path, relative, module=""):
    raw = path.read_bytes()
    declarations, warnings = parse(str(path))
    entries = []
    for declaration in declarations:
        name = ".".join(declaration["modpath"] + [declaration["name"]])
        entries.append({"name": name, "qualified": f"{module}.{name}" if module else name,
                        "line": declaration["line"], "kind": declaration["kind"],
                        "status": declaration["status"], "keyword": declaration["kw"]})
    return {"path": relative, "text": raw.decode("utf-8"), "sha256": hashlib.sha256(raw).hexdigest(),
            "declarations": entries, "index_warnings": warnings, "audit": None}


def bundle_reader_files(repo, existing_paths):
    """Bundle the remaining public .v files for reading, outside the worker manifest."""
    repo = Path(repo).resolve()
    if (repo / ".git").exists():
        tracked = subprocess.check_output(["git", "ls-files", "-z", "--", "*.v"], cwd=repo)
        paths = {p for p in tracked.decode("utf-8").split("\0") if p}
    else:  # Building an unpacked source distribution without Git metadata.
        roots = [*ROOTS, "research", "atlas_data/audits", "atlas_data/probes"]
        paths = {p.relative_to(repo).as_posix() for root in roots for p in (repo / root).rglob("*.v")}
    result = {}
    for relative in sorted(paths - existing_paths):
        path = repo / relative
        if path.resolve() != path or not path.is_file():
            raise ValueError(f"Expected a regular repository source: {relative}")
        result[relative] = indexed_source(path, relative)
    return result


def bundle_sources(records, repo):
    repo = Path(repo).resolve()
    sources = {}
    for record in records:
        key = record.get("key", record.get("_key"))
        original = record["file"]
        # A neutral historical root preserves old record identity. Resolve it
        # only inside this checkout, with the same path confinement below.
        relative = original.removeprefix("/historical-checkout/")
        relative = relative.split("/revisiting-formal-semantics/", 1)[-1]
        path = (repo / relative).resolve()
        if not path.is_relative_to(repo) or path.suffix != ".v":
            raise ValueError(f"Unsafe proof source path: {original}")
        relative = path.relative_to(repo).as_posix()
        if relative.split("/")[0] not in ROOTS:
            raise ValueError(f"Proof source outside Coq roots: {relative}")
        module = relative.split("/", 1)[1][:-2].replace("/", ".")
        audit_path = repo / "atlas_data" / "records" / f"{key}.mech.json"
        audit = json.loads(audit_path.read_text()) if audit_path.exists() else None
        if audit and audit.get("file") != relative:
            raise ValueError(f"Audit/source mismatch: {key}")
        sources[key] = indexed_source(path, relative, module)
        if audit:
            sources[key]["audit"] = {k: audit.get(k) for k in ("coq_version", "compile", "assumptions")}
            sources[key]["audit"]["statements"] = audit.get("statements", {})
    return sources
