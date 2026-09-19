"""Explicit source provenance and a conservative, offline evidence migration.

Candidate matches never establish identity, consultation or F1/F2. Published
low tiers remain labelled historical observations pending migration review.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DEFAULT = HERE / "source_registry.json"


def string_list(value, label, nonempty=False):
    if not isinstance(value, list) or any(not isinstance(s, str) or not s.strip() for s in value) or (nonempty and not value):
        raise ValueError(f"{label} must be a list of nonempty strings")
    return value


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def relative_path(value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError("Expected a nonempty portable relative path")
    path = Path(value)
    if path.is_absolute() or any(p in ("", ".", "..") for p in value.split("/")):
        raise ValueError(f"Unsafe path: {value}")
    return path


def contained(root, value):
    root = Path(root).resolve()
    path = (root / relative_path(value)).resolve()
    if not path.is_relative_to(root):
        raise ValueError(f"Path escapes root: {value}")
    return path


def reference(root, ref):
    if not isinstance(ref, dict) or not re.fullmatch(r"[a-f0-9]{64}", ref.get("sha256", "")):
        raise ValueError("Reference needs a SHA256")
    path = contained(root, ref["path"])
    if not path.is_file() or digest(path) != ref["sha256"]:
        raise ValueError(f"Missing or stale reference: {ref['path']}")
    return path


def validate(data, papers, root=ROOT):
    if data.get("schema_version") != 1 or data.get("migration_status") != "pending_review":
        raise ValueError("Unsupported registry version or unapproved migration state")
    expected = {str(p["id"]): p["citation"] for p in papers}
    sources = data.get("sources", [])
    ids = [str(s["paper_id"]) for s in sources]
    if len(ids) != len(set(ids)) or set(ids) != set(expected):
        raise ValueError("Registry must cover exactly the survey's unique source IDs")
    supplements = data.get("supplementary_sources", [])
    supplemental_ids = [s.get("supplement_id") for s in supplements]
    if any(s.get("paper_id") is not None or "published_level" in s for s in supplements) or \
            any(not s for s in supplemental_ids) or len(set(supplemental_ids)) != len(supplemental_ids):
        raise ValueError("Supplementary sources need unique non-survey identities without F grades")
    baseline = json.loads(reference(root, data["baseline"]).read_text())
    if baseline.get("git_commit") != data.get("baseline_commit"):
        raise ValueError("Baseline commit mismatch")
    baseline_sources = baseline["sources"]
    if set(baseline_sources) != set(expected):
        raise ValueError("Baseline source inventory mismatch")
    artifacts = data.get("artifacts", {})
    for key, artifact in artifacts.items():
        if key != artifact.get("sha256") or not re.fullmatch(r"[a-f0-9]{64}", key):
            raise ValueError("Artifact ID must be its SHA256")
        string_list(artifact.get("paths"), "Artifact paths", nonempty=True)
        for name in artifact["paths"]:
            relative_path(name)
        for ref in artifact.get("manifests", []):
            manifest = json.loads(reference(root, ref).read_text())
            if not any(manifest.get("external_sources", {}).get(p) == key for p in artifact["paths"]):
                raise ValueError("Artifact digest not supported by its manifest")
    for source in sources + data.get("supplementary_sources", []):
        sid = str(source.get("paper_id"))
        if source.get("paper_id") is not None:
            if source.get("citation") != expected.get(sid):
                raise ValueError(f"Citation mismatch: {sid}")
            observed = baseline_sources[sid]
            if observed["citation"] != source["citation"] or source.get("published_level") != observed["level"]:
                raise ValueError(f"Published baseline mismatch: {sid}")
            if source["published_level"] not in ("F0", "F1", "F2", "F3", "F4", "F5"):
                raise ValueError("Invalid published level")
        elif not source.get("supplement_id"):
            raise ValueError("Supplementary works need separate IDs, not survey grades")
        links = source.get("artifact_links", [])
        for field in ("artifact_links", "consultations", "designs"):
            if not isinstance(source.get(field), list):
                raise ValueError(f"Source {field} must be an explicit list")
        if len({a["artifact"] for a in links}) != len(links):
            raise ValueError("Duplicate artifact link")
        for link in links:
            if link["artifact"] not in artifacts or link.get("status") not in ("candidate", "documented"):
                raise ValueError("Unknown artifact or identity status")
            if link.get("edition") is not None and not isinstance(link["edition"], str):
                raise ValueError("Edition must be text or null")
            if not isinstance(link.get("identity_note"), str) or not link["identity_note"].strip():
                raise ValueError("Identity link needs an explanation")
            if not isinstance(link.get("identifiers"), list):
                raise ValueError("Identifiers must be an explicit list")
            if link["status"] == "documented":
                reference(root, link["identity_reference"])
                if not link.get("edition") or not link.get("identity_note"):
                    raise ValueError("Documented identity needs an edition and explanation")
                if not artifacts[link["artifact"]].get("manifests"):
                    raise ValueError("Documented identity needs historical artifact provenance")
            for identifier in link.get("identifiers", []):
                if identifier.get("kind") not in ("doi", "isbn", "arxiv") or not identifier.get("value"):
                    raise ValueError("Invalid bibliographic identifier")
                reference(root, identifier["reference"])
        for consultation in source.get("consultations", []):
            if not any(a["artifact"] == consultation["artifact"] and a["status"] == "documented" for a in links):
                raise ValueError("Consultation needs a documented source/artifact link")
            reference(root, consultation["report"])
            string_list(consultation.get("passages"), "Consulted passages", nonempty=True)
            if not isinstance(consultation.get("reviewer"), str) or not consultation["reviewer"].strip():
                raise ValueError("Consultation needs passages and reviewer provenance")
            if consultation.get("independent_review") is not False:
                raise ValueError("This bootstrap records no independent review")
        for design in source.get("designs", []):
            reference(root, design)
            if design.get("status") not in ("candidate", "documented"):
                raise ValueError("Invalid design binding status")
            if design["status"] == "documented" and not design.get("scope"):
                raise ValueError("Documented design needs source-specific scope")
    return data


def load_registry(papers, path=DEFAULT, root=ROOT):
    return validate(json.loads(Path(path).read_text()), papers, root)


def registered_low_level(source):
    if any(d["status"] == "documented" for d in source.get("designs", [])):
        return "F2"
    if any(a["status"] == "documented" for a in source.get("artifact_links", [])):
        return "F1"
    return "F0"


def low_levels(data, mode="published"):
    if mode not in ("published", "registered"):
        raise ValueError("Unknown evidence mode")
    # No automatic publication of either upgrades or downgrades. Coq-based
    # F3–F5 progress is still independently computed by consolidate.py.
    return {str(s["paper_id"]):
            (s["published_level"] if mode == "published" and s["published_level"] in ("F0", "F1", "F2")
             else registered_low_level(s)) for s in data["sources"]}


def report(data, papers):
    current = {str(p["id"]): p["level"] for p in papers}
    rows = []
    for source in data["sources"]:
        sid = str(source["paper_id"])
        registered = registered_low_level(source)
        proposed = current[sid] if current[sid] in ("F3", "F4", "F5") else registered
        rows.append({"paper_id": source["paper_id"], "citation": source["citation"],
                     "published_level": current[sid], "registered_only_level": proposed,
                     "documented_artifacts": sum(a["status"] == "documented" for a in source["artifact_links"]),
                     "candidate_artifacts": sum(a["status"] == "candidate" for a in source["artifact_links"]),
                     "documented_designs": sum(d["status"] == "documented" for d in source["designs"]),
                     "consultations": len(source["consultations"]), "migration_pending": True})
    return {"schema_version": 1, "migration_status": "pending_review",
            "baseline_commit": data["baseline_commit"], "survey_sources": len(rows),
            "artifact_count": len(data["artifacts"]),
            "sources_with_documented_identity": sum(r["documented_artifacts"] > 0 for r in rows),
            "sources_with_candidates_only": sum(r["candidate_artifacts"] > 0 and not r["documented_artifacts"] for r in rows),
            "supplementary_sources": len(data.get("supplementary_sources", [])),
            "differences": [r for r in rows if r["published_level"] != r["registered_only_level"]],
            "sources": rows}


def check_corpus(data, corpus):
    """Read-only byte verification, separate from identity and consultation."""
    rows = []
    for key, artifact in sorted(data["artifacts"].items()):
        for name in artifact["paths"]:
            path = contained(corpus, name)
            status = "missing" if not path.is_file() else "match" if digest(path) == key else "mismatch"
            rows.append({"path": name, "sha256": key, "status": status})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registry", type=Path, default=DEFAULT)
    parser.add_argument("--corpus", type=Path, help="verify local bytes; never change published evidence")
    parser.add_argument("--report", action="store_true", help="emit diagnostic migration JSON")
    args = parser.parse_args()
    atlas = json.loads((HERE / "atlas.json").read_text())
    data = load_registry(atlas["papers"], args.registry)
    if args.corpus:
        rows = check_corpus(data, args.corpus)
        print(json.dumps({"artifacts": rows}, indent=2))
        return int(any(r["status"] != "match" for r in rows))
    result = report(data, atlas["papers"])
    if args.report:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        print(f"Registry valid: {result['survey_sources']} survey sources; "
              f"{result['sources_with_documented_identity']} with documented identities; "
              f"{len(result['differences'])} proposed tier differences, NOT published.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
