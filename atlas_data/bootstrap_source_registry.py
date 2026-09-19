"""One-time migration; historical heuristics generate candidates, not evidence.

Refuses to overwrite existing registry files. Source-specific bindings are
imported from source_bindings.json. No PDF is copied into the repository.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import unicodedata

from source_registry import HERE, ROOT, digest, validate, report, contained


def norm(value):
    value = unicodedata.normalize("NFKD", str(value)).encode("ascii", "ignore").decode()
    return re.sub(r"[^a-z0-9]", "", value.lower())


def ref(path):
    return {"path": str(path.relative_to(ROOT)), "sha256": digest(path)}


def bootstrap(corpus):
    output = HERE / "source_registry.json"
    baseline_path = HERE / "source_registry_baseline.json"
    report_path = HERE / "source_registry_migration.json"
    if any(p.exists() for p in (output, baseline_path, report_path)):
        raise ValueError("Refusing to overwrite an existing migration")
    atlas = json.loads((HERE / "atlas.json").read_text())
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    baseline = {"git_commit": commit, "atlas_sha256": digest(HERE / "atlas.json"),
                "sources": {str(p["id"]): {"citation": p["citation"], "level": p["level"]} for p in atlas["papers"]}}
    inventory = sorted(p for p in corpus.rglob("*") if p.suffix.lower() in (".pdf", ".djvu") and p.is_file())
    designs = sorted((HERE / "designs").glob("*.md"))
    design_text = {p: p.read_text().lower() for p in designs}
    artifacts, by_path = {}, {}

    def artifact(path):
        name = str(path.relative_to(corpus))
        path = contained(corpus, name)
        if name not in by_path:
            sha = digest(path)
            by_path[name] = sha
            item = artifacts.setdefault(sha, {"sha256": sha, "paths": [], "manifests": []})
            if name not in item["paths"]:
                item["paths"].append(name)
        return by_path[name]

    sources = []
    for paper in atlas["papers"]:
        first = (paper.get("authors") or "").split("&")[0].split(",")[0].strip()
        surname = norm(first.split()[-1]) if first else ""
        year = str(paper.get("year") or "")
        candidates = sorted({artifact(p) for p in inventory if surname and surname in norm(p.name) and year in norm(p.name)})
        source = {"paper_id": paper["id"], "citation": paper["citation"],
                  "published_level": paper["level"],
                  "artifact_links": [{"artifact": sha, "status": "candidate", "edition": None,
                                      "identifiers": [], "identity_note": "Legacy surname/year filename match; identity unverified."} for sha in candidates],
                  "consultations": [], "designs": []}
        for path in designs:
            if surname and re.search(r"(?<![a-z0-9])" + re.escape(surname) + r"(?![a-z0-9])", design_text[path]):
                source["designs"].append({**ref(path), "status": "candidate",
                                          "scope": "Legacy surname token; not an exact source binding."})
        sources.append(source)
    by_id = {str(s["paper_id"]): s for s in sources}
    supplementary = []
    bindings = json.loads((HERE / "source_bindings.json").read_text())
    for binding in bindings:
        if binding.get("paper_id") is None:
            source = {"paper_id": None, "supplement_id": binding["supplement_id"],
                      "citation": binding["citation"], "artifact_links": [], "consultations": [], "designs": []}
            supplementary.append(source)
        else:
            source = by_id[str(binding["paper_id"])]
            if source["citation"] != binding["citation"]:
                raise ValueError("Curated source citation mismatch")
        sha = artifact(corpus / binding["artifact_path"])
        manifest_path = ROOT / binding["manifest"]
        manifest = json.loads(manifest_path.read_text())
        if manifest["external_sources"].get(binding["artifact_path"]) != sha:
            raise ValueError("Curated artifact does not match the historical manifest")
        item = artifacts[sha]
        manifest_ref = ref(manifest_path)
        if manifest_ref not in item["manifests"]:
            item["manifests"].append(manifest_ref)
        audit_ref = ref(ROOT / binding["audit"])
        source["artifact_links"] = [a for a in source["artifact_links"] if a["artifact"] != sha]
        source["artifact_links"].append({"artifact": sha, "status": binding.get("status", "documented"),
                                         "edition": binding["edition"], "identity_reference": audit_ref,
                                         "identity_note": binding["identity_note"],
                                         "identifiers": [{**i, "reference": audit_ref} for i in binding.get("identifiers", [])]})
        if binding.get("passages") and binding.get("status", "documented") == "documented":
            source["consultations"].append({"artifact": sha, "report": audit_ref,
                "passages": binding["passages"], "reviewer": binding["reviewer"], "independent_review": False})
        for design in binding.get("designs", []):
            source["designs"] = [d for d in source["designs"] if d["path"] != design["path"]]
            source["designs"].append({**ref(ROOT / design["path"]), "status": "documented", "scope": design["scope"]})
    baseline_path.write_text(json.dumps(baseline, indent=2, ensure_ascii=False) + "\n")
    data = {"schema_version": 1, "migration_status": "pending_review", "baseline_commit": commit,
            "baseline": ref(baseline_path), "artifacts": dict(sorted(artifacts.items())),
            "sources": sources, "supplementary_sources": supplementary}
    validate(data, atlas["papers"])
    output.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    result = report(data, atlas["papers"])
    report_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(f"Created registry: {len(sources)} surveyed sources, {len(artifacts)} pinned artifacts; "
          f"{len(result['differences'])} proposed tier differences, not published.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, required=True)
    args = parser.parse_args()
    if not args.corpus.is_dir():
        parser.error("Corpus directory does not exist")
    bootstrap(args.corpus.resolve())
