"""Validated qualitative claim profiles, separate from P grades and F levels.

No success rate or ordering is calculated: inventory groups are unequal and
the semantic annotations are retrospective, single-researcher judgments.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DISPOSITIONS = {
    "representation_only", "conditional_fragment", "direct_logical_fragment",
    "illustrative_model", "restricted_construction", "mixed", "uncovered",
}


def validate_comparison(data, files, papers, root=HERE.parent):
    if data.get("schema_version") != 1:
        raise ValueError("Unsupported claim comparison schema")
    if data.get("assessment_basis") != "retrospective_single_researcher":
        raise ValueError("Claim comparison review provenance is missing")
    by_key = {r["_key"]: r for r in files}
    by_paper = {str(p["id"]): p for p in papers}
    seen_keys, seen_papers = set(), set()
    for profile in data["profiles"]:
        key, pid = profile["record_key"], str(profile["paper_id"])
        if key in seen_keys or pid in seen_papers:
            raise ValueError("Duplicate claim profile")
        seen_keys.add(key)
        seen_papers.add(pid)
        if key not in by_key or pid not in by_paper:
            raise ValueError("Claim profile refers to missing paper/record")
        record, paper = by_key[key], by_paper[pid]
        if profile["formality"] != paper.get("formality"):
            raise ValueError("Claim profile disagrees with frozen formality")
        if record["file"] not in paper.get("coq_files", []):
            raise ValueError("Claim profile is not linked to this paper")
        if record.get("assessment_status") != "pilot" or record.get("determination") != "unassessed":
            raise ValueError("Reassess claim profile when source status changes")
        digest = hashlib.sha256((Path(root) / record["file"]).read_bytes()).hexdigest()
        if digest != profile["code_sha256"]:
            raise ValueError("Stale claim profile: code changed for " + key)
        names = {t["name"] for t in record["theorems"]}
        seen_targets = set()
        for target in profile["targets"]:
            if target["id"] in seen_targets:
                raise ValueError("Duplicate source-target group")
            seen_targets.add(target["id"])
            if target["disposition"] not in DISPOSITIONS:
                raise ValueError("Unknown source-target disposition")
            for field in ("source_claim", "pages", "established", "limit"):
                if not target.get(field):
                    raise ValueError("Missing claim traceability: " + field)
            if not set(target["evidence"]) <= names:
                raise ValueError("Unknown theorem reference in " + target["id"])
            if target["disposition"] == "uncovered":
                if target["evidence"]:
                    raise ValueError("Uncovered target cannot claim theorem evidence")
            elif not target["evidence"]:
                raise ValueError("Covered target needs named evidence")
        if not seen_targets:
            raise ValueError("Empty source inventory")
    return data


def load_comparison(files, papers):
    path = HERE / "campaigns" / "claim_comparison_2026_09_13.json"
    if not path.exists():
        return None
    # Malformed or stale semantic annotations must fail visibly, not disappear.
    return validate_comparison(json.loads(path.read_text()), files, papers)
