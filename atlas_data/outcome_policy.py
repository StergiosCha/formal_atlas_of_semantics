"""Paper-level outcomes require explicit, source-bound review.

File opinions, compilation, edges and P/F grades are not semantic approval.
This module validates declared provenance and source binding, not reviewer
identity, independence, or the truth of the reasoning.
"""
import hashlib
import json
from pathlib import Path

OUTCOMES = {"as_is", "slight_modification", "major_restructuring", "cannot"}
FAITHFUL = {"faithful", "faithful-with-corrections"}


def candidate(record):
    final = record.get("_final") or {}
    outcome = final.get("determination", record.get("determination"))
    if outcome not in OUTCOMES:
        return None
    faith = final.get("faithfulness", (record.get("faithfulness") or {}).get("verdict"))
    mech = record.get("_mech") or {}
    counts = record.get("counts") or {}
    issues = []
    if record.get("assessment_status") in {"pilot", "incomplete"}:
        issues.append("pilot_or_incomplete")
    if faith not in FAITHFUL:
        issues.append("partial_or_unfaithful_source_mapping")
    if not mech.get("compiles"):
        issues.append("no_successful_mechanical_check")
    if counts.get("admitted", 0):
        issues.append("admitted_proofs_or_definitions")
    if not counts.get("proved", 0):
        issues.append("no_proved_claims")
    if mech.get("unsafe_flags"):
        issues.append("unsafe_checking_flags")
    if mech.get("undocumented_axioms"):
        issues.append("assumption_dependencies_need_review")
    return {"record_key": record.get("_key"), "file": record.get("file"),
            "determination": outcome, "faithfulness": faith,
            "assessment_status": record.get("assessment_status"),
            "record_limits": issues,
            "source_citations": [s.get("citation", "") for s in record.get("sources", [])],
            "rationale": record.get("determination_rationale", "")}


def load_reviews(path, papers, records, root):
    """Fail visibly on stale/malformed declarations; never invent a review.

    An entry is a source-level review of the declared core, not certification
    that every page of a book has been implemented. Reviewers must state scope
    and why it supports the paper-level comparison. Raw record/code hashes pin
    the exact evidence. The empty registry deliberately certifies nobody.
    """
    data = json.loads(Path(path).read_text())
    if data.get("schema_version") != 1:
        raise ValueError("Unsupported paper-outcome review schema")
    by_paper = {str(p["id"]): p for p in papers}
    by_key = {r["_key"]: r for r in records}
    reviews = {}
    for review in data["reviews"]:
        pid = str(review["paper_id"])
        if pid in reviews or pid not in by_paper:
            raise ValueError("Duplicate or unknown reviewed paper: " + pid)
        if review.get("status") != "reviewed" or review.get("determination") not in OUTCOMES:
            raise ValueError("Invalid review status/outcome: " + pid)
        if review.get("source_citation") != by_paper[pid].get("citation"):
            raise ValueError("Review source identity mismatch: " + pid)
        if review.get("coverage") != "source_core":
            raise ValueError("Fragment review is not a paper outcome: " + pid)
        for field in ("scope", "coverage_justification", "reviewer", "review_reference",
                      "independence_statement", "source_passages", "rationale", "record_resolution"):
            if not isinstance(review.get(field), str) or not review[field].strip():
                raise ValueError("Missing review provenance: " + field)
        support = review.get("support") or []
        if not support or len({s["record_key"] for s in support}) != len(support):
            raise ValueError("Missing or duplicate review support: " + pid)
        for item in support:
            key = item["record_key"]
            if key not in by_key:
                raise ValueError("Unknown supporting record: " + key)
            rec = by_key[key]
            if rec["file"] not in by_paper[pid].get("coq_files", []):
                raise ValueError("Review record is not linked to its paper: " + key)
            if rec.get("assessment_status") in {"pilot", "incomplete"}:
                raise ValueError("Pilot/incomplete evidence cannot settle a source: " + key)
            mech, counts = rec.get("_mech") or {}, rec.get("counts") or {}
            if not mech.get("compiles") or mech.get("unsafe_flags") or counts.get("admitted", 0):
                raise ValueError("Incomplete/unsafe mechanical evidence: " + key)
            if not counts.get("proved", 0) or mech.get("queried", 0) < counts["proved"]:
                raise ValueError("Proof/assumption evidence missing: " + key)
            faith = (rec.get("_final") or {}).get("faithfulness", (rec.get("faithfulness") or {}).get("verdict"))
            if review["determination"] in {"as_is", "slight_modification"} and faith not in FAITHFUL:
                raise ValueError("Positive source outcome needs faithful support: " + key)
            if mech.get("undocumented_axioms"):
                notes = item.get("assumption_evidence") or {}
                if any(not notes.get(a) for a in mech["undocumented_axioms"]):
                    raise ValueError("Unreviewed assumption dependencies: " + key)
            targets = {t["name"] for t in rec.get("theorems", []) if t.get("status") == "proved"}
            if not item.get("theorems") or not set(item["theorems"]) <= targets:
                raise ValueError("Review must cite proved source evidence: " + key)
            for rel, field in ((rec["file"], "code_sha256"),
                               (f"atlas_data/records/{key}.json", "record_sha256"),
                               (f"atlas_data/records/{key}.mech.json", "mechanical_sha256")):
                file = Path(root) / rel
                if hashlib.sha256(file.read_bytes()).hexdigest() != item.get(field):
                    raise ValueError("Stale reviewed evidence: " + rel)
        if review["determination"] in {"major_restructuring", "cannot"}:
            evidence = review.get("necessity_evidence")
            if not isinstance(evidence, str) or not evidence.strip():
                raise ValueError("Resistance outcome needs necessity/obstruction evidence: " + pid)
        reviews[pid] = review
    return reviews


def apply_outcome(paper, records, reviews=None):
    candidates = [c for r in records if (c := candidate(r)) is not None]
    candidates.sort(key=lambda c: (c["record_key"] or "", c["file"] or ""))
    paper["determination_candidates"] = candidates
    paper["record_outcome_conflict"] = len({c["determination"] for c in candidates}) > 1
    review = (reviews or {}).get(str(paper["id"]))
    paper["determination_review"] = review
    paper["determination_status"] = "reviewed" if review else "review_required" if candidates else "unassessed"
    paper["determination_actual"] = review["determination"] if review else None
    pred = paper.get("survey_determination")
    paper["prediction_disputed"] = bool(review and pred in OUTCOMES and review["determination"] != pred)
    return paper
