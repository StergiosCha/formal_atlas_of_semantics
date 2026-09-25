"""Scoped comparison profiles; never infer theoretical equivalence from scores."""
import copy
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
OBLIGATIONS = {
    "compositionality": "Does a specified translation respect all constructors and contexts in its declared fragment?",
    "preservation": "Which judgments or observations are preserved, in which direction and under which assumptions?",
    "reflection": "Does the translation introduce additional consequences for the source fragment?",
    "model_coverage": "Which admissible models are covered, and how does the translation handle changes of model?",
    "recoverability": "What survives a round trip, up to which explicitly specified equivalence?",
}


def load_profiles(edges, root=HERE.parent):
    root = Path(root).resolve()
    data = json.loads((root / "atlas_data/edge_profiles.json").read_text())
    return validate_profiles(data, edges, root)


def validate_profiles(data, edges, root=HERE.parent):
    root = Path(root).resolve()
    if data.get("schema_version") != 1 or data.get("assessment_basis") != "editorial_restatement_of_existing_artifacts":
        raise ValueError("Unsupported edge-profile provenance")
    profiles = data["profiles"]
    if set(profiles) != {e["_key"] for e in edges}:
        raise ValueError("Every edge needs exactly one explicit comparison profile")
    for key, p in profiles.items():
        if p.get("theory_relation") != "unassessed":
            raise ValueError("This migration cannot approve a theory-level relationship")
        for field in ("scope", "observations", "representation_choices", "direction", "limitations"):
            if not isinstance(p.get(field), str) or not p[field].strip():
                raise ValueError(f"Missing {field} for {key}")
        for support in p["support"]:
            record_key = support["record_key"]
            if not re.fullmatch(r"[A-Za-z0-9_]+", record_key):
                raise ValueError("Unsafe support record key")
            mech = json.loads((root / "atlas_data/records" / f"{record_key}.mech.json").read_text())
            path = (root / mech["file"]).resolve()
            if not path.is_relative_to(root) or path.suffix != ".v":
                raise ValueError("Unsafe support source")
            if not mech["compile"]["ok"]:
                raise ValueError("Supporting file has no successful recorded compilation")
            if hashlib.sha256(path.read_bytes()).hexdigest() != support["source_sha256"]:
                raise ValueError("Stale comparison support: " + record_key)
            if not support.get("theorems"):
                raise ValueError("Supporting record needs named statements")
            for name, fingerprint in support["theorems"].items():
                if mech["statements"].get(name) != fingerprint:
                    raise ValueError("Unknown or changed supporting statement: " + name)
    return profiles


def attach_profiles(edges, profiles):
    for e in edges:
        phen = e["phenomena"]
        names = [p["name"] for p in phen]
        if len(names) != len(set(names)):
            raise ValueError("Duplicate phenomenon: " + e["_key"])
        if any(set(p.get("attempted_by", [])) - {"a", "b"} for p in phen):
            raise ValueError("Unknown comparison endpoint")
        a = {p["name"] for p in phen if "a" in p.get("attempted_by", [])}
        b = {p["name"] for p in phen if "b" in p.get("attempted_by", [])}
        profile = copy.deepcopy(profiles[e["_key"]])
        profile["coverage"] = {"listed": len(phen), "shared": len(a & b),
                               "a_only": sorted(a - b), "b_only": sorted(b - a)}
        profile["obligations"] = [
            {"id": key, "question": question, "status": "unassessed"}
            for key, question in OBLIGATIONS.items()]
        e["_profile"] = profile
    return edges


def legacy_atlas_view(atlas):
    """Reconstruct the pre-migration schema for the exact preservation gate."""
    old = copy.deepcopy(atlas)
    for e in old["edges"]:
        e.pop("_profile", None)
        # Preserve insertion order, including the historical _computed position.
        restored = {("_computed" if k == "_legacy_scores" else k): v for k, v in e.items()}
        e.clear()
        e.update(restored)
    return old
