"""Publish separately audited research without promoting atlas assessments.

The read-only research library is deliberately NOT part of proof_sources or
the live worker's library fingerprint. Checkpoints pin the exact source bytes;
CI reruns their checkers. Neither operation constitutes semantic-review approval.
"""
import hashlib
import json
from pathlib import Path
import re

from verify import parse


PACKAGES = (
    {
        "id": "montague_ptq", "namespace": "MontaguePTQ", "title": "Source-first PTQ",
        "summary": "Typed English analysis trees, a T1-T17 compiler and Boolean interpretation, read against Montague's primary text.",
        "boundary": "Explicit BooleanTruth and FunExt premises. Source correspondence still needs independent review. Whole-search completeness is unproved.",
        "documents": ["README.md", "SOURCE_MAP.md", "FINISHING_REPORT.md", "READING_CLASSIFICATION.md", "SURFACE_AMENDMENT.md", "OVERVIEW_FOR_ROBIN_AND_RASMUS.md"],
    },
    {
        "id": "montague_core", "namespace": "MontagueProof", "title": "Proof-theory workbench",
        "summary": "Explicit proof calculi, model interpretations and a meaning-preserving translation of a selected world-only IL fragment into Ty2.",
        "boundary": "A separate source-informed workbench, not full PTQ or Gallin equivalence. Soundness and model constructions retain their stated premises.",
        "documents": ["README.md", "MODEL_SPEC.md", "IL_SPEC.md", "TECHNICAL_REPORT.md"],
    },
    {
        "id": "montague_legacy", "namespace": "MontagueLegacy", "title": "Legacy correspondence",
        "summary": "A translation preserving the older IL implementation, plus a guarded comparison of Prop and Boolean observations.",
        "boundary": "Preserves the older encoding's choices, including fixed-time necessity. Code-to-code preservation does not validate those choices against PTQ.",
        "documents": ["README.md", "LEGACY_SPEC.md", "OBSERVATION_SPEC.md"],
    },
    {
        "id": "montague_gallin", "namespace": "MontagueGallin", "title": "Gallin: models and proof translation",
        "summary": "PTQ interpretation preservation, correspondence with specified Ty2 model classes, and forward translation of the implemented untensed IL proof calculus, including proofs from assumptions.",
        "boundary": "Forward proof translation, not reverse proof equivalence, the description extension or Henkin completeness. Semantic results retain BooleanTruth and FunExt inputs. Independent source review is pending; the locally indexed source calculus is an explicit encoding choice.",
        "documents": ["README.md", "SOURCE_MAP.md", "MODEL_CORRESPONDENCE.md", "UNTENSED_MODELS.md", "IL_CALCULUS.md", "FULL_PROOF_TRANSLATION.md"],
    },
)

FEATURES = (
    ("Meaning.v", "translation_interpretation", "Translation preserves interpretation",
     "The compiled IL term and an independently defined interpretation of the English analysis tree agree under related assignments."),
    ("PostulateFormulas.v", "compiled_postulates_exact", "Postulates constrain the models",
     "The nine object-language postulate families characterize precisely the encoded semantic admissibility conditions."),
    ("Examples.v", "temperature_countermodel", "An admissible temperature countermodel",
     "The translated premises hold and the translated conclusion fails in a supplied model satisfying the postulates, under explicit foundational inputs."),
)

GALLIN_FEATURES = (
    ("UntensedModels.v", "untensed_standard_consequence", "Compare consequence across models",
     "Untensed IL and its translation agree on consequence over the specified standard model classes, with explicit foundational premises."),
    ("ILFullProofTranslation.v", "compile_il_proof", "Translate every implemented source proof",
     "A proof-producing function covers all source axiom families and rules R1-R8. It takes a source derivation, not a semantic truth or completeness assumption."),
    ("ProofDischarge.v", "compile_il_from", "Carry assumptions through the translation",
     "Derivations from source premises become target derivations from the translated premises, with assumption discharge preserved."),
)


def read_public(repo, relative):
    path = (repo / relative).resolve()
    if not path.is_relative_to(repo):
        raise ValueError(f"Research path escapes repository: {relative}")
    return path.read_bytes()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def bundle_research(repo):
    repo = Path(repo).resolve()
    result = {"packages": [], "sources": {}, "features": [], "gallin_features": [],
              "source_review": "Independent semantic review pending", "live_execution": False}
    for config in PACKAGES:
        package = dict(config)
        folder = "deep/" + config["id"]
        checkpoint_path = folder + "/verification.json"
        raw_checkpoint = read_public(repo, checkpoint_path)
        checkpoint = json.loads(raw_checkpoint)
        if checkpoint.get("kernel_rechecked") is not True:
            raise ValueError(f"Missing research kernel checkpoint: {folder}")
        expected = set(checkpoint["files"])
        actual = {p.name for p in (repo / folder).glob("*.v")}
        if expected != actual:
            raise ValueError(f"Research module inventory drift: {folder}")
        # The legacy bridge also pins the old source and selected core modules.
        if "legacy_source" in checkpoint:
            old = checkpoint["legacy_source"]
            if digest(read_public(repo, old["path"])) != old["sha256"]:
                raise ValueError("Legacy research dependency drift")
        for filename, sha in checkpoint.get("core_dependencies", {}).items():
            if digest(read_public(repo, "deep/montague_core/" + filename)) != sha:
                raise ValueError("Research core dependency drift")
        for filename, sha in checkpoint.get("ptq_dependencies", {}).items():
            if digest(read_public(repo, "deep/montague_ptq/" + filename)) != sha:
                raise ValueError("Research PTQ dependency drift")
        keys = []
        statement_count = 0
        for filename, evidence in checkpoint["files"].items():
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*\.v", filename):
                raise ValueError(f"Invalid research module: {filename}")
            relative = folder + "/" + filename
            raw = read_public(repo, relative)
            if digest(raw) != evidence["sha256"]:
                raise ValueError(f"Research source/checkpoint mismatch: {relative}")
            declarations, warnings = parse(str(repo / relative))
            entries = []
            for declaration in declarations:
                name = ".".join(declaration["modpath"] + [declaration["name"]])
                qualified = config["namespace"] + "." + filename[:-2] + "." + name
                entries.append({"name": name, "qualified": qualified, "line": declaration["line"],
                                "kind": declaration["kind"], "status": declaration["status"],
                                "keyword": declaration["kw"]})
            proved = evidence["proved_statements"]
            indexed = {d["qualified"] for d in entries if d["status"] == "proved" and d["kind"] == "theorem"}
            if set(proved) != indexed:
                raise ValueError(f"Research statement inventory drift: {relative}")
            statement_count += len(proved)
            dependencies = checkpoint.get("global_dependencies_by_statement")
            if dependencies is not None:
                recorded = {name: dependencies[name] for name in proved}
            elif checkpoint.get("global_axiom_dependencies") == []:
                recorded = {name: [] for name in proved}
            else:
                raise ValueError(f"Missing research assumption checkpoint: {relative}")
            # Proof-producing Definitions have their own audited dependencies.
            # Do not count them as theorem/lemma statements or infer missing audits.
            declaration_dependencies = checkpoint.get("global_dependencies_by_declaration", {})
            for declaration in entries:
                name = declaration["qualified"]
                if name in declaration_dependencies:
                    recorded[name] = declaration_dependencies[name]
            key = "research__" + config["id"] + "__" + filename[:-2]
            result["sources"][key] = {
                "path": relative, "text": raw.decode("utf-8"), "sha256": digest(raw),
                "declarations": entries, "index_warnings": warnings, "audit": None,
                "research": {"package": config["id"], "title": config["title"],
                             "summary": config["summary"], "boundary": config["boundary"],
                             "coq_version": checkpoint["coq_version"],
                             "checkpoint_path": checkpoint_path, "checkpoint_sha256": digest(raw_checkpoint),
                             "statement_count": len(proved),
                             "global_dependencies": recorded},
            }
            keys.append(key)
        if statement_count != checkpoint["proved_statement_count"]:
            raise ValueError(f"Research statement count drift: {folder}")
        package.update({"source_keys": keys, "modules": len(keys), "statements": statement_count,
                        "negative_fixtures": len(checkpoint["negative_fixtures_rejected"]),
                        "coq_version": checkpoint["coq_version"], "checkpoint": checkpoint_path,
                        "checkpoint_sha256": digest(raw_checkpoint),
                        "check_command": f"python3 {folder}/check.py --check"})
        package["documents"] = [{"title": name, "path": folder + "/" + name} for name in config["documents"]]
        for document in package["documents"]:
            read_public(repo, document["path"])
        result["packages"].append(package)
    for package, field, features in (("montague_ptq", "features", FEATURES),
                                     ("montague_gallin", "gallin_features", GALLIN_FEATURES)):
        for filename, name, title, summary in features:
            key = "research__" + package + "__" + filename[:-2]
            matches = [d for d in result["sources"][key]["declarations"] if d["name"] == name and d["status"] == "proved"]
            if len(matches) != 1:
                raise ValueError(f"Missing research feature proof: {name}")
            result[field].append({"key": key, "line": matches[0]["line"], "name": name,
                                  "kind": matches[0]["kind"], "title": title, "summary": summary})
    report = json.loads(read_public(repo, "deep/montague_ptq/reading_exploration.json"))
    if report["search_completeness_proved"] is not False:
        raise ValueError("Review the research scope before changing the completeness claim")
    result["readings"] = {k: report[k] for k in ("witnesses", "registered_classes_reached", "search_completeness_proved")}
    return result
