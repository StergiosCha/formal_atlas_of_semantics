"""Provenance structure and offline reproducibility, not semantic review."""
import copy
import json
import hashlib
from pathlib import Path
import tempfile
import unittest
from collections import Counter
from unittest.mock import patch

import consolidate
import source_registry as registry
from edge_profiles import legacy_atlas_view

HERE, ROOT = registry.HERE, registry.ROOT


class SourceRegistryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.atlas = json.loads((HERE / "atlas.json").read_text())
        cls.data = registry.load_registry(cls.atlas["papers"])

    def test_exact_survey_and_supplement_separation(self):
        self.assertEqual(len(self.data["sources"]), 230)
        self.assertEqual({str(s["paper_id"]) for s in self.data["sources"]},
                         {str(p["id"]) for p in self.atlas["papers"]})
        cooper = self.data["supplementary_sources"][0]
        self.assertEqual(cooper["supplement_id"], "cooper-2023")
        self.assertIsNone(cooper["paper_id"])
        self.assertNotIn("published_level", cooper)
        old_cooper = next(s for s in self.data["sources"] if str(s["paper_id"]) == "50")
        self.assertNotIn(cooper["artifact_links"][0]["artifact"],
                         [a["artifact"] for a in old_cooper["artifact_links"]])

    def test_research_and_historical_edges_are_byte_identical_to_pre_migration(self):
        baseline = json.loads((HERE / "source_registry_baseline.json").read_text())
        # Reverse the reporting-schema migration and remove ONE explicitly
        # added comparison-infrastructure record. Recalculate historical
        # totals from the remaining records, not from a trusted replacement
        # snapshot. Every old paper, record, grade, edge and statistic is
        # still checked against the original byte hash.
        prior = legacy_atlas_view(self.atlas)
        prior["files"] = [f for f in prior["files"]
                          if f["file"] != "atlas/ttr/Witness_Contract.v"]
        self.assertEqual(len(prior["files"]), 86)
        prior["generated_from"]["records"] = len(prior["files"])
        for field in ("theorems", "proved", "admitted"):
            prior["stats"][field] = sum(f.get("counts", {}).get(field, 0) for f in prior["files"])
        for field in ("determination", "faithfulness"):
            prior["stats"][field] = dict(Counter(f["_final"][field] for f in prior["files"]))
        prior["stats"]["disputed_records"] = [f["_key"] for f in prior["files"] if f["_final"]["disputed"]]
        historical = json.dumps(prior, indent=1, ensure_ascii=False).encode()
        self.assertEqual(hashlib.sha256(historical).hexdigest(), baseline["atlas_sha256"])
        self.assertEqual(baseline["git_commit"], "91983bc561226f90f7b306620f7d4fe8fd07ed86")

    def test_offline_levels_and_outcomes_match_without_filesystem_search(self):
        papers = copy.deepcopy(self.atlas["papers"])
        with patch.dict("os.environ", {"ATLAS_PAPERS": "/does-not-exist"}), \
             patch("os.walk", side_effect=AssertionError("No corpus inference allowed")):
            result = consolidate.compute_levels(papers, self.atlas["files"], self.atlas["edges"],
                                                source_levels=registry.low_levels(self.data))
        for old, new in zip(self.atlas["papers"], result):
            for field in ("level", "formality", "determination_actual", "determination_status", "prediction_disputed"):
                self.assertEqual(old[field], new[field], (old["id"], field))

    def test_candidates_do_not_count_as_registered_evidence(self):
        candidate = {"artifact_links": [{"status": "candidate"}], "designs": [{"status": "candidate"}]}
        self.assertEqual(registry.registered_low_level(candidate), "F0")
        candidate["artifact_links"][0]["status"] = "documented"
        self.assertEqual(registry.registered_low_level(candidate), "F1")
        candidate["designs"][0]["status"] = "documented"
        self.assertEqual(registry.registered_low_level(candidate), "F2")

    def test_report_is_reproducible_and_not_a_publication(self):
        result = registry.report(self.data, self.atlas["papers"])
        self.assertEqual(result, json.loads((HERE / "source_registry_migration.json").read_text()))
        self.assertEqual(result["sources_with_documented_identity"], 7)
        self.assertEqual(len(result["differences"]), 104)
        self.assertEqual(result["migration_status"], "pending_review")
        self.assertTrue(all(r["published_level"] in ("F1", "F2") for r in result["differences"]))

    def test_wrong_missing_duplicate_citations_and_ids_fail_closed(self):
        for mutation in (
            lambda d: d["sources"].pop(),
            lambda d: d["sources"].append(d["sources"][0]),
            lambda d: d["sources"][0].update(citation="Different book"),
            lambda d: d.update(migration_status="approved"),
            lambda d: d["sources"][0].update(published_level="F5"),
            lambda d: d["supplementary_sources"][0].update(paper_id=50),
            lambda d: d["supplementary_sources"].append(d["supplementary_sources"][0]),
            lambda d: d["sources"][0].update(consultations=None),
            lambda d: next(c for s in d["sources"] for c in s["consultations"]).update(passages="not a list"),
        ):
            data = copy.deepcopy(self.data)
            mutation(data)
            with self.assertRaises(ValueError):
                registry.validate(data, self.atlas["papers"])

    def test_stale_identity_design_and_manifest_references_fail(self):
        for select in (
            lambda d: next(a["identity_reference"] for s in d["sources"] for a in s["artifact_links"] if a["status"] == "documented"),
            lambda d: next(x for s in d["sources"] for x in s["designs"]),
            lambda d: next(m for a in d["artifacts"].values() for m in a["manifests"]),
        ):
            data = copy.deepcopy(self.data)
            select(data)["sha256"] = "0" * 64
            with self.assertRaises(ValueError):
                registry.validate(data, self.atlas["papers"])

    def test_arbitrary_documented_or_independent_labels_are_rejected(self):
        data = copy.deepcopy(self.data)
        candidate = next(a for s in data["sources"] for a in s["artifact_links"] if a["status"] == "candidate" and "identity_reference" not in a)
        candidate["status"] = "documented"
        with self.assertRaises((KeyError, ValueError)):
            registry.validate(data, self.atlas["papers"])
        data = copy.deepcopy(self.data)
        next(c for s in data["sources"] for c in s["consultations"])["independent_review"] = True
        with self.assertRaises(ValueError):
            registry.validate(data, self.atlas["papers"])

    def test_bekki_ranta_hobbs_identity_boundaries(self):
        sources = {str(s["paper_id"]): s for s in self.data["sources"]}
        dts = next(a for a in sources["38"]["artifact_links"] if a["status"] == "documented")
        self.assertIn("misleading", dts["identity_note"])
        for sid in ("x216", "101"):
            self.assertTrue(sources[sid]["artifact_links"])
            self.assertFalse(any(a["status"] == "documented" for a in sources[sid]["artifact_links"]))
            self.assertFalse(sources[sid]["consultations"])

    def test_safe_relative_paths_and_symlink_escape(self):
        for name in ("../secret", "/tmp/secret", "a/../b", "a\\b", "a//b"):
            with self.assertRaises(ValueError):
                registry.relative_path(name)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "corpus"
            root.mkdir()
            (root / "escape").symlink_to(Path(tmp))
            with self.assertRaises(ValueError):
                registry.contained(root, "escape/outside.pdf")

    def test_missing_mismatched_and_matching_local_bytes_do_not_mutate_registry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "paper.pdf"
            path.write_bytes(b"fixture bytes, not a real PDF")
            sha = registry.digest(path)
            data = {"artifacts": {sha: {"paths": ["paper.pdf", "missing.pdf"]}}}
            before = copy.deepcopy(data)
            self.assertEqual([r["status"] for r in registry.check_corpus(data, root)], ["match", "missing"])
            path.write_bytes(b"different")
            self.assertEqual(registry.check_corpus(data, root)[0]["status"], "mismatch")
            self.assertEqual(data, before)

    def test_no_source_binding_can_promote_into_proof_tiers(self):
        with self.assertRaises(ValueError):
            consolidate.compute_levels([{"id": 1}], [], [], source_levels={"1": "F5"})


if __name__ == "__main__":
    unittest.main()
