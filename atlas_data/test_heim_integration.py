"""Heim step-1 integrity/traceability checks, not independent semantic review."""
import hashlib
import json
from pathlib import Path
import unittest

import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
COUNTS = {"atlas__heim1982_binding": 25, "atlas__heim1982_integration": 23,
          "atlas__heim1982_endtoend": 13}


def record(key, suffix=""):
    return json.loads((HERE / "records" / f"{key}{suffix}.json").read_text())


def ledger():
    return json.loads((HERE / "campaigns/heim_1982_integration_results.json").read_text())


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def baseline_files():
    # Compare the original projection, allowing additive later campaigns.
    return set(json.loads((HERE / "campaigns/heim_1982_integration_baseline_paths.json").read_text())["files"])


class HeimIntegrationTests(unittest.TestCase):
    def test_three_modules_registered_after_dependencies(self):
        project = (ROOT / "_CoqProject").read_text().splitlines()
        links = json.loads((HERE / "paper_evidence.json").read_text())["7"]
        previous = "atlas/dynamic/Heim1982_Indexed.v"
        for path in ledger()["files"]:
            self.assertEqual(project.count(path), 1)
            self.assertGreater(project.index(path), project.index(previous))
            self.assertIn(path, links)
            previous = path

    def test_all_declarations_have_exact_inventory_entries(self):
        results = ledger()
        self.assertEqual([t["id"] for t in results["targets"]], [f"I{n:02d}" for n in range(1, 9)])
        support = {n: target["id"] for target in results["targets"] for n in target["support"]}
        self.assertEqual(len(support), 61)
        measured = set()
        for key, count in COUNTS.items():
            rec, mech = record(key), record(key, ".mech")
            decls, warnings = verify.parse(ROOT / rec["file"])
            self.assertFalse(warnings)
            parsed = {".".join(d["modpath"] + [d["name"]])
                      for d in decls if d["kind"] == "theorem"}
            listed = [t["name"] for t in rec["theorems"]]
            self.assertEqual(len(listed), count)
            self.assertEqual(len(set(listed)), count)
            self.assertEqual(set(listed), parsed)
            prefix = "dynamic." + Path(rec["file"]).stem + "."
            for theorem in rec["theorems"]:
                self.assertEqual(theorem["status"], "proved")
                self.assertEqual(support[prefix + theorem["name"]], theorem["inventory_id"])
                self.assertTrue(theorem["source_claim"])
            measured.update(mech["statements"])
        self.assertEqual(set(support), measured)

    def test_all_61_proofs_are_closed_and_compiled_safely(self):
        for key, count in COUNTS.items():
            mech = record(key, ".mech")
            self.assertTrue(mech["compile"]["ok"])
            self.assertFalse(mech["compile"]["unsafe_flags"])
            self.assertEqual(mech["counts"]["proved"], count)
            self.assertEqual(mech["counts"]["theorems"], count)
            for field in ("admitted", "admitted_definitions", "aborted", "unparsed_status", "toplevel_axioms"):
                self.assertEqual(mech["counts"][field], 0)
            self.assertEqual(mech["assumptions"]["queried"], count)
            self.assertEqual(mech["assumptions"]["closed"], count)
            self.assertFalse(mech["assumptions"]["unresolved"])
            self.assertFalse(mech["assumptions"]["undocumented_axioms"])
            self.assertFalse(mech["disputes_vs_record"])

    def test_depth_flags_retained_and_queries_complete(self):
        for (key, count), trivial in zip(COUNTS.items(), [4, 4, 3]):
            probe = record(key, ".probe")
            self.assertEqual(probe["summary"],
                             {"probed": count, "vacuous": 0, "trivial": trivial, "bailout": 0})
            self.assertEqual(set(probe["probes"]), set(record(key, ".mech")["statements"]))
            for result in probe["probes"].values():
                self.assertFalse(any(v.startswith("BAILOUT") for v in result.values()))

    def test_prior_research_and_frozen_grades_are_unchanged(self):
        previous = json.loads((HERE / "campaigns/heim_1982_manifest.json").read_text())
        shared = {"README.md", "_CoqProject", "atlas_data/ATLAS.md", "atlas_data/atlas.json",
                  "atlas_data/claims.lock", "atlas_data/paper_evidence.json", "atlas_data/site/index.html"}
        for name, expected in previous["files"].items():
            if name in shared:
                continue
            with self.subTest(file=name):
                self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), expected)

    def test_only_new_files_and_heim_links_change_consolidated_evidence(self):
        results = ledger()
        baseline = results["baseline"]
        atlas = json.loads((HERE / "atlas.json").read_text())
        prior = [rec for rec in atlas["files"] if rec["file"] in baseline_files()]
        self.assertEqual(len(prior), baseline["file_count"])
        self.assertEqual(digest(prior), baseline["files_sha256"])
        for paper in atlas["papers"]:
            if str(paper["id"]) == "7":
                self.assertLessEqual(set(results["files"]), set(paper.pop("coq_files")))
        self.assertEqual(digest(atlas["papers"]), baseline["papers_except_heim_links_sha256"])

    def test_previous_claims_unchanged_and_61_new_claims_locked(self):
        results = ledger()
        claims = json.loads((HERE / "claims.lock").read_text())["claims"]
        prior = {n: c for n, c in claims.items() if c["file"] in baseline_files()}
        self.assertEqual(len(prior), results["baseline"]["claim_count"])
        self.assertEqual(digest(prior), results["baseline"]["claim_entries_sha256"])
        self.assertEqual(sum(c["file"] in results["files"] for c in claims.values()), 61)
        for key in COUNTS:
            mech = record(key, ".mech")
            for name, sha in mech["statements"].items():
                self.assertEqual(claims[name]["statement_sha"], sha)
                self.assertEqual(claims[name]["file"], mech["file"])
                self.assertEqual(claims[name]["status"], "active")

    def test_integration_does_not_approve_whole_source(self):
        results = ledger()
        self.assertFalse(results["whole_source_complete"])
        self.assertFalse(results["independent_review"])
        self.assertIsNone(results["accepted_outcome"])
        self.assertEqual(len(results["boundaries"]), 6)
        for key in COUNTS:
            rec = record(key)
            self.assertEqual(rec["assessment_status"], "incomplete")
            self.assertEqual(rec["determination"], "unassessed")
            self.assertEqual(rec["faithfulness"]["verdict"], "partial")
        atlas = json.loads((HERE / "atlas.json").read_text())
        paper = next(p for p in atlas["papers"] if str(p["id"]) == "7")
        self.assertEqual((paper["level"], paper["formality"], paper["determination_status"]),
                         ("F3", 4, "review_required"))
        self.assertIsNone(paper["determination_actual"])


if __name__ == "__main__":
    unittest.main()
