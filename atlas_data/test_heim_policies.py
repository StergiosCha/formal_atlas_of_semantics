"""Policy-comparison evidence checks; not empirical or independent source review."""
import hashlib
import json
from pathlib import Path
import unittest

import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
KEY = "atlas__heim1982_policies"


def record(suffix=""):
    return json.loads((HERE / "records" / f"{KEY}{suffix}.json").read_text())


def ledger():
    return json.loads((HERE / "campaigns/heim_1982_policy_results.json").read_text())


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


class HeimPolicyTests(unittest.TestCase):
    def test_registered_and_linked(self):
        rec = record()
        project = (ROOT / "_CoqProject").read_text().splitlines()
        links = json.loads((HERE / "paper_evidence.json").read_text())["7"]
        self.assertEqual(project.count(rec["file"]), 1)
        self.assertGreater(project.index(rec["file"]), project.index("atlas/dynamic/Heim1982_EndToEnd.v"))
        self.assertIn(rec["file"], links)

    def test_all_33_statements_mapped(self):
        rec = record()
        decls, warnings = verify.parse(ROOT / rec["file"])
        self.assertFalse(warnings)
        parsed = {".".join(d["modpath"] + [d["name"]]) for d in decls if d["kind"] == "theorem"}
        names = [t["name"] for t in rec["theorems"]]
        self.assertEqual(len(names), 33)
        self.assertEqual(set(names), parsed)
        self.assertEqual(len(set(names)), 33)
        targets = ledger()["targets"]
        self.assertEqual([t["id"] for t in targets], [f"K{n:02d}" for n in range(1, 8)])
        support = {n: t["id"] for t in targets for n in t["support"]}
        self.assertEqual(set(support), set(record(".mech")["statements"]))
        for theorem in rec["theorems"]:
            self.assertEqual(theorem["status"], "proved")
            self.assertEqual(support["dynamic.Heim1982_Policies." + theorem["name"]], theorem["inventory_id"])
            self.assertTrue(theorem["source_claim"])

    def test_safe_complete_closed_mechanical_audit(self):
        mech = record(".mech")
        self.assertTrue(mech["compile"]["ok"])
        self.assertFalse(mech["compile"]["unsafe_flags"])
        self.assertEqual(mech["counts"]["proved"], 33)
        self.assertEqual(mech["counts"]["theorems"], 33)
        for field in ("admitted", "admitted_definitions", "aborted", "unparsed_status", "toplevel_axioms"):
            self.assertEqual(mech["counts"][field], 0)
        self.assertEqual(mech["assumptions"]["queried"], 33)
        self.assertEqual(mech["assumptions"]["closed"], 33)
        self.assertFalse(mech["assumptions"]["unresolved"])
        self.assertFalse(mech["assumptions"]["undocumented_axioms"])
        self.assertFalse(mech["disputes_vs_record"])

    def test_depth_flags_retained(self):
        probe = record(".probe")
        self.assertEqual(probe["summary"], {"probed": 33, "vacuous": 0, "trivial": 3, "bailout": 0})
        self.assertEqual(set(probe["probes"]), set(record(".mech")["statements"]))
        self.assertEqual({n.removeprefix("dynamic.Heim1982_Policies.")
                          for n, p in probe["probes"].items() if p["triviality"] == "TRIVIAL"},
                         {"repaired_description_licensed", "world_safe_implies_bridge_only", "deny_is_least_policy"})

    def test_prior_research_and_grades_preserved(self):
        prior = json.loads((HERE / "campaigns/heim_1982_integration_manifest.json").read_text())
        expected_changes = {"README.md", "_CoqProject", "atlas_data/ATLAS.md", "atlas_data/atlas.json",
                            "atlas_data/claims.lock", "atlas_data/paper_evidence.json", "atlas_data/site/index.html",
                            "atlas_data/test_heim_integration.py"}
        for path, expected in prior["files"].items():
            if path in expected_changes:
                continue
            with self.subTest(file=path):
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), expected)

    def test_prior_85_records_1129_claims_and_paper_outcomes_unchanged(self):
        data = ledger()
        base = data["baseline"]
        atlas = json.loads((HERE / "atlas.json").read_text())
        prior_files = [f for f in atlas["files"] if f["file"] in base["files"]]
        self.assertEqual(len(prior_files), 85)
        self.assertEqual(digest(prior_files), base["files_sha256"])
        for paper in atlas["papers"]:
            if str(paper["id"]) == "7":
                self.assertIn(record()["file"], paper.pop("coq_files"))
        self.assertEqual(digest(atlas["papers"]), base["papers_except_heim_links_sha256"])
        claims = json.loads((HERE / "claims.lock").read_text())["claims"]
        old_claims = {n: c for n, c in claims.items() if c["file"] in base["files"]}
        self.assertEqual(len(old_claims), 1129)
        self.assertEqual(digest(old_claims), base["claim_entries_sha256"])
        for name, sha in record(".mech")["statements"].items():
            self.assertEqual(claims[name]["statement_sha"], sha)
            self.assertEqual(claims[name]["status"], "active")

    def test_every_comparison_has_checked_support(self):
        data = ledger()
        proved = {t["name"] for t in record()["theorems"]}
        self.assertEqual(len(data["negation_comparison"]), 2)
        self.assertEqual(len(data["proxy_comparison"]), 3)
        for row in data["negation_comparison"] + data["proxy_comparison"]:
            self.assertTrue(row["support"])
            self.assertLessEqual(set(row["support"]), proved)
        self.assertEqual(len(data["commitments"]), 5)

    def test_no_default_policy_or_whole_source_outcome_adopted(self):
        data, rec = ledger(), record()
        self.assertIsNone(data["selected_default_policy"])
        self.assertIsNone(data["accepted_outcome"])
        self.assertFalse(data["whole_source_complete"])
        self.assertFalse(data["independent_review"])
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
