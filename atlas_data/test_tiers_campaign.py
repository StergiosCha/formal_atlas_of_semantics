"""Checks for the September 2026 P0/P1/P2 campaign's reporting contract.

These validate traceability and honest evidence levels, not source faithfulness.
"""
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import consolidate
import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
COHORT = {
    "172": ("atlas__derrida1972", 0),
    "177": ("atlas__austin1962", 1),
    "67": ("atlas__horn1984", 2),
}
FROZEN = {
    "formality.json": "35dc302ae28c91e7e7d4c9677713b35bbd6af014ccb3aef6253e126f59eead0e",
    "papers.json": "176bb99d48bc4d2eee9a1eab0896ab5d04e416e3eb189abc16e2849446fe7e98",
    "papers_addendum.json": "c119cac262bdab87d1a8f6a2e6f9efcffc074d64aaed58c42208c1a57edc9880",
}


def read_record(key, suffix=""):
    return json.loads((HERE / "records" / (key + suffix + ".json")).read_text())


class TierCampaignTests(unittest.TestCase):
    def test_frozen_survey_and_grades_unchanged(self):
        for name, digest in FROZEN.items():
            with self.subTest(file=name):
                self.assertEqual(hashlib.sha256((HERE / name).read_bytes()).hexdigest(), digest)
        grades = json.loads((HERE / "formality.json").read_text())
        self.assertEqual(len(grades), 230)
        for paper, (_, tier) in COHORT.items():
            self.assertEqual(grades[paper]["formality"], tier)

    def test_every_proof_has_explicit_source_or_new_mapping(self):
        for key, _ in COHORT.values():
            record = read_record(key)
            declarations, warnings = verify.parse(ROOT / record["file"])
            self.assertFalse(warnings)
            expected = {".".join(d["modpath"] + [d["name"]])
                        for d in declarations if d["kind"] == "theorem"}
            listed = [t["name"] for t in record["theorems"]]
            self.assertEqual(len(listed), len(set(listed)))
            self.assertEqual(set(listed), expected)
            for theorem in record["theorems"]:
                self.assertTrue(theorem["source_claim"])
                self.assertTrue(theorem["inventory_id"])
                self.assertIn(theorem["claim_kind"], {
                    "new", "illustrative reconstruction", "conditional result",
                    "direct source formalization"})

    def test_pilots_do_not_become_whole_source_outcomes(self):
        links = json.loads((HERE / "paper_evidence.json").read_text())
        for paper, (key, _) in COHORT.items():
            record = read_record(key)
            self.assertIn(record["file"], links[paper])
            self.assertIn(record["file"], (ROOT / "_CoqProject").read_text().splitlines())
            self.assertEqual(record["assessment_status"], "pilot")
            self.assertEqual(record["determination"], "unassessed")
            # Even a future edge/agreement must not silently promote a pilot.
            record["_verify"] = {"agrees": True}
            p = {"id": paper, "coq_files": links[paper], "survey_determination": "cannot"}
            edges = [{"a_file": record["file"], "b_file": "unused.v"}]
            with patch.dict("os.environ", {"ATLAS_PAPERS": "/nonexistent-test-corpus"}):
                result = consolidate.compute_levels([p], [record], edges)[0]
            self.assertEqual(result["level"], "F3")
            self.assertIsNone(result["determination_actual"])
            self.assertFalse(result["prediction_disputed"])

    def test_mechanical_records_are_closed_and_complete(self):
        for key, _ in COHORT.values():
            record, mech = read_record(key), read_record(key, ".mech")
            self.assertTrue(mech["compile"]["ok"])
            self.assertFalse(mech["compile"]["unsafe_flags"])
            self.assertEqual(mech["counts"]["proved"], len(record["theorems"]))
            for field in ("admitted", "admitted_definitions", "aborted", "unparsed_status", "toplevel_axioms"):
                self.assertEqual(mech["counts"][field], 0)
            self.assertEqual(mech["assumptions"]["closed"], len(record["theorems"]))
            self.assertFalse(mech["assumptions"]["unresolved"])
            self.assertFalse(mech["disputes_vs_record"])

    def test_probe_findings_are_preserved(self):
        vacuous, trivial = set(), set()
        for key, _ in COHORT.values():
            probe = read_record(key, ".probe")
            self.assertEqual(len(probe["probes"]), len(read_record(key)["theorems"]))
            for name, results in probe["probes"].items():
                self.assertFalse(any(v.startswith("BAILOUT") for v in results.values()))
                if results["vacuity"] == "VACUOUS":
                    vacuous.add(name)
                if results["triviality"] == "TRIVIAL":
                    trivial.add(name)
        self.assertEqual(vacuous, {"pragmatics.Horn1984.q_r_incompatible"})
        self.assertEqual(len(trivial), 10)


if __name__ == "__main__":
    unittest.main()
