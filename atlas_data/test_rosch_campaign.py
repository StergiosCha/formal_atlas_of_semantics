"""Rosch pilot traceability/reporting checks, not semantic-fidelity grading."""
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import consolidate
import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
KEY = "atlas__pilots__rosch1978"


def record(suffix=""):
    return json.loads((HERE / "records" / f"{KEY}{suffix}.json").read_text())


class RoschCampaignTests(unittest.TestCase):
    def test_frozen_cohort_materials_and_grades_unchanged(self):
        previous = json.loads((HERE / "campaigns/cohort2_2026_09_13_manifest.json").read_text())
        names = [p for p in previous["files"] if "campaigns/cohort2_2026_09_13" in p]
        names += ["atlas_data/formality.json", "atlas_data/papers.json",
                  "atlas_data/papers_addendum.json"]
        self.assertEqual(len(names), 10)
        for name in names:
            with self.subTest(file=name):
                self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(),
                                 previous["files"][name])

    def test_all_eight_inventory_targets_have_scoped_dispositions(self):
        rec = record()
        self.assertEqual([d["inventory_id"] for d in rec["inventory_dispositions"]],
                         [f"R2-{n:02d}" for n in range(1, 9)])
        for disposition in rec["inventory_dispositions"]:
            self.assertTrue(disposition["scope"])
        by_id = {d["inventory_id"]: d["disposition"] for d in rec["inventory_dispositions"]}
        self.assertEqual(by_id["R2-02"], "representation only")
        self.assertEqual(by_id["R2-03"], "conditional/source-linked fragment")
        self.assertEqual(by_id["R2-04"], "illustrative model")
        self.assertEqual(sum(v == "uncovered" for v in by_id.values()), 5)

    def test_each_checked_declaration_has_an_explicit_mapping(self):
        rec = record()
        decls, warnings = verify.parse(ROOT / rec["file"])
        self.assertFalse(warnings)
        expected = {".".join(d["modpath"] + [d["name"]])
                    for d in decls if d["kind"] == "theorem"}
        listed = [t["name"] for t in rec["theorems"]]
        self.assertEqual(len(listed), len(set(listed)))
        self.assertEqual(set(listed), expected)
        self.assertEqual(len(listed), 25)
        for theorem in rec["theorems"]:
            self.assertEqual(theorem["status"], "proved")
            self.assertIn(theorem["inventory_id"], {"R2-03", "R2-04"})
            self.assertIn(theorem["claim_kind"],
                          {"new", "conditional result", "illustrative reconstruction"})
            self.assertTrue(theorem["source_claim"])

    def test_mechanical_checks_are_complete_and_closed(self):
        mech = record(".mech")
        self.assertTrue(mech["compile"]["ok"])
        self.assertFalse(mech["compile"]["unsafe_flags"])
        self.assertEqual(mech["counts"]["proved"], 25)
        for name in ("admitted", "admitted_definitions", "aborted",
                     "unparsed_status", "toplevel_axioms"):
            self.assertEqual(mech["counts"][name], 0)
        self.assertEqual(mech["assumptions"]["queried"], 25)
        self.assertEqual(mech["assumptions"]["closed"], 25)
        self.assertFalse(mech["assumptions"]["unresolved"])
        self.assertFalse(mech["disputes_vs_record"])

    def test_probe_flags_are_preserved_not_treated_as_semantic_verdicts(self):
        probe = record(".probe")
        self.assertEqual(probe["summary"],
                         {"probed": 25, "vacuous": 0, "trivial": 5, "bailout": 0})
        expected = {
            "ConstructedCategories.fixed_cues_favor_parent",
            "ConstructedCategories.assigned_category_cues_allow_interior_maximum",
            "ConstructedCategories.undefined_is_not_defined_zero",
            "ConstructedCategories.negative_weight_breaks_monotonicity",
            "Typicality.ConstructedBirds.members_can_differ_in_typicality",
        }
        actual = {n.removeprefix("pilots.Rosch1978.") for n, p in probe["probes"].items()
                  if p["triviality"] == "TRIVIAL"}
        self.assertEqual(actual, expected)
        for result in probe["probes"].values():
            self.assertFalse(any(v.startswith("BAILOUT") for v in result.values()))

    def test_pilot_cannot_become_a_whole_source_verdict(self):
        rec = record()
        links = json.loads((HERE / "paper_evidence.json").read_text())
        self.assertIn(rec["file"], links["122"])
        self.assertIn(rec["file"], (ROOT / "_CoqProject").read_text().splitlines())
        self.assertEqual(rec["assessment_status"], "pilot")
        self.assertEqual(rec["determination"], "unassessed")
        rec["_verify"] = {"agrees": True}
        paper = {"id": "122", "coq_files": links["122"],
                 "survey_determination": "major_restructuring"}
        with patch.dict("os.environ", {"ATLAS_PAPERS": "/nonexistent-test-corpus"}):
            actual = consolidate.compute_levels([paper], [rec],
                [{"a_file": rec["file"], "b_file": "unused.v"}])[0]
        self.assertEqual(actual["level"], "F3")
        self.assertIsNone(actual["determination_actual"])
        self.assertFalse(actual["prediction_disputed"])


if __name__ == "__main__":
    unittest.main()
