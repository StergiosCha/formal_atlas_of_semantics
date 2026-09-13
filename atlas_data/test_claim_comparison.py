"""Traceability and non-promotion tests; these do not certify source fidelity."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import unittest

from claim_comparison import validate_comparison

HERE = Path(__file__).resolve().parent


class ClaimComparisonTests(unittest.TestCase):
    def setUp(self):
        self.atlas = json.loads((HERE / "atlas.json").read_text())
        self.data = json.loads((HERE / "campaigns/claim_comparison_2026_09_13.json").read_text())

    def validate(self):
        return validate_comparison(self.data, self.atlas["files"], self.atlas["papers"])

    def test_valid_profiles_do_not_mutate_grades_or_outcomes(self):
        before = copy.deepcopy(self.atlas)
        self.validate()
        self.assertEqual(self.atlas, before)
        for profile in self.data["profiles"]:
            paper = next(p for p in self.atlas["papers"] if p["id"] == profile["paper_id"])
            self.assertEqual(paper["level"], "F3")
            self.assertIsNone(paper["determination_actual"])
            self.assertFalse(paper["prediction_disputed"])

    def test_all_inventory_groups_retained_without_success_rate(self):
        expected = {"atlas__derrida1972": ("D", 6), "atlas__austin1962": ("A", 7),
                    "atlas__horn1984": ("H", 6), "atlas__grice1975": ("G", 4),
                    "atlas__tarski1944": ("T", 4)}
        for p in self.data["profiles"]:
            prefix, count = expected[p["record_key"]]
            self.assertEqual({t["id"] for t in p["targets"]},
                             {prefix + str(i) for i in range(1, count + 1)})
            self.assertEqual(p["encoding_robustness"], "not_tested")
            self.assertTrue(p["ordinary_parameters"])
            self.assertNotIn("success_rate", p)
            self.assertNotIn("tier_score", p)

    def test_wrong_frozen_tier_rejected(self):
        self.data["profiles"][0]["formality"] = 5
        with self.assertRaisesRegex(ValueError, "frozen formality"):
            self.validate()

    def test_stale_code_profile_rejected(self):
        self.data["profiles"][0]["code_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Stale claim profile"):
            self.validate()

    def test_unknown_theorem_rejected(self):
        self.data["profiles"][0]["targets"][0]["evidence"] = ["invented_result"]
        with self.assertRaisesRegex(ValueError, "Unknown theorem"):
            self.validate()

    def test_duplicate_profile_rejected(self):
        self.data["profiles"].append(copy.deepcopy(self.data["profiles"][0]))
        with self.assertRaisesRegex(ValueError, "Duplicate claim profile"):
            self.validate()

    def test_duplicate_target_rejected(self):
        p = self.data["profiles"][0]
        p["targets"].append(copy.deepcopy(p["targets"][0]))
        with self.assertRaisesRegex(ValueError, "Duplicate source-target"):
            self.validate()

    def test_uncovered_target_does_not_claim_a_proof(self):
        p = self.data["profiles"][0]
        p["targets"][-1]["evidence"] = p["targets"][0]["evidence"]
        with self.assertRaisesRegex(ValueError, "Uncovered target"):
            self.validate()

    def test_missing_source_limit_rejected(self):
        self.data["profiles"][0]["targets"][0]["limit"] = ""
        with self.assertRaisesRegex(ValueError, "Missing claim traceability"):
            self.validate()

    def test_independent_review_cannot_be_silently_claimed(self):
        self.data["assessment_basis"] = "independent_review"
        with self.assertRaisesRegex(ValueError, "review provenance"):
            self.validate()

    def test_generated_atlas_contains_the_validated_profiles(self):
        self.assertEqual(self.atlas["claim_comparison"], self.data)
        self.assertEqual(len(self.atlas["papers"]), 230)
        self.assertEqual(len({p["id"] for p in self.atlas["papers"]}), 230)

    @unittest.skipUnless(shutil.which("node"), "Node needed for rendered-view tests")
    def test_rendered_views_and_escaping(self):
        result = subprocess.run(["node", str(HERE / "site/test_claim_comparison.cjs")],
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
