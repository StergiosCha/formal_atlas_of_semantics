"""Regression tests for evidence status versus theory determinations."""
import copy
import unittest
from unittest.mock import patch

import consolidate


class EvidenceStatusTests(unittest.TestCase):
    def grade(self, status=None, determination="as_is", agrees=None, edge=False):
        rec = {"file": "atlas/test/Example.v", "counts": {"admitted": 0},
               "determination": determination}
        if status:
            rec["assessment_status"] = status
        if agrees is not None:
            rec["_verify"] = {"agrees": agrees}
        paper = {"id": 1, "coq_files": [rec["file"]],
                 "survey_determination": "as_is"}
        edges = [{"a_file": rec["file"], "b_file": "unused.v"}] if edge else []
        with patch.dict("os.environ", {"ATLAS_PAPERS": "/nonexistent-test-corpus"}):
            return consolidate.compute_levels([copy.deepcopy(paper)], [rec], edges)[0]

    def test_incomplete_code_does_not_become_source_verified_via_edge(self):
        p = self.grade("incomplete", "unassessed", edge=True)
        self.assertEqual(p["level"], "F3")
        self.assertIsNone(p["determination_actual"])
        self.assertFalse(p["prediction_disputed"])

    def test_clean_pilot_remains_pilot(self):
        self.assertEqual(self.grade("pilot", "unassessed")["level"], "F3")

    def test_disagreeing_review_is_not_agreement(self):
        self.assertEqual(self.grade(agrees=False)["level"], "F4")
        self.assertEqual(self.grade(agrees=True)["level"], "F5")

    def test_graded_edge_remains_existing_alternative(self):
        self.assertEqual(self.grade(edge=True)["level"], "F5")

    def test_infrastructure_is_not_a_theory_outcome(self):
        p = self.grade(determination="not_applicable")
        self.assertIsNone(p["determination_actual"])
        self.assertFalse(p["prediction_disputed"])

    def test_actual_determination_can_dispute_prediction(self):
        p = self.grade(determination="slight_modification")
        self.assertTrue(p["prediction_disputed"])


if __name__ == "__main__":
    unittest.main()
