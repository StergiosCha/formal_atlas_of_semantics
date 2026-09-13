"""Source-review gating and provenance checks, not semantic approval."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import consolidate
from outcome_policy import apply_outcome, load_reviews

HERE = Path(__file__).resolve().parent


def example_record():
    return {"_key": "example", "file": "atlas/Example.v",
            "determination": "as_is", "faithfulness": {"verdict": "faithful"},
            "counts": {"proved": 1, "admitted": 0},
            "_mech": {"compiles": True, "queried": 1, "unsafe_flags": [],
                      "undocumented_axioms": []},
            "theorems": [{"name": "example", "status": "proved"}]}


def example_paper():
    return {"id": 1, "citation": "Example (2026). The source.",
            "coq_files": ["atlas/Example.v"], "survey_determination": "as_is"}


class CandidateTests(unittest.TestCase):
    def test_even_faithful_file_and_agreeing_review_do_not_approve_source(self):
        rec = example_record()
        rec["_verify"] = {"agrees": True}
        paper = apply_outcome(example_paper(), [rec])
        self.assertIsNone(paper["determination_actual"])
        self.assertFalse(paper["prediction_disputed"])
        self.assertEqual(paper["determination_status"], "review_required")
        self.assertEqual(paper["determination_candidates"][0]["determination"], "as_is")

    def test_all_candidates_retained_order_independently(self):
        a, b = example_record(), example_record()
        b.update(_key="another", determination="major_restructuring")
        first = apply_outcome(example_paper(), [a, b])
        second = apply_outcome(example_paper(), [b, a])
        self.assertEqual(first, second)
        self.assertTrue(first["record_outcome_conflict"])
        self.assertIsNone(first["determination_actual"])

    def test_cautions_do_not_erase_original_opinion(self):
        rec = example_record()
        rec.update(assessment_status="pilot", faithfulness={"verdict": "unfaithful"})
        rec["counts"] = {"proved": 0, "admitted": 2}
        rec["_mech"].update(compiles=False, unsafe_flags=["guard"],
                            undocumented_axioms=["Signature.individual"])
        c = apply_outcome(example_paper(), [rec])["determination_candidates"][0]
        self.assertEqual(c["determination"], "as_is")
        self.assertEqual(len(c["record_limits"]), 7)

    def test_non_outcomes_do_not_become_candidates(self):
        for value in (None, "not_applicable", "unassessed"):
            rec = example_record()
            rec["determination"] = value
            paper = apply_outcome(example_paper(), [rec])
            self.assertEqual(paper["determination_status"], "unassessed")
            self.assertEqual(paper["determination_candidates"], [])

    def test_missing_or_unknown_file_agreement_is_not_a_dispute(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "example.json").write_text(json.dumps(example_record()))
            for value in (None, True, False):
                (root / "example.verify.json").write_text(json.dumps({"agrees": value}))
                with patch.object(consolidate, "REC", directory):
                    rec = consolidate.merge_records()[0]
                self.assertEqual(rec["_final"]["disputed"], value is False)
            (root / "example.verify.json").write_text('{"confidence": "unknown"}')
            with patch.object(consolidate, "REC", directory):
                self.assertFalse(consolidate.merge_records()[0]["_final"]["disputed"])


class ReviewValidationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.rec, self.paper = example_record(), example_paper()
        self.paths = {"code_sha256": "atlas/Example.v",
                      "record_sha256": "atlas_data/records/example.json",
                      "mechanical_sha256": "atlas_data/records/example.mech.json"}
        support = {"record_key": "example", "theorems": ["example"]}
        for field, rel in self.paths.items():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("fixture evidence: " + field)
            support[field] = hashlib.sha256(path.read_bytes()).hexdigest()
        # Synthetic test declaration, never installed in the real review registry.
        self.review = {"paper_id": 1, "source_citation": self.paper["citation"],
                       "status": "reviewed", "determination": "as_is", "coverage": "source_core",
                       "scope": "Declared test core", "coverage_justification": "Fixture only",
                       "source_passages": "Fixture page 1", "reviewer": "Test fixture",
                       "review_reference": "Fixture review", "independence_statement": "Fixture only",
                       "rationale": "Fixture rationale", "record_resolution": "One fixture record",
                       "support": [support]}

    def load(self, reviews=None):
        path = self.root / "reviews.json"
        path.write_text(json.dumps({"schema_version": 1,
                                   "reviews": [self.review] if reviews is None else reviews}))
        return load_reviews(path, [self.paper], [self.rec], self.root)

    def test_empty_registry_does_not_invent_reviews(self):
        self.assertEqual(self.load([]), {})

    def test_valid_declaration_controls_outcome_and_comparison(self):
        for prediction, differs in (("as_is", False), ("major_restructuring", True), (None, False)):
            paper = copy.deepcopy(self.paper)
            paper["survey_determination"] = prediction
            result = apply_outcome(paper, [self.rec], self.load())
            self.assertEqual(result["determination_actual"], "as_is")
            self.assertEqual(result["determination_status"], "reviewed")
            self.assertEqual(result["prediction_disputed"], differs)

    def test_wrong_or_missing_source_review_provenance_rejected(self):
        bad = {"paper_id": 99, "source_citation": "Another paper", "status": "pending",
               "determination": "not_applicable", "coverage": "fragment", "scope": "",
               "coverage_justification": "", "reviewer": "", "review_reference": "",
               "independence_statement": "", "source_passages": "", "rationale": "",
               "record_resolution": "", "support": []}
        original = copy.deepcopy(self.review)
        for field, value in bad.items():
            with self.subTest(field=field):
                self.review = dict(original, **{field: value})
                with self.assertRaises(ValueError):
                    self.load()

    def test_duplicate_review_or_support_rejected(self):
        with self.assertRaises(ValueError):
            self.load([self.review, self.review])
        self.review["support"] *= 2
        with self.assertRaises(ValueError):
            self.load()

    def test_unknown_unlinked_and_unproved_support_rejected(self):
        item = self.review["support"][0]
        item["record_key"] = "unknown"
        with self.assertRaises(ValueError):
            self.load()
        item["record_key"] = "example"
        item["theorems"] = ["invented"]
        with self.assertRaises(ValueError):
            self.load()
        item["theorems"] = ["example"]
        self.paper["coq_files"] = []
        with self.assertRaises(ValueError):
            self.load()

    def test_stale_code_record_or_mechanical_evidence_rejected(self):
        for rel in self.paths.values():
            with self.subTest(file=rel):
                path = self.root / rel
                original = path.read_text()
                path.write_text("changed")
                with self.assertRaisesRegex(ValueError, "Stale"):
                    self.load()
                path.write_text(original)

    def test_incomplete_or_unfaithful_evidence_rejected(self):
        for field, value in (("assessment_status", "pilot"), ("assessment_status", "incomplete"),
                             ("faithfulness", {"verdict": "partial"}),
                             ("counts", {"proved": 1, "admitted": 1}),
                             ("counts", {"proved": 0, "admitted": 0})):
            with self.subTest(field=field, value=value):
                self.rec = dict(example_record(), **{field: value})
                with self.assertRaises(ValueError):
                    self.load()

    def test_failed_unsafe_or_unqueried_mechanical_evidence_rejected(self):
        for field, value in (("compiles", False), ("unsafe_flags", ["guard"]), ("queried", 0)):
            with self.subTest(field=field):
                self.rec = example_record()
                self.rec["_mech"][field] = value
                with self.assertRaises(ValueError):
                    self.load()

    def test_assumption_parameters_need_review_not_automatic_rejection(self):
        self.rec["_mech"]["undocumented_axioms"] = ["Signature.individual"]
        with self.assertRaises(ValueError):
            self.load()
        self.review["support"][0]["assumption_evidence"] = {
            "Signature.individual": "Signature type parameter; not a propositional premise."}
        self.assertIn("1", self.load())

    def test_resistance_outcomes_require_necessity_not_just_partial_code(self):
        self.rec["faithfulness"]["verdict"] = "partial"
        for outcome in ("major_restructuring", "cannot"):
            self.review["determination"] = outcome
            self.review.pop("necessity_evidence", None)
            with self.assertRaises(ValueError):
                self.load()
            self.review["necessity_evidence"] = "Fixture obstruction argument, not a real review."
            self.assertIn("1", self.load())


class RepositoryOutcomeTests(unittest.TestCase):
    def test_all_230_sources_preserve_levels_and_frozen_grades(self):
        atlas = json.loads((HERE / "atlas.json").read_text())
        audit = json.loads((HERE / "audits/outcome_flags_2026_09_13.json").read_text())
        previous = {str(p["id"]): p for p in audit["papers"]}
        self.assertEqual(len(previous), 230)
        self.assertEqual(len(atlas["papers"]), 230)
        old_flags, old_outcomes = [], []
        for paper in atlas["papers"]:
            before = previous[str(paper["id"])]["before"]
            self.assertEqual((paper["level"], paper["formality"]),
                             (before["level"], before["formality"]))
            self.assertFalse(paper["prediction_disputed"])
            self.assertIsNone(paper["determination_actual"])
            if before["prediction_disputed"]:
                old_flags.append(str(paper["id"]))
            if before["determination_actual"]:
                old_outcomes.append(paper)
        self.assertEqual(set(old_flags), {"7", "11", "19", "26", "31", "32", "33", "36", "50", "159"})
        self.assertEqual(len(old_outcomes), 29)
        self.assertTrue(all(p["determination_candidates"] for p in old_outcomes))
        self.assertEqual(atlas["stats"]["paper_outcome_status"],
                         {"unassessed": 201, "review_required": 29})
        self.assertEqual(atlas["stats"]["paper_outcomes"], {})


if __name__ == "__main__":
    unittest.main()
