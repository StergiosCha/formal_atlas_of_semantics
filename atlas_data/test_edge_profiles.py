"""No numerical/theory-level promotion; scoped support and archive integrity."""
import copy
import json
from pathlib import Path
import unittest

import consolidate
import edge_profiles as profiles

HERE = Path(__file__).resolve().parent


class EdgeProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.edges = consolidate.merge_edges()
        cls.data = json.loads((HERE / "edge_profiles.json").read_text())

    def test_all_nine_edges_have_explicit_unassessed_obligations(self):
        self.assertEqual(len(self.edges), 9)
        for e in self.edges:
            self.assertNotIn("_computed", e)
            self.assertIn("_legacy_scores", e)
            p = e["_profile"]
            self.assertEqual(p["theory_relation"], "unassessed")
            self.assertEqual({o["id"] for o in p["obligations"]}, set(profiles.OBLIGATIONS))
            self.assertTrue(all(o["status"] == "unassessed" for o in p["obligations"]))

    def test_high_historical_mean_does_not_approve_equivalence(self):
        e = next(e for e in self.edges if e["_key"] == "ptq__lambek")
        self.assertEqual(e["_legacy_scores"]["similarity"], 5)
        self.assertEqual(e["_profile"]["theory_relation"], "unassessed")
        self.assertEqual(e["_profile"]["coverage"]["shared"], 4)

    def test_missing_bridge_and_information_loss_are_explicit(self):
        e = {e["_key"]: e for e in self.edges}
        self.assertIsNone(e["lambek__discocat"]["bridge_file"])
        self.assertFalse(e["lambek__discocat"]["_profile"]["support"])
        self.assertIn("No Coq bridge yet", e["lambek__discocat"]["_profile"]["direction"])
        ttr = e["ttr__mtt"]["_profile"]
        self.assertEqual(ttr["coverage"]["a_only"], ["external-type-assignments"])
        self.assertIn("subject projection only", ttr["limitations"])

    def test_original_edge_inputs_and_annotations_are_unchanged(self):
        restored = profiles.legacy_atlas_view({"edges": self.edges})["edges"]
        for e in restored:
            original = json.loads((HERE / "edges" / (e["_key"] + ".json")).read_text())
            self.assertEqual({k: v for k, v in e.items() if not k.startswith("_")}, original)

    def test_unknown_changed_and_stale_support_is_rejected(self):
        for mutate in (
            lambda p: p.update(theory_relation="equivalent"),
            lambda p: p.update(scope=""),
            lambda p: p["support"][0].update(source_sha256="0" * 64),
            lambda p: p["support"][0].update(theorems={"invented.theorem": "abc"}),
            lambda p: p["support"][0].update(record_key="../private"),
        ):
            data = copy.deepcopy(self.data)
            mutate(data["profiles"]["ttr__mtt"])
            with self.assertRaises(ValueError):
                profiles.validate_profiles(data, self.edges)

    def test_missing_profile_and_duplicate_checklist_entries_fail(self):
        data = copy.deepcopy(self.data)
        del data["profiles"]["ttr__mtt"]
        with self.assertRaises(ValueError):
            profiles.validate_profiles(data, self.edges)
        edges = copy.deepcopy(self.edges)
        edges[0]["phenomena"].append(edges[0]["phenomena"][0])
        with self.assertRaises(ValueError):
            profiles.attach_profiles(edges, self.data["profiles"])


if __name__ == "__main__":
    unittest.main()
