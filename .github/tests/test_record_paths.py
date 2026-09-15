"""The verifier must bind the same source records on macOS and Linux CI."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "atlas_data"))
import verify


class RecordPathTests(unittest.TestCase):
    def test_relative_and_relocated_absolute_paths_resolve_identically(self):
        files = ["extras/FocusEven.v", "atlas/dynamic/DPL.v"]
        for rel in files:
            for prefix in ("", "/Users/old/checkout/", "/__w/repo/repo/", "/tmp/new/"):
                self.assertEqual(verify.record_project_path(prefix + rel, files), rel)

    def test_no_basename_fuzzy_or_case_insensitive_matching(self):
        files = ["extras/FocusEven.v"]
        for value in (None, "FocusEven.v", "/another/FocusEven.v",
                      "/tmp/notextras/FocusEven.v", "/tmp/extras/focuseven.v",
                      "other/extras/FocusEven.v"):
            with self.subTest(value=value):
                self.assertIsNone(verify.record_project_path(value, files))

    def test_ambiguous_suffix_is_an_error(self):
        with self.assertRaisesRegex(ValueError, "Ambiguous"):
            verify.record_project_path("/old/extras/Thing.v", ["Thing.v", "extras/Thing.v"])

    def test_duplicate_or_malformed_records_fail_visibly(self):
        with tempfile.TemporaryDirectory(prefix="atlas-record-index-") as directory:
            root = Path(directory)
            record = {"file": "extras/Thing.v"}
            (root / "one.json").write_text(json.dumps(record))
            (root / "two.json").write_text(json.dumps(record))
            with patch.object(verify, "REC", directory):
                with self.assertRaisesRegex(ValueError, "Duplicate"):
                    verify.index_records([record["file"]])
                (root / "two.json").write_text("malformed")
                with self.assertRaises(json.JSONDecodeError):
                    verify.index_records([record["file"]])

    def test_all_real_project_files_keep_their_record_keys_on_ci(self):
        files = [line.strip() for line in (ROOT / "_CoqProject").read_text().splitlines()
                 if line.strip().endswith(".v")]
        with patch.object(verify, "REPO", "/__w/fresh/repository"):
            index = verify.index_records(files)
        self.assertEqual(set(index), set(files))
        absolute_records = 0
        for rel, (key, record) in index.items():
            if record["file"].startswith("/"):
                absolute_records += 1
            self.assertEqual(record, json.loads((ROOT / "atlas_data/records" / (key + ".json")).read_text()))
            mech = json.loads((ROOT / "atlas_data/records" / (key + ".mech.json")).read_text())
            self.assertEqual(mech["file"], rel)
            self.assertEqual(mech["key"], key)
        self.assertEqual(absolute_records, 17)
        self.assertEqual(index["extras/FocusEven.v"][0], "extras__FocusEven")

    def test_five_discrepancy_records_remain_attached_to_their_claims(self):
        files = [line.strip() for line in (ROOT / "_CoqProject").read_text().splitlines()
                 if line.strip().endswith(".v")]
        index = verify.index_records(files)
        for rel in ("deep/kratzer_deep2.v", "extras/dowty_roles.v", "extras/mass.v",
                    "extras/quanrifiers2.v", "shallow/kratzer2.v"):
            key, record = index[rel]
            before = copy.deepcopy(record)
            mech = json.loads((ROOT / "atlas_data/records" / (key + ".mech.json")).read_text())
            self.assertTrue(mech["disputes_vs_record"])
            for dispute in mech["disputes_vs_record"]:
                self.assertEqual(dispute["claimed"], record["counts"][dispute["field"].split(".")[1]])
            self.assertEqual(record, before)


if __name__ == "__main__":
    unittest.main()
