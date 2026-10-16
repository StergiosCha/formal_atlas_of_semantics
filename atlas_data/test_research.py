"""Research publication must remain separate from atlas grades and live Coq."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from proof_sources import bundle_sources, library_fingerprint
from research import bundle_research, read_public

ROOT = Path(__file__).resolve().parent.parent


class ResearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.research = bundle_research(ROOT)

    def test_inventory_is_measured_from_separate_checkpoints(self):
        packages = {p["id"]: p for p in self.research["packages"]}
        self.assertEqual(len(self.research["sources"]), 53)
        self.assertEqual([packages[k]["statements"] for k in
                          ("montague_ptq", "montague_core", "montague_legacy")], [443, 173, 76])
        self.assertFalse(self.research["live_execution"])
        self.assertFalse(self.research["readings"]["search_completeness_proved"])
        for key, source in self.research["sources"].items():
            self.assertEqual(source["text"].encode(), (ROOT / source["path"]).read_bytes())
            self.assertEqual(source["sha256"], hashlib.sha256(source["text"].encode()).hexdigest())
            self.assertTrue(key.startswith("research__"))
            self.assertIsNone(source["audit"])

    def test_live_library_and_assessments_are_not_extended(self):
        atlas = json.loads((ROOT / "atlas_data/atlas.json").read_text())
        sources = bundle_sources(atlas["files"], ROOT)
        self.assertFalse(set(sources) & set(self.research["sources"]))
        self.assertFalse({f["file"] for f in atlas["files"]} &
                         {s["path"] for s in self.research["sources"].values()})
        self.assertEqual(len(sources), len(atlas["files"]))
        self.assertEqual(len(library_fingerprint(sources)), 64)

    def test_feature_links_and_legacy_dependencies_are_real(self):
        for feature in self.research["features"]:
            source = self.research["sources"][feature["key"]]
            declaration = next(d for d in source["declarations"] if d["line"] == feature["line"])
            self.assertEqual(declaration["name"], feature["name"])
            self.assertIn(declaration["qualified"], source["research"]["global_dependencies"])
        legacy = self.research["sources"]["research__montague_legacy__LegacyTranslation"]
        self.assertTrue(any(legacy["research"]["global_dependencies"].values()))

    def test_source_drift_fails_closed(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            shutil.copytree(ROOT / "deep/montague_ptq", root / "deep/montague_ptq",
                            ignore=shutil.ignore_patterns("*.vo", "*.glob", "*.aux", "__pycache__"))
            source = root / "deep/montague_ptq/Syntax.v"
            source.write_text(source.read_text() + "\n(* changed *)\n")
            with self.assertRaisesRegex(ValueError, "source/checkpoint mismatch"):
                bundle_research(root)

    def test_symlink_and_path_escape_rejected(self):
        with tempfile.TemporaryDirectory() as folder, tempfile.TemporaryDirectory() as outside:
            root = Path(folder)
            (root / "escape").symlink_to(Path(outside), target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "escapes repository"):
                read_public(root, "escape/anything")
            with self.assertRaisesRegex(ValueError, "escapes repository"):
                read_public(root, "../anything")


if __name__ == "__main__":
    unittest.main()
