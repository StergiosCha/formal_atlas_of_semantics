"""Source-bundle integrity and path confinement, independent of Coq execution."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from proof_sources import bundle_sources


ROOT = Path(__file__).resolve().parent.parent


class ProofSourceTests(unittest.TestCase):
    def test_every_record_bundles_exact_repository_bytes(self):
        records = json.loads((ROOT / "atlas_data/atlas.json").read_text())["files"]
        sources = bundle_sources(records, ROOT)
        self.assertEqual(len(sources), len(records))
        for source in sources.values():
            raw = (ROOT / source["path"]).read_bytes()
            self.assertEqual(source["text"].encode("utf-8"), raw)
            self.assertEqual(source["sha256"], hashlib.sha256(raw).hexdigest())
            for d in source["declarations"]:
                self.assertIn(d["name"].split(".")[-1], source["text"].splitlines()[d["line"] - 1])
        ttr = sources["atlas__ttr_model"]
        self.assertTrue(any(d["name"] == "Countermodels.inhabited_conjuncts_empty_meet"
                            for d in ttr["declarations"]))

    def test_no_audit_does_not_invent_one_and_bytes_are_preserved(self):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            (repo / "atlas").mkdir()
            raw = b'(* source <script> *)\r\nLemma witness : True. Proof. exact I. Qed.\r\n'
            (repo / "atlas/Test.v").write_bytes(raw)
            result = bundle_sources([{"file": "atlas/Test.v", "key": "test"}], repo)["test"]
            self.assertEqual(result["text"].encode(), raw)
            self.assertIsNone(result["audit"])

    def test_paths_missing_sources_and_wrong_audits_fail_build(self):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            for path in ("../escape.v", "/etc/escape.v", "README.md", "tool/private.v"):
                with self.assertRaises(ValueError, msg=path):
                    bundle_sources([{"file": path, "key": "bad"}], repo)
            with self.assertRaises(FileNotFoundError):
                bundle_sources([{"file": "atlas/Missing.v", "key": "bad"}], repo)
            (repo / "atlas").mkdir()
            (repo / "atlas/Test.v").write_text("Lemma ok : True. Proof. exact I. Qed.\n")
            (repo / "atlas_data/records").mkdir(parents=True)
            (repo / "atlas_data/records/test.mech.json").write_text('{"file":"atlas/Wrong.v"}')
            with self.assertRaisesRegex(ValueError, "Audit/source mismatch"):
                bundle_sources([{"file": "atlas/Test.v", "key": "test"}], repo)

    def test_symlink_escape_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp, tempfile.TemporaryDirectory() as outside:
            repo = Path(temp)
            (repo / "atlas").mkdir()
            target = Path(outside) / "Private.v"
            target.write_text("(* must not publish *)")
            (repo / "atlas/Private.v").symlink_to(target)
            with self.assertRaises(ValueError):
                bundle_sources([{"file": "atlas/Private.v", "key": "bad"}], repo)


if __name__ == "__main__":
    unittest.main()
