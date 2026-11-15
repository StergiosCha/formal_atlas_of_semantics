"""Privacy redaction cannot silently accept a different research baseline."""
import json
import unittest

from privacy_migration import LEDGER, LEDGERS, expected_digest, step


class PrivacyMigrationTests(unittest.TestCase):
    def test_only_named_original_fingerprints_can_be_migrated(self):
        entries = json.loads(LEDGER.read_text())["fingerprints"]
        self.assertEqual(len(entries), 10)
        for scope, entry in entries.items():
            with self.subTest(scope=scope):
                self.assertEqual(step(LEDGER, scope, entry["before"]), entry["after"])
                self.assertRegex(entry["after"], r"^[0-9a-f]{64}$")
                with self.assertRaises(ValueError):
                    expected_digest(scope, "0" * 64)

    def test_later_ledgers_chain_from_the_previous_fingerprint(self):
        for earlier, later in zip(LEDGERS, LEDGERS[1:]):
            before = json.loads(earlier.read_text())["fingerprints"]
            for scope, entry in json.loads(later.read_text())["fingerprints"].items():
                with self.subTest(ledger=later.name, scope=scope):
                    self.assertEqual(entry["before"], step(earlier, scope, before[scope]["before"]))
                    self.assertRegex(entry["after"], r"^[0-9a-f]{64}$")

    def test_unlisted_research_keeps_original_fingerprint(self):
        for scope in ("atlas_data/claims.lock", "atlas/montague/PTQ.v", "unknown"):
            self.assertEqual(expected_digest(scope, "unchanged"), "unchanged")
