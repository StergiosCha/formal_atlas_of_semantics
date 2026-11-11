"""Exact post-redaction fingerprints for a documented, non-scientific migration.

Historical expected hashes remain recorded. A replacement is permitted only
for the specific scope and original digest named in the migration ledger.
Unlisted files and later edits still have to match their original checks.
"""
import json
from pathlib import Path

LEDGER = Path(__file__).with_name('privacy_migration_2026_11_11.json')


def expected_digest(scope, original):
    entry = json.loads(LEDGER.read_text())['fingerprints'].get(scope)
    if entry is None:
        return original
    if entry['before'] != original:
        raise ValueError(f'Unexpected historical privacy baseline: {scope}')
    return entry['after']
