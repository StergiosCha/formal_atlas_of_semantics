"""Exact post-redaction fingerprints for a documented, non-scientific migration.

Historical expected hashes remain recorded. A replacement is permitted only
for the specific scope and original digest named in the migration ledger.
Unlisted files and later edits still have to match their original checks.
"""
import json
from pathlib import Path

LEDGER = Path(__file__).with_name('privacy_migration_2026_11_11.json')
# Later documented, non-scientific migrations, applied in order after LEDGER.
LEDGERS = (LEDGER, Path(__file__).with_name('survey_correction_2026_11_15.json'))


def step(ledger, scope, original):
    entry = json.loads(ledger.read_text())['fingerprints'].get(scope)
    if entry is None:
        return original
    if entry['before'] != original:
        raise ValueError(f'Unexpected historical baseline in {ledger.name}: {scope}')
    return entry['after']


def expected_digest(scope, original):
    for ledger in LEDGERS:
        original = step(ledger, scope, original)
    return original
