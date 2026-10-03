#!/bin/sh
set -eu
docker exec -i atlas-coq-worker opam exec -- python3 <<'PY'
import json
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

sys.path.insert(0, '/srv')
import isolation
import workspace

cap = isolation.capability('/atlas')
assert cap['available'] and cap['sandbox'] == 'bubblewrap', cap
sources, fingerprint = workspace.library()

def check(code):
    body = dict(path='atlas/montague/PTQ.v',
                source_sha256=sources['atlas/montague/PTQ.v'],
                library_sha256=fingerprint, code=code, mode='file',
                cursor=len(code))
    request = urllib.request.Request(
        'http://127.0.0.1:8477/workspace/check',
        data=json.dumps(body).encode(),
        headers={'Content-Type': 'application/json'})
    with urllib.request.urlopen(request, timeout=40) as response:
        return json.load(response)

assert check('Lemma control : True. Proof. exact I. Qed.')['ok']
# The fixture really exists and loads in the outer container. The exact same
# Load command must fail through the running API's filesystem sandbox.
with tempfile.TemporaryDirectory(prefix='atlas-isolation-canary-') as outer:
    fixture = Path(outer) / 'canary.v'
    fixture.write_text('Definition atlas_canary_marker : True := I.\n')
    code = f'Load "{fixture}".\nCheck atlas_canary_marker.\n'
    control = Path(outer) / 'control.v'
    control.write_text(code)
    ordinary = subprocess.run(['coqtop', '-batch', '-l', str(control)],
                              capture_output=True, text=True, timeout=15)
    assert ordinary.returncode == 0, ordinary.stderr
    assert 'atlas_canary_marker' in ordinary.stdout, ordinary.stdout
    assert fixture.is_file()
    denied = check(code)
    assert not denied['ok'], denied
    assert 'canary.v' in denied['output'], denied
    assert any(message in denied['output'] for message in
               ("Can't find file", 'Cannot find', 'No such file')), denied
print(json.dumps({'passed': True, 'sandbox': cap['sandbox'],
                  'outer_coq_load': True, 'api_coq_load_blocked': True,
                  'fixture_cleaned': not Path(outer).exists()}))
PY
