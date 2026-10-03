"""One-time VM migration to persistent Coq; restore the previous service on failure.

Run as root through Azure Run Command. No credentials are printed or retained.
The old image and root-only configuration backup are kept for rollback.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import urllib.request

OLD = 'formalatlasacr.azurecr.io/atlas-checker@sha256:31a276f63ef8bb9c21d9d739632e38559a64a379f2960bcf7606b20301ddf8b6'
NEW = 'formalatlasacr.azurecr.io/atlas-checker@sha256:24f488c892065bfaab0b49ffd79d8e17a085cda5a7432cb49b38e7328da35495'
LIBRARY = '9dfe0dbdad82d8e23445ef3c7dff79af01189558d3af10577846daab23ae1536'
FILES = [Path('/usr/local/sbin/atlas-pull'), Path('/etc/systemd/system/atlas-coq.service')]


def command(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True, timeout=600).stdout.strip()


def capabilities(persistent):
    for _ in range(40):
        try:
            with urllib.request.urlopen('http://127.0.0.1:8477/workspace/capabilities', timeout=5) as response:
                cap = json.load(response)
            assert cap['available'] and cap['sandbox'] == 'bubblewrap'
            assert cap['coq_version'] == '8.20.1' and cap['library_sha256'] == LIBRARY
            assert bool(cap.get('session_available')) == persistent
            if persistent:
                assert cap['session_lsp_version'] == '0.2.5'
            return
        except Exception:
            time.sleep(1)
    raise RuntimeError('Worker capabilities did not match the expected release')


SMOKE = r'''
import json, sys, urllib.request
sys.path.insert(0, '/srv')
import workspace
sources, fingerprint = workspace.library()
base = dict(path='atlas/montague/PTQ.v', source_sha256=sources['atlas/montague/PTQ.v'], library_sha256=fingerprint)
def call(path, body, token=None):
    headers = {'Content-Type': 'application/json'}
    if token:
        headers['X-Coq-Session'] = token
    req = urllib.request.Request('http://127.0.0.1:8477'+path, data=json.dumps(body).encode(), headers=headers)
    with urllib.request.urlopen(req, timeout=35) as response:
        assert response.headers['Cache-Control'] == 'no-store'
        return json.load(response)
token = call('/workspace/session/open', {**base, 'code': ''})['session_token']
try:
    for sequence, (code, ok) in enumerate([
        ('Goal True. Proof.', True), ('Goal True. Proof. exact I.', True),
        ('Goal True. Proof.', True), ('Goal False. Qed. Goal True.', False),
        ('(* 😀 *) Goal forall α : Prop, α -> α. intros α H.', True)], 1):
        result = call('/workspace/session/check', {**base, 'code': code, 'cursor': len(code), 'sequence': sequence}, token)
        assert result['ok'] == ok and result['sequence'] == sequence
    code = 'Goal True. exact I. Qed.'
    result = call('/workspace/check', {**base, 'code': code, 'cursor': len(code), 'mode': 'file'})
    assert result['ok'] and result['status'] == 'compiled_copy'
finally:
    call('/workspace/session/close', {}, token)
print('Live session forward/back, invalid Qed, Unicode and fresh compilation passed')
'''


def main():
    if os.geteuid() != 0:
        raise SystemExit('Run only as root on the dedicated worker VM')
    assert command('docker', 'inspect', '--format', '{{.Config.Image}}', 'atlas-coq-worker') == OLD
    command('docker', 'image', 'inspect', NEW)  # Candidate was already pulled and tested.
    previous = {path: path.read_bytes() for path in FILES}
    for content in previous.values():
        assert content.count(OLD.encode()) == 1 and NEW.encode() not in content
    caddy = Path('/etc/caddy/Caddyfile').read_text()
    assert 'request>headers delete' in caddy and 'resp_headers delete' in caddy
    command('systemctl', 'is-active', 'caddy', 'atlas-metadata-guard')
    command('iptables', '-C', 'DOCKER-USER', '-d', '169.254.169.254/32', '-j', 'REJECT')
    directory = Path('/var/lib/atlas-deployments')
    directory.mkdir(mode=0o700, exist_ok=True)
    backup = Path(tempfile.mkdtemp(prefix='persistent-20261003-', dir=directory))
    for path, content in previous.items():
        (backup / path.name).write_bytes(content)
    print('Rollback configuration: ' + str(backup), flush=True)
    try:
        FILES[0].write_bytes(previous[FILES[0]].replace(OLD.encode(), NEW.encode()))
        command(str(FILES[0]))  # Managed-identity pull while old service still runs.
        FILES[1].write_bytes(previous[FILES[1]].replace(OLD.encode(), NEW.encode()))
        command('systemctl', 'daemon-reload')
        command('systemctl', 'restart', 'atlas-coq')
        capabilities(True)
        assert command('docker', 'inspect', '--format', '{{.Config.Image}}', 'atlas-coq-worker') == NEW
        print(command('docker', 'exec', 'atlas-coq-worker', 'python3', '-c', SMOKE))
    except BaseException:
        for path, content in previous.items():
            path.write_bytes(content)
        command('systemctl', 'daemon-reload')
        command('systemctl', 'restart', 'atlas-coq')
        capabilities(False)
        print('Activation failed; previous worker restored', flush=True)
        raise
    print('Persistent Coq worker activated; previous image retained: ' + OLD)


if __name__ == '__main__':
    main()
