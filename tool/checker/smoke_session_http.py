"""Real session HTTP contract inside a private candidate container; no model calls."""
import json
from pathlib import Path
import subprocess
import sys
import time
import urllib.error
import urllib.request

sys.path.insert(0, str(Path(__file__).resolve().parent) if '__file__' in globals() else '/srv')
sys.path.insert(0, '/srv')
import workspace


def main():
    server = subprocess.Popen(['uvicorn', 'server:app', '--app-dir', '/srv', '--host', '127.0.0.1', '--port', '8499'],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    token = None

    def call(path, body=None, expected=200, credential=None):
        headers = {'Content-Type': 'application/json'}
        if credential:
            headers['X-Coq-Session'] = credential
        req = urllib.request.Request('http://127.0.0.1:8499'+path, headers=headers,
                                     data=None if body is None else json.dumps(body).encode())
        try:
            response = urllib.request.urlopen(req, timeout=35)
        except urllib.error.HTTPError as error:
            response = error
        with response:
            result = json.load(response)
            assert response.code == expected, (path, response.code, result)
            if path.startswith('/workspace/'):
                assert response.headers['Cache-Control'] == 'no-store'
            return result

    try:
        for _ in range(50):
            try:
                call('/health')
                break
            except urllib.error.URLError:
                time.sleep(.1)
        else:
            raise AssertionError('Candidate HTTP server did not start')
        sources, fingerprint = workspace.library()
        base = {'path': 'atlas/montague/PTQ.v', 'source_sha256': sources['atlas/montague/PTQ.v'], 'library_sha256': fingerprint}
        cap = call('/workspace/capabilities')
        assert cap['session_available'] and cap['library_sha256'] == fingerprint
        token = call('/workspace/session/open', {**base, 'code': ''})['session_token']
        for sequence, code in enumerate(['', 'Goal True. Proof.', 'Goal True. Proof. exact I.', '',
                                         '(* 😀 *) Goal forall α : Prop, α -> α. intros α H.'], 1):
            result = call('/workspace/session/check', {**base, 'code': code, 'cursor': len(code), 'sequence': sequence}, credential=token)
            assert result['ok'], result
            assert result['sequence'] == sequence
        bad = 'Goal False. Qed. Goal True.'
        result = call('/workspace/session/check', {**base, 'code': bad, 'cursor': len(bad), 'sequence': 6}, credential=token)
        assert not result['ok'] and result['goals'] is None, result
        call('/workspace/session/check', {**base, 'code': '', 'cursor': 0, 'sequence': 6}, expected=409, credential=token)
        good = 'Goal True. exact I. Qed.'
        result = call('/workspace/check', {**base, 'code': good, 'mode': 'file', 'cursor': len(good)})
        assert result['ok'] and result['status'] == 'compiled_copy', result
        call('/workspace/session/check', {**base, 'code': '', 'cursor': 0, 'sequence': 7}, expected=401)
        call('/workspace/session/close', {}, credential=token)
        call('/workspace/session/check', {**base, 'code': '', 'cursor': 0, 'sequence': 7}, expected=410, credential=token)
        print(json.dumps({'passed': True, 'real_http': True, 'real_coq_sessions': True,
                          'empty_prefix_and_unicode': True, 'fresh_compilation': True, 'model_calls': 0}))
    finally:
        if token:
            try:
                call('/workspace/session/close', {}, credential=token)
            except Exception:
                pass
        server.terminate()
        server.wait(timeout=10)


if __name__ == '__main__':
    main()
