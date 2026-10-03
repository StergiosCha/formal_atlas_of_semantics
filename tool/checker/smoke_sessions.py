"""Browser lifecycle contracts with explicitly mocked Coq session responses.

Real Coq tests are test_sessions.py --live. No model request is made here.
"""
from functools import partial
import hashlib
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
import threading
from urllib.parse import urlsplit

from playwright.sync_api import sync_playwright
import workspace


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass


def run():
    _, fingerprint = workspace.library()
    site = Path(__file__).resolve().parents[2] / "atlas_data/site"
    server = ThreadingHTTPServer(("127.0.0.1", 0), partial(QuietHandler, directory=str(site)))
    threading.Thread(target=server.serve_forever, daemon=True).start()
    backend = "https://formal-atlas-coq-crete.westus2.cloudapp.azure.com"
    calls, tokens, errors = [], [], []
    fixtures = {"expire": False, "fail": False, "stale": False}
    with tempfile.TemporaryDirectory(prefix="atlas-session-browser-") as artifacts, sync_playwright() as playwright:
        browser = playwright.chromium.launch()
        context = browser.new_context(viewport={"width": 1440, "height": 1000})
        page = context.new_page()
        page.on("pageerror", lambda error: errors.append(str(error)))

        def route_api(route):
            request = route.request
            path = urlsplit(request.url).path
            assert "x-openrouter-key" not in request.headers
            body = request.post_data_json if request.post_data else {}
            calls.append((path, body, request.headers.get("x-coq-session")))
            if path == "/workspace/capabilities":
                reply = {"available": True, "coq_version": "8.20.1", "sandbox": "test fixture",
                         "library_sha256": fingerprint, "session_available": True}
            elif path == "/models":
                reply = {"models": [{"deployment": "gpt-6-astra", "model": "openai/gpt-6-astra"}]}
            elif path == "/workspace/session/open":
                assert body["code"] == "", "Session creation must not send the draft"
                token = str(len(tokens) + 1).zfill(43)
                tokens.append(token)
                reply = {"session_token": token, "library_sha256": fingerprint}
            elif path == "/workspace/session/close":
                reply = {"closed": True}
            elif path in ("/workspace/session/check", "/workspace/check"):
                persistent = path.endswith("session/check")
                if persistent:
                    assert request.headers["x-coq-session"] in tokens
                if fixtures["expire"]:
                    fixtures["expire"] = False
                    route.fulfill(status=410, json={"detail": "Coq session expired. Start a new session."})
                    return
                code = body["code"]
                reply = {"ok": not fixtures["fail"], "output": "fixture diagnostic" if fixtures["fail"] else "",
                         "mode": body.get("mode", "prefix"), "code_sha256": hashlib.sha256(code.encode()).hexdigest(),
                         "library_sha256": fingerprint, "checked_characters": body["cursor"],
                         "sequence": body.get("sequence"), "document_version": body.get("sequence", 1),
                         "goals": {"goals": [{"hyps": [{"names": ["H"], "ty": "True"}], "ty": "True"}]},
                         "diagnostics": [{"severity": 1, "range": {"start": {"line": 0, "character": 0},
                             "end": {"line": 0, "character": 4}}, "message": "fixture failure"}] if fixtures["fail"] else []}
                if fixtures["stale"]:
                    fixtures["stale"] = False
                    page.locator("#live-code").evaluate(r"el=>el.coqEditor.setValue(el.coqEditor.getValue()+'\n(* changed *)')")
            else:
                raise AssertionError("Unexpected API call: " + path)
            route.fulfill(json=reply)

        context.route(backend + "/**", route_api)
        url = f"http://127.0.0.1:{server.server_port}/#/edit/atlas__ptq"
        page.goto(url)
        page.wait_for_selector("#live-code .cm-editor")
        assert calls == []
        page.locator("#live-connect").click()
        page.wait_for_function("document.getElementById('live-connection').textContent.includes('Library snapshot matches')")
        assert tokens == []
        page.locator("#live-code").evaluate("el=>el.coqEditor.setValue('Goal True. Proof. exact I. Qed.')")

        def prefix():
            page.locator("#live-next").click()
            page.wait_for_function("!document.getElementById('live-next').disabled")

        prefix()
        assert "Session prefix accepted" in page.locator("#live-check-status").inner_text()
        assert "H : True" in page.locator(".live-hypotheses").inner_text()
        prefix()
        assert len(tokens) == 1
        checks = [call for call in calls if call[0] == "/workspace/session/check"]
        assert [call[1]["sequence"] for call in checks] == [1, 2]
        assert checks[0][2] == checks[1][2]
        assert all(token not in page.evaluate("JSON.stringify(localStorage)") for token in tokens)
        page.locator("#live-file").click()
        page.wait_for_function("!document.getElementById('live-file').disabled")
        assert calls[-1][0] == "/workspace/check"
        assert calls[-1][2] is None

        fixtures["fail"] = True
        prefix()
        assert "reported an error" in page.locator("#live-check-status").inner_text()
        assert page.locator(".cm-coq-accepted").count() == 0
        assert page.locator(".cm-coq-error").count() > 0
        fixtures["fail"] = False
        fixtures["expire"] = True
        prefix()
        assert "expired" in page.locator("#live-check-status").inner_text()
        prefix()
        assert len(tokens) == 2
        fixtures["stale"] = True
        prefix()
        assert "stale" in page.locator("#live-check-status").inner_text()
        assert page.locator(".cm-coq-accepted").count() == 0
        page.screenshot(path=str(Path(artifacts) / "session.png"), full_page=True)
        page.locator("#live-settings summary").click()
        page.locator("#live-session-close").click()
        page.wait_for_timeout(100)
        assert any(call[0] == "/workspace/session/close" and call[2] == tokens[-1] for call in calls)
        assert not errors, errors
        browser.close()
    server.shutdown()
    print(json.dumps({"passed": True, "browser_session_contracts": True, "coq_output": "mocked", "model_calls": 0}))


if __name__ == "__main__":
    run()
