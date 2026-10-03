"""Real browser + local sandboxed Coq; AI text is an explicitly mocked fixture.

Run with the project's Playwright-capable Python. No credentials or paid calls.
Creates only temporary logs/screenshots, not edits to library sources.
"""
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
import hashlib
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import threading
import time
import urllib.request

from playwright.sync_api import sync_playwright

REPO=Path(__file__).resolve().parents[2]


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self,*args): pass


def main():
    artifacts=Path(tempfile.mkdtemp(prefix="atlas-workspace-browser-"))
    site=ThreadingHTTPServer(("127.0.0.1",0),partial(QuietHandler,directory=str(REPO/"atlas_data/site")))
    threading.Thread(target=site.serve_forever,daemon=True).start()
    with socket.socket() as sock:
        sock.bind(("127.0.0.1",0)); api_port=sock.getsockname()[1]
    api=f"http://127.0.0.1:{api_port}"
    env={"PATH":os.environ.get("PATH","/usr/bin:/bin"),"HOME":str(artifacts),
         "ATLAS_REPO":str(REPO),"ATLAS_JSON":str(REPO/"atlas_data/atlas.json")}
    with (artifacts/"server.log").open("w") as log:
        process=subprocess.Popen([sys.executable,"-m","uvicorn","server:app","--app-dir",str(REPO/"tool/checker"),
                                  "--host","127.0.0.1","--port",str(api_port)],env=env,stdout=log,stderr=log)
        try:
            for _ in range(100):
                try:
                    with urllib.request.urlopen(api+"/health",timeout=1): break
                except OSError: time.sleep(.1)
            else: raise RuntimeError("Local backend did not start")
            with sync_playwright() as p:
                browser=p.chromium.launch()
                context=browser.new_context(accept_downloads=True)
                page=context.new_page(); errors=[]; calls=[]
                page.on("pageerror",lambda error: errors.append(str(error)))
                page.on("request",lambda req:calls.append(req.url))
                def check_key_destination(req):
                    if req.headers.get("x-openrouter-key"):
                        assert req.url in (api+"/workspace/explain",api+"/verify")
                page.on("request",check_key_destination)
                url=f"http://127.0.0.1:{site.server_port}/#/edit/atlas__ptq"
                page.goto(url)
                page.wait_for_selector("#live-code .cm-editor")
                def value():
                    return page.locator("#live-code").evaluate("el=>el.coqEditor.getValue()")
                def edit(code):
                    page.locator("#live-code").evaluate("(el,code)=>el.coqEditor.setValue(code)",code)
                original=value()
                assert "Lemma" in original or "Theorem" in original
                assert not any("/workspace/" in c for c in calls),"Opening a draft must not send code"
                page.locator("#live-settings summary").click()
                page.locator("#live-api").fill(api)
                page.locator("#live-connect").click()
                page.wait_for_function("!document.getElementById('live-connection').textContent.startsWith('Checking sandbox')")
                print("Connection:",page.locator("#live-connection").text_content(),flush=True)
                assert "Library snapshot matches" in page.locator("#live-connection").text_content(), errors
                page.wait_for_function("document.getElementById('live-connection').textContent.includes('Library snapshot matches')")
                page.wait_for_function("document.querySelector('#live-model option:checked').textContent === 'openai/gpt-6-astra'")
                assert page.locator("#live-model").input_value()=="gpt-6-astra"
                page.locator("#live-file").click()
                page.wait_for_function("document.getElementById('live-check-status').textContent.startsWith('This copy compiled')")
                prefix="Lemma browser_demo : forall P : Prop, P -> P.\nProof.\nintros P HP."
                edit(prefix)
                page.locator("#live-code").evaluate("el=>el.coqEditor.select(el.coqEditor.getValue().length)")
                page.locator("#live-cursor").click()
                page.wait_for_function("document.getElementById('live-check-status').textContent.includes('accepted the prefix')")
                assert "HP : P" in page.locator("#live-output").text_content()
                page.locator("#live-file").click()
                page.wait_for_function("document.getElementById('live-check-status').textContent.includes('reported an error')")
                edit(prefix+"\nexact HP. Qed.\n")
                page.locator("#live-file").click()
                page.wait_for_function("document.getElementById('live-check-status').textContent.startsWith('This copy compiled')")
                edited=value()
                page.reload();page.wait_for_selector("#live-code .cm-editor")
                assert value()==edited
                assert "Not checked" in page.locator("#live-copy-status").inner_text()
                with page.expect_download() as download:
                    page.locator("#live-patch").click()
                patch_path=artifacts/"proposal.patch";download.value.save_as(patch_path)
                assert "--- a/atlas/montague/PTQ.v" in patch_path.read_text()
                checkout=artifacts/"patch-check";target=checkout/"atlas/montague/PTQ.v"
                target.parent.mkdir(parents=True);target.write_text(original)
                subprocess.run(["git","apply","--check",str(patch_path)],cwd=checkout,check=True)
                def explanation(route):
                    body=route.request.post_data_json
                    assert body["code"]==edited
                    assert body["start"] < body["end"]
                    assert route.request.headers["x-openrouter-key"]=="sk-or-browser-fixture"
                    assert "sk-or-browser-fixture" not in json.dumps(body)
                    route.fulfill(json={"text":"UNVERIFIED TEST FIXTURE <img src=x onerror=alert(1)>\nThis explains the selected implication.",
                                        "model":"gpt-6-astra","model_id":"openai/gpt-6-astra",
                                        "provider":"openrouter","verified":False})
                page.route("**/workspace/explain",explanation)
                page.locator("#live-code").evaluate("el=>el.coqEditor.select(0,44)")
                page.locator("#live-tab-assistant").click()
                page.locator("#live-explain").click()
                page.wait_for_function("document.getElementById('live-explain-status').textContent.includes('Enter your OpenRouter')")
                page.locator("#live-key").fill("sk-or-browser-fixture")
                page.locator("#live-explain").click()
                page.wait_for_function("document.getElementById('live-explanation').textContent.includes('TEST FIXTURE')")
                assert page.locator("#live-explanation img").count()==0
                assert "unverified" in page.locator("#live-explain-status").inner_text()
                assert "openai/gpt-6-astra via openrouter" in page.locator("#live-explain-status").inner_text()
                assert value()==edited
                assert page.evaluate("!JSON.stringify(localStorage).includes('sk-or-browser-fixture') && !JSON.stringify(sessionStorage).includes('sk-or-browser-fixture')")
                page.locator("#live-clear-key").click()
                assert page.locator("#live-key").input_value()==""
                page.locator("#live-key").fill("sk-or-browser-fixture")
                page.reload();page.wait_for_selector("#live-code .cm-editor")
                assert page.locator("#live-key").input_value()==""
                # A delayed successful response must not label a newer edit.
                page.locator("#live-connect").click()
                page.wait_for_function("document.getElementById('live-connection').textContent.includes('Library snapshot matches')")
                def stale_check(route):
                    body=route.request.post_data_json
                    route.fulfill(json={"ok":True,"mode":"file","output":"fixture",
                                        "code_sha256":hashlib.sha256(body["code"].encode()).hexdigest(),
                                        "library_sha256":body["library_sha256"]})
                page.route("**/workspace/check",stale_check)
                page.evaluate("""() => {
                    document.getElementById('live-file').click();
                    const editor=document.getElementById('live-code').coqEditor;
                    editor.setValue(editor.getValue()+'(* changed while checking *)');
                }""")
                page.wait_for_function("document.getElementById('live-check-status').textContent.includes('Result is stale')")
                assert "compiled" not in page.locator("#live-check-status").inner_text()
                page.evaluate("scrollTo({top:0,behavior:'instant'})")
                page.screenshot(path=str(artifacts/"desktop.png"),full_page=True)
                page.set_viewport_size({"width":390,"height":844})
                print("Mobile overflow:",page.evaluate("[...document.querySelectorAll('body *')].filter(e=>e.getBoundingClientRect().right>innerWidth+2).slice(0,12).map(e=>[e.tagName,e.id,e.className,e.getBoundingClientRect().width])"),flush=True)
                assert page.evaluate("document.documentElement.scrollWidth <= innerWidth+2")
                page.screenshot(path=str(artifacts/"mobile.png"),full_page=True)
                # The Verifier has the same user-key flow, not a shared secret.
                page.goto(f"http://127.0.0.1:{site.server_port}/#/check")
                page.wait_for_selector("#ck-key")
                page.wait_for_function("document.querySelector('#ck-model option:checked').value === 'gpt-5.4-mini'")
                page.locator("#ck-claim").fill("Explain whether this implication is provable")
                page.locator("#ck-go").click()
                page.wait_for_function("document.getElementById('ck-out').textContent.includes('Enter your OpenRouter')")
                def verify(route):
                    assert route.request.headers["x-openrouter-key"]=="sk-or-browser-fixture"
                    assert "sk-or-browser-fixture" not in json.dumps(route.request.post_data_json)
                    route.fulfill(json={"bucket":"UNKNOWN_MODEL_CLAIMED_UNVERIFIED","model":"gpt-5.4-mini","rounds":1,
                                        "code":"(* test fixture only *)","audit":{},"notes":"Browser fixture","turns":[]})
                page.route("**/verify",verify)
                page.locator("#ck-key").fill("sk-or-browser-fixture")
                page.locator("#ck-go").click()
                page.wait_for_function("document.getElementById('ck-out').textContent.includes('MODEL CLAIMED UNVERIFIED'.toLowerCase())")
                assert page.evaluate("!JSON.stringify(localStorage).includes('sk-or-browser-fixture') && !JSON.stringify(sessionStorage).includes('sk-or-browser-fixture') && !JSON.stringify(window._ck).includes('sk-or-browser-fixture')")
                page.reload();page.wait_for_selector("#ck-key")
                assert page.locator("#ck-key").input_value()==""
                assert not errors,errors
                browser.close()
            print(json.dumps({"passed":True,"real_coq":True,"ai":"mocked, no provider call", "artifacts":str(artifacts)}))
        finally:
            process.terminate();process.wait(timeout=10);site.shutdown();site.server_close()


if __name__=="__main__": main()
