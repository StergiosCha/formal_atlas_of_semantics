"""Real Coq browser checks; only LLM and stale-response fixtures are mocked.

Omit --site to serve the release bundle locally against the given live worker.
No paid model call, persistent key, or library change.
"""
import argparse
from functools import partial
import hashlib
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
import threading
from playwright.sync_api import sync_playwright


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass


def run(site, backend, artifacts):
    with sync_playwright() as p:
        browser=p.chromium.launch()
        context=browser.new_context(viewport={'width':1440,'height':1000},accept_downloads=True)
        page=context.new_page()
        errors=[]
        calls=[]
        page.on('pageerror',lambda error:errors.append(str(error)))
        page.on('request',lambda request:calls.append(request.url))
        def key_destination(request):
            if request.headers.get('x-openrouter-key'):
                assert request.url==backend+'/workspace/explain'
        page.on('request',key_destination)
        def value():
            return page.locator('#live-code').evaluate('el=>el.coqEditor.getValue()')
        def edit(code):
            page.locator('#live-code').evaluate('(el,code)=>el.coqEditor.setValue(code)',code)
        def select(start,end=None):
            page.locator('#live-code').evaluate('(el,p)=>el.coqEditor.select(p[0],p[1])',[start,start if end is None else end])
        def status(text):
            page.wait_for_function('(s)=>document.getElementById("live-check-status").textContent.includes(s)',arg=text)
        try:
            page.goto(site.rstrip('/')+'/#/edit/atlas__ptq')
            page.wait_for_selector('#live-code .cm-editor')
            assert page.locator('.cm-lineNumbers').count()==1
            assert 'Lemma' in value() or 'Theorem' in value()
            assert not any('/workspace/' in url for url in calls),'Opening must not send code'
            assert page.locator('#live-api').input_value()==backend
            page.locator('#live-connect').click()
            page.wait_for_function("document.getElementById('live-connection').textContent.includes('Library snapshot matches')")
            assert 'bubblewrap' in page.locator('#live-connection').text_content()
            page.wait_for_function("document.querySelector('#live-model option:checked').textContent === 'openai/gpt-6-astra'")
            persistent=page.locator('#live-session-status').count()>0 and 'Persistent Coq is available' in page.locator('#live-session-status').inner_text()
            prefix_status='Session prefix accepted' if persistent else 'accepted the prefix'
            prefix='Lemma public_browser : forall P : Prop, P -> P.\nProof.\n  intros P HP.'
            code=prefix+'\n  exact HP.\nQed.\n'
            edit(code);select(len(prefix))
            page.keyboard.press('ControlOrMeta+Enter')
            status(prefix_status)
            assert 'HP : P' in page.locator('.live-hypotheses').inner_text()
            assert page.locator('#live-goal-count').inner_text()=='1'
            assert page.locator('.cm-coq-accepted').count()>0
            assert page.locator('.cm-coq-current').count()>0
            assert page.locator('.cm-line span').count()>0,'Syntax-highlighted tokens expected'
            page.screenshot(path=str(artifacts/'live-goal.png'),full_page=True)
            page.keyboard.press('Alt+ArrowDown');status(prefix_status+' through line 4')
            page.keyboard.press('Alt+ArrowUp');status(prefix_status+' through line 3')
            assert 'HP : P' in page.locator('.live-hypotheses').inner_text()
            page.keyboard.press('ControlOrMeta+Shift+Enter');status('This copy compiled')
            assert page.locator('#live-progress').inner_text()=='Full copy compiled'
            # Search, real typing and undo work inside CodeMirror.
            select(len(code));page.keyboard.press('ControlOrMeta+f')
            assert page.locator('.cm-search').is_visible()
            page.keyboard.press('Escape');select(len(code));page.keyboard.type('(* note *)')
            assert value().endswith('(* note *)')
            assert page.locator('.cm-coq-accepted').count()==0
            page.keyboard.press('ControlOrMeta+z');assert value()==code
            # The resizer is usable without a mouse.
            page.locator('#live-divider').focus();page.keyboard.press('ArrowLeft')
            assert page.locator('#live-divider').get_attribute('aria-valuenow')=='60'
            wrong='Lemma wrong : False.\nProof.\n  exact I.\nQed.'
            edit(wrong);page.locator('#live-file').click();status('reported an error')
            assert page.locator('#live-tab-diagnostics').get_attribute('aria-selected')=='true'
            assert page.locator('.cm-coq-error').count()>0
            page.locator('#live-error-jump').click()
            assert page.locator('#live-code').evaluate('el=>el.coqEditor.getSelection().to>el.coqEditor.getSelection().from')
            page.screenshot(path=str(artifacts/'diagnostic.png'),full_page=True)
            # A late successful result must not mark an edited snapshot accepted.
            def stale(route):
                body=route.request.post_data_json
                route.fulfill(json={'ok':True,'output':'fixture','code_sha256':hashlib.sha256(body['code'].encode()).hexdigest(),'library_sha256':body['library_sha256']})
            page.route('**/workspace/check',stale)
            page.evaluate(r"""() => {
                document.getElementById('live-file').click();
                const editor=document.getElementById('live-code').coqEditor;
                editor.setValue(editor.getValue()+'\n(* changed while checking *)');
            }""")
            status('stale')
            assert page.locator('.cm-coq-accepted').count()==0
            page.unroute('**/workspace/check',stale)
            # A model response stays text, and credentials stay out of storage.
            select(0,10);page.locator('#live-tab-assistant').click()
            page.locator('#live-explain').click()
            page.wait_for_function("document.getElementById('live-explain-status').textContent.includes('Enter your OpenRouter')")
            def explain(route):
                assert route.request.headers['x-openrouter-key']=='sk-or-public-fixture'
                body=route.request.post_data_json
                assert body['start']==0 and body['end']==10
                assert 'sk-or-public-fixture' not in json.dumps(body)
                route.fulfill(json={'text':'Unverified fixture <script>not executable</script>','model_id':'openai/gpt-6-astra','provider':'openrouter','verified':False})
            page.route('**/workspace/explain',explain)
            page.locator('#live-key').fill('sk-or-public-fixture')
            page.locator('#live-question').fill('Explain this selection')
            # No reselection: CodeMirror must retain the selection across fields.
            page.locator('#live-explain').click()
            page.wait_for_function("document.getElementById('live-explanation').textContent.includes('Unverified fixture')")
            assert page.locator('#live-explanation script').count()==0
            assert page.evaluate("!JSON.stringify(localStorage).includes('sk-or-public-fixture') && !JSON.stringify(sessionStorage).includes('sk-or-public-fixture')")
            page.locator('#live-clear-key').click();assert page.locator('#live-key').input_value()==''
            page.locator('#live-key').fill('sk-or-public-fixture')
            page.locator('#live-settings summary').click()
            page.locator('#live-api').fill('https://different-backend.invalid')
            assert page.locator('#live-key').input_value()==''
            assert page.locator('#live-badge').inner_text()=='Not connected'
            page.locator('#live-api').fill(backend)
            page.locator('#live-settings summary').click()
            page.locator('#live-key').fill('sk-or-public-fixture')
            edited=value()
            with page.expect_download() as downloaded:
                page.locator('#live-patch').click()
            download_path=artifacts/'proposal.patch';downloaded.value.save_as(download_path)
            assert 'sk-or-public-fixture' not in download_path.read_text()
            page.reload();page.wait_for_selector('#live-code .cm-editor')
            assert page.locator('#live-key').input_value()==''
            assert value()==edited
            assert page.locator('.cm-coq-accepted').count()==0
            page.set_viewport_size({'width':390,'height':844})
            assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
            page.screenshot(path=str(artifacts/'mobile.png'),full_page=True)
            page.set_viewport_size({'width':1440,'height':1000})
            page.goto(site.rstrip('/')+'/#/proof/atlas__ptq')
            assert not page.locator('body').evaluate("el=>el.classList.contains('atlas-editing')")
            assert not errors,errors
        except Exception:
            page.screenshot(path=str(artifacts/'failure.png'),full_page=True)
            print(json.dumps({'artifacts':str(artifacts),'page_errors':errors,
                'status':page.locator('#live-check-status').text_content() if page.locator('#live-check-status').count() else 'not in editor'}),flush=True)
            raise
        finally:
            browser.close()
    print(json.dumps({'passed':True,'browser':True,'real_coq':True,'model_output':'mocked','artifacts':str(artifacts)}))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site')
    parser.add_argument('--backend',required=True)
    args=parser.parse_args()
    artifacts=Path(tempfile.mkdtemp(prefix='atlas-public-browser-'))
    server=None
    if not args.site:
        directory=Path(__file__).resolve().parents[2]/'atlas_data/site'
        server=ThreadingHTTPServer(('127.0.0.1',0),partial(QuietHandler,directory=str(directory)))
        threading.Thread(target=server.serve_forever,daemon=True).start()
        args.site=f'http://127.0.0.1:{server.server_port}'
    try:
        run(args.site,args.backend.rstrip('/'),artifacts)
    finally:
        if server:server.shutdown();server.server_close()


if __name__=='__main__':
    main()
