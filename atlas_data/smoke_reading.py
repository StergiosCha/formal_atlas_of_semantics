"""Browser regression for discovery and read-only proofs. No Coq or model calls.

Serves the generated site locally, blocks external requests, and saves screenshots
and a JSON summary in a fresh temporary directory (or --artifacts directory).
"""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import tempfile
import threading
from urllib.parse import urlparse

from playwright.sync_api import sync_playwright, expect


class QuietHandler(SimpleHTTPRequestHandler):
    def log_message(self, *args):
        pass


def run(site, artifacts):
    checks=[]
    with sync_playwright() as playwright:
        browser=playwright.chromium.launch()
        context=browser.new_context(viewport={"width":1440,"height":1040},accept_downloads=True)
        page=context.new_page()
        errors=[]
        external=[]
        page.on('pageerror',lambda error:errors.append(str(error)))

        def network(route):
            url=route.request.url
            if url.startswith(site) or url.startswith('blob:'):
                route.continue_()
            else:
                external.append(url)
                route.abort()

        context.route('**/*',network)

        def visit(path):
            page.goto(site+'/#/'+path)
            page.wait_for_selector('#app section')

        def no_overflow():
            assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+1')

        visit('explore')
        expect(page.get_by_role('navigation',name='Main navigation').get_by_role('link',name='Explore',exact=True)).to_have_attribute('aria-current','page')
        assert page.locator('.entry-card').count()==3
        no_overflow()
        page.screenshot(path=str(artifacts/'explore-desktop.png'),full_page=True)
        page.get_by_role('link',name='Walk through the result').click()
        expect(page.locator('h1')).to_have_text('Witnesses matter.')
        expect(page.locator('#witness-answer')).to_be_hidden()
        page.locator('#witness-reveal').click()
        expect(page.locator('#witness-answer')).to_be_visible()
        expect(page.locator('#witness-reveal')).to_have_attribute('aria-expanded','true')
        page.locator('#witness-reveal').click()
        expect(page.locator('#witness-answer')).to_be_hidden()
        page.screenshot(path=str(artifacts/'witnesses-desktop.png'),full_page=True)
        checks.append('Discovery navigation and guided reveal')

        # Guided evidence points into the actual bundled, immutable source.
        page.locator('.result-evidence a').nth(1).click()
        page.wait_for_selector('#proof-editor .cm-editor')
        expect(page.locator('.reader-selection h2')).to_have_text('Packages.Separation.shared_empty')
        assert 'Closed under the global context' in page.locator('.evidence-strip').inner_text()
        expect(page.locator('#proof-fallback')).to_be_hidden()
        expect(page.locator('#proof-editor .cm-content')).to_have_attribute('contenteditable','false')
        assert 'Theorem shared_empty' in page.locator('.cm-reader-selected').inner_text()
        assert page.locator('#proof-editor .cm-line span').count()>0
        page.locator('#proof-editor .cm-content').focus()
        before=page.locator('#proof-editor .cm-content').inner_text()
        page.keyboard.type('DO_NOT_INSERT')
        assert page.locator('#proof-editor .cm-content').inner_text()==before
        page.keyboard.press('ControlOrMeta+f')
        expect(page.locator('#proof-editor .cm-search')).to_be_visible()
        page.keyboard.press('Escape')
        page.locator('#proof-search').fill('no_total_recovery')
        assert page.locator('#proof-outline a:visible').count()==1
        page.locator('#proof-search').fill('no such declaration')
        expect(page.locator('#proof-no-match')).to_be_visible()
        page.locator('#proof-search').fill('')
        no_overflow()
        page.evaluate('window.scrollTo({top:0,behavior:"instant"})')
        page.wait_for_function('Array.from(document.querySelectorAll("#proof-editor .cm-reader-selected span")).some(e=>e.textContent==="Theorem" && getComputedStyle(e).color==="rgb(128, 80, 160)")')
        page.screenshot(path=str(artifacts/'proof-reader-desktop.png'),full_page=True)
        checks.append('Read-only syntax highlighting, selected line, search and declaration outline')

        page.locator('#proof-view-toggle').click()
        expect(page.locator('#proof-fallback')).to_be_visible()
        expect(page.locator('#proof-editor')).to_be_hidden()
        bundled=page.evaluate("D.proof_sources.atlas__witness_contract.text")
        with page.expect_download() as download_info:
            page.get_by_role('button',name='Download .v',exact=True).click()
        download=download_info.value
        assert download.suggested_filename=='Witness_Contract.v'
        assert Path(download.path()).read_bytes()==bundled.encode('utf-8')
        # Line links remain available in the plain view and open matching evidence.
        other_line=page.evaluate("D.proof_sources.atlas__witness_contract.declarations.find(d=>d.name==='Packages.Separation.independent_inhabited').line")
        page.locator(f'#coq-L{other_line} .line-no').click()
        page.wait_for_selector('#proof-editor .cm-editor')
        page.get_by_role('link',name='Edit and run in Coq').click()
        page.wait_for_selector('#live-code .cm-editor')
        assert page.locator('#live-code').evaluate('el=>el.coqEditor.getValue()')==bundled
        assert 'Not connected' in page.locator('#live-badge').inner_text()
        expect(page.locator('body')).to_have_class('atlas-editing')
        page.get_by_role('link',name='Original proof & audit').click()
        page.wait_for_selector('#proof-editor .cm-editor')
        assert 'atlas-editing' not in (page.locator('body').get_attribute('class') or '')
        assert page.locator('.cm-editor').count()==1
        checks.append('Original-byte download, deep links and editor lifecycle without backend calls')

        # Mobile remains readable without a page-wide horizontal scroll.
        page.set_viewport_size({'width':390,'height':844})
        visit('explore');no_overflow()
        page.screenshot(path=str(artifacts/'explore-mobile.png'),full_page=True)
        visit('result/witnesses');no_overflow()
        page.screenshot(path=str(artifacts/'witnesses-mobile.png'),full_page=True)
        visit('proof/atlas__witness_contract?line=112')
        page.wait_for_selector('#proof-editor .cm-editor');no_overflow()
        assert page.locator('.reader-sidebar details[open]').count()==0
        page.locator('.reader-outline summary').click()
        expect(page.locator('#proof-search')).to_be_visible()
        page.locator('.reader-outline summary').click()
        page.evaluate('window.scrollTo({top:0,behavior:"instant"})')
        page.screenshot(path=str(artifacts/'proof-reader-mobile.png'),full_page=True)
        checks.append('390px mobile layouts without horizontal overflow')

        # Reader stays usable if its enhancement bundle fails.
        page.route('**/vendor/coq-editor.js*',lambda route:route.abort())
        visit('proof/atlas__witness_contract?line=112')
        page.reload()
        expect(page.locator('#proof-fallback')).to_be_visible()
        expect(page.locator('#proof-editor')).to_be_hidden()
        assert 'Theorem shared_empty' in page.locator('#coq-L112').inner_text()
        checks.append('Plain-source fallback when editor bundle is unavailable')

        assert not errors,errors
        assert all(urlparse(url).hostname in {'fonts.googleapis.com','fonts.gstatic.com'} for url in external),external
        checks.append('No runtime errors; no Coq, model or other application-service requests')
        browser.close()
    return {'checks':checks,'external_font_requests_blocked':len(external),'coq_calls':0,'model_calls':0}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--artifacts',type=Path)
    args=parser.parse_args()
    artifacts=args.artifacts or Path(tempfile.mkdtemp(prefix='atlas-reading-'))
    artifacts.mkdir(parents=True,exist_ok=True)
    print(f'Browser artifacts: {artifacts}',flush=True)
    site=Path(__file__).resolve().parent/'site'
    server=ThreadingHTTPServer(('127.0.0.1',0),partial(QuietHandler,directory=str(site)))
    thread=threading.Thread(target=server.serve_forever,daemon=True)
    thread.start()
    try:
        result=run(f'http://127.0.0.1:{server.server_port}',artifacts)
        (artifacts/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'artifacts':str(artifacts),**result},indent=2))
    finally:
        server.shutdown();server.server_close();thread.join()


if __name__=='__main__':
    main()
