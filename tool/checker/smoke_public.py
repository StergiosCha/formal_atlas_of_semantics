"""Public-browser proof test. Model output is mocked; no paid model calls."""
import argparse
import json
import tempfile
from pathlib import Path
from playwright.sync_api import sync_playwright


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site',required=True)
    parser.add_argument('--backend',required=True)
    args=parser.parse_args()
    artifacts=Path(tempfile.mkdtemp(prefix='atlas-public-browser-'))
    with sync_playwright() as p:
        browser=p.chromium.launch()
        page=browser.new_page(viewport={'width':1440,'height':1000})
        errors=[]
        page.on('pageerror',lambda error:errors.append(str(error)))
        page.goto(args.site.rstrip('/')+'/#/edit/atlas__ptq')
        page.wait_for_selector('#live-code')
        assert page.locator('#live-api').input_value()==args.backend
        page.locator('#live-connect').click()
        page.wait_for_function("document.getElementById('live-connection').textContent.includes('Library snapshot matches')")
        assert 'bubblewrap' in page.locator('#live-connection').inner_text()
        page.wait_for_function("document.querySelector('#live-model option:checked').textContent === 'openai/gpt-6-astra'")
        code='Lemma public_browser : forall P : Prop, P -> P. Proof. intros P HP.'
        page.locator('#live-code').fill(code)
        page.locator('#live-code').evaluate('el=>el.setSelectionRange(el.value.length,el.value.length)')
        page.locator('#live-cursor').click()
        page.wait_for_function("document.getElementById('live-check-status').textContent.includes('accepted the prefix')")
        assert 'HP : P' in page.locator('#live-output').inner_text()
        page.screenshot(path=str(artifacts/'live-goal.png'),full_page=True)
        page.locator('#live-code').fill(code+' exact HP. Qed.')
        page.locator('#live-file').click()
        page.wait_for_function("document.getElementById('live-check-status').textContent.startsWith('This copy compiled')")
        page.locator('#live-code').fill('Lemma wrong : False. Proof. exact I. Qed.')
        page.locator('#live-file').click()
        page.wait_for_function("document.getElementById('live-check-status').textContent.includes('reported an error')")
        page.locator('#live-code').evaluate('el=>el.setSelectionRange(0,10)')
        page.locator('#live-explain').click()
        page.wait_for_function("document.getElementById('live-explain-status').textContent.includes('Enter your OpenRouter')")
        def explain(route):
            assert route.request.url==args.backend+'/workspace/explain'
            assert route.request.headers['x-openrouter-key']=='sk-or-public-fixture'
            assert 'sk-or-public-fixture' not in json.dumps(route.request.post_data_json)
            route.fulfill(json={'text':'Unverified fixture <script>not executable</script>','model':'gpt-6-astra','model_id':'openai/gpt-6-astra','provider':'openrouter','verified':False})
        page.route('**/workspace/explain',explain)
        page.locator('#live-key').fill('sk-or-public-fixture')
        page.locator('#live-explain').click()
        page.wait_for_function("document.getElementById('live-explanation').textContent.includes('Unverified fixture')")
        assert page.locator('#live-explanation script').count()==0
        assert page.evaluate("!JSON.stringify(localStorage).includes('sk-or-public-fixture') && !JSON.stringify(sessionStorage).includes('sk-or-public-fixture')")
        page.reload(); page.wait_for_selector('#live-key')
        assert page.locator('#live-key').input_value()==''
        page.set_viewport_size({'width':390,'height':844})
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
        page.screenshot(path=str(artifacts/'mobile.png'),full_page=True)
        assert not errors,errors
        browser.close()
    print(json.dumps({'passed':True,'public_browser':True,'real_coq':True,'model_output':'mocked','artifacts':str(artifacts)}))


if __name__=='__main__':
    main()
