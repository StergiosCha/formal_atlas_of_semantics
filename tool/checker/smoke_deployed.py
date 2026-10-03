"""Read-only hosted checks plus temporary proof execution. No paid model calls."""
import argparse
import hashlib
import json
import re
import urllib.error
import urllib.request
from pathlib import Path


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend',required=True)
    parser.add_argument('--site',help='Check the published site, otherwise use this release bundle')
    args=parser.parse_args()
    repo=Path(__file__).resolve().parents[2]
    def call(path,body=None,expected=200,origin=None,token=None):
        headers={'Content-Type':'application/json'}
        if origin: headers['Origin']=origin
        if token: headers['X-Coq-Session']=token
        request=urllib.request.Request(args.backend.rstrip('/')+path,
            data=None if body is None else json.dumps(body).encode(),headers=headers)
        try:
            with urllib.request.urlopen(request,timeout=45) as response:
                status=response.status; result=json.load(response)
        except urllib.error.HTTPError as error:
            status=error.code; result=json.load(error)
        assert status==expected,(path,status,result)
        return result
    if args.site:
        with urllib.request.urlopen(args.site,timeout=30) as response:
            html=response.read().decode()
    else:
        html=(repo/'atlas_data/site/index.html').read_text()
    data=json.loads(re.search(r'<script id="atlas-data" type="application/json">(.*?)</script>',html,re.S).group(1))
    cap=call('/workspace/capabilities')
    assert cap['available'] and cap['coq_version']=='8.20.1' and cap['sandbox']=='bubblewrap',cap
    assert cap['library_sha256']==data['workspace_library_sha256']
    models=call('/models')
    assert models['provider']=='openrouter'
    assert any(m['model']=='openai/gpt-6-astra' for m in models['models'])
    source=data['proof_sources']['atlas__ptq']
    base={'path':source['path'],'source_sha256':source['sha256'],'library_sha256':cap['library_sha256']}
    def check(code,mode='file'):
        result=call('/workspace/check',{**base,'code':code,'mode':mode,'cursor':len(code)},origin='https://orange-beach-0c447e210.5.azurestaticapps.net')
        assert result['code_sha256']==hashlib.sha256(code.encode()).hexdigest()
        return result
    prefix='Lemma hosted_demo : forall P : Prop, P -> P. Proof. intros P HP.'
    result=check(prefix,'prefix')
    assert result['ok'] and 'HP : P' in result['output'],result
    assert not check(prefix)['ok']
    assert check(prefix+' exact HP. Qed.')['ok']
    assert not check('Lemma invalid : False. Proof. exact I. Qed.')['ok']
    assert check(source['text'])['ok']
    call('/workspace/check',{**base,'source_sha256':'0'*64,'code':prefix,'mode':'file','cursor':0},expected=409)
    call('/workspace/check',{**base,'code':prefix,'mode':'file','cursor':0},expected=403,origin='https://untrusted.invalid')
    call('/workspace/explain',{**base,'code':prefix,'start':0,'end':10,'question':'Explain'},expected=401)
    call('/verify',{'claim':'No key, no model call'},expected=401)
    if cap.get('session_available'):
        opened=call('/workspace/session/open',{**base,'code':''})
        token=opened['session_token']
        try:
            for sequence,code,expected_ok in [(1,prefix,True),(2,prefix+' exact HP.',True),
                    (3,prefix,True),(4,'Goal False. Qed. Goal True.',False),
                    (5,'Goal True. exact I. Qed.',True)]:
                result=call('/workspace/session/check',{**base,'code':code,'cursor':len(code),'sequence':sequence},token=token)
                assert result['ok']==expected_ok,result
                assert result['code_sha256']==hashlib.sha256(code.encode()).hexdigest()
                assert result['sequence']==sequence
                if sequence in (1,3):assert result['goals']['goals'][0]['ty']=='P',result
        finally:
            call('/workspace/session/close',{},token=token)
        call('/workspace/session/check',{**base,'code':'','cursor':0,'sequence':6},token=token,expected=410)
    # Isolation needs a known existing Coq fixture outside the sandbox.
    # Run tool/deploy/probe-sandbox.sh on the host for that test.
    print(json.dumps({'passed':True,'real_coq':True,'sandbox':cap['sandbox'],
        'model_provider':'openrouter','paid_model_calls':0,'library_sha256':cap['library_sha256'],
        'site_revision':data.get('revision'),'source_count':len(data['proof_sources']),
        'persistent_sessions_tested':bool(cap.get('session_available'))}))


if __name__=='__main__':
    main()
