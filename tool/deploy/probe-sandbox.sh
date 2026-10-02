#!/bin/sh
set -eu
docker exec -i atlas-coq-worker opam exec -- python3 <<'PY'
import sys, tempfile, json
sys.path.insert(0, '/srv')
import isolation, workspace
from starlette.requests import Request
original = isolation.command
def without_proc(*args):
    command = original(*args)
    if '--proc' in command:
        index = command.index('--proc')
        return command[:index] + command[index+2:]
    return command
isolation.command = without_proc
print(json.dumps(isolation.capability('/atlas')))
sources, fingerprint = workspace.library()
def check(code, mode):
    req = workspace.CheckRequest(path='atlas/montague/PTQ.v',source_sha256=sources['atlas/montague/PTQ.v'],library_sha256=fingerprint,code=code,mode=mode,cursor=len(code))
    request = Request({'type':'http','headers':[],'client':('127.0.0.1',1)})
    result = workspace.check(req,request)
    print(json.dumps({'ok':result['ok'],'output':result['output'][:1800]}))
check('Lemma live : forall P : Prop, P -> P. Proof. intros P HP.', 'prefix')
check('Lemma live : forall P : Prop, P -> P. Proof. intros P HP. exact HP. Qed.', 'file')
check('Lemma bad : False. Proof. exact I. Qed.', 'file')
PY
