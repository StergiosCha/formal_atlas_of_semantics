"""One explicitly requested OpenRouter smoke call using a server-side key.

The new explanation prompt/context is sent to the current provider adapter.
This does not deploy or test the new HTTP endpoint. A key is read only from
the target process environment, never printed, copied or written. Run only
with authorization for a model call.
"""
import argparse
import base64
import subprocess
import sys
import zlib

import workspace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--revision", help="Probe this existing Azure checker revision")
    target.add_argument("--local", action="store_true", help="Use this checkout and environment")
    args = parser.parse_args()
    # Read the short existing modal section remotely, rather than transporting
    # a whole local context through ACA's length-limited handshake URL.
    remote = "\n".join([
        "import sys,json,re",
        'sys.path.insert(0,"/srv/llm")',
        "import providers",
        "try:",
        " if providers.CFG.get('provider')!='openrouter': raise RuntimeError('OpenRouter adapter is not deployed')",
        ' from pathlib import Path',
        f' code=Path({str(workspace.REPO / "atlas/montague/PTQ.v")!r}).read_text()' if args.local else ' code=Path("/atlas/atlas/montague/PTQ.v").read_text()',
        ' start=code.index("Section Modal.")',
        ' end=code.index("Qed.",code.index("Theorem box_K :",start))+4',
        ' context={"path":"atlas/montague/PTQ.v","selection":code[start:end],"context_is_partial":True,"question":"In at most 100 words, explain box_K and why the proof works. Does it identify complete semantic theories?"}',
        f" messages=[{{'role':'system','content':{workspace.EXPLAIN_POLICY!r}}},{{'role':'user','content':json.dumps(context)}}]",
        " answer=providers.chat('gpt-6-astra',messages,max_tokens=2400,timeout=90,retries=0)",
        " print(json.dumps({'ok':True,'provider':'openrouter','model':'openai/gpt-6-astra','verified':False,'text':answer}))",
        "except Exception as error:",
        " message=str(error)",
        " http=re.search(r'HTTP (\\d{3})',message)",
        ' code=re.search(r\'"code"\\s*:\\s*"([A-Za-z0-9_.-]+)"\',message)',
        " print(json.dumps({'ok':False,'error_type':type(error).__name__,'http_status':http.group(1) if http else None,'provider_code':code.group(1) if code else None,'missing_key':'is not set' in message,'adapter_not_deployed':'not deployed' in message,'incomplete':'response incomplete' in message,'unknown_model':'not in models.json' in message}))",
        " sys.exit(1)",
    ])
    if args.local:
        remote = remote.replace('sys.path.insert(0,"/srv/llm")',
                                f"sys.path.insert(0,{str(workspace.REPO / 'tool/llm')!r})")
        raise SystemExit(subprocess.run([sys.executable, "-c", remote]).returncode)
    # ACA includes the command in its terminal handshake. Compress this public
    # fixture to avoid its URL length limit; this is not credential storage.
    packed = base64.b64encode(zlib.compress(remote.encode())).decode()
    # ACA's exec bridge splits on whitespace rather than parsing shell quotes.
    # Keep the Python expression a single whitespace-free argument.
    launcher = f"exec(__import__('zlib').decompress(__import__('base64').b64decode({packed!r})).decode())"
    result = subprocess.run([
        "az", "containerapp", "exec", "--name", "atlas-checker",
        "--resource-group", "formal-atlas", "--revision", args.revision,
        "--command", "python3 -c " + launcher, "--only-show-errors",
    ])
    if result.returncode:
        raise SystemExit("Azure terminal probe failed; no model response established")


if __name__ == "__main__":
    main()
