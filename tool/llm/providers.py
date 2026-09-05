"""Azure Foundry model access for the Semantics Workbench.

Every deployment in models.json is served by the same Foundry resource
through the OpenAI-compatible inference route
    POST {endpoint}/models/chat/completions?api-version=...
with the deployment name as `model`. Azure-OpenAI-native deployments
(gpt-*) also answer on /openai/deployments/{name}/chat/completions; we
try the unified route first and fall back once per process.

The key comes from the environment (AZURE_AI_KEY) and is never written
anywhere. In production it is an Azure Container Apps secret
(HOSTING.md); locally: export AZURE_AI_KEY=... before running.
"""
import http.client
import json
import os
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
CFG = json.load(open(os.path.join(HERE, "models.json")))

ENDPOINT = os.environ.get(CFG["endpoint_env"], CFG["default_endpoint"]).rstrip("/")
API_VERSION = CFG["api_version"]
ROSTER = {m["deployment"]: m for m in CFG["roster"]}
POLICY = CFG["policy"]

_openai_fallback: set[str] = set()


class ModelError(RuntimeError):
    pass


def _key() -> str:
    k = os.environ.get(CFG["key_env"])
    if not k:
        raise ModelError(
            f"{CFG['key_env']} is not set. Get it from Foundry → Manage → "
            "Keys for the crete-xamoulis resource, then: export "
            f"{CFG['key_env']}=<key>")
    return k


def _post(url: str, payload: dict, timeout: int) -> dict:
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode(),
        headers={"content-type": "application/json", "api-key": _key(),
                 "x-api-key": _key(), "anthropic-version": "2023-06-01",
                 "authorization": f"Bearer {_key()}"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def chat(deployment: str, messages: list[dict], *, max_tokens: int = 8000,
         temperature: float = 0.2, timeout: int = 300, retries: int = 2) -> str:
    """One chat call; returns the assistant text. Raises ModelError with the
    server's own words on failure — never invents a reply.

    Foundry serves three API shapes behind one endpoint (measured 2026-09-05):
    - Anthropic deployments: native Messages API at /anthropic/v1/messages
      (the OpenAI-compatible routes 404 with api_not_supported)
    - gpt-5.x: OpenAI route, but max_completion_tokens and no temperature
      (reasoning models reject both legacy params)
    - everything else (grok/deepseek/kimi/mistral): plain OpenAI-compatible
    """
    if deployment not in ROSTER:
        raise ModelError(f"{deployment} is not in models.json roster")
    family = ROSTER[deployment]["family"]
    last = None
    for attempt in range(retries + 1):
        try:
            if family == "anthropic":
                out = _post(f"{ENDPOINT}/anthropic/v1/messages",
                            {"model": deployment, "max_tokens": max_tokens,
                             "messages": messages}, timeout)
                texts = [c.get("text", "") for c in out.get("content", [])
                         if c.get("type") == "text"]
                if not texts:
                    raise ModelError(f"{deployment}: no text block in reply")
                return "\n".join(texts)
            if family == "openai":
                out = _post(f"{ENDPOINT}/openai/deployments/{deployment}"
                            f"/chat/completions?api-version={API_VERSION}",
                            {"model": deployment, "messages": messages,
                             "max_completion_tokens": max_tokens}, timeout)
            else:
                out = _post(f"{ENDPOINT}/models/chat/completions"
                            f"?api-version={API_VERSION}",
                            {"model": deployment, "messages": messages,
                             "max_tokens": max_tokens,
                             "temperature": temperature}, timeout)
            return out["choices"][0]["message"]["content"]
        except urllib.error.HTTPError as e:
            body = e.read().decode(errors="replace")[:500]
            last = ModelError(f"{deployment}: HTTP {e.code} {body}")
            if e.code in (400, 401, 403, 404):
                break                 # config error: retrying won't help
        except (urllib.error.URLError, TimeoutError, OSError,
                http.client.HTTPException, ValueError) as e:
            # includes IncompleteRead (dropped stream mid-body) and bad JSON —
            # both transient on long generations; retry
            last = ModelError(f"{deployment}: {type(e).__name__}: {e}")
        time.sleep(2 * (attempt + 1))
    raise last or ModelError(f"{deployment}: exhausted retries")


def smoke(deployments: list[str] | None = None) -> dict[str, str]:
    """One tiny call per deployment; returns {deployment: 'ok'|error}."""
    res = {}
    for d in deployments or list(ROSTER):
        try:
            chat(d, [{"role": "user", "content": "Reply with exactly: pong"}],
                 max_tokens=200, timeout=60, retries=0)
            res[d] = "ok"
        except ModelError as e:
            res[d] = str(e)[:200]
    return res


if __name__ == "__main__":
    for d, status in smoke().items():
        print(f"{d:24s} {status}")
