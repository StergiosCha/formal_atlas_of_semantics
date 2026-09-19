"""Azure Foundry model access for the Semantics Workbench.

Deployments are allowlisted in models.json. Astra and GPT-5.4 Pro use
POST {endpoint}/openai/v1/responses. Existing OpenAI chat deployments keep
their versioned route; other text models keep the Foundry inference route.
Model values are deployment names, which can differ from base model names.

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
with open(os.path.join(HERE, "models.json")) as _cfg_file:
    CFG = json.load(_cfg_file)

ENDPOINT = os.environ.get(CFG["endpoint_env"], CFG["default_endpoint"]).rstrip("/")
API_VERSION = CFG["api_version"]
ROSTER = {m["deployment"]: m for m in CFG["roster"]}
POLICY = CFG["policy"]


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
    key = _key()
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode(),
        headers={"content-type": "application/json", "api-key": key,
                 "authorization": f"Bearer {key}"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def chat(deployment: str, messages: list[dict], *, max_tokens: int = 8000,
         temperature: float = 0.2, timeout: int = 300, retries: int = 2) -> str:
    """One chat call; returns the assistant text. Raises ModelError with the
    server's own words on failure — never invents a reply.

    Responses models omit sampling parameters and use max_output_tokens.
    Incomplete/refusal-only/empty replies are errors, never proof candidates.
    Other routes preserve their existing request contracts.
    """
    if deployment not in ROSTER:
        raise ModelError(f"{deployment} is not in models.json roster")
    family = ROSTER[deployment]["family"]
    last = None
    for attempt in range(retries + 1):
        try:
            if ROSTER[deployment].get("api") == "responses":
                out = _post(f"{ENDPOINT}/openai/v1/responses",
                            {"model": deployment, "input": messages,
                             "max_output_tokens": max_tokens, "store": False}, timeout)
                if out.get("status") != "completed":
                    raise ModelError(f"{deployment}: response {out.get('status', 'missing status')}")
                texts = [c["text"] for item in out.get("output", [])
                         if item.get("type") == "message" and item.get("role") == "assistant"
                         for c in item.get("content", [])
                         if c.get("type") == "output_text" and isinstance(c.get("text"), str)]
                text = "\n".join(texts)
                if not text.strip():
                    raise ModelError(f"{deployment}: no assistant text in reply")
                return text
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
            text = out["choices"][0]["message"]["content"]
            if not isinstance(text, str) or not text.strip():
                raise ModelError(f"{deployment}: no assistant text in reply")
            return text
        except (KeyError, IndexError, TypeError, AttributeError) as e:
            raise ModelError(f"{deployment}: malformed model response") from e
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
        if attempt < retries:
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
