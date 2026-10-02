"""OpenRouter-only model access for the Semantics Workbench.

models.json maps stable application aliases to explicit OpenRouter model IDs.
Web requests supply a request-scoped user key. Trusted CLI calls may read
OPENROUTER_API_KEY. No Azure route, model substitution, or redirect is used.
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

ENDPOINT = CFG["endpoint"]
ROSTER = {m["deployment"]: m for m in CFG["roster"]}
POLICY = CFG["policy"]


class ModelError(RuntimeError):
    pass


def _key(api_key: str | None = None) -> str:
    key = (os.environ.get("OPENROUTER_API_KEY", "") if api_key is None else api_key).strip()
    if not key:
        raise ModelError("Supply an OpenRouter key; OPENROUTER_API_KEY is not set or the request key is empty")
    return key


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        # Do not forward a paid credential to an unexpected destination.
        return None


_HTTP = urllib.request.build_opener(_NoRedirect())


def _post(url: str, payload: dict, timeout: int, *, api_key: str | None = None) -> dict:
    if url != "https://openrouter.ai/api/v1/chat/completions":
        raise ModelError("Only the configured OpenRouter chat endpoint is allowed")
    key = _key(api_key)
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode(),
        headers={"Content-Type": "application/json",
                 "Authorization": f"Bearer {key}",
                 "X-OpenRouter-Title": "Formalizability Atlas"})
    with _HTTP.open(req, timeout=timeout) as response:
        raw = response.read(2_000_001)
    if len(raw) > 2_000_000:
        raise ModelError("OpenRouter response exceeded the size limit")
    if key in raw.decode(errors="replace"):
        raise ModelError("Provider echoed a credential; response withheld")
    result = json.loads(raw)
    if key in json.dumps(result, ensure_ascii=False):
        raise ModelError("Provider echoed a credential; response withheld")
    return result


def chat(deployment: str, messages: list[dict], *, max_tokens: int = 8000,
         temperature: float = 0.2, timeout: int = 300, retries: int = 2,
         api_key: str | None = None) -> str:
    """Return completed assistant text, or a sanitized ModelError.

    No reasoning text, partial output, refusal, tool call, or upstream error body
    is accepted as a proof candidate. Retries keep the exact selected model.
    """
    if deployment not in ROSTER:
        raise ModelError("Model is not in models.json roster")
    entry = ROSTER[deployment]
    payload = {"model": entry["model"], "messages": messages,
               "max_tokens": max_tokens, "stream": False}
    # The catalog does not list temperature for these OpenAI reasoning models.
    if entry["family"] != "openai":
        payload["temperature"] = temperature
    last = None
    for attempt in range(retries + 1):
        try:
            out = _post(f"{ENDPOINT}/chat/completions", payload, timeout, api_key=api_key)
            if out.get("error"):
                raise ModelError("OpenRouter returned a provider error")
            choice = out["choices"][0]
            if choice.get("error") or choice.get("finish_reason") != "stop":
                raise ModelError("OpenRouter response incomplete or rejected")
            message = choice["message"]
            if (message.get("role") != "assistant" or message.get("refusal")
                    or message.get("tool_calls")):
                raise ModelError("OpenRouter returned no completed assistant message")
            text = message.get("content")
            if not isinstance(text, str) or not text.strip():
                raise ModelError("OpenRouter returned no assistant text")
            return text
        except (KeyError, IndexError, TypeError, AttributeError) as e:
            raise ModelError("Malformed OpenRouter response") from e
        except urllib.error.HTTPError as e:
            # Error bodies can contain private inputs or credentials.
            last = ModelError(f"OpenRouter: HTTP {e.code}")
            e.close()
            if e.code not in (408, 429) and e.code < 500:
                break
        except (urllib.error.URLError, TimeoutError, OSError,
                http.client.HTTPException, ValueError) as e:
            last = ModelError(f"OpenRouter transport failure: {type(e).__name__}")
        if attempt < retries:
            time.sleep(2 * (attempt + 1))
    raise last or ModelError("OpenRouter exhausted retries")


def smoke(deployments: list[str] | None = None) -> dict[str, str]:
    """One tiny call per requested alias. Defaults to Astra, not the whole roster."""
    results = {}
    for alias in deployments or ["gpt-6-astra"]:
        try:
            chat(alias, [{"role": "user", "content": "Reply with exactly: pong"}],
                 max_tokens=2000, timeout=90, retries=0)
            results[alias] = "ok"
        except ModelError as error:
            results[alias] = str(error)
    return results


if __name__ == "__main__":
    for alias, status in smoke().items():
        print(f"{alias:24s} {status}")
