"""Offline contract tests; no credentials, paid calls or Coq required."""
import io
import json
import os
import unittest
import urllib.error
from unittest.mock import patch

import providers


class ProviderTests(unittest.TestCase):
    def test_allowlist_and_policy(self):
        self.assertIn("gpt-6-astra", providers.ROSTER)
        self.assertIn("gpt-5.4-pro-2", providers.ROSTER)
        self.assertEqual(providers.POLICY["first_draft"], "gpt-5.4-mini")
        self.assertEqual(providers.POLICY["escalate_to"], "gpt-6-astra")
        self.assertFalse(any("claude" in d for d in providers.ROSTER))
        with patch.object(providers, "_post") as post:
            for name in ("claude-opus-5", "claude-fable-5", "gpt-image-2", "unknown"):
                with self.assertRaises(providers.ModelError):
                    providers.chat(name, [])
            post.assert_not_called()

    def test_astra_and_pro_responses_contract(self):
        response = {"status": "completed", "output": [
            {"type": "reasoning", "summary": []},
            {"type": "message", "role": "assistant", "content": [
                {"type": "output_text", "text": "first"},
                {"type": "output_text", "text": "second"}]}]}
        messages = [{"role": "user", "content": "draft"}]
        for name in ("gpt-6-astra", "gpt-5.4-pro-2"):
            with patch.object(providers, "_post", return_value=response) as post:
                self.assertEqual(providers.chat(name, messages, max_tokens=900), "first\nsecond")
                url, payload, _ = post.call_args.args
                self.assertEqual(url, providers.ENDPOINT + "/openai/v1/responses")
                self.assertEqual(payload, {"model": name, "input": messages,
                                          "max_output_tokens": 900, "store": False})

    def test_existing_chat_contracts_preserved(self):
        response = {"choices": [{"message": {"content": "draft"}}]}
        for name in ("gpt-5.6-sol", "gpt-5.4-mini", "mistral-medium-2505", "DeepSeek-V4-Flash"):
            with patch.object(providers, "_post", return_value=response) as post:
                self.assertEqual(providers.chat(name, [], max_tokens=700), "draft")
                url, payload, _ = post.call_args.args
                if providers.ROSTER[name]["family"] == "openai":
                    self.assertIn(f"/openai/deployments/{name}/chat/completions", url)
                    self.assertEqual(payload["max_completion_tokens"], 700)
                    self.assertNotIn("temperature", payload)
                else:
                    self.assertIn("/models/chat/completions", url)
                    self.assertEqual(payload["max_tokens"], 700)

    def test_invalid_or_incomplete_replies_fail_closed(self):
        for response in ({}, {"status": "incomplete", "output": []},
                         {"status": "completed", "output": []},
                         {"status": "completed", "output": [{"type": "message",
                          "role": "assistant", "content": [{"type": "refusal"}]}]},
                         {"status": "completed", "output": None}):
            with patch.object(providers, "_post", return_value=response):
                with self.assertRaises(providers.ModelError):
                    providers.chat("gpt-6-astra", [], retries=0)
        with patch.object(providers, "_post", return_value={"choices": []}):
            with self.assertRaises(providers.ModelError):
                providers.chat("gpt-5.4-mini", [], retries=0)

    def test_auth_is_server_side_without_anthropic_headers(self):
        with patch.dict(os.environ, {"AZURE_AI_KEY": "test-key"}), \
                patch.object(providers.urllib.request, "urlopen") as send:
            send.return_value.__enter__.return_value = io.StringIO('{}')
            providers._post("https://example.invalid", {"model": "gpt-6-astra"}, 10)
            req = send.call_args.args[0]
            headers = {k.lower(): v for k, v in req.header_items()}
            self.assertEqual(headers["authorization"], "Bearer test-key")
            self.assertNotIn("anthropic-version", headers)
            self.assertNotIn("x-api-key", headers)
            self.assertNotIn("test-key", json.dumps(json.loads(req.data)))

    def test_missing_key_and_http_config_errors_do_not_retry(self):
        with patch.dict(os.environ, {}, clear=True):
            with self.assertRaises(providers.ModelError):
                providers._key()
        err = urllib.error.HTTPError("https://example.invalid", 404, "missing", {}, io.BytesIO(b"missing"))
        with patch.object(providers, "_post", side_effect=err) as post, \
                patch.object(providers.time, "sleep") as sleep:
            with self.assertRaisesRegex(providers.ModelError, "HTTP 404"):
                providers.chat("gpt-6-astra", [])
            self.assertEqual(post.call_count, 1)
            sleep.assert_not_called()


if __name__ == "__main__":
    unittest.main()
