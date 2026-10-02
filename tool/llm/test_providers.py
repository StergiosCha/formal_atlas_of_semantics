"""Offline OpenRouter contracts. No credentials, paid calls or Coq required."""
import io
import json
import os
import unittest
import urllib.error
from unittest.mock import patch

import providers


def reply(text="draft", finish="stop", **message):
    return {"choices": [{"finish_reason": finish,
                         "message": {"role": "assistant", "content": text, **message}}]}


class ProviderTests(unittest.TestCase):
    def test_allowlist_and_policy(self):
        self.assertEqual(providers.CFG["provider"], "openrouter")
        self.assertEqual(providers.ROSTER["gpt-6-astra"]["model"], "openai/gpt-6-astra")
        self.assertEqual(providers.ROSTER["gpt-5.4-pro-2"]["model"], "openai/gpt-5.4-pro")
        self.assertEqual(providers.POLICY["first_draft"], "gpt-5.4-mini")
        self.assertEqual(providers.POLICY["escalate_to"], "gpt-6-astra")
        ids = [m["model"] for m in providers.ROSTER.values()]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertTrue(all("/" in model and "claude" not in model for model in ids))
        with patch.object(providers, "_post") as post:
            for name in ("claude-opus-5", "anthropic/claude-fable-5", "unknown",
                         "MAI-Thinking-1", "grok-4-1-fast-reasoning"):
                with self.assertRaises(providers.ModelError):
                    providers.chat(name, [])
            post.assert_not_called()

    def test_all_models_use_openrouter_ids_and_chat_contract(self):
        messages = [{"role": "system", "content": "policy"},
                    {"role": "user", "content": "explain"}]
        for alias, entry in providers.ROSTER.items():
            with self.subTest(alias=alias), patch.object(providers, "_post", return_value=reply()) as post:
                self.assertEqual(providers.chat(alias, messages, max_tokens=900), "draft")
                url, payload, _ = post.call_args.args
                self.assertEqual(url, "https://openrouter.ai/api/v1/chat/completions")
                expected = {"model": entry["model"], "messages": messages,
                            "max_tokens": 900, "stream": False}
                if entry["family"] != "openai":
                    expected["temperature"] = 0.2
                self.assertEqual(payload, expected)

    def test_incomplete_or_refusal_replies_fail_closed(self):
        for response in ({}, None, [], {"choices": []}, {"choices": None},
                         {"error": {"message": "private"}},
                         reply(finish="length"), reply(finish="content_filter"),
                         reply(finish=None), reply(finish="tool_calls"),
                         reply(text=None), reply(text=" "), reply(text=[{"text": "no"}]),
                         reply(refusal="refused"), reply(tool_calls=[{}]), reply(role="user")):
            with self.subTest(response=response), patch.object(providers, "_post", return_value=response):
                with self.assertRaises(providers.ModelError):
                    providers.chat("gpt-6-astra", [], retries=0)

    def test_only_assistant_text_is_returned(self):
        with patch.object(providers, "_post", return_value=reply(reasoning="private reasoning")):
            self.assertEqual(providers.chat("gpt-6-astra", []), "draft")

    def test_auth_is_server_side_bearer_only(self):
        with patch.dict(os.environ, {"OPENROUTER_API_KEY": "test-key", "AZURE_AI_KEY": "wrong-key"}), \
                patch.object(providers._HTTP, "open") as send:
            send.return_value.__enter__.return_value = io.BytesIO(b'{}')
            providers._post(providers.ENDPOINT + "/chat/completions", {"model": "openai/gpt-6-astra"}, 10)
            req = send.call_args.args[0]
            headers = {k.lower(): v for k, v in req.header_items()}
            self.assertEqual(headers["authorization"], "Bearer test-key")
            for name in ("api-key", "x-api-key", "anthropic-version"):
                self.assertNotIn(name, headers)
            self.assertNotIn("test-key", req.data.decode())
            self.assertEqual(req.full_url, "https://openrouter.ai/api/v1/chat/completions")

    def test_missing_key_does_not_fall_back_to_azure(self):
        with patch.dict(os.environ, {"AZURE_AI_KEY": "legacy"}, clear=True), \
                patch.object(providers._HTTP, "open") as send:
            with self.assertRaisesRegex(providers.ModelError, "OPENROUTER_API_KEY is not set"):
                providers.chat("gpt-6-astra", [])
            send.assert_not_called()

    def test_request_keys_are_isolated_and_never_installed_in_environment(self):
        with patch.dict(os.environ, {"OPENROUTER_API_KEY":"server-key"}), patch.object(providers._HTTP,"open") as send:
            for key in ("sk-or-user-a", "sk-or-user-b"):
                send.return_value.__enter__.return_value=io.BytesIO(json.dumps(reply()).encode())
                self.assertEqual(providers.chat("gpt-6-astra",[],api_key=key),"draft")
                self.assertEqual(send.call_args.args[0].get_header("Authorization"),"Bearer "+key)
                self.assertEqual(os.environ["OPENROUTER_API_KEY"],"server-key")
            with self.assertRaises(providers.ModelError):
                providers.chat("gpt-6-astra",[],api_key="")
            self.assertEqual(send.call_count,2)

    def test_destination_is_locked_and_redirects_are_refused(self):
        with patch.object(providers._HTTP, "open") as send:
            for url in ("https://example.invalid", "http://openrouter.ai/api/v1/chat/completions"):
                with self.assertRaises(providers.ModelError):
                    providers._post(url, {}, 1)
            send.assert_not_called()
        self.assertIsNone(providers._NoRedirect().redirect_request(None, None, 302, "", {}, "https://other.invalid"))

    def test_provider_credential_echo_is_withheld(self):
        with patch.dict(os.environ, {"OPENROUTER_API_KEY": "test-key"}), \
                patch.object(providers._HTTP, "open") as send:
            send.return_value.__enter__.return_value = io.BytesIO(b'{"content":"test-key"}')
            with self.assertRaises(providers.ModelError) as error:
                providers._post(providers.ENDPOINT + "/chat/completions", {}, 1)
            self.assertNotIn("test-key", str(error.exception))

    def test_http_config_errors_do_not_retry_or_echo_bodies(self):
        for status in (301, 400, 401, 402, 403, 404):
            err = urllib.error.HTTPError("https://example.invalid", status, "private", {}, io.BytesIO(b"SECRET"))
            with patch.object(providers, "_post", side_effect=err) as post, patch.object(providers.time, "sleep") as sleep:
                with self.assertRaisesRegex(providers.ModelError, f"HTTP {status}") as raised:
                    providers.chat("gpt-6-astra", [])
                self.assertNotIn("SECRET", str(raised.exception))
                self.assertEqual(post.call_count, 1)
                sleep.assert_not_called()

    def test_transient_error_retries_same_model(self):
        err = urllib.error.HTTPError("https://example.invalid", 429, "busy", {}, io.BytesIO())
        with patch.object(providers, "_post", side_effect=[err, reply()]) as post, patch.object(providers.time, "sleep"):
            self.assertEqual(providers.chat("gpt-6-astra", []), "draft")
            self.assertEqual(post.call_count, 2)
            self.assertTrue(all(call.args[1]["model"] == "openai/gpt-6-astra" for call in post.call_args_list))

    def test_transport_error_is_sanitized(self):
        with patch.object(providers, "_post", side_effect=urllib.error.URLError("SECRET")):
            with self.assertRaises(providers.ModelError) as error:
                providers.chat("gpt-6-astra", [], retries=0)
            self.assertNotIn("SECRET", str(error.exception))


if __name__ == "__main__":
    unittest.main()
