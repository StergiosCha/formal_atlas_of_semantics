"""Offline contracts; --live additionally runs trusted fixtures in the OS sandbox."""
import json
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "llm"))
import isolation
import workspace as w
import providers
from fastapi import HTTPException
from starlette.requests import Request

LIVE = "--live" in sys.argv
if LIVE:
    sys.argv.remove("--live")


def request(api_key="sk-or-test-user"):
    headers=[] if api_key is None else [(b"x-openrouter-key",api_key.encode())]
    return Request({"type": "http", "headers": headers, "client": ("127.0.0.1", 1234)})


class WorkspaceTests(unittest.TestCase):
    def test_route_paths(self):
        self.assertEqual({r.path for r in w.router.routes},
                         {"/workspace/capabilities", "/workspace/check", "/workspace/explain"})

    def setUp(self):
        w.HITS.clear()
        w.GLOBAL_HITS.clear()
        sources, fingerprint = w.library()
        self.path = "atlas/montague/PTQ.v"
        self.base = dict(path=self.path, source_sha256=sources[self.path], library_sha256=fingerprint,
                         code="Lemma demo : forall P : Prop, P -> P.\nProof. intros P H. exact H. Qed.\n")

    def test_manifest_matches_site_algorithm(self):
        sys.path.insert(0, str(w.REPO / "atlas_data"))
        from proof_sources import library_fingerprint
        sources, fingerprint = w.library()
        self.assertEqual(fingerprint, library_fingerprint({p: {"path": p, "sha256": h} for p, h in sources.items()}))

    def test_changed_source_and_library_rejected(self):
        for field in ["source_sha256", "library_sha256"]:
            with self.assertRaises(HTTPException) as e:
                w.validate_source(w.SourceRequest(**{**self.base, field: "0" * 64}))
            self.assertEqual(e.exception.status_code, 409)

    def test_unknown_path_rejected(self):
        with self.assertRaises(HTTPException) as e:
            w.validate_source(w.SourceRequest(**{**self.base, "path": "../../secret"}))
        self.assertEqual(e.exception.status_code, 404)

    def test_no_sandbox_no_execution(self):
        with patch.object(isolation, "capability", return_value={"available": False, "error": "disabled"}), patch.object(isolation, "run") as run:
            with self.assertRaises(HTTPException) as e:
                w.check(w.CheckRequest(**self.base, mode="file", cursor=0), request())
            self.assertEqual(e.exception.status_code, 503)
            run.assert_not_called()

    def test_prefix_uses_loader_not_stdin_recovery(self):
        cap={"available": True, "coq_version": "8.20.1", "sandbox": "test double"}
        with patch.object(isolation, "capability", return_value=cap), patch.object(isolation, "run", return_value={"returncode": 0, "output": "1 goal", "timeout": False, "truncated": False}) as run:
            out=w.check(w.CheckRequest(**self.base, mode="prefix", cursor=35), request())
            self.assertIn("-load-vernac-source", run.call_args.args[3])
            self.assertEqual(run.call_args.kwargs["stdin"], "Show.\n")
            self.assertEqual(out["status"], "checked_prefix")
            self.assertEqual(out["checked_characters"], 35)
            self.assertEqual(out["code_sha256"], w.digest(self.base["code"]))

    def test_explain_no_compiler_no_verification(self):
        req=w.ExplainRequest(**self.base, start=0, end=10, question="Explain")
        with patch.object(providers,"chat",return_value="<script>not executed</script>") as chat, patch.object(isolation,"run") as run:
            out=w.explain(req,request())
            self.assertFalse(out["verified"])
            self.assertEqual(out["provider"], "openrouter")
            self.assertEqual(out["model_id"], "openai/gpt-6-astra")
            self.assertEqual(chat.call_args.kwargs["api_key"], "sk-or-test-user")
            run.assert_not_called()
            payload=json.loads(chat.call_args.args[1][1]["content"])
            self.assertEqual(payload["selection"], self.base["code"][:10])
            self.assertTrue(payload["modified"])
            self.assertIn("cannot", chat.call_args.args[1][0]["content"])

    def test_provider_error_does_not_echo_secrets(self):
        with patch.object(providers,"chat",side_effect=providers.ModelError("SECRET_KEY private request")):
            with self.assertRaises(HTTPException) as e:
                w.explain(w.ExplainRequest(**self.base, start=0, end=10, question="Explain"),request())
            self.assertNotIn("SECRET", e.exception.detail)

    def test_explanation_uses_openrouter_transport(self):
        reply={"choices":[{"finish_reason":"stop","message":{"role":"assistant","content":"Explanation fixture"}}]}
        req=w.ExplainRequest(**self.base,start=0,end=10,question="Explain")
        with patch.dict("os.environ", {"OPENROUTER_API_KEY":"fixture-key"}), patch.object(providers._HTTP,"open") as send:
            send.return_value.__enter__.return_value=io.BytesIO(json.dumps(reply).encode())
            out=w.explain(req,request())
            upstream=send.call_args.args[0]
            self.assertEqual(upstream.full_url,"https://openrouter.ai/api/v1/chat/completions")
            self.assertEqual(json.loads(upstream.data)["model"],"openai/gpt-6-astra")
            self.assertEqual(upstream.get_header("Authorization"),"Bearer sk-or-test-user")
            self.assertEqual(out["text"],"Explanation fixture")
            self.assertFalse(out["verified"])

    def test_missing_user_key_never_uses_server_key(self):
        with patch.dict("os.environ", {"OPENROUTER_API_KEY":"server-key"}), patch.object(providers,"chat") as chat:
            with self.assertRaises(HTTPException) as error:
                w.explain(w.ExplainRequest(**self.base,start=0,end=10,question="Explain"),request(None))
            self.assertEqual(error.exception.status_code,401)
            chat.assert_not_called()

    def test_invalid_user_key_is_not_echoed(self):
        for key in ["secret-invalid", "sk-or-"+"a"*513, "sk-or-bad key"]:
            with self.assertRaises(HTTPException) as error:
                w.user_model_key(request(key))
            self.assertEqual(error.exception.status_code,400)
            self.assertNotIn(key,error.exception.detail)

    def test_verifier_passes_request_key_without_caching(self):
        with patch.dict("os.environ", {"ATLAS_REPO":str(w.REPO), "ATLAS_JSON":str(w.CATALOG)}):
            import server
            import loop
        fixture={"bucket":"PROVED","rounds":1,"code":"fixture","audit":{}}
        with patch.object(loop,"one_run",return_value=fixture) as run, patch.object(isolation,"capability",return_value={"available":True}):
            for key in ("sk-or-user-a","sk-or-user-b"):
                result=server.verify(server.VerifyRequest(claim="same claim"),request(key))
                self.assertEqual(run.call_args.kwargs["api_key"],key)
                self.assertNotIn(key,json.dumps(result))
            self.assertEqual(run.call_count,2)
        with self.assertRaises(HTTPException) as error:
            server.verify(server.VerifyRequest(claim="same claim"),request(None))
        self.assertEqual(error.exception.status_code,401)

    def test_verifier_unavailable_never_spends_user_credits(self):
        import server
        with patch.object(isolation,"capability",return_value={"available":False}), patch.object(server,"_verify") as run:
            with self.assertRaises(HTTPException) as error:
                server.verify(server.VerifyRequest(claim="test"),request())
            self.assertEqual(error.exception.status_code,503)
            run.assert_not_called()

    def test_empty_selection_and_unknown_model(self):
        for extra in [dict(start=3,end=3), dict(start=0,end=10,model="claude")]:
            with self.assertRaises(HTTPException):
                w.explain(w.ExplainRequest(**self.base,question="Explain",**extra),request())

    def test_context_is_bounded(self):
        req=w.ExplainRequest(**{**self.base,"code":"x"*100000},start=50000,end=50100,question="Explain")
        context=w.explanation_context(req)
        self.assertTrue(context["context_is_partial"])
        self.assertLess(len(context["context"]),11000)

    def test_credentials_not_in_child_environment(self):
        with patch.dict("os.environ", {"AZURE_AI_KEY":"secret", "OPENROUTER_API_KEY":"secret"}):
            self.assertNotIn("AZURE_AI_KEY", isolation.clean_env())
            self.assertNotIn("OPENROUTER_API_KEY", isolation.clean_env())

    def test_linux_sandbox_has_no_procfs_and_keeps_namespaces(self):
        with patch.object(isolation.platform,"system",return_value="Linux"), patch.object(isolation.shutil,"which",side_effect=lambda name:"/usr/bin/"+name):
            command=isolation.command(w.REPO,"/tmp/atlas-fixture","coqtop",["--version"])
        self.assertIn("--unshare-all",command)
        self.assertNotIn("--proc",command)
        self.assertNotIn("/proc",command)
        self.assertNotIn("/srv",command)

    def test_exit_scan_ignores_nested_comments_and_strings(self):
        self.assertNotIn("Quit",w.visible_commands('(* outer (* Quit. *) *) Check "Quit.".'))
        self.assertIn("Quit",w.visible_commands('(* comment *) Quit.'))

    def test_origin_and_budget(self):
        bad=Request({"type":"http","headers":[(b"origin",b"https://untrusted.example")],"client":("x",1)})
        with self.assertRaises(HTTPException): w.guard(bad,"check")
        for _ in range(30): w.guard(request(),"explain")
        with self.assertRaises(HTTPException) as e: w.guard(request(),"explain")
        self.assertEqual(e.exception.status_code,429)


@unittest.skipUnless(LIVE, "pass --live to test real sandboxed Coq")
class LiveCoqTests(unittest.TestCase):
    def setUp(self):
        WorkspaceTests.setUp(self)
        cap=isolation.capability(str(w.REPO))
        self.assertTrue(cap["available"],cap)

    def run_code(self,code,mode="file"):
        return w.check(w.CheckRequest(**{**self.base,"code":code},mode=mode,cursor=len(code)),request())

    def test_real_success_failure_open_goals_and_imports(self):
        result=self.run_code(self.base["code"])
        self.assertTrue(result["ok"],result)
        result=self.run_code("Lemma bad : False. Proof. exact I. Qed.")
        self.assertFalse(result["ok"],result)
        result=self.run_code("Lemma open_goal : forall P : Prop, P -> P. Proof. intros P H.","prefix")
        self.assertTrue(result["ok"],result)
        self.assertIn("H : P",result["output"])
        result=self.run_code("Lemma bad : False. Proof. exact I. Abort.","prefix")
        self.assertFalse(result["ok"],result)
        result=self.run_code("Require Import ttr.TTR_Model. Check TTR_Model.Countermodels.inhabited_conjuncts_empty_meet.")
        self.assertTrue(result["ok"],result)
        result=self.run_code((w.REPO/self.path).read_text())
        self.assertTrue(result["ok"],result)

    def test_real_pending_proof_is_not_full_compilation(self):
        result=self.run_code("Lemma unfinished : True. Proof.")
        self.assertFalse(result["ok"],result)

    def test_real_prefix_outside_proof(self):
        result=self.run_code("Definition x := 1.","prefix")
        self.assertTrue(result["ok"],result)
        self.assertNotIn("Error:",result["output"])

    def test_real_exit_command_rejected(self):
        with self.assertRaises(HTTPException):
            self.run_code("Quit. Lemma unchecked : False.","prefix")

    def test_real_private_file_read_denied(self):
        # A fake secret lives outside every permitted Coq root. No real secret
        # is opened. Load would print the marker if isolation were broken.
        with tempfile.TemporaryDirectory(prefix="atlas-fake-secret-") as outside:
            secret=Path(outside)/"Private.v"
            secret.write_text('Goal True. idtac "PRIVATE_CANARY_SHOULD_NOT_BE_READ". exact I. Qed.')
            result=self.run_code(f'Load "{secret}".')
            self.assertFalse(result["ok"],result)
            self.assertNotIn("PRIVATE_CANARY_SHOULD_NOT_BE_READ",result["output"])

    def test_real_admitted_is_not_a_verified_badge(self):
        result=self.run_code("Lemma assumption : False. Admitted.")
        self.assertEqual(result["status"],"compiled_copy")
        self.assertIn("Admissions",result["notice"])

    def test_legacy_public_checker_requires_same_sandbox(self):
        import check_local
        with patch.dict("os.environ", {"ATLAS_REQUIRE_SANDBOX":"1"}):
            result=check_local.check("Lemma public_demo : True. Proof. exact I. Qed.", audit=["public_demo"])
            self.assertTrue(result["ok"], result)
            self.assertEqual(result["audit"]["public_demo"], "closed")
            with patch.object(isolation,"capability",return_value={"available":False,"error":"sandbox unavailable"}), patch.object(isolation,"run") as run:
                result=check_local.check("Goal True. exact I. Qed.")
                self.assertFalse(result["ok"])
                run.assert_not_called()


if __name__ == "__main__":
    if "--diagnose" in sys.argv:
        with tempfile.TemporaryDirectory(prefix="atlas-sandbox-diagnostic-") as scratch:
            cmd=isolation.command(w.REPO,scratch,"coqtop",["--version"])
            direct=subprocess.run(cmd,env=isolation.clean_env(),capture_output=True,text=True)
            print("without limit launcher",direct.returncode,direct.stdout,direct.stderr)
            print("with limit launcher",isolation.run(w.REPO,scratch,"coqtop",["--version"]))
    else:
        unittest.main()
