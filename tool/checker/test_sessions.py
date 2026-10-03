"""Private-session contracts; --live also tests real, sandboxed coq-lsp.

No provider call or model key is used. The live fixtures are deliberately small
and do not claim source fidelity or a performance result for every atlas file.
"""
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sessions as s
import workspace as w
from fastapi import HTTPException
from starlette.requests import Request

LIVE = "--live" in sys.argv
if LIVE:
    sys.argv.remove("--live")


def request(token=None):
    return Request({"type": "http", "headers": [] if token is None else [(b"x-coq-session", token.encode())],
                    "client": ("127.0.0.1", 1000)})


class FakeSession:
    def __init__(self, repo, path, source_hash, library_hash):
        self.path, self.source_hash, self.library_hash = path, source_hash, library_hash
        self.lock = threading.Lock()
        self.created = self.used = time.monotonic()
        self.sequence = 0
        self.closed = False

    expired = s.LspSession.expired

    def close(self):
        self.closed = True

    def prefix(self, code):
        return {"ok": True, "goals": None, "diagnostics": [], "output": "", "execution": "persistent"}


class PoolTests(unittest.TestCase):
    def setUp(self):
        self.slots = threading.BoundedSemaphore(2)
        self.pool = s.Pool(self.slots, FakeSession)
        self.pool.started = True
        self.addCleanup(self.pool.close_all)

    def open(self):
        return self.pool.open("/atlas", "atlas/Test.v", "a"*64, "b"*64)

    def test_token_separation_and_capacity(self):
        t1, a = self.open()
        t2, b = self.open()
        self.assertNotEqual(t1, t2)
        self.assertEqual(len(t1), 43)
        self.assertIsNot(a, b)
        with self.assertRaises(s.SessionError):
            self.open()
        self.assertTrue(self.pool.close(t1))
        self.assertTrue(a.closed)
        self.assertFalse(b.closed)
        self.open()

    def test_idle_and_absolute_expiry(self):
        for absolute in (False, True):
            token, session = self.open()
            if absolute:
                session.created -= s.LIFETIME_SECONDS + 1
            else:
                session.used -= s.IDLE_SECONDS + 1
            with self.assertRaises(s.SessionExpired):
                self.pool.get(token)
            self.pool.reap()
            self.assertTrue(session.closed)
            self.assertNotIn(token, self.pool.items)

    def test_busy_session_not_closed_mid_operation(self):
        token, session = self.open()
        with session.lock:
            self.assertFalse(self.pool.close(token))
        self.assertTrue(self.pool.close(token))
        self.assertTrue(self.pool.close(token))

    def test_failed_start_releases_slot(self):
        self.pool.factory = lambda *args: (_ for _ in ()).throw(RuntimeError("fixture"))
        for _ in range(4):
            with self.assertRaises(RuntimeError):
                self.open()
        self.assertTrue(self.slots.acquire(False))
        self.assertTrue(self.slots.acquire(False))
        self.slots.release()
        self.slots.release()


class RouteTests(unittest.TestCase):
    def setUp(self):
        w.HITS.clear()
        w.GLOBAL_HITS.clear()
        self.pool = s.Pool(threading.BoundedSemaphore(2), FakeSession)
        self.pool.started = True
        self.addCleanup(self.pool.close_all)
        sources, library = w.library()
        self.base = dict(path="atlas/montague/PTQ.v", source_sha256=sources["atlas/montague/PTQ.v"],
                         library_sha256=library, code="Goal True.")
        self.token, self.session = self.pool.open(str(w.REPO), self.base["path"], self.base["source_sha256"], library)
        self.patcher = patch.object(w, "SESSIONS", self.pool)
        self.patcher.start()
        self.addCleanup(self.patcher.stop)

    def req(self, **overrides):
        return w.SessionCheckRequest(**{**self.base, "sequence": 1, "cursor": 10, **overrides})

    def test_token_required_never_uses_model_key(self):
        for token in (None, "invalid", "a"*44):
            with self.assertRaises(HTTPException) as error:
                w.session_check(self.req(), request(token))
            self.assertEqual(error.exception.status_code, 401)

    def test_unknown_token_and_source_mismatch(self):
        with self.assertRaises(HTTPException) as error:
            w.session_check(self.req(), request("a"*43))
        self.assertEqual(error.exception.status_code, 410)
        self.session.path = "atlas/Another.v"
        with self.assertRaises(HTTPException) as error:
            w.session_check(self.req(), request(self.token))
        self.assertEqual(error.exception.status_code, 409)

    def test_sequence_digest_and_busy_guard(self):
        result = w.session_check(self.req(), request(self.token))
        self.assertEqual(result["code_sha256"], w.digest(self.base["code"]))
        self.assertEqual(result["checked_characters"], 10)
        self.assertEqual(result["sequence"], 1)
        self.assertEqual(result["status"], "session_prefix")
        with self.assertRaises(HTTPException) as error:
            w.session_check(self.req(), request(self.token))
        self.assertEqual(error.exception.status_code, 409)
        with self.session.lock, self.assertRaises(HTTPException) as error:
            w.session_check(self.req(sequence=2), request(self.token))
        self.assertEqual(error.exception.status_code, 409)

    def test_runtime_failure_closes_only_this_session(self):
        other_token, other = self.pool.open(str(w.REPO), self.base["path"], self.base["source_sha256"], self.base["library_sha256"])
        with patch.object(self.session, "prefix", side_effect=RuntimeError("SECRET raw transport")):
            with self.assertRaises(HTTPException) as error:
                w.session_check(self.req(), request(self.token))
        self.assertEqual(error.exception.status_code, 503)
        self.assertNotIn("SECRET", error.exception.detail)
        self.assertTrue(self.session.closed)
        self.assertIs(self.pool.get(other_token), other)

    def test_exit_and_cursor_rejected(self):
        for req in (self.req(code="Quit.", cursor=5), self.req(cursor=11)):
            with self.assertRaises(HTTPException) as error:
                w.session_check(req, request(self.token))
            self.assertEqual(error.exception.status_code, 422)

    def test_isolation_fail_closed(self):
        with patch.object(s, "capability", return_value=False), patch.object(self.pool, "open") as opened:
            with self.assertRaises(HTTPException) as error:
                w.open_session(w.SourceRequest(**self.base), request())
            self.assertEqual(error.exception.status_code, 503)
            opened.assert_not_called()


class ProtocolTests(unittest.TestCase):
    def fixture(self, diagnostics=None, complete="Yes", goal_error=None):
        instance = object.__new__(s.LspSession)
        instance.uri = "file:///tmp/Test.v"
        instance.version = 1
        instance.last_prefix = "Goal True."
        instance.server_version = {"coq": "8.20.1", "coq_lsp": s.LSP_VERSION}
        instance.diagnostics = diagnostics or []
        instance.perf = {}
        instance.rpc = lambda method, params: ({"completed": {"status": [complete]}} if method == "coq/getDocument" else
            {"textDocument": {"uri": instance.uri, "version": 1}, "goals": {"goals": []}, "error": goal_error})
        return instance

    def test_unicode_uses_utf16(self):
        self.assertEqual(s.end_position("a\nα😀x"), {"line": 1, "character": 4})

    def test_runtime_version_is_distinct_from_opam_package(self):
        self.assertEqual(s.LSP_PACKAGE, "0.2.5+8.20")
        self.assertEqual(s.LSP_VERSION, "0.2.5")

    def test_earlier_diagnostic_rejects_even_successful_completion(self):
        session = self.fixture([{"severity": 1, "message": "earlier failed tactic"}])
        result = session.prefix("Goal True.")
        self.assertFalse(result["ok"])
        self.assertIsNone(result["goals"])

    def test_actual_completion_wire_variant_is_accepted(self):
        self.assertTrue(self.fixture().prefix("Goal True.")["ok"])

    def test_failed_completion_is_not_success(self):
        self.assertFalse(self.fixture(complete="Failed").prefix("Goal True.")["ok"])
        self.assertFalse(self.fixture(goal_error="failed tactic").prefix("Goal True.")["ok"])

    def test_wrong_version_is_not_success(self):
        session = self.fixture()
        session.server_version["coq"] = "8.19.0"
        with self.assertRaises(s.SessionError):
            session.prefix("Goal True.")

    def test_stale_diagnostics_and_perf_ignored(self):
        session = self.fixture()
        session.notification({"method": "textDocument/publishDiagnostics", "params": {
            "uri": session.uri, "version": 0, "diagnostics": [{"severity": 1}]}})
        self.assertEqual(session.diagnostics, [])
        session.notification({"method": "$/coq/filePerfData", "params": {
            "textDocument": {"uri": session.uri, "version": 2}, "summary": "wrong"}})
        self.assertEqual(session.perf, {})

    def test_oversized_frame_rejected_before_body_read(self):
        session = self.fixture()
        session.begin_operation()
        session.buffer = bytearray(b"Content-Length: 4000001\r\n\r\n")
        with self.assertRaises(s.SessionError):
            session.receive()


@unittest.skipUnless(LIVE, "requires sandboxed coq-lsp 0.2.5+8.20")
class LiveTests(unittest.TestCase):
    def new(self):
        session = s.LspSession(str(w.REPO), "atlas/montague/PTQ.v", "a"*64, "b"*64)
        self.addCleanup(session.close)
        return session

    def test_forward_backward_edit_and_process_reuse(self):
        session = self.new()
        pid = session.proc.pid
        first = session.prefix("Goal forall P : Prop, P -> P. Proof. intros P H.")
        self.assertTrue(first["ok"], first)
        self.assertEqual(first["goals"]["goals"][0]["ty"], "P")
        second = session.prefix("Goal forall P : Prop, P -> P. Proof. intros P H. exact H.")
        self.assertTrue(second["ok"], second)
        self.assertEqual(second["goals"]["goals"], [])
        back = session.prefix("Goal forall P : Prop, P -> P. Proof. intros P H.")
        self.assertTrue(back["ok"], back)
        self.assertEqual(back["goals"]["goals"][0]["ty"], "P")
        edited = session.prefix("Goal False. Proof.")
        self.assertTrue(edited["ok"], edited)
        self.assertEqual(edited["goals"]["goals"][0]["ty"], "False")
        self.assertEqual(pid, session.proc.pid)

    def test_recovery_never_masks_invalid_tactics_qed_or_bullets(self):
        session = self.new()
        for text in ("Goal False. exact I. Qed. Goal True.", "Goal False. Qed. Goal True.",
                     "Goal True /\\ True. split. - idtac. - exact I. Qed."):
            result = session.prefix(text)
            self.assertFalse(result["ok"], result)
            self.assertIsNone(result["goals"])
        self.assertTrue(session.prefix("Goal True. exact I. Qed.")["ok"])

    def test_sessions_do_not_share_definitions(self):
        first, second = self.new(), self.new()
        self.assertTrue(first.prefix("Definition only_this_tab := 42.")["ok"])
        self.assertFalse(second.prefix("Check only_this_tab.")["ok"])

    def test_real_library_import_and_unicode(self):
        result = self.new().prefix("Require Import montague.PTQ.\n(* 😀 *) Goal forall α : Prop, α -> α. intros α H.")
        self.assertTrue(result["ok"], result)
        self.assertEqual(result["goals"]["goals"][0]["ty"], "α")

    def test_forbidden_file(self):
        with tempfile.TemporaryDirectory(prefix="atlas-session-canary-") as directory:
            target = Path(directory) / "Canary.v"
            target.write_text("Axiom private_canary : False.")
            result = self.new().prefix(f'Load "{target}". Check private_canary.')
            self.assertFalse(result["ok"], result)


if __name__ == "__main__":
    unittest.main()
