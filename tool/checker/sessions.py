"""Bounded private coq-lsp sessions. A goal state is not a verification verdict.

Only prefixes are sent to the language server. didChange preserves its prefix
cache on forward steps and invalidates edited suffixes. Full compilation stays
on the independent, fresh coqc route. No arbitrary JSON-RPC is exposed to HTTP.
"""
import atexit
import functools
import json
import os
from pathlib import Path
import secrets
import select
import signal
import tempfile
import threading
import time

import isolation

# The opam package includes the Coq compatibility suffix; the executable and
# serverVersion notification report only 0.2.5. Check Coq's version separately.
LSP_PACKAGE = "0.2.5+8.20"
LSP_VERSION = "0.2.5"
IDLE_SECONDS = 300
LIFETIME_SECONDS = 1800
OP_SECONDS = 25
MAX_FRAME = 4_000_000
MAX_TRAFFIC = 16_000_000


class SessionError(RuntimeError):
    """Messages are fixed public text, never raw process/provider exceptions."""


class SessionExpired(SessionError):
    pass


def end_position(text):
    return {"line": text.count("\n"),
            "character": len(text.rsplit("\n", 1)[-1].encode("utf-16-le")) // 2}


@functools.lru_cache(maxsize=4)
def capability(repo):
    if not isolation.capability(repo)["available"]:
        return False
    try:
        with tempfile.TemporaryDirectory(prefix="atlas-lsp-probe-") as scratch:
            result = isolation.run(repo, scratch, "coq-lsp", ["--version"], timeout=8)
        return result["returncode"] == 0 and result["output"].strip() == LSP_VERSION
    except (isolation.IsolationUnavailable, OSError):
        return False


class LspSession:
    def __init__(self, repo, path, source_hash, library_hash):
        self.repo, self.path = Path(repo), path
        self.source_hash, self.library_hash = source_hash, library_hash
        self.lock = threading.Lock()
        self.created = self.used = time.monotonic()
        self.sequence = self.version = self.request_id = 0
        self.closed = False
        self.buffer = bytearray()
        self.diagnostics = None
        self.perf = None
        self.server_version = None
        self.last_prefix = None
        self.proc = self.stderr = None
        self.directory = tempfile.TemporaryDirectory(prefix="atlas-session-")
        self.scratch = Path(self.directory.name)
        self.uri = (self.scratch / Path(path).name).as_uri()
        try:
            (self.scratch / "_CoqProject").write_text("\n".join(
                f'-R "{self.repo / root}" ""' for root in isolation.ROOTS) + "\n")
            self.stderr = tempfile.TemporaryFile(dir=self.scratch)
            self.proc = isolation.start_session(repo, self.scratch, "coq-lsp", [], self.stderr)
            os.set_blocking(self.proc.stdout.fileno(), False)
            os.set_blocking(self.proc.stdin.fileno(), False)
            self.begin_operation()
            self.rpc("initialize", {
                "processId": None, "rootUri": self.scratch.as_uri(),
                "workspaceFolders": [{"uri": self.scratch.as_uri(), "name": "Private copy"}],
                "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}},
                "initializationOptions": {
                    "client_version": "any", "admit_on_bad_qed": False,
                    "max_errors": 0, "check_only_on_request": False,
                    "eager_diagnostics": True, "send_diags": True, "send_perf_data": True,
                    "pp_type": 0, "verbosity": 2}})
            self.notify("initialized", {})
        except Exception:
            self.close()
            raise

    def begin_operation(self):
        self.deadline = time.monotonic() + OP_SECONDS
        self.traffic = 0

    def remaining(self):
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise SessionError("Coq session timed out and was closed. Retry in a new session.")
        return remaining

    def send(self, message):
        payload = json.dumps(message, ensure_ascii=True).encode("utf-8")
        frame = f"Content-Length: {len(payload)}\r\n\r\n".encode() + payload
        offset = 0
        while offset < len(frame):
            _, writable, _ = select.select([], [self.proc.stdin], [], self.remaining())
            if writable:
                offset += os.write(self.proc.stdin.fileno(), frame[offset:])

    def receive(self):
        while True:
            self.remaining()
            boundary = self.buffer.find(b"\r\n\r\n")
            if boundary >= 0:
                if boundary > 4096:
                    raise SessionError("Invalid Coq session protocol header.")
                fields = self.buffer[:boundary].decode("ascii").split("\r\n")
                lengths = [line.split(":", 1)[1].strip() for line in fields
                           if line.lower().startswith("content-length:")]
                if len(lengths) != 1 or not lengths[0].isdigit():
                    raise SessionError("Invalid Coq session protocol frame.")
                size = int(lengths[0])
                if size > MAX_FRAME:
                    raise SessionError("Coq session output exceeded its size limit.")
                total = boundary + 4 + size
                if len(self.buffer) >= total:
                    payload = bytes(self.buffer[boundary + 4:total])
                    del self.buffer[:total]
                    self.traffic += total
                    if self.traffic > MAX_TRAFFIC:
                        raise SessionError("Coq session output exceeded its operation limit.")
                    message = json.loads(payload)
                    if not isinstance(message, dict):
                        raise SessionError("Invalid Coq session protocol response.")
                    return message
            elif len(self.buffer) > 4096:
                raise SessionError("Invalid Coq session protocol header.")
            readable, _, _ = select.select([self.proc.stdout], [], [], self.remaining())
            if readable:
                data = os.read(self.proc.stdout.fileno(), 65536)
                if not data:
                    raise SessionError("Coq session stopped. Retry in a new session.")
                self.buffer.extend(data)

    def notification(self, message):
        method, params = message.get("method"), message.get("params", {})
        if "id" in message:
            # The server cannot ask this adapter to execute commands or read
            # arbitrary documents. Unsupported server requests are rejected.
            self.send({"jsonrpc": "2.0", "id": message["id"],
                       "error": {"code": -32601, "message": "Unsupported server request"}})
        elif method == "$/coq/serverVersion":
            self.server_version = params
        elif method == "textDocument/publishDiagnostics":
            if params.get("uri") == self.uri and params.get("version") == self.version:
                self.diagnostics = params.get("diagnostics")
        elif method == "$/coq/filePerfData":
            doc = params.get("textDocument", {})
            if doc.get("uri") == self.uri and doc.get("version") == self.version:
                self.perf = params

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def rpc(self, method, params):
        self.request_id += 1
        ident = self.request_id
        self.send({"jsonrpc": "2.0", "id": ident, "method": method, "params": params})
        while True:
            message = self.receive()
            if message.get("id") == ident and "method" not in message:
                if "error" in message:
                    raise SessionError("Coq could not complete the session query. No successful check is claimed.")
                return message.get("result")
            self.notification(message)

    def prefix(self, text):
        self.begin_operation()
        changed = text != self.last_prefix
        if changed:
            self.version += 1
            self.diagnostics = self.perf = None
            document = {"uri": self.uri, "version": self.version}
            if self.last_prefix is None:
                self.notify("textDocument/didOpen", {"textDocument": {
                    **document, "languageId": "coq", "text": text}})
            else:
                self.notify("textDocument/didChange", {
                    "textDocument": document, "contentChanges": [{"text": text}]})
            # The final versioned perf notification is emitted after checking
            # completes, including failure. Requesting getDocument too early
            # can otherwise wait forever after max_errors stops processing.
            while self.perf is None or self.diagnostics is None:
                self.notification(self.receive())
            self.last_prefix = text
        version = self.server_version or {}
        if version.get("coq") != isolation.COQ_VERSION or version.get("coq_lsp") != LSP_VERSION:
            raise SessionError("Coq language-server version mismatch; session closed.")
        document = {"uri": self.uri, "version": self.version}
        snapshot = self.rpc("coq/getDocument", {"textDocument": document})
        diagnostics = self.diagnostics or []
        # ppx_deriving_yojson encodes the nullary variant as a one-item array,
        # not a bare string (PROTOCOL.md CompletionStatus).
        ok = snapshot.get("completed", {}).get("status") == ["Yes"] and not any(
            item.get("severity", 1) == 1 for item in diagnostics)
        answer = None
        if ok:
            answer = self.rpc("proof/goals", {"textDocument": document,
                "position": end_position(text), "pp_format": "Str", "compact": True, "mode": "After"})
            if answer.get("textDocument") != document:
                raise SessionError("Coq returned a different document version; session closed.")
            ok = not answer.get("error")
        messages = [item.get("message", "") for item in diagnostics]
        if answer:
            messages.extend(item.get("text", "") for item in answer.get("messages", []))
            if answer.get("error"):
                messages.append(answer["error"])
        output = "\n".join(str(item) for item in messages)
        return {"ok": ok, "goals": answer.get("goals") if answer and ok else None,
                "diagnostics": diagnostics, "output": output[-60000:],
                "truncated": len(output) > 60000, "document_version": self.version,
                "execution": "persistent", "lsp_version": LSP_VERSION,
                "same_prefix": not changed, "timeout": False}

    def expired(self, now):
        return self.closed or now - self.used > IDLE_SECONDS or now - self.created > LIFETIME_SECONDS

    def close(self):
        if self.closed:
            return
        self.closed = True
        if self.proc:
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait(timeout=5)
            self.proc.stdin.close()
            self.proc.stdout.close()
        if self.stderr:
            self.stderr.close()
        self.directory.cleanup()


class Pool:
    """Sessions reserve a worker slot for their entire lifetime, including idle.

    This shares the existing global Coq budget rather than adding two further
    large processes beside the replay workers. A token is a bearer capability,
    carried only in a header, not a URL, cookie, or model context.
    """
    def __init__(self, slots, factory=LspSession):
        self.slots, self.factory = slots, factory
        self.lock = threading.RLock()
        self.items = {}
        self.started = False
        atexit.register(self.close_all)

    def open(self, repo, path, source_hash, library_hash):
        self.reap()
        if not self.slots.acquire(blocking=False):
            raise SessionError("Coq capacity is occupied. Close an idle session or retry shortly.")
        try:
            session = self.factory(repo, path, source_hash, library_hash)
        except Exception:
            self.slots.release()
            raise
        token = secrets.token_urlsafe(32)
        with self.lock:
            self.items[token] = session
            if not self.started:
                threading.Thread(target=self._reaper, daemon=True, name="coq-session-expiry").start()
                self.started = True
        return token, session

    def get(self, token):
        with self.lock:
            session = self.items.get(token)
            if session is None or session.expired(time.monotonic()):
                raise SessionExpired("Coq session expired or is unknown. Start a new session.")
            return session

    def close(self, token):
        with self.lock:
            session = self.items.get(token)
            if session is None:
                return True
            if not session.lock.acquire(blocking=False):
                return False
            try:
                session.close()
                del self.items[token]
                self.slots.release()
            finally:
                session.lock.release()
            return True

    def reap(self):
        with self.lock:
            expired = [token for token, session in self.items.items() if session.expired(time.monotonic())]
        for token in expired:
            self.close(token)

    def _reaper(self):
        while True:
            time.sleep(10)
            self.reap()

    def close_all(self):
        with self.lock:
            tokens = list(self.items)
        for token in tokens:
            self.close(token)
