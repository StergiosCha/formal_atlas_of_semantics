"""Fail-closed OS isolation for visitor Coq. Never run it beside API secrets.

Linux requires usable bubblewrap user/PID/network namespaces. macOS uses
sandbox-exec for local development. A timeout or an empty environment alone
is not a sandbox. No unrestricted fallback is provided.
"""
import functools
import os
from pathlib import Path
import platform
import resource
import shutil
import signal
import subprocess
import sys
import tempfile

ROOTS = ("shallow", "deep", "extras", "ttr_mtt", "atlas")
COQ_VERSION = "8.20.1"


class IsolationUnavailable(RuntimeError):
    pass


def clean_env():
    return {"PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": "/tmp", "TMPDIR": "/tmp", "LANG": "C.UTF-8"}


def command(repo, scratch, executable, args):
    binary = shutil.which(executable)
    if not binary:
        raise IsolationUnavailable(f"{executable} is not installed")
    repo, scratch = Path(repo).resolve(), Path(scratch).resolve()
    libraries = [str(repo / root) for root in ROOTS if (repo / root).is_dir()]
    system = platform.system()
    if system == "Linux" and shutil.which("bwrap"):
        cmd = [shutil.which("bwrap"), "--die-with-parent", "--new-session",
               "--unshare-all", "--clearenv", "--setenv", "PATH", clean_env()["PATH"],
               "--setenv", "HOME", "/tmp", "--setenv", "LANG", "C.UTF-8",
               "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
        # Only runtime libraries and public Coq roots are visible. In particular,
        # /srv, API credentials, the host home, and the parent /proc are absent.
        paths = ["/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache"]
        opam = Path(binary).resolve()
        if ".opam" in opam.parts:
            paths.append(str(Path(*opam.parts[:opam.parts.index(".opam") + 2])))
        for path in paths + libraries:
            if Path(path).exists():
                cmd += ["--ro-bind", path, path]
        return cmd + ["--bind", str(scratch), str(scratch), "--chdir", str(scratch),
                      "--", binary, *args]
    if system == "Darwin" and Path("/usr/bin/sandbox-exec").exists():
        # sandbox-exec is a local-development adapter, not an Azure substitute.
        import json
        readable = ["/usr", "/bin", "/System/Library", "/System/Volumes/Preboot", "/Library/Apple", "/opt/homebrew",
                    "/private/var/db/dyld", "/dev", str(scratch), *libraries]
        rules = " ".join(f"(subpath {json.dumps(p)})" for p in readable)
        parents = {str(parent) for p in readable for parent in Path(p).parents}
        rules += " " + " ".join(f"(literal {json.dumps(p)})" for p in sorted(parents))
        profile = ("(version 1)(deny default)(allow process-exec process-fork)"
                   "(allow sysctl-read)(allow file-read-metadata)"
                   f"(allow file-read* {rules})"
                   f"(allow file-write* (subpath {json.dumps(str(scratch))})"
                   ' (literal "/dev/null"))')
        return ["/usr/bin/sandbox-exec", "-p", profile, binary, *args]
    raise IsolationUnavailable("An OS sandbox is required; install and enable bubblewrap on Linux")


def run(repo, scratch, executable, args, *, stdin="", timeout=25):
    cmd = command(repo, scratch, executable, args)
    # Limits are installed by a separate launcher, not preexec_fn in a threaded
    # web server. Logs go to a size-limited file, never an unbounded PIPE buffer.
    with tempfile.TemporaryFile(dir=scratch) as log:
        proc = subprocess.Popen([sys.executable, str(Path(__file__).resolve()),
                                 "--limited", str(timeout), *cmd],
                                stdin=subprocess.PIPE, stdout=log, stderr=log,
                                cwd=scratch, env=clean_env(), start_new_session=True)
        timed_out = False
        try:
            proc.communicate(stdin.encode(), timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
        finally:
            # A loaded plugin must not leave descendant processes behind.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        log.seek(0, os.SEEK_END)
        size = log.tell()
        log.seek(max(0, size - 60000))
        output = log.read().decode("utf-8", errors="replace")
    return {"returncode": proc.returncode, "output": output,
            "timeout": timed_out, "truncated": size > 60000}


@functools.lru_cache(maxsize=4)
def capability(repo):
    try:
        with tempfile.TemporaryDirectory(prefix="atlas-sandbox-probe-") as scratch:
            result = run(repo, scratch, "coqtop", ["--version"], timeout=8)
        if result["returncode"] or f"version {COQ_VERSION}" not in result["output"]:
            raise IsolationUnavailable("Sandbox startup or Coq version check failed")
        return {"available": True, "coq_version": COQ_VERSION,
                "sandbox": "bubblewrap" if platform.system() == "Linux" else "macOS sandbox-exec"}
    except (IsolationUnavailable, OSError) as error:
        return {"available": False, "coq_version": COQ_VERSION, "error": str(error)}


if __name__ == "__main__" and sys.argv[1:2] == ["--limited"]:
    seconds = int(sys.argv[2])
    resource.setrlimit(resource.RLIMIT_CPU, (seconds, seconds + 1))
    resource.setrlimit(resource.RLIMIT_FSIZE, (2_000_000, 2_000_000))
    resource.setrlimit(resource.RLIMIT_NOFILE, (128, 128))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    if platform.system() == "Linux":
        resource.setrlimit(resource.RLIMIT_AS, (1536 * 1024**2, 1536 * 1024**2))
    os.execv(sys.argv[3], sys.argv[3:])
