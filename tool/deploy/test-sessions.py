"""Run on the approved VM as root; no production service/config changes.

Pull a digest-pinned candidate with the VM identity and run bounded tests in a
separate, networkless container. Never print or persist registry credentials.
"""
import argparse
import json
import re
import secrets
import subprocess
import tempfile
import urllib.parse
import urllib.request


def run(image):
    registry = "formalatlasacr.azurecr.io"
    if not re.fullmatch(re.escape(registry) + r"/atlas-checker@sha256:[a-f0-9]{64}", image):
        raise SystemExit("A digest-pinned atlas-checker image is required")
    query = urllib.parse.urlencode({"api-version": "2018-02-01", "resource": "https://management.azure.com/"})
    req = urllib.request.Request("http://169.254.169.254/metadata/identity/oauth2/token?" + query,
                                 headers={"Metadata": "true"})
    with urllib.request.urlopen(req, timeout=20) as response:
        access = json.load(response)["access_token"]
    data = urllib.parse.urlencode({"grant_type": "access_token", "service": registry, "access_token": access}).encode()
    with urllib.request.urlopen(urllib.request.Request("https://" + registry + "/oauth2/exchange", data=data), timeout=20) as response:
        token = json.load(response)["refresh_token"]
    with tempfile.TemporaryDirectory(prefix="atlas-session-pull-", dir="/run") as config:
        subprocess.run(["docker", "--config", config, "login", registry, "--username",
                        "00000000-0000-0000-0000-000000000000", "--password-stdin"],
                       input=token.encode(), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        subprocess.run(["docker", "--config", config, "pull", image],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True, timeout=300)
    name = "atlas-session-test-" + secrets.token_hex(5)
    command = ["docker", "run", "--rm", "--name", name, "--network", "none",
               "--cap-drop", "ALL", "--security-opt", "no-new-privileges:true",
               "--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
               "--read-only", "--tmpfs", "/tmp:rw,nosuid,nodev,size=128m",
               "--pids-limit", "128", "--memory", "1536m", "--cpus", "1",
               image, "python3", "/srv/test_sessions.py", "--live", "-v"]
    try:
        result = subprocess.run(command, timeout=240)
        if result.returncode:
            raise SystemExit("Candidate session tests failed; production was not changed")
    finally:
        subprocess.run(["docker", "stop", "-t", "1", name],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    print("Candidate session tests passed; production service and image unchanged")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", required=True)
    args = parser.parse_args()
    run(args.image)
