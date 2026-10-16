#!/usr/bin/env python3
"""Assemble and recheck existing review exports without changing mathematics.

No network access, email sending, document rerendering or source mutation.
Requires two hash-pinned input packets and a new destination directory.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_inputs(directory):
    manifest = json.loads((directory / "MANIFEST.json").read_text())
    for name, expected in manifest["files"].items():
        path = (directory / name).resolve()
        if not path.is_relative_to(directory) or digest(path) != expected:
            raise RuntimeError(f"Input hash or path mismatch: {name}")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brief-packet", type=Path, required=True)
    parser.add_argument("--walkthrough-packet", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    brief, walkthrough, out = (p.resolve() for p in
                               (args.brief_packet, args.walkthrough_packet, args.output_dir))
    archive = out.with_suffix(".zip")
    checksum = Path(str(archive) + ".sha256")
    if any(p.exists() for p in (out, archive, checksum)):
        raise RuntimeError("Use a new destination to preserve completed or partial packets.")
    manifests = {"brief": checked_inputs(brief), "walkthrough": checked_inputs(walkthrough)}
    for name, old_hash in manifests["brief"]["files"].items():
        if name in manifests["walkthrough"]["files"]:
            if manifests["walkthrough"]["files"][name] != old_hash:
                raise RuntimeError(f"Input packets disagree: {name}")
    for name, expected in manifests["walkthrough"]["files"].items():
        if name.startswith("proofs/") and name.endswith(".v"):
            if digest(ROOT / name.removeprefix("proofs/")) != expected:
                raise RuntimeError(f"Current proof differs from the frozen source: {name}")

    out.mkdir(parents=True)
    for directory, key in ((brief, "brief"), (walkthrough, "walkthrough")):
        for name in manifests[key]["files"]:
            target = out / name
            if target.exists():
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(directory / name, target)
        target = out / "provenance" / (key.upper() + "_MANIFEST.json")
        target.parent.mkdir(exist_ok=True)
        shutil.copy2(directory / "MANIFEST.json", target)
    for source, target in (("REVIEW_START_HERE.md", "START_HERE.md"),
                           ("REVIEW_RESPONSE.md", "REVIEW_RESPONSE.md"),
                           ("REVIEW_EMAIL.md", "COVER_EMAIL.md")):
        text = (HERE / source).read_text()
        if "\u2014" in text or "\u2013" in text:
            raise RuntimeError(f"Unsupported dash in authored document: {source}")
        shutil.copy2(HERE / source, out / target)
    shutil.copy2(__file__, out / "renderer" / Path(__file__).name)

    for name in ("START_HERE.md",):
        for target in re.findall(r"\]\(([^)]+)\)", (out / name).read_text()):
            if not (out / target).is_file():
                raise RuntimeError(f"Missing reading link: {target}")

    logs = out / "checks"
    logs.mkdir()
    version = subprocess.check_output(["coqc", "--version"], text=True)
    if "version 8.20.1" not in version:
        raise RuntimeError("This packet is pinned to Coq 8.20.1.")
    (logs / "VERSIONS.txt").write_text(version + "Python " + sys.version + "\n")

    def run_check(branch):
        command = [sys.executable, f"deep/{branch}/check.py", "--check"]
        run = subprocess.run(command, cwd=out / "proofs", text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        (logs / (branch.upper() + ".txt")).write_text(run.stdout)
        expected = 173 if branch == "montague_core" else 76
        negatives = 23 if branch == "montague_core" else 14
        if (run.returncode or f"PASS: {expected} " not in run.stdout
                or "Kernel recheck passed" not in run.stdout
                or run.stdout.count("Rejected invalid fixture:") != negatives):
            raise RuntimeError(f"Fresh check failed: {branch}; inspect its log.")
        print(f"PASS {branch}: {expected} statements, {negatives} negative fixtures", flush=True)
        return {"statements": expected, "negative_fixtures": negatives, "kernel_recheck": "passed"}

    branches = ("montague_core", "montague_legacy")
    with ThreadPoolExecutor(max_workers=2) as pool:
        checks = dict(zip(branches, pool.map(run_check, branches)))

    # The checkers may create Python caches. Deliver only intentional files.
    def files():
        return sorted(p for p in out.rglob("*") if p.is_file() and "__pycache__" not in p.parts)

    for key, original in manifests.items():
        for name, expected in original["files"].items():
            if digest(out / name) != expected:
                raise RuntimeError(f"Frozen file changed during assembly: {name}")
    manifest = {
        "assembled_date": "2026-10-10", "mathematical_checkpoint": 7,
        "status": "assembled for review; not sent, endorsed or published",
        "reviewer_approval": False, "sent": False,
        "identity_note": "Source includes uncommitted work; identify it by these hashes, not Git HEAD.",
        "scope": "Existing brief, report and walkthrough plus unchanged frozen proofs and fresh checks",
        "fresh_checks": checks,
        "input_manifest_sha256": {key: digest(directory / "MANIFEST.json")
                                  for key, directory in (("brief", brief), ("walkthrough", walkthrough))},
        "files": {p.relative_to(out).as_posix(): digest(p) for p in files()},
    }
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
    with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_DEFLATED) as bundle:
        for path in files():
            bundle.write(path, Path(out.name) / path.relative_to(out))
    with zipfile.ZipFile(archive) as bundle:
        if bundle.testzip() is not None:
            raise RuntimeError("Archive integrity check failed.")
        for path in files():
            entry = (Path(out.name) / path.relative_to(out)).as_posix()
            if bundle.read(entry) != path.read_bytes():
                raise RuntimeError(f"Archive content differs: {entry}")
    checksum.write_text(f"{digest(archive)}  {archive.name}\n")
    print(archive)
    print(checksum)
    print("Not sent. Reviewer approval remains pending.")


if __name__ == "__main__":
    main()
