#!/usr/bin/env python3
"""Flag private paths and credential patterns without printing their contents.

The default checks tracked and non-ignored candidate files in the working tree.
--history additionally checks all file versions reachable from local Git refs.
This is a conservative pattern check, not a comprehensive security assessment.
"""
import argparse
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PRIVATE_DIRS = {'.claude', '.codex', '.agents', 'handover', 'handovers', 'private', '__pycache__'}
PRIVATE_NAMES = {'REVIEW_EMAIL.md', 'ANTIGRAVITY_PROMPT.md', 'BRAND_PROMPT.md', 'A3_PLAN.md'}
PATTERNS = {
    'provider_key': rb'(?<![A-Za-z0-9])sk-(?:or-v1-|ant-|proj-|svcacct-)?[A-Za-z0-9_-]{30,}',
    'github_token': rb'(?:gh[pousr]_[A-Za-z0-9]{25,}|github_pat_[A-Za-z0-9_]{35,})',
    'private_key': rb'-----BEGIN (?:RSA |EC |OPENSSH |DSA )?PRIVATE KEY-----',
    'aws_access_key': rb'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b',
    'azure_sas': rb'[?&]sig=[A-Za-z0-9%+/]{25,}',
    'credential_url': rb'https?://[^\s/:]{2,}:[^\s/@]{6,}@',
    'personal_home': rb'/Users/(?!example/|old/|USER/)[A-Za-z0-9._-]+/',
    'assistant_scratch': rb'/(?:private/)?tmp/claude-[^\s\"\x27]+',
}


def inspect(path, data):
    """Return locations and categories only, never matched text."""
    name = PurePosixPath(path).name
    parts = set(PurePosixPath(path).parts)
    findings = []
    if (parts & PRIVATE_DIRS or name in PRIVATE_NAMES or name.upper().startswith('HANDOVER')
            or path == 'atlas_data/NEXT.md' or name.endswith(('.pyc', '.pem', '.key', '.p12', '.pfx', '.publishsettings'))
            or (name.startswith('.env') and name not in ('.env.example', '.env.template'))):
        findings.append({'path': path, 'kind': 'private_file'})
    for kind, pattern in PATTERNS.items():
        lines = sorted({data[:m.start()].count(b'\n') + 1 for m in re.finditer(pattern, data)})
        if lines:
            findings.append({'path': path, 'kind': kind, 'lines': lines})
    return findings


def working_tree(root):
    paths = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=root
    ).decode().split('\0')
    findings, count = [], 0
    for name in sorted(set(paths) - {''}):
        path = root / name
        if path.is_symlink():
            # Do not follow links into private files outside the repository.
            findings.append({'path': name, 'kind': 'symlink_requires_review'})
        elif path.is_file():
            count += 1
            findings.extend(inspect(name, path.read_bytes()))
    return count, findings


def history(root):
    objects = subprocess.check_output(['git', 'rev-list', '--objects', '--all'], cwd=root).splitlines()
    process = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=root,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    findings, count = [], 0
    try:
        for entry in objects:
            parts = entry.split(b' ', 1)
            if len(parts) != 2:
                continue
            oid, name = parts
            process.stdin.write(oid + b'\n')
            process.stdin.flush()
            header = process.stdout.readline().split()
            data = process.stdout.read(int(header[2]))
            process.stdout.read(1)
            if header[1] != b'blob':
                continue
            count += 1
            for finding in inspect(name.decode(errors='replace'), data):
                finding['blob'] = oid.decode()
                findings.append(finding)
    finally:
        process.stdin.close()
        process.stdout.close()
        process.wait()
    return count, findings


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--history', action='store_true')
    args = parser.parse_args()
    count, findings = working_tree(ROOT)
    report = {'scope': 'working_tree', 'files_checked': count, 'findings': findings}
    if args.history:
        blobs, old = history(ROOT)
        report.update(history_blobs_checked=blobs, history_findings=old)
    print(json.dumps(report, indent=2))
    return int(bool(findings or report.get('history_findings')))


if __name__ == '__main__':
    raise SystemExit(main())
