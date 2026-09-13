"""Read-only validation of a local revision checkpoint's file hashes."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--corpus", type=Path, help="also check external source PDFs/DjVu")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    data = json.loads(args.manifest.read_text())
    checks = [(root / rel, digest) for rel, digest in data["files"].items()]
    if args.corpus:
        checks += [(args.corpus / rel, digest)
                   for rel, digest in data["external_sources"].items()]
    bad = []
    for path, expected in checks:
        if not path.is_file():
            bad.append(f"missing: {path}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            bad.append(f"changed: {path}")
    if bad:
        print("\n".join(bad))
        return 1
    print(f"Checkpoint verified: {len(checks)} file hashes match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
