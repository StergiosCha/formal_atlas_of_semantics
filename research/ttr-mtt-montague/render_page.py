"""Render the study for the static Atlas. Requires pandoc and a full git checkout."""
import argparse
import hashlib
import re
import subprocess
from pathlib import Path
from urllib.parse import quote

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SITE = ROOT / "atlas_data/site/research/ttr-mtt-montague/index.html"
HEADINGS = {
    "1. How many books did John pick up and master?": "books",
    "2. Quantification and anaphora": "quantification",
    "The five farmers": "five-farmers",
    "3. Belief, intention and modality": "attitudes",
    "4. Adjectives, adverbs and event types": "modification",
    "5. Other overlaps and the question about foundations": "foundations",
    "What Rocq checked": "verification",
    "Sources": "sources",
}


def render(commit):
    revision = subprocess.check_output(
        ["git", "rev-parse", "--verify", f"{commit}^{{commit}}"], cwd=ROOT, text=True
    ).strip()
    prefix = f"https://github.com/StergiosCha/formal_atlas_of_semantics/blob/{revision}/research/ttr-mtt-montague/"
    article = subprocess.check_output(
        ["git", "show", f"{revision}:research/ttr-mtt-montague/README.md"], cwd=ROOT, text=True
    )
    for heading, anchor in HEADINGS.items():
        article, count = re.subn(r"^(#{2,3}) " + re.escape(heading) + "$",
                                 lambda m: m[0] + " {#" + anchor + "}", article, flags=re.M)
        if count != 1:
            raise ValueError(f"Expected one heading: {heading}")
    article = re.sub(r"\]\((?!https?://|#)([^)]+)\)", lambda m: "](" + prefix + m[1] + ")", article)
    body = subprocess.run(["pandoc", "--from=markdown-smart", "--to=html5", "--wrap=none"],
                          input=article, capture_output=True, check=True, text=True).stdout
    def reader_link(match):
        commit, path, line = match.groups()
        raw = subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)
        digest = hashlib.sha256(raw).hexdigest()
        return f'href="../../#/file/{quote(path, safe="")}?line={line or 1}&amp;sha={digest}&amp;rev={commit}"'

    body = re.sub(r'href="https://github\.com/StergiosCha/formal_atlas_of_semantics/blob/'
                  r'([0-9a-f]{40})/([^"#]+?\.v)(?:#L(\d+))?"', reader_link, body)
    template = (HERE / "page.html").read_text()
    SITE.parent.mkdir(parents=True, exist_ok=True)
    SITE.write_text(template.replace("<!-- ARTICLE -->", body))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence_commit", help="commit containing the edition of the paper and proofs to publish")
    render(parser.parse_args().evidence_commit)
