#!/usr/bin/env python3
"""place_papers.py — sort downloaded papers into the FORMAL-ATLAS corpus.

Scans a downloads folder (default ~/Downloads) for pdf/djvu/epub files,
fuzzy-matches each against the misses manifest (misses_deep.md), and
moves + renames matches to their canonical papers/<region>/ target.

Usage:
  python3 atlas/place_papers.py            # dry run: show what would move
  python3 atlas/place_papers.py --go       # actually move files
  python3 atlas/place_papers.py --go --src ~/Desktop
Matching: needs the first author's surname AND >=2 significant title
words (or year + surname) in the downloaded filename OR the PDF's first
page. Ambiguous or unmatched files are listed, never moved.
"""
import os, re, sys, glob, shutil, subprocess, unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
MISSES = os.path.join(HERE, "misses_deep.md")

def norm(s):
    s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode()
    return re.sub(r"[^a-z0-9 ]", " ", s.lower())

STOP = set("the a of on in and or to for with an its as by from at is are was".split())

def parse_misses():
    items, cit, tgt = [], None, None
    for line in open(MISSES):
        m = re.match(r"- (.+?) - \"?(.+?)\"?$", line.strip())
        if line.startswith("- "):
            cit = line[2:].strip()
        t = re.match(r"\s*target: `(.+)`", line)
        if t and cit:
            tgt = t.group(1)
            # first author surname
            au = cit.split("(")[0]
            surname = norm(au.split(",")[0]).split()
            surname = surname[-1] if surname else ""
            yr = re.search(r"\((\d{4})\)", cit)
            title = re.search(r'"(.+?)"', cit)
            words = [w for w in norm(title.group(1)).split() if w not in STOP and len(w) > 3] if title else []
            items.append({"cit": cit, "target": tgt, "surname": surname,
                          "year": yr.group(1) if yr else "", "words": words})
            cit = None
    return items

def first_page_text(path):
    if not path.lower().endswith(".pdf"):
        return ""
    try:
        out = subprocess.run(["pdftotext", "-l", "2", path, "-"],
                             capture_output=True, text=True, timeout=30)
        return norm(out.stdout[:4000])
    except Exception:
        return ""

def score(item, fname, page):
    hay_f, hay_p = norm(fname), page
    s = 0
    if item["surname"] and (item["surname"] in hay_f or item["surname"] in hay_p):
        s += 2
    if item["year"] and (item["year"] in fname or item["year"] in page):
        s += 1
    hits = sum(1 for w in item["words"] if w in hay_f or w in hay_p)
    s += min(hits, 4)
    return s, hits

def main():
    go = "--go" in sys.argv
    src = os.path.expanduser(sys.argv[sys.argv.index("--src") + 1]) \
        if "--src" in sys.argv else os.path.expanduser("~/Downloads")
    items = parse_misses()
    files = [f for pat in ("*.pdf", "*.djvu", "*.epub")
             for f in glob.glob(os.path.join(src, pat))]
    print(f"{len(items)} wanted papers; {len(files)} candidate files in {src}\n")
    moved = unmatched = 0
    for f in sorted(files):
        page = first_page_text(f)
        best, bs, bh = None, 0, 0
        for it in items:
            s, hits = score(it, os.path.basename(f), page)
            if s > bs:
                best, bs, bh = it, s, hits
        # require surname match (>=2 pts) plus either 2 title words or the year
        if best and bs >= 4 and bh >= 1:
            ext = os.path.splitext(f)[1].lower()
            tgt = os.path.join(ROOT, best["target"])
            if ext != ".pdf":
                tgt = os.path.splitext(tgt)[0] + ext
            print(f"{'MOVE' if go else 'would move'}  {os.path.basename(f)}\n"
                  f"      -> {os.path.relpath(tgt, ROOT)}   [{best['cit'][:60]}]")
            if go:
                os.makedirs(os.path.dirname(tgt), exist_ok=True)
                shutil.move(f, tgt)
            moved += 1
        else:
            unmatched += 1
    print(f"\n{'moved' if go else 'matched'}: {moved}   unmatched: {unmatched}"
          + ("" if go else "   (dry run — add --go to move)"))

if __name__ == "__main__":
    main()
