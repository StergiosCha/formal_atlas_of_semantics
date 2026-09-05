#!/usr/bin/env python3
"""place_papers.py — sort downloaded papers into the FORMAL-ATLAS corpus.

Scans a drop folder (default ~/Downloads) for pdf/djvu/epub files and matches
each against the FULL survey (papers.json + papers_addendum.json, ~226 entries),
not just the outstanding-misses list. Matches are moved and renamed to the
canonical papers/<region>/Surname_Year_TitleWords.ext.

Three outcomes per file:
  MOVE       confident match against a survey entry we do NOT yet have
  DUPLICATE  confident match, but that entry already has a file on disk
  SKIP       no confident match (the detected title is printed so you can see why)

Usage:
  python3 atlas/place_papers.py                 # dry run
  python3 atlas/place_papers.py --go            # actually move
  python3 atlas/place_papers.py --go --src ~/Desktop
  python3 atlas/place_papers.py --dupes         # also move duplicates (as *_alt)
  python3 atlas/place_papers.py --loose         # relax the acceptance threshold

Acceptance rule (deliberately strict — a wrong file under a right name is
worse than an unsorted file): a first-author surname must appear in the
filename or the first two pages, AND either the normalized title appears
verbatim or at least 60% of the title's content words are found; the total
score must clear the threshold and beat the runner-up by 2 points.
"""
import os, re, sys, glob, json, shutil, subprocess, unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CORPUS = os.path.join(ROOT, "papers")

STOP = set("""the a an of on in and or to for with as by from at is are was were
that this these those into via toward towards its their our it his her a some
new an be been being do does not no non""".split())

TOPIC_REGION = {
    "Categorical Grammar and Linear Logic Approaches": "type_logical",
    "Distributional and Vector Semantics": "categorical",
    "Quantum and Non-Classical Approaches": "categorical",
    "Dynamic Semantics Foundations": "dynamic",
    "Discourse and Coherence": "dynamic",
    "Presupposition Theory": "dynamic",
    "Questions and Inquisitive Semantics": "inquisitive",
    "Focus and Alternatives": "inquisitive",
    "Computational and Probabilistic Approaches": "probabilistic",
    "Experimental Semantics": "probabilistic",
    "Game-Theoretic and Optimality-Theoretic Approaches": "probabilistic",
    "Vagueness and Gradability": "probabilistic",
}


def norm(s):
    s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode()
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9 ]", " ", s.lower())).strip()


def surnames(authors):
    """'Coecke, B., Sadrzadeh, M. & Clark, S.' -> ['coecke','sadrzadeh','clark']"""
    out = []
    for chunk in re.split(r"&|;| and ", str(authors)):
        chunk = chunk.strip()
        if not chunk:
            continue
        # 'Surname, X.' or 'X. Surname'
        head = chunk.split(",")[0].strip()
        toks = [t for t in norm(head).split() if len(t) > 1]
        if toks:
            out.append(toks[-1])
    return out[:3]


def camel(title, maxw=7):
    ws = [w for w in norm(title).split() if w not in STOP]
    return "".join(w.capitalize() for w in ws[:maxw])[:70]


def load_survey():
    papers = json.load(open(os.path.join(HERE, "papers.json")))
    add = json.load(open(os.path.join(HERE, "papers_addendum.json")))
    by_cit = {}
    for p in papers:
        by_cit[p["citation"]] = dict(p)
    for a in add:                       # corrections replace, additions append
        old = a.get("replaces_citation")
        new = a.get("citation", old)    # annotation-only entries carry no new citation
        if not new:
            continue
        base = dict(by_cit.pop(old, {})) if old else dict(by_cit.get(new, {}))
        base.update({k: v for k, v in a.items() if k != "replaces_citation"})
        by_cit[new] = base

    items = []
    for cit, p in by_cit.items():
        title = p.get("title") or (re.search(r'"(.+?)"', cit).group(1)
                                   if re.search(r'"(.+?)"', cit) else cit)
        authors = p.get("authors") or cit.split("(")[0]
        yr = p.get("year") or (re.search(r"\((\d{4})\)", cit).group(1)
                               if re.search(r"\((\d{4})\)", cit) else "")
        sn = surnames(authors)
        words = [w for w in norm(title).split() if w not in STOP and len(w) > 3]
        region = TOPIC_REGION.get(p.get("topic", ""), "foundations")
        items.append({
            "cit": cit, "title": title, "ntitle": norm(title), "words": words,
            "surnames": sn, "year": str(yr), "region": region,
            "stem": f"{'_'.join(s.capitalize() for s in sn) or 'Unknown'}_{yr}_{camel(title)}",
        })
    return items


def index_corpus():
    """map (first-surname, year) -> existing path, for have/missing detection"""
    have = {}
    for f in glob.glob(os.path.join(CORPUS, "*", "*")):
        b = os.path.basename(f)
        m = re.match(r"([A-Za-z_]+?)_(\d{4})_", b)
        if not m:
            continue
        first = m.group(1).split("_")[0].lower()
        have.setdefault((first, m.group(2)), []).append(f)
    return have


def existing_for(item, have):
    if not item["surnames"] or not item["year"]:
        return None
    y = int(item["year"]) if item["year"].isdigit() else None
    for dy in (0, -1, 1):               # publication-year drift
        key = (item["surnames"][0], str(y + dy) if y else item["year"])
        if key in have:
            return have[key][0]
    return None


def page_text(path):
    if path.lower().endswith(".pdf"):
        try:
            out = subprocess.run(["pdftotext", "-l", "2", path, "-"],
                                 capture_output=True, text=True, timeout=40)
            return out.stdout[:6000]
        except Exception:
            return ""
    if path.lower().endswith(".djvu"):
        try:
            out = subprocess.run(["djvutxt", "--page=1-2", path],
                                 capture_output=True, text=True, timeout=40)
            return out.stdout[:6000]
        except Exception:
            return ""
    return ""


def score(item, fname, page):
    hay_f, hay_p = norm(fname), norm(page)
    s, why = 0, []
    sn_hit = False
    for i, sn in enumerate(item["surnames"]):
        w = 3 if i == 0 else 1
        if sn in hay_f:
            s += w + 1; sn_hit = True; why.append(f"{sn}@name")
        elif sn in hay_p:
            s += w; sn_hit = True; why.append(f"{sn}@page")
    if item["year"]:
        if item["year"] in fname:
            s += 2; why.append("year@name")
        elif item["year"] in page:
            s += 1; why.append("year@page")
    exact = len(item["ntitle"]) > 12 and (item["ntitle"] in hay_f or item["ntitle"] in hay_p)
    if exact:
        s += 5; why.append("title-verbatim")
    ratio = 0.0
    if item["words"]:
        hits = sum(1 for w in item["words"] if w in hay_f or w in hay_p)
        ratio = hits / len(item["words"])
        s += round(4 * ratio)
        why.append(f"title {hits}/{len(item['words'])}")
    return s, sn_hit, ratio, exact, why


def detected_title(path, page):
    for line in page.splitlines():
        line = line.strip()
        if len(line) > 8 and not line.lower().startswith(("http", "doi", "www")):
            return line[:78]
    return os.path.basename(path)[:78]


def main():
    go = "--go" in sys.argv
    dupes = "--dupes" in sys.argv
    thresh = 6 if "--loose" in sys.argv else 7
    src = os.path.expanduser(sys.argv[sys.argv.index("--src") + 1]) \
        if "--src" in sys.argv else os.path.expanduser("~/Downloads")

    items = load_survey()
    have = index_corpus()
    files = sorted(f for pat in ("*.pdf", "*.djvu", "*.epub")
                   for f in glob.glob(os.path.join(src, pat)))
    missing = sum(1 for it in items if not existing_for(it, have))
    print(f"survey: {len(items)} entries, {missing} still without a file")
    print(f"drop folder: {src} — {len(files)} candidates\n")

    moved = dup = skip = 0
    for f in files:
        page = page_text(f)
        ranked = []
        for it in items:
            s, sn, ratio, exact, why = score(it, os.path.basename(f), page)
            ranked.append((s, sn, ratio, exact, why, it))
        ranked.sort(key=lambda r: -r[0])
        s, sn, ratio, exact, why, best = ranked[0]
        runner = ranked[1][0] if len(ranked) > 1 else 0
        ok = sn and (exact or ratio >= 0.6) and s >= thresh and (s - runner) >= 2

        if not ok:
            skip += 1
            reason = ("no author match" if not sn else
                      f"weak title ({ratio:.0%})" if not exact and ratio < 0.6 else
                      f"ambiguous vs runner-up" if (s - runner) < 2 else f"score {s}<{thresh}")
            print(f"SKIP       {os.path.basename(f)}")
            print(f"           looks like: {detected_title(f, page)}")
            print(f"           best guess: {best['cit'][:66]}  [{reason}]")
            continue

        ext = os.path.splitext(f)[1].lower()
        prior = existing_for(best, have)
        if prior and not dupes:
            dup += 1
            print(f"DUPLICATE  {os.path.basename(f)}")
            print(f"           = {best['cit'][:66]}")
            print(f"           already at {os.path.relpath(prior, ROOT)}")
            continue

        stem = best["stem"] + ("_alt" if prior else "")
        tgt = os.path.join(CORPUS, best["region"], stem + ext)
        print(f"{'MOVE      ' if go else 'would move'} {os.path.basename(f)}")
        print(f"           -> {os.path.relpath(tgt, ROOT)}")
        print(f"           = {best['cit'][:66]}  [{', '.join(why)}]")
        if go:
            os.makedirs(os.path.dirname(tgt), exist_ok=True)
            shutil.move(f, tgt)
        moved += 1

    print(f"\n{'moved' if go else 'matched'}: {moved}   duplicates: {dup}   skipped: {skip}"
          + ("" if go else "   (dry run — add --go to move)"))


if __name__ == "__main__":
    main()
