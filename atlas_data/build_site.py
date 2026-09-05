#!/usr/bin/env python3
"""Build atlas/site/index.html from atlas.json (or papers.json alone when no
file records exist yet) by injecting the data into site/template.html.

site/assets/ is vendored in the repo so the build works standalone; when the
brand handoff folder is present alongside, it is re-synced first so a re-theme
propagates without a manual copy."""
import json, os, re, sys, shutil, datetime

HERE = os.path.dirname(os.path.abspath(__file__))
SITE = os.path.join(HERE, "site")
BRAND = os.path.join(os.path.dirname(HERE), "handoff", "assets")

REGIONS = [
    ("model", "Model-theoretic core", ["Foundational Logic & Semantics", "Quantification Theory", "Plurality and Mereology", "Modality and Conditionals", "Focus and Alternatives", "Degree Semantics and Comparison", "Tense and Aspect", "Event Semantics Extensions", "Information Structure", "Vagueness and Gradability", "Hyperintensionality"]),
    ("dynamic", "Dynamic & discourse", ["Dynamic Semantics Foundations", "Presupposition Theory", "Discourse and Coherence"]),
    ("mtt", "Type-theoretic (MTT & TTR)", ["Modern Type Theory for Semantics"]),
    ("typelogical", "Type-logical & categorical", ["Categorical Grammar and Linear Logic Approaches", "Distributional and Vector Semantics"]),
    ("inquisitive", "Questions & inquisitive", ["Questions and Inquisitive Semantics"]),
    ("probabilistic", "Probabilistic, computational & experimental", ["Computational and Probabilistic Approaches", "Experimental Semantics", "Game-Theoretic and Optimality-Theoretic Approaches"]),
    ("pragmatics", "Pragmatics & lexical semantics", ["Pragmatics and Implicature", "Polysemy and Lexical Semantics"]),
    ("cognitive", "Situation & cognitive semantics", ["Situation Semantics", "Cognitive Semantics Foundations", "Mental Spaces and Blending", "Construction Grammar", "Embodiment and Simulation", "Affect and Embodied Meaning"]),
    ("crossling", "Cross-linguistic & historical", ["Cross-linguistic Semantics", "Cross-linguistic Typology and Variation", "Semantic Change and Historical Semantics"]),
    ("philosophical", "Philosophical, social & non-classical", ["Phenomenological and Hermeneutic Approaches", "Deconstructionist Approaches", "Ordinary Language Philosophy", "Dialogical and Interactive Approaches", "Evolutionary and Emergent Approaches", "Indigenous and Non-Western Perspectives", "Postcolonial and Critical Approaches", "Creative and Artistic Meaning", "Quantum and Non-Classical Approaches"]),
]
TOPIC_TO_REGION = {t: key for key, _, topics in REGIONS for t in topics}

# free-text region strings from the audit records -> region key
FILE_REGION_RULES = [
    (r"ttr|type-theoretic|mtt", "mtt"), (r"dynamic|file change|presupposition", "dynamic"),
    (r"inquisitive", "inquisitive"), (r"probabil", "probabilistic"), (r"type-logical|categorical|lambek", "typelogical"),
    (r"boundary|cognitive|prototype", "cognitive"), (r"model-theoretic|modality|quantif|mereolog|focus|aspect|tense|proto-role|polydefinite", "model"),
]


def file_region(rec, papers):
    r = (rec.get("region") or "").lower()
    for pat, key in FILE_REGION_RULES:
        if re.search(pat, r):
            return key
    for p in papers:  # fall back to the region of a paper that lists this file
        if rec.get("file") in p.get("coq_files", []):
            return p["region"]
    return "model"


def sync_assets():
    """Refresh site/assets from the brand handoff, if it is checked out here."""
    if not os.path.isdir(BRAND):
        return 0
    n = 0
    for sub in ("svg", "favicon"):
        src, dst = os.path.join(BRAND, sub), os.path.join(SITE, "assets", sub)
        if not os.path.isdir(src):
            continue
        os.makedirs(dst, exist_ok=True)
        for f in sorted(os.listdir(src)):
            if f.startswith("."):
                continue
            shutil.copy2(os.path.join(src, f), os.path.join(dst, f))
            n += 1
    fav = os.path.join(BRAND, "svg", "favicon.svg")
    if os.path.exists(fav):
        shutil.copy2(fav, os.path.join(SITE, "assets", "favicon.svg"))
    return n


def main():
    atlas_path = os.path.join(HERE, "atlas.json")
    if os.path.exists(atlas_path):
        atlas = json.load(open(atlas_path))
        files, papers, stats = atlas["files"], atlas["papers"], atlas["stats"]
        edges = atlas.get("edges", [])
    else:
        files, stats, edges = [], {}, []
        papers = json.load(open(os.path.join(HERE, "papers.json")))
    for p in papers:
        p["region"] = TOPIC_TO_REGION.get(p["topic"], "philosophical")
    slim_files = []
    for r in files:
        v = r.get("_verify") or {}
        slim_files.append({
            "file": r.get("file"), "key": r.get("_key"), "region": file_region(r, papers), "summary": r.get("summary"),
            "sources": r.get("sources", []), "counts": r.get("counts", {}), "compiles": r.get("compiles"),
            "faithfulness": r.get("faithfulness", {}), "determination": r.get("determination"),
            "determination_rationale": r.get("determination_rationale"), "artifact_classes": r.get("artifact_classes", []),
            "definitions_mapped": r.get("definitions_mapped", []), "theorems": r.get("theorems", []),
            "duplicate_of": r.get("duplicate_of"), "source_gap": r.get("source_gap"), "notes": r.get("notes"),
            "final": r.get("_final", {}), "verify": {"agrees": v.get("agrees"), "disputes": v.get("disputes", []), "confidence": v.get("confidence")} if v else None,
        })
    known_files = {f["file"] for f in slim_files}
    for p in papers:
        p["coq_present"] = [f for f in p.get("coq_files", []) if f in known_files]
    data = {"generated": datetime.date.today().isoformat(), "regions": [{"key": k, "name": n} for k, n, _ in REGIONS],
            "papers": papers, "files": slim_files, "stats": stats, "edges": edges}
    tpl = open(os.path.join(SITE, "template.html")).read()
    blob = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    html = tpl.replace("__ATLAS_DATA__", blob).replace("__GENERATED__", data["generated"])
    out = os.path.join(SITE, "index.html")
    open(out, "w").write(html)
    n_assets = sync_assets()
    print(f"wrote {out}: {len(papers)} papers, {len(slim_files)} file records, "
          f"{len(edges)} edges, {len(html)//1024} KB"
          + (f"; synced {n_assets} brand assets" if n_assets else ""))


if __name__ == "__main__":
    main()
