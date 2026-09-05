#!/usr/bin/env python3
"""Merge per-file atlas records (atlas/records/*.json + *.verify.json) and the
paper assessment (atlas/papers.json) into atlas/atlas.json and atlas/ATLAS.md.

The verifier's revised verdict wins over the auditor's when they disagree; both
are kept so the disagreement is visible.
"""
import json, glob, os, re, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REC = os.path.join(HERE, "records")
EDGES = os.path.join(HERE, "edges")
DET_ORDER = ["as_is", "slight_modification", "major_restructuring", "cannot", "not_applicable"]
DET_LABEL = {"as_is": "1 as-is", "slight_modification": "2 slight modification",
             "major_restructuring": "3 major restructuring", "cannot": "4 cannot", "not_applicable": "n/a"}
FAITH_ORDER = ["faithful", "partial", "unfaithful", "not_applicable"]


def load(path):
    if not os.path.exists(path):
        return None
    try:
        with open(path) as f:
            return json.load(f)
    except Exception as e:  # malformed agent output should not kill the merge
        print(f"WARN cannot parse {path}: {e}", file=sys.stderr)
        return None


def merge_records():
    out = []
    for path in sorted(glob.glob(os.path.join(REC, "*.json"))):
        if path.endswith((".verify.json", ".mech.json")):
            continue  # sidecars, not records: .verify.json is merged below,
                      # .mech.json is verify.py's raw coqc/Print Assumptions output
        rec = load(path)
        if not rec:
            continue
        key = os.path.basename(path)[:-5]
        ver = load(path[:-5] + ".verify.json")
        final_faith = rec.get("faithfulness", {}).get("verdict")
        final_det = rec.get("determination")
        disputed = False
        if ver:
            if not ver.get("agrees"):
                disputed = True
                final_faith = ver.get("revised_faithfulness") or final_faith
                final_det = ver.get("revised_determination") or final_det
        rec["_key"] = key
        rec["_verify"] = ver
        rec["_final"] = {"faithfulness": final_faith, "determination": final_det, "disputed": disputed}
        out.append(rec)
    return out


def merge_edges():
    """Load atlas/edges/*.json (framework-comparison edges) and compute the
    two aggregates: similarity = mean grade over jointly attempted phenomena
    (grades 0-5, from bridge theorems); overlap = Jaccard of the phenomenon
    sets each side attempts ("are they looking for the same things")."""
    out = []
    for path in sorted(glob.glob(os.path.join(EDGES, "*.json"))):
        e = load(path)
        if not e:
            continue
        e["_key"] = os.path.basename(path)[:-5]
        phen = e.get("phenomena") or []
        joint = [p for p in phen
                 if set(p.get("attempted_by") or []) >= {"a", "b"}
                 and isinstance(p.get("grade"), (int, float))]
        a_set = {p["name"] for p in phen if "a" in (p.get("attempted_by") or [])}
        b_set = {p["name"] for p in phen if "b" in (p.get("attempted_by") or [])}
        e["_computed"] = {
            "similarity": round(sum(p["grade"] for p in joint) / len(joint), 2) if joint else None,
            "overlap": round(len(a_set & b_set) / len(a_set | b_set), 2) if (a_set | b_set) else None,
            "joint_phenomena": len(joint),
            "a_only": sorted(a_set - b_set),
            "b_only": sorted(b_set - a_set),
        }
        out.append(e)
    return out


def md_table(rows, header):
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    for r in rows:
        lines.append("| " + " | ".join(str(c).replace("|", "\\|").replace("\n", " ") for c in r) + " |")
    return "\n".join(lines)


LEVEL_LABEL = {
    "F0": "surveyed only (A-D prediction, no source on disk)",
    "F1": "sourced (PDF/djvu on disk)",
    "F2": "designed (design doc maps its content)",
    "F3": "piloted (some Coq exists; record may be partial)",
    "F4": "formalized (atlas-standard file, audited record)",
    "F5": "verified & connected (verify agrees and/or in a graded edge)",
}


def compute_levels(papers, files, edges):
    """Evidence-based formalizability levels replacing the A-D
    predictions (rubric §5: predictions until a formalization exists).
    Each paper gets `level`, and where a determination exists that
    disagrees with the survey's prediction, `prediction_disputed`."""
    import unicodedata

    def norm(s):
        s = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode()
        return re.sub(r"[^a-z0-9]", "", s.lower())

    papers_dir = os.path.join(os.path.dirname(HERE), "papers")
    disk = []
    if os.path.isdir(papers_dir):
        for root, _, fs in os.walk(papers_dir):
            disk += [norm(f) for f in fs if f.lower().endswith((".pdf", ".djvu"))]
    designs = " ".join(
        open(os.path.join(HERE, "designs", d)).read().lower()
        for d in (os.listdir(os.path.join(HERE, "designs"))
                  if os.path.isdir(os.path.join(HERE, "designs")) else [])
        if d.endswith(".md"))
    rec_by_file = {r.get("file"): r for r in files}
    edge_files = set()
    for e in edges:
        edge_files.add(e.get("a_file")); edge_files.add(e.get("b_file"))

    for p in papers:
        au = (p.get("authors") or "").split("&")[0].split(",")[0].strip()
        sn = norm(au.split()[-1]) if au else ""
        yr = str(p.get("year") or "")
        sourced = any(sn and sn in f and yr in f for f in disk)
        designed = bool(sn) and sn in designs
        cfs = p.get("coq_files") or []
        recs = [rec_by_file[f] for f in cfs if f in rec_by_file]
        atlas_recs = [r for r in recs if r.get("file", "").startswith("atlas/")]
        clean = [r for r in atlas_recs
                 if (r.get("counts") or {}).get("admitted", 1) == 0]
        verified = any(r.get("_verify") for r in recs) or \
            any(f in edge_files for f in cfs)
        if clean and verified:
            level = "F5"
        elif clean:
            level = "F4"
        elif recs:
            level = "F3"
        elif designed:
            level = "F2"
        elif sourced:
            level = "F1"
        else:
            level = "F0"
        p["level"] = level
        # prediction vs determination (rubric §5: disagreements are findings)
        det = None
        for r in clean or recs:
            det = r.get("_final", {}).get("determination") or r.get("determination")
            if det:
                break
        p["determination_actual"] = det
        pred = p.get("survey_determination")
        p["prediction_disputed"] = bool(det and pred and det != pred)
    return papers


def main():
    files = merge_records()
    edges = merge_edges()
    papers_path = os.path.join(HERE, "papers.json")
    papers = load(papers_path) or []
    # survey corrections/additions live in an addendum, never by editing
    # the frozen 200-paper list in place
    addendum = load(os.path.join(HERE, "papers_addendum.json")) or []
    by_id = {p.get("citation"): p for p in papers}
    for a in addendum:
        if a.get("replaces_citation") and a["replaces_citation"] in by_id:
            by_id[a["replaces_citation"]].update(
                {k: v for k, v in a.items() if k != "replaces_citation"})
        else:
            papers.append(a)
    papers = compute_levels(papers, files, edges)

    # --- summary statistics over Coq files
    det_count = Counter(r["_final"]["determination"] for r in files)
    faith_count = Counter(r["_final"]["faithfulness"] for r in files)
    thm = sum((r.get("counts") or {}).get("theorems", 0) for r in files)
    proved = sum((r.get("counts") or {}).get("proved", 0) for r in files)
    admitted = sum((r.get("counts") or {}).get("admitted", 0) for r in files)
    disputed = [r["_key"] for r in files if r["_final"]["disputed"]]
    regions = defaultdict(list)
    for r in files:
        regions[r.get("region", "?")].append(r)

    atlas = {
        "generated_from": {"records": len(files), "papers": len(papers)},
        "stats": {"theorems": thm, "proved": proved, "admitted": admitted,
                  "determination": dict(det_count), "faithfulness": dict(faith_count),
                  "disputed_records": disputed},
        "files": files,
        "papers": papers,
        "edges": edges,
    }
    with open(os.path.join(HERE, "atlas.json"), "w") as f:
        json.dump(atlas, f, indent=1, ensure_ascii=False)

    # --- markdown
    md = ["# Formalizability Atlas of Semantics — current state", "",
          f"Coq files audited: **{len(files)}** · theorem statements: **{thm}** (proved {proved}, admitted {admitted}) · "
          f"papers assessed: **{len(papers)}** · records disputed by the verifier: **{len(disputed)}**", "",
          "## Determination (four-point scale) over formalized sources", "",
          md_table([[DET_LABEL.get(d, d), det_count.get(d, 0)] for d in DET_ORDER], ["Determination", "Files"]), "",
          "## Faithfulness verdicts", "",
          md_table([[f, faith_count.get(f, 0)] for f in FAITH_ORDER], ["Verdict", "Files"]), ""]
    for region in sorted(regions):
        rows = []
        for r in sorted(regions[region], key=lambda x: x.get("file", "")):
            c = r.get("counts") or {}
            src = "; ".join(s.get("citation", "") for s in (r.get("sources") or [])[:2])
            flag = " ⚠" if r["_final"]["disputed"] else ""
            gap = " (source gap)" if r.get("source_gap") else ""
            rows.append([r.get("file", r["_key"]), src + gap, f"{c.get('proved', 0)}/{c.get('theorems', 0)}" + (f" +{c.get('admitted')} adm" if c.get("admitted") else ""),
                         r["_final"]["faithfulness"], DET_LABEL.get(r["_final"]["determination"], r["_final"]["determination"]) + flag,
                         ", ".join(a.get("class", "") for a in (r.get("artifact_classes") or [])) or "—",
                         r.get("duplicate_of") or "—"])
        md += [f"## {region}", "", md_table(rows, ["File", "Source", "Proved/Total", "Faithful", "Determination", "Artifacts", "Dup of"]), ""]
    if edges:
        md += ["## Framework-comparison edges", "",
               "Grades per phenomenon, from bridge theorems: 5 definitional / 4 equivalence / "
               "3 one-way or mediated / 2 divergent (countermodel) / 1 after re-encoding. "
               "Similarity = mean grade over jointly attempted phenomena; "
               "overlap = Jaccard of attempted phenomenon sets.", "",
               md_table([[e["_key"], e.get("level", "?"), e.get("bridge_file") or "—",
                          e["_computed"]["similarity"] if e["_computed"]["similarity"] is not None else "—",
                          e["_computed"]["overlap"] if e["_computed"]["overlap"] is not None else "—",
                          e["_computed"]["joint_phenomena"],
                          len(e["_computed"]["a_only"]), len(e["_computed"]["b_only"])]
                         for e in edges],
                        ["Edge", "Level", "Bridge", "Similarity", "Overlap", "Joint", "A-only", "B-only"]), ""]
    if disputed:
        md += ["## Verifier disputes", ""]
        for r in files:
            if not r["_final"]["disputed"]:
                continue
            md.append(f"### {r.get('file', r['_key'])}")
            for d in (r["_verify"].get("disputes") or []):
                md.append(f"- **{d.get('field')}**: record says *{d.get('record_says')}*; verifier says *{d.get('you_say')}* — {d.get('evidence')}")
            md.append("")
    if papers:
        cats = Counter(p.get("category") for p in papers)
        md += ["## Paper assessment (200-paper survey)", "",
               md_table([[k, v] for k, v in sorted(cats.items())], ["Category", "Papers"]), ""]
        lvls = Counter(p.get("level") for p in papers)
        md += ["## Formalizability levels (evidence-based; rubric §5)", "",
               md_table([[l, LEVEL_LABEL.get(l, ""), lvls.get(l, 0)]
                         for l in ["F0", "F1", "F2", "F3", "F4", "F5"]],
                        ["Level", "Meaning", "Papers"]), ""]
        disputed_preds = [p for p in papers if p.get("prediction_disputed")]
        if disputed_preds:
            md += ["### Survey prediction vs actual determination (findings)", "",
                   md_table([[p.get("citation", "")[:70],
                              p.get("survey_determination"),
                              p.get("determination_actual"),
                              p.get("level")]
                             for p in disputed_preds],
                            ["Paper", "Predicted", "Determined", "Level"]), ""]
    with open(os.path.join(HERE, "ATLAS.md"), "w") as f:
        f.write("\n".join(md))
    print(f"atlas.json: {len(files)} file records, {len(edges)} edges, {len(papers)} papers; ATLAS.md written; {len(disputed)} disputed")


if __name__ == "__main__":
    main()
