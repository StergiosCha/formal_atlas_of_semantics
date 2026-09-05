#!/usr/bin/env python3
"""Parse the 200-paper formalizability assessment (pdftotext -layout output)
into atlas/papers.json: one record per paper with category, topic, citation,
the assessment lines, and the Coq files (if any) that formalize it."""
import json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "assessment200.txt")
OUT = os.path.join(HERE, "papers.json")

CATEGORY = {"A": "fully formalizable", "B": "mostly formalizable", "C": "partially formalizable", "D": "resists formalization"}
# four-point determination implied by the survey category (to be revised by actual formalization work)
CAT_TO_DET = {"A": "as_is", "B": "slight_modification", "C": "major_restructuring", "D": "cannot"}

# citation-key regex -> Coq files in the revisiting-formal-semantics repo
COQ = [
    (r"Montague.*1973", ["shallow/PTQ.v", "shallow/MontagueFragment.v", "deep/PTQ_deep2.v", "deep/theorems_deep_PTQ.v", "extras/theorems_PTQ.v", "extras/Montague.v"]),
    (r"Kamp.*1981", ["extras/DonkeyScope.v", "atlas/dynamic/DRT_DPL.v"]),
    (r"Heim.*1982", ["extras/FCS.v", "extras/FCS2.v", "extras/DonkeyScope.v"]),
    (r"Groenendijk.*Stokhof.*1991", ["atlas/dynamic/DPL.v", "extras/DonkeyScope.v"]),
    (r"Barwise.*Cooper.*1981", ["extras/BarwiseCooper.v", "extras/Quantifiers.v"]),
    (r"Link.*1983", ["extras/Link1983.v", "extras/mass.v"]),
    (r"Champollion.*2017", ["extras/champollion_full.v", "extras/Champollion.v"]),
    (r"Kratzer.*1991.*Modality|Kratzer.*1977|Kratzer.*1981", ["shallow/kratzer2.v", "deep/kratzer_deep2.v", "extras/kratzer_1977.v", "extras/kratzer_deep.v"]),
    (r"Rooth.*1992", ["extras/FocusEven.v", "extras/FocusEven2.v", "extras/additive.v", "extras/additive_new.v"]),
    (r"Chatzikyriakidis.*Luo.*2013", ["extras/AdjectivesExtension.v", "ttr_mtt/Book_Inter_Sub.v"]),
    (r"Chatzikyriakidis.*Luo.*2017|Chatzikyriakidis.*Luo.*2018|Chatzikyriakidis.*Luo.*2014", ["ttr_mtt/Coq_book_ontology.v", "ttr_mtt/Book_Individuation.v", "ttr_mtt/Book_gradable.v", "ttr_mtt/Book_Multi.v", "ttr_mtt/Book_veridical.v", "ttr_mtt/Book_Event_Adv.v", "ttr_mtt/Book_Homonymy.v", "extras/mass.v", "extras/indi.v"]),
    (r"Luo.*2012.*Common Nouns", ["extras/MTT_base.v", "extras/MTTbase.v", "extras/indi.v"]),
    (r"Luo.*2010.*Coercive", ["ttr_mtt/Coq_book_ontology.v"]),
    (r"Cooper.*2005.*Records", ["ttr_mtt/TTR_base.v", "ttr_mtt/TTR_types.v", "ttr_mtt/TTR_records.v", "ttr_mtt/TTR_shallow.v", "ttr_mtt/TTR_theorems_shallow.v", "ttr_mtt/TTR_theorems_deep.v"]),
    (r"Dowty.*1991", ["extras/dowty_roles.v"]),
    (r"Dowty.*1979", ["extras/DowtyTense.v", "extras/Aspect.v", "extras/ImperfectiveParadox.v", "extras/Imperfective2.v"]),
    (r"Lakoff.*1987", ["extras/LakoffPrototypes.v"]),
    (r"Heim.*1983", ["extras/PresuppositionProjection.v"]),
    (r"Ciardelli.*Groenendijk.*Roelofsen.*2019|Roelofsen.*2013", ["atlas/inquisitive/InqB.v"]),
    (r"Goodman.*Lassiter.*2015|Bergen.*Levy.*Goodman.*2016", ["atlas/probabilistic/RSA.v"]),
    (r"Coecke|Sadrzadeh", ["atlas/categorical/DisCoCat.v"]),
    (r"Lambek|Moortgat|Morrill", ["atlas/type_logical/Lambek.v"]),
    (r"Muskens.*1996", ["atlas/dynamic/DRT_DPL.v"]),
    (r"Veltman", []),
]

entry_re = re.compile(r"^\s*(\d{1,3})\.\s+(.*)$")
field_re = re.compile(r"^\s{6,}(Formalization|Key insight|Gap|Issue|Barrier|Limitation|Problem|Assessment|Status|Challenge|Note)\s*:\s*(.*)$", re.I)
cat_re = re.compile(r"^CATEGORY ([A-D]):")


def main():
    papers, cur, cat, topic = [], None, None, None
    with open(SRC) as f:
        lines = f.read().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = cat_re.match(line)
        if m:
            cat = m.group(1); topic = None; cur = None; i += 1; continue
        if line.startswith("SUMMARY STATISTICS"):
            break
        m = entry_re.match(line)
        if m and cat:
            n = int(m.group(1)); cit = m.group(2).strip()
            # continuation of a wrapped citation line (indented, before the description block)
            while i + 1 < len(lines) and lines[i + 1].startswith("     ") and not lines[i + 1].startswith("          ") and not entry_re.match(lines[i + 1]):
                cit += " " + lines[i + 1].strip(); i += 1
            # the survey's own numbering restarts at 36 inside category A, so n is not unique; id is
            cur = {"id": len(papers) + 1, "n": n, "category": cat, "category_label": CATEGORY[cat], "topic": topic, "citation": cit,
                   "survey_determination": CAT_TO_DET[cat], "description": None, "fields": {}, "coq_files": []}
            ym = re.search(r"\((\d{4})", cit)
            cur["year"] = int(ym.group(1)) if ym else None
            am = re.match(r"^(.*?)\s*\(\d{4}", cit)
            cur["authors"] = am.group(1).strip() if am else None
            tm = re.search(r'"([^"]+)"', cit)
            cur["title"] = tm.group(1) if tm else None
            for pat, files in COQ:
                if re.search(pat, cit):
                    cur["coq_files"] = files; break
            papers.append(cur); i += 1; continue
        if cur and line.startswith("          ") or (cur and line.startswith("           ")):
            fm = field_re.match(line)
            if fm:
                cur["fields"][fm.group(1).lower().replace(" ", "_")] = fm.group(2).strip()
            elif cur["description"] is None and line.strip():
                cur["description"] = line.strip()
            elif line.strip() and cur["fields"]:
                # wrapped field continuation
                k = list(cur["fields"])[-1]; cur["fields"][k] += " " + line.strip()
            i += 1; continue
        if cat and line.strip() and not line.startswith(" ") and not cat_re.match(line):
            topic = line.strip(); cur = None
        i += 1
    with open(OUT, "w") as f:
        json.dump(papers, f, indent=1, ensure_ascii=False)
    from collections import Counter
    print(len(papers), "papers;", Counter(p["category"] for p in papers), "; with coq:", sum(1 for p in papers if p["coq_files"]),
          "; missing description:", sum(1 for p in papers if not p["description"]), "; missing fields:", sum(1 for p in papers if not p["fields"]))
    bad = [p["n"] for p in papers if not p["title"]]
    if bad:
        print("no title parsed for:", bad)


if __name__ == "__main__":
    main()
