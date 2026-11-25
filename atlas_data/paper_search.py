"""Public papers linked to implementation records, source supplements, and research studies."""
from pathlib import Path
from urllib.parse import quote


FOCUS_TITLE = "Chatzikyriakidis, Michelioudakis and Spathas, Greek Focus Operators and Their Associates"
POLY_TITLE = "Stergios Chatzikyriakidis and Giorgos Spathas, Polydefinites as Markers of Prominence: A Unified Analysis of Greek Polydefinites"
COOPER = "Robin Cooper (2023), From Perception to Communication: A Theory of Types for Action and Meaning"
PTQ = "Richard Montague (1973), The Proper Treatment of Quantification in Ordinary English"
COMPARISON = "research/ttr-mtt-montague/index.html#sources"


def comparison_citations(root):
    """Read the source column of the published study's passage-by-passage bibliography."""
    lines = iter((root / "research/ttr-mtt-montague/CMM_SOURCES.md").read_text().splitlines())
    for line in lines:
        if line.startswith("| Source | Passages used |"):
            break
    else:
        raise ValueError("Missing source table in CMM_SOURCES.md")
    next(lines)  # Markdown column separator
    for line in lines:
        if not line.startswith("|"):
            break
        citation = line.split("|")[1].strip().replace("*", "")
        # The final row cites two works in one cell.
        first, conjunction, second = citation.partition(", and Retoré, ")
        yield first
        if conjunction:
            yield "Retoré, " + second


def build_paper_index(data, root):
    works = {}

    def add(citation, label, href, *, identity=None, aliases=()):
        title = citation
        if "from perception to communication" in citation.lower() and "cooper" in citation[:30].lower():
            title = identity = COOPER
        elif "the proper treatment of quantification in ordinary english" in citation.lower() and "montague" in citation[:30].lower():
            title = identity = PTQ
        work = works.setdefault(identity or title, {"citation": title, "aliases": [], "links": []})
        for alias in (citation, *aliases):
            if alias and alias != work["citation"] and alias not in work["aliases"]:
                work["aliases"].append(alias)
        link = {"label": label, "href": href}
        if link not in work["links"]:
            work["links"].append(link)

    for record in data["files"]:
        key = record["key"]
        path = data["proof_sources"][key]["path"]
        for source in record["sources"]:
            citation = source["citation"].strip()
            if not citation or citation.startswith("None. Helper definitions only"):
                continue
            source_path = (source.get("path") or "").removeprefix("external-corpus/")
            identity = source_path if source_path.startswith("papers/") else citation
            # The original audits left the attribution open. The Greek study supplies
            # the paper title and identifies these two modules as related implementations.
            focus = (key == "extras__additive" and citation.startswith("'CSM&S'") or
                     key == "extras__additive_new" and citation.startswith("Unidentified analysis of Greek"))
            if focus:
                add(FOCUS_TITLE, "Related implementation: " + Path(path).name, "#/proof/" + key,
                    aliases=(citation, "Stergios Chatzikyriakidis Giorgos Spathas"))
            elif key == "extras__PolydefiniteSemantics" and citation.startswith("Chatzikyriakidis, S. & Spathas, G."):
                add(POLY_TITLE, Path(path).name, "#/proof/" + key, aliases=(citation,))
            else:
                add(citation, Path(path).name, "#/proof/" + key, identity=identity)

    for source in data.get("source_registry", {}).get("supplementary_sources", []):
        key = source["supplement_id"]
        add(source["citation"], "Source record", "#/sources?entry=" + quote(key, safe=""))
        if key == "chatzikyriakidis-spathas-2015-ke":
            add(source["citation"], "Study and proofs", "#/research/greek-double-ke",
                aliases=("AMGL36 double ke ke…ke καί καί",))
        if key == "cooper-2023":
            add(source["citation"], "Set types in Rocq", "#/proof/ttr_mtt__TTR_types")

    add(FOCUS_TITLE, "Comparison with double ke", "#/research/greek-double-ke")
    for citation in comparison_citations(root):
        add(citation, "Sources and passages in the comparison", COMPARISON)

    gallin = "Daniel Gallin (1975), Intensional and Higher-Order Modal Logic: With Applications to Montague Semantics"
    for package in data["research"]["packages"]:
        if package["id"] == "montague_gallin":
            add(gallin, package["title"], "#/research/gallin", aliases=("IL Ty2",))
        elif package["id"] == "montague_ptq":
            add(PTQ, package["title"], "#/research", aliases=("PTQ",))
        else:
            # Workbenches may cover several sources. Keep their own titles and links.
            add(package["title"], "Research code", "#/research-proof/" + package["source_keys"][0],
                aliases=(package["namespace"],))

    return sorted(works.values(), key=lambda work: work["citation"].casefold())
