#!/usr/bin/env python3
r"""ROADMAP A3 — mechanical verification of the atlas Coq files.

Every audit record asserts `compiles: true` and its own theorem counts on its
own authority. This script replaces that self-report with three checks Coq
performs itself, and writes the result to records/<key>.mech.json:

  1. compile     — coqc the file fresh, capturing warnings and errors
  2. assumptions — Print Assumptions on every theorem-like declaration, so
                   "zero axioms" is Coq's verdict rather than a grep's
  3. counts      — theorem/admitted census from the parsed source

The output is deliberately opinion-free: it records what Coq said, not whether
the record's *prose* is right. The semantic pass (records/<key>.verify.json,
consumed by consolidate.py) is a separate job that reads these numbers.

Why not grep: `DPL.v:1950` contains the words "Axiom-free." inside a comment,
and a naive /^\s*Axiom/ flags it as an axiom. Comments are stripped here, and
the assumption check goes through Coq regardless.

Usage:
  ./verify.py                 # atlas/*/*.v
  ./verify.py --all           # every .v listed in _CoqProject
  ./verify.py atlas/dynamic/DPL.v ...
"""
import json, os, re, subprocess, sys, shutil, tempfile, glob

HERE = os.path.dirname(os.path.abspath(__file__))
REC = os.path.join(HERE, "records")
REPO = "/Users/graogro/Dropbox/revisiting-formal-semantics"
ROOTS = ["shallow", "deep", "extras", "ttr_mtt", "atlas"]
INCLUDES = [a for r in ROOTS for a in ("-R", os.path.join(REPO, r), "")]

# Declarations that carry a proof and therefore have assumptions worth printing.
THEOREM_KW = ("Theorem", "Lemma", "Corollary", "Proposition", "Remark", "Fact",
              "Property", "Example")
# Declarations that introduce a definition; counted but not queried by default.
DEF_KW = ("Definition", "Fixpoint", "CoFixpoint", "Instance", "Let", "Record",
          "Inductive", "Structure", "Class")
# Declarations that introduce something unproved. Inside a Section these are
# discharged into the theorem statement and are NOT axioms; at top level they
# are. The stack depth tells us which.
ASSUM_KW = ("Axiom", "Parameter", "Parameters", "Conjecture", "Hypothesis",
            "Hypotheses", "Variable", "Variables", "Context")
TERMINATOR = ("Qed", "Defined", "Admitted", "Abort", "Save")

# Axioms Coq itself ships that the project has documented as acceptable.
KNOWN_AXIOMS = {
    "classic": "classical logic (documented)",
    "functional_extensionality_dep": "funext (documented)",
    "functional_extensionality": "funext (documented)",
    "proof_irrelevance": "proof irrelevance (documented)",
    "Eqdep.Eq_rect_eq.eq_rect_eq": "UIP/K (documented)",
    "JMeq_eq": "John Major equality (documented)",
}


def strip_comments(src):
    """Blank out (* nested *) comments and string bodies, preserving offsets
    and newlines so line numbers survive."""
    out, i, depth, n = [], 0, 0, len(src)
    in_str = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if not in_str and c == "(" and nxt == "*":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth and c == "*" and nxt == ")":
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth:
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if c == '"':
            in_str = not in_str
            out.append('"')
            i += 1
            continue
        out.append(" " if (in_str and c != "\n") else c)
        i += 1
    return "".join(out)


# A Coq command starts at the beginning of a line or straight after the period
# that closed the previous one — `Proof. reflexivity. Qed.` is three commands on
# one line, and anchoring to ^ would miss two of them.
CMD = r"(?:^|\.)[ \t]*"
DECL_RE = re.compile(
    CMD + r"(?:(?:Local|Global|Program|#\[[^\]]*\][ \t]*)[ \t]*)*"
    r"(?P<kw>%s)[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
    % "|".join(THEOREM_KW + DEF_KW + ASSUM_KW), re.M)
SCOPE_RE = re.compile(
    CMD + r"(?P<kw>Module|Section|End)[ \t]+(?P<rest>[^.]*)\.", re.M)
TERM_RE = re.compile(CMD + r"(?P<kw>%s)[ \t]*\." % "|".join(TERMINATOR), re.M)


def parse(path):
    """Return (decls, scopes_ok). Each decl carries its Module path — Sections
    are transparent to naming, Modules are not, so only Modules join the path."""
    src = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    line_of = lambda pos: src.count("\n", 0, pos) + 1

    events = []
    for m in DECL_RE.finditer(src):
        events.append((m.start(), "decl", m.group("kw"), m.group("name")))
    for m in SCOPE_RE.finditer(src):
        events.append((m.start(), "scope", m.group("kw"), m.group("rest").strip()))
    for m in TERM_RE.finditer(src):
        events.append((m.start(), "term", m.group("kw"), None))
    events.sort()

    def settle(d, end_pos):
        """A theorem that reaches the next command without Qed/Admitted is
        either a term-mode proof (`Theorem foo : T := e.`) or genuinely
        unfinished. Never silently count the second as the first."""
        d["status"] = "proved" if ":=" in src[d["_pos"]:end_pos] else "unknown"

    decls, stack, pending, unbalanced = [], [], None, []
    for pos, kind, kw, arg in events:
        if kind in ("scope", "decl") and pending is not None:
            settle(pending, pos)
            pending = None
        if kind == "scope":
            if kw == "End":
                nm = arg.split()[0] if arg.split() else ""
                if stack and stack[-1][1] == nm:
                    stack.pop()
                else:  # tolerate, but report
                    unbalanced.append(f"line {line_of(pos)}: End {nm}")
                    if stack:
                        stack.pop()
            elif kw == "Module":
                # `Module X := Y.` and `Module Type T.` do not open a body we
                # need to track for naming the same way; := opens nothing.
                if ":=" in arg:
                    continue
                parts = [p for p in arg.split() if p not in ("Type", "Import", "Export")]
                if parts:
                    stack.append(("Module", parts[0]))
            else:  # Section
                parts = arg.split()
                if parts:
                    stack.append(("Section", parts[0]))
            continue

        if kind == "decl":
            modpath = [n for k, n in stack if k == "Module"]
            in_section = any(k == "Section" for k in (s[0] for s in stack))
            d = {"kw": kw, "name": arg, "line": line_of(pos), "_pos": pos,
                 "modpath": modpath, "in_section": in_section,
                 "kind": ("theorem" if kw in THEOREM_KW else
                          "assumption" if kw in ASSUM_KW else "definition"),
                 "status": None}
            decls.append(d)
            # Only theorem-like decls await a terminator; a Definition may or
            # may not have one, and would otherwise steal the next Qed.
            pending = d if kw in THEOREM_KW else None
            continue

        if kind == "term" and pending is not None:
            pending["status"] = {"Qed": "proved", "Defined": "proved",
                                 "Save": "proved", "Admitted": "admitted",
                                 "Abort": "aborted"}.get(kw)
            pending = None

    if pending is not None:
        settle(pending, len(src))
    for d in decls:
        d.pop("_pos", None)
    return decls, unbalanced


def logical_name(path):
    """atlas/montague/PTQ.v -> montague.PTQ.

    Each -R root is bound to the empty logical prefix, so the path *below* the
    root is the module path. The short name is not usable: shallow/PTQ.v and
    atlas/montague/PTQ.v would both be `PTQ`, and `Require Import PTQ` silently
    loads whichever the loadpath hits first."""
    rel = os.path.relpath(os.path.abspath(path), REPO)
    for r in ROOTS:
        if rel.startswith(r + os.sep):
            rel = rel[len(r) + 1:]
            break
    return rel[:-2].replace(os.sep, ".")


def compile_check(path, scratch):
    out = os.path.join(scratch, "build")
    os.makedirs(out, exist_ok=True)
    cmd = ["coqc", "-o", os.path.join(out, os.path.basename(path) + "o")] + INCLUDES + [path]
    p = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True, timeout=900)
    err = p.stderr.strip()
    warnings = [l for l in err.splitlines() if l.startswith("Warning:")]
    return {"ok": p.returncode == 0, "returncode": p.returncode,
            "warnings": len(warnings),
            "stderr_tail": "\n".join(err.splitlines()[-12:]) if err else ""}


ASSUM_HEAD = re.compile(r"^(Axioms|Variables|Parameters|Opaque constants)\s*:", re.M)


def assumptions(path, decls, scratch):
    """Print Assumptions every theorem, one Redirect file each. An unresolvable
    name aborts the run, so drop the reported name and retry."""
    targets = [d for d in decls if d["kind"] == "theorem" and d["status"] == "proved"]
    if not targets:
        return {}, []
    work = os.path.join(scratch, "assum")
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(os.path.join(work, "out"), exist_ok=True)
    mod = logical_name(path)
    qual = {}
    for i, d in enumerate(targets):
        qual[i] = ".".join([mod] + d["modpath"] + [d["name"]])

    live, unresolved = dict(qual), []
    for _ in range(60):  # each retry removes >=1 name
        drv = [f"Require Import {mod}."]
        for i in sorted(live):
            drv.append(f'Redirect "out/{i:05d}" Print Assumptions {live[i]}.')
        open(os.path.join(work, "drv.v"), "w").write("\n".join(drv) + "\n")
        p = subprocess.run(["coqc", "-output-directory", ".", "-o", "drv.vo"] + INCLUDES + ["drv.v"],
                           cwd=work, capture_output=True, text=True, timeout=900)
        if p.returncode == 0:
            break
        bad = re.findall(r"The reference ([\w.']+) was not found", p.stderr)
        bad += re.findall(r"([\w.']+) (?:was not found|not a defined object)", p.stderr)
        hit = False
        for i in list(live):
            if live[i] in bad:
                unresolved.append(live.pop(i))
                hit = True
        if not hit:  # unknown failure mode: stop rather than spin
            unresolved.append(f"__driver_error__: {p.stderr.strip().splitlines()[-1] if p.stderr.strip() else '?'}")
            break

    res = {}
    for i, q in qual.items():
        f = os.path.join(work, "out", f"{i:05d}.out")
        if not os.path.exists(f):
            continue
        txt = open(f).read().strip()
        if not txt:
            continue
        if txt.startswith("Closed under the global context"):
            res[q] = {"closed": True, "axioms": []}
        else:
            names = re.findall(r"^([\w.']+)\s*:", txt, re.M)
            names = [n for n in names if not ASSUM_HEAD.match(n + ":")]
            res[q] = {"closed": False, "axioms": sorted(set(names)),
                      "raw": txt[:1500]}
    return res, unresolved


def verify_file(path, key, record, scratch):
    decls, unbalanced = parse(path)
    comp = compile_check(path, scratch)
    assum, unresolved = assumptions(path, decls, scratch) if comp["ok"] else ({}, [])

    thms = [d for d in decls if d["kind"] == "theorem"]
    proved = [d for d in thms if d["status"] == "proved"]
    admitted = [d for d in thms if d["status"] == "admitted"]
    aborted = [d for d in thms if d["status"] == "aborted"]
    unknown = [d for d in thms if d["status"] not in ("proved", "admitted", "aborted")]
    # Top-level (non-Section) unproved declarations are real axioms; inside a
    # Section they are discharged into the statement.
    hard = [d for d in decls if d["kind"] == "assumption"
            and d["kw"] in ("Axiom", "Parameter", "Parameters", "Conjecture")
            and not d["in_section"]]
    sectioned = [d for d in decls if d["kind"] == "assumption" and d["in_section"]]

    dirty = {q: v for q, v in assum.items() if not v["closed"]}
    undocumented = sorted({a for v in dirty.values() for a in v["axioms"]
                           if a.split(".")[-1] not in KNOWN_AXIOMS
                           and a not in KNOWN_AXIOMS})

    mech = {
        "_generated_by": "atlas/verify.py (ROADMAP A3)",
        "file": os.path.relpath(path, REPO),
        "key": key,
        "coq_version": COQ_VERSION,
        "compile": comp,
        "counts": {
            "theorems": len(thms), "proved": len(proved),
            "admitted": len(admitted), "aborted": len(aborted),
            "unparsed_status": len(unknown),
            "definitions": len([d for d in decls if d["kind"] == "definition"]),
            "toplevel_axioms": len(hard),
            "section_assumptions": len(sectioned),
        },
        "assumptions": {
            "queried": len(assum), "closed": len(assum) - len(dirty),
            "not_closed": len(dirty),
            "undocumented_axioms": undocumented,
            "detail": {q: v for q, v in sorted(dirty.items())},
            "unresolved": unresolved,
        },
        "admitted_names": [{"name": d["name"], "line": d["line"]} for d in admitted],
        "aborted_names": [{"name": d["name"], "line": d["line"]} for d in aborted],
        "unparsed_names": [{"name": d["name"], "line": d["line"]} for d in unknown],
        "toplevel_axiom_names": [{"name": d["name"], "kw": d["kw"], "line": d["line"]} for d in hard],
        "parse_warnings": unbalanced,
    }

    # Compare with what the record claims about itself.
    disputes = []
    if record:
        rc = record.get("counts") or {}
        if record.get("compiles") is True and not comp["ok"]:
            disputes.append({"field": "compiles", "claimed": True, "measured": False,
                             "detail": comp["stderr_tail"][:400]})
        for f in ("theorems", "proved", "admitted"):
            if f in rc and isinstance(rc[f], int) and rc[f] != mech["counts"][f]:
                disputes.append({"field": f"counts.{f}", "claimed": rc[f],
                                 "measured": mech["counts"][f]})
        pa = rc.get("propositional_axioms")
        if isinstance(pa, int) and pa != len(undocumented):
            disputes.append({"field": "counts.propositional_axioms",
                             "claimed": pa, "measured": len(undocumented),
                             "detail": ", ".join(undocumented[:8])})
    mech["disputes_vs_record"] = disputes
    return mech


def main():
    global COQ_VERSION
    COQ_VERSION = subprocess.run(["coqc", "--version"], capture_output=True, text=True
                                 ).stdout.split("version")[-1].strip().split()[0]

    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    if "--all" in sys.argv:
        files = [l.strip() for l in open(os.path.join(REPO, "_CoqProject"))
                 if l.strip().endswith(".v")]
    elif args:
        files = args
    else:
        files = sorted(glob.glob("atlas/*/*.v", root_dir=REPO))

    # file -> record key, taken from the records themselves
    by_file = {}
    for p in sorted(glob.glob(os.path.join(REC, "*.json"))):
        if p.endswith(".verify.json") or p.endswith(".mech.json"):
            continue
        try:
            r = json.load(open(p))
        except Exception:
            continue
        f = (r.get("file") or "").replace(REPO + "/", "")
        if f:
            by_file[f] = (os.path.basename(p)[:-5], r)

    scratch = tempfile.mkdtemp(prefix="atlas-verify-", dir=os.environ.get("TMPDIR"))
    summary, bad = [], 0
    try:
        for rel in files:
            path = os.path.join(REPO, rel)
            if not os.path.exists(path):
                print(f"SKIP {rel}: not on disk", file=sys.stderr)
                continue
            key, record = by_file.get(rel, (None, None))
            key = key or rel.replace("/", "__").replace(".v", "").lower()
            m = verify_file(path, key, record, scratch)
            open(os.path.join(REC, key + ".mech.json"), "w").write(
                json.dumps(m, indent=2, ensure_ascii=False) + "\n")
            c, a = m["counts"], m["assumptions"]
            flag = ""
            if not m["compile"]["ok"]:
                flag = " ✗ COMPILE"
            elif m["disputes_vs_record"]:
                flag = f" ⚠ {len(m['disputes_vs_record'])} dispute(s)"
            if flag:
                bad += 1
            print(f"{rel:38s} {c['proved']:4d}/{c['theorems']:<4d} proved  "
                  f"adm={c['admitted']:<3d} ax={len(a['undocumented_axioms']):<3d} "
                  f"closed={a['closed']}/{a['queried']}{flag}")
            summary.append(m)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)

    tot = lambda f: sum(m["counts"][f] for m in summary)
    print(f"\n{len(summary)} files · {tot('theorems')} theorems · {tot('proved')} proved · "
          f"{tot('admitted')} admitted · {tot('toplevel_axioms')} top-level axioms · "
          f"{bad} file(s) flagged")
    return 0


if __name__ == "__main__":
    sys.exit(main())
