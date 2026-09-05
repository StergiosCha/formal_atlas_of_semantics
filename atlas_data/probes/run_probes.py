#!/usr/bin/env python3
r"""A3 L2 — vacuity/triviality probes over the atlas corpus.

For every proved theorem in the 12 atlas files, VacuityProbe.v (Ltac2) builds
two goals symbolically from the statement's Prod telescope — hypotheses ->
False (vacuity) and the conclusion with non-dependent Prop premises stripped
(triviality) — and tries a bounded trivial tactic bank on each, inside one
`Goal True` proof per theory. coqc's stdout carries one machine-parseable
PROBE| line per (theorem, probe); this script generates the drivers, runs
them, and writes records/<key>.probe.json.

Honesty rules baked in:
  - a probe that did not run is BAILOUT:<reason>, never "ok";
  - the self-test (SelfTest.v: one vacuous, one honest, one hidden-True
    lemma) must produce its six expected verdicts or the whole run aborts;
  - driver runs are wall-clock capped; on a timeout the first theorem whose
    output is incomplete is the wedged one (output is sequential), it gets
    BAILOUT:timeout and the batch resumes after it.

Usage:
  ./run_probes.py                 # self-test, then all 12 atlas theories
  ./run_probes.py atlas__ptq ...  # self-test, then just these keys
  ./run_probes.py --selftest-only
  ./run_probes.py --timeout 300   # per-driver-run cap in seconds
"""
import json, os, re, subprocess, sys, glob

HERE = os.path.dirname(os.path.abspath(__file__))            # .../atlas/probes
ATLAS = os.path.dirname(HERE)                                # .../atlas
REC = os.path.join(ATLAS, "records")
sys.path.insert(0, ATLAS)
import verify                                                # parse(), logical_name(), REPO, INCLUDES

REPO = verify.REPO
TMP = os.environ.get("TMPDIR") or "/tmp/claude"
WORK = os.path.join(TMP, "atlas-probes")
PROBEVO = os.path.join(WORK, "probevo")

PROBE_RE = re.compile(r"^PROBE\|(.+)\|(vacuity|triviality)\|(.+?)\s*$")
UNRESOLVED_RE = re.compile(r"The reference ([\w.']+) was not found")


def sh(cmd, cwd, timeout):
    """subprocess.run that survives a timeout and always returns
    (returncode|None, stdout, stderr) as text."""
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                           timeout=timeout)
        return p.returncode, p.stdout or "", p.stderr or ""
    except subprocess.TimeoutExpired as e:
        dec = lambda b: (b.decode(errors="replace") if isinstance(b, bytes)
                         else (b or ""))
        return None, dec(e.stdout), dec(e.stderr)


def coq_version():
    out = subprocess.run(["coqc", "--version"], capture_output=True,
                         text=True).stdout
    return out.split("version")[-1].strip().split()[0]


def compile_probe_lib():
    os.makedirs(PROBEVO, exist_ok=True)
    rc, out, err = sh(["coqc", "-noglob",
                       "-o", os.path.join(PROBEVO, "VacuityProbe.vo"),
                       os.path.join(HERE, "VacuityProbe.v")],
                      cwd=WORK, timeout=300)
    if rc != 0:
        sys.exit(f"VacuityProbe.v failed to compile:\n{err}")


SELFTEST_EXPECT = {
    ("SelfTest.st_vacuous", "vacuity"): "VACUOUS",
    ("SelfTest.st_vacuous", "triviality"): "ok",
    ("SelfTest.st_normal", "vacuity"): "ok",
    ("SelfTest.st_normal", "triviality"): "ok",
    ("SelfTest.st_trivial", "vacuity"): "ok",
    ("SelfTest.st_trivial", "triviality"): "TRIVIAL",
}


def selftest():
    rc, out, err = sh(["coqc", "-R", PROBEVO, "", "-noglob",
                       "-o", os.path.join(PROBEVO, "SelfTest.vo"),
                       os.path.join(HERE, "SelfTest.v")],
                      cwd=WORK, timeout=300)
    if rc != 0:
        sys.exit(f"SelfTest.v failed to compile:\n{err}")
    got = {}
    for line in out.splitlines():
        m = PROBE_RE.match(line.strip())
        if m:
            got[(m.group(1), m.group(2))] = m.group(3)
    if got != SELFTEST_EXPECT:
        sys.exit("self-test MISMATCH:\n  expected %r\n  got      %r"
                 % (SELFTEST_EXPECT, got))
    print("self-test: 6/6 verdicts as expected "
          "(VACUOUS, ok, ok, ok, ok, TRIVIAL)")


def proved_fqnames(path):
    """Proved-theorem fully qualified names, in source order, deduplicated.
    Ground truth is the .v source parsed exactly as verify.py does for the
    mech records."""
    decls, _ = verify.parse(path)
    mod = verify.logical_name(path)
    seen, out = set(), []
    for d in decls:
        if d["kind"] == "theorem" and d["status"] == "proved":
            q = ".".join([mod] + d["modpath"] + [d["name"]])
            if q not in seen:
                seen.add(q)
                out.append(q)
    return out


def driver_text(mod, names):
    L = ["From Ltac2 Require Import Ltac2.",
         "Require VacuityProbe.",
         f"Require {mod}.",
         'Ltac2 Eval (VacuityProbe.emit "__driver__" "start" "ok").',
         "Goal True.",
         "Proof."]
    for q in names:
        L.append(f'VacuityProbe.probe_theorem "{q}" reference:({q}).')
    L.append("Abort.")
    return "\n".join(L) + "\n"


def run_driver(mod, names, tag, timeout):
    """One coqc run. Returns (parsed, timed_out, saw_start, stderr)."""
    drv = os.path.join(WORK, f"drv_{tag}.v")
    with open(drv, "w") as f:
        f.write(driver_text(mod, names))
    cmd = (["coqc", "-noglob"] + verify.INCLUDES +
           ["-R", PROBEVO, "", "-o", os.path.join(WORK, f"drv_{tag}.vo"), drv])
    rc, out, err = sh(cmd, cwd=REPO, timeout=timeout)
    parsed, saw_start = {}, False
    for line in out.splitlines():
        m = PROBE_RE.match(line.strip())
        if not m:
            continue
        name, probe, verdict = m.groups()
        if name == "__driver__":
            saw_start = True
            continue
        verdict = verdict.replace("BAILOUT|", "BAILOUT:", 1)
        parsed.setdefault(name, {})[probe] = verdict
    return rc, parsed, saw_start, err


def mark(results, name, reason):
    """Fill any missing probe verdicts of `name` with a BAILOUT."""
    slot = results.setdefault(name, {})
    for probe in ("vacuity", "triviality"):
        slot.setdefault(probe, f"BAILOUT:{reason}")


def probe_theory(key, relfile, timeout):
    path = os.path.join(REPO, relfile)
    mod = verify.logical_name(path)
    names = proved_fqnames(path)
    results = {}
    pending = list(names)
    rounds = 0
    while pending:
        rounds += 1
        if rounds > len(names) + 20:  # each round must retire >= 1 name
            for n in pending:
                mark(results, n, "runner_loop_guard")
            break
        rc, parsed, saw_start, err = run_driver(
            mod, pending, f"{key}_{rounds}", timeout)
        for name, verdicts in parsed.items():
            results.setdefault(name, {}).update(verdicts)
        remaining = [n for n in pending
                     if len(results.get(n, {})) < 2]
        if rc == 0:
            for n in remaining:      # should not happen: emitted nothing
                mark(results, n, "no_output")
            break
        if rc is None:               # wall-clock timeout
            if not saw_start:
                for n in remaining:
                    mark(results, n, "require_timeout")
                break
            if not remaining:
                break
            # output is sequential: the first incomplete theorem is the one
            # that wedged (Ltac1 timeout cannot interrupt vm/native compute)
            mark(results, remaining[0], "timeout")
            pending = remaining[1:]
            continue
        # compile error
        bad = set(UNRESOLVED_RE.findall(err))
        hit = [n for n in remaining if n in bad]
        if hit:
            for n in hit:
                mark(results, n, "unresolved_reference")
            pending = [n for n in remaining if n not in hit]
            continue
        if not saw_start:
            tail = err.strip().splitlines()[-1][:120] if err.strip() else "?"
            print(f"  {key}: driver failed before probing: {tail}",
                  file=sys.stderr)
            for n in remaining:
                mark(results, n, "driver_error_before_probes")
            break
        if remaining:
            # sequential output again: first incomplete name is the culprit
            mark(results, remaining[0], "driver_error")
            pending = remaining[1:]
            continue
        break
    for n in names:                  # belt and braces: no silent skips
        mark(results, n, "never_attempted")
    return names, results


def write_record(key, relfile, cv, names, results):
    probes = {n: {"vacuity": results[n]["vacuity"],
                  "triviality": results[n]["triviality"]} for n in names}
    summary = {
        "probed": len(names),
        "vacuous": sum(1 for n in names
                       if probes[n]["vacuity"] == "VACUOUS"),
        "trivial": sum(1 for n in names
                       if probes[n]["triviality"] == "TRIVIAL"),
        "bailout": sum(1 for n in names
                       if any(v.startswith("BAILOUT:")
                              for v in probes[n].values())),
    }
    rec = {"_generated_by": "atlas/probes/run_probes.py (A3 L2)",
           "file": relfile,
           "coq_version": cv,
           "probes": probes,
           "summary": summary}
    out = os.path.join(REC, f"{key}.probe.json")
    with open(out, "w") as f:
        json.dump(rec, f, indent=2, ensure_ascii=False)
        f.write("\n")
    return summary


def atlas_targets(keys=None):
    """(key, relfile) pairs from the atlas mech records."""
    pairs = []
    for p in sorted(glob.glob(os.path.join(REC, "atlas__*.mech.json"))):
        m = json.load(open(p))
        if keys and m["key"] not in keys:
            continue
        pairs.append((m["key"], m["file"]))
    return pairs


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    timeout = 240
    if "--timeout" in sys.argv:
        timeout = int(sys.argv[sys.argv.index("--timeout") + 1])
        args = [a for a in args if a != str(timeout)]
    os.makedirs(WORK, exist_ok=True)
    compile_probe_lib()
    selftest()
    if "--selftest-only" in sys.argv:
        return 0
    cv = coq_version()
    grand = {"probed": 0, "vacuous": 0, "trivial": 0, "bailout": 0}
    findings = []
    for key, relfile in atlas_targets(set(args) or None):
        names, results = probe_theory(key, relfile, timeout)
        s = write_record(key, relfile, cv, names, results)
        for k in grand:
            grand[k] += s[k]
        for n in names:
            if results[n]["vacuity"] == "VACUOUS":
                findings.append(("VACUOUS", n))
            if results[n]["triviality"] == "TRIVIAL":
                findings.append(("TRIVIAL", n))
        print(f"{key:22s} probed={s['probed']:<4d} vacuous={s['vacuous']:<3d} "
              f"trivial={s['trivial']:<3d} bailout={s['bailout']}")
    print(f"\nTOTAL probed={grand['probed']} vacuous={grand['vacuous']} "
          f"trivial={grand['trivial']} bailout={grand['bailout']}")
    for kind, n in findings:
        print(f"  {kind}: {n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
