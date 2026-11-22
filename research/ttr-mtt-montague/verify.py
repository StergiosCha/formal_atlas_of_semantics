"""Run the comparison in a fresh checkout, retaining source hashes and kernel output."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import hashlib
import re
import shlex
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
PIN = "f6774ec0adc45e90096eb41e4f9310cb91a4a9d5"
MAPS = [("atlas/mtt_ranta", "mtt_ranta"), ("atlas/montague", "montague"), ("atlas/ttr", "ttr"),
        ("deep/montague_ptq", "MontaguePTQ"), ("ttr_mtt", "Book"), ("check", "")]
ATLAS = ["atlas/mtt_ranta/MTT", "atlas/mtt_ranta/Ranta", "atlas/mtt_ranta/DTS",
         "atlas/mtt_ranta/MTT_vs_Ranta", "atlas/mtt_ranta/MTT_vs_DTS", "atlas/montague/PTQ", "atlas/mtt_ranta/Ranta_GQ", "atlas/mtt_ranta/Donkey_Sums",
         "atlas/ttr/TTR", "atlas/ttr/TTR_Model", "deep/montague_ptq/Syntax",
         "deep/montague_ptq/Models", "ttr_mtt/Book_Individuation"]
UNITS = ["CMM_Comparison_spec", "CMM_Comparison_spec_probe"]


def call(args, cwd, stream, *, display=None):
    print("$", shlex.join(list(map(str, display or args))), file=stream, flush=True)
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    output = "\n".join(line.rstrip() for line in p.stdout.splitlines())
    print(output, f"[exit {p.returncode}]", sep="\n", file=stream, flush=True)
    if p.returncode:
        raise RuntimeError(f"{args[0]} failed: {p.stdout[-1800:]}")
    return p.stdout


def run(repo, logs):
    logs.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(prefix="atlas-cmm-") as temp:
        clone = Path(temp) / "atlas"
        flags = [arg for path, name in MAPS for arg in ("-Q", path, name)]
        with (logs / "CMM_build.txt").open("w") as log:
            call(["git", "clone", "--quiet", "--no-hardlinks", "--no-checkout", repo, "atlas"], temp, log,
                 display=["git", "clone", "--quiet", "--no-hardlinks", "--no-checkout", "ATLAS_CHECKOUT", "atlas"])
            call(["git", "checkout", "--quiet", "-b", "scratch-cmm", PIN], clone, log)
            assert call(["git", "rev-parse", "HEAD"], clone, log).strip() == PIN
            if "8.20.1" not in call(["coqc", "--version"], clone, log):
                raise RuntimeError("use Rocq 8.20.1")
            check = clone / "check"
            check.mkdir()
            for name in UNITS:
                shutil.copyfile(HERE / (name+".v"), check / (name+".v"))
            for stem in ATLAS + ["check/" + u for u in UNITS]:
                path = Path(stem + ".v")
                print(f"SHA256 {hashlib.sha256((clone/path).read_bytes()).hexdigest()}  {path}", file=log)
                call(["coqc", "-q", *flags, str(path)], clone, log)
        text = "\n".join((check / (u+".v")).read_text() for u in UNITS)
        def qualified_proofs(source):
            proofs = []
            module = []
            for line in source.splitlines():
                if match := re.match(r"^Module (\w+)\.", line):
                    module.append(match.group(1))
                elif match := re.match(r"^End (\w+)\.", line):
                    assert module.pop() == match.group(1)
                elif match := re.match(r"^(?:Example|Theorem) (\w+)", line):
                    proofs.append(".".join(module + [match.group(1)]))
            return proofs
        proofs = qualified_proofs(text)
        statements = re.findall(r"^Definition (\w+_statement)\b", text, re.M)
        cmds = ["Require Import " + " ".join(UNITS) + ".", "Set Printing Width 100."]
        cmds += ["Print " + s + "." for s in statements]
        for c in proofs:
            cmds += [f"Check {c}.", f"Print Assumptions {c}."]
        (check / "CMM_Queries.v").write_text("\n".join(cmds) + "\n")
        with (logs / "CMM_assumptions.txt").open("w") as log:
            out = call(["coqc", "-q", *flags, "check/CMM_Queries.v"], clone, log)
            if out.count("Closed under the global context") != len(proofs):
                raise RuntimeError("inspect global dependencies in the new comparison")
            print(f"{len(proofs)} new example and theorem proofs closed under the global context.", file=log)
            (check / "CMM_AtlasQueries.v").write_text("Require Book.Book_Individuation.\n" +
                "\n".join(f"Check Book_Individuation.{n}.\nPrint Assumptions Book_Individuation.{n}."
                         for n in ("copred_dd1", "copred_dd2")) + "\n")
            call(["coqc", "-q", *flags, "check/CMM_AtlasQueries.v"], clone, log)
        with (logs / "CMM_kernel.txt").open("w") as log:
            call(["coqchk", "-silent", "-o", *flags, *UNITS, "Book.Book_Individuation"], clone, log)
        print(f"{len(proofs)} new example/theorem proofs, with source and kernel logs at {logs}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="a full local Atlas checkout containing the pinned revision")
    parser.add_argument("--logs", type=Path, default=Path("verification-run"))
    opts = parser.parse_args()
    run(opts.repo.resolve(), opts.logs.resolve())
