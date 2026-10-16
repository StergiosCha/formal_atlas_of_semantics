#!/usr/bin/env python3
"""Rebuild the Gallin translation in isolation and audit its exact boundary.

No PDF, API key, network access or existing .vo files are needed.
--record explicitly creates a new checkpoint; --check rejects any drift.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PTQ = HERE.parent / "montague_ptq"
sys.path.insert(0, str(ROOT / "atlas_data"))
import verify

UNITS = ("Types", "Target", "Translation", "Examples")
DEPENDENCIES = ("Syntax", "Models", "Grammar", "Translation", "Meaning", "Postulates", "Examples")
PRELUDE = """From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Postulates Examples.
From MontagueGallin Require Import Types Target Translation Examples.
Import ListNotations.
"""
SIGNATURES = """
Definition all_source_terms : forall G a, tm G a ->
  target_term (map translate_type G) (garr gs (translate_type a)) := @translate_intension.
Definition all_source_assignments : forall M G a (p : tm G a) rho sigma i,
  target_eval M sigma (translate_intension p) (canonical_env rho) i =
  lift_value (carrier M) a (eval M p rho sigma i) := @open_preservation.
Definition environment_premise_is_nonvacuous : forall M G (rho : env M G),
  environments_match (@canonical_map G) (canonical_env rho) rho := @canonical_environments_match.
Definition direct_english_connection : forall M A (u : tree A) sigma i,
  target_eval M sigma (english_translation u) (gempty (carrier M)) i =
  lift_value (carrier M) (category_type A) (denote M u (fun n => sigma ic (2*n)) i) :=
  @english_interpretation_preserved.
Definition consequence_has_an_explicit_model_boundary : forall restriction ps q,
  image_consequence restriction ps q <-> source_consequence restriction ps q :=
  @consequence_on_model_image.
Definition temperature_still_requires_foundations : forall (B : BooleanTruth) (FE : FunExt),
  let M := sample_model B FE in let sigma := sample_assignment B FE in
  admissible M /\\
  target_eval M sigma (english_translation temperature_is_ninety) (gempty (carrier M)) (tt,false) = true /\\
  target_eval M sigma (english_translation temperature_rises) (gempty (carrier M)) (tt,false) = true /\\
  target_eval M sigma (english_translation ninety_rises) (gempty (carrier M)) (tt,false) = false :=
  temperature_countermodel_transported.
"""
NEGATIVE = {
    "source_index_is_not_an_entity": (
        "Example bad : translate_type e = gs. Proof. reflexivity. Qed.", "Unable to unify"),
    "iv_does_not_gain_an_extra_intension": (
        "Example bad : translate_type ivty = garr (garr gs ge) (garr gs gt). Proof. reflexivity. Qed.",
        "Unable to unify"),
    "constant_is_not_a_rigid_free_variable": (
        "Example bad : translate_intension (@Con [] e 7) = GLam (GFree (SourceFree e 7)). "
        "Proof. reflexivity. Qed.", "Unable to unify"),
    "free_variable_is_not_an_indexed_constant": (
        "Example bad : translate_intension (@Free [] e 7) = "
        "GLam (GApp (GCon (IndexedConstant e 7)) (GVar gz)). Proof. reflexivity. Qed.",
        "Unable to unify"),
    "index_binder_does_not_capture_a_source_variable": (
        "Example bad : translate_intension (@Lam [] e (intens e) (Up (Var vz))) = "
        "GLam (GLam (GLam (GFree (SourceFree e 0)))). Proof. reflexivity. Qed.",
        "Unable to unify"),
    "translation_is_not_a_source_model_validity_proof": (
        "Definition bad : forall restriction ps q, source_consequence restriction ps q := "
        "@consequence_on_model_image.", "expected to have type"),
    "countermodel_does_not_supply_its_own_foundations": (
        "Definition bad : exists M, admissible M := source_model_conditions_are_satisfiable.",
        "expected to have type"),
    "current_time_truth_is_not_absolute_necessity": (
        "Definition bad B FE : let M := sample_model B FE in "
        "target_eval M (sample_assignment B FE) (translate_intension (Box (@Con [] t 0))) "
        "(gempty (carrier M)) (tt,false) = true := "
        "proj2 (translated_necessity_keeps_both_coordinates B FE).", "expected to have type"),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(cmd, cwd, input=None):
    return subprocess.run(cmd, cwd=cwd, input=input, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)


def require(cmd, cwd, input=None):
    result = run(cmd, cwd, input)
    if result.returncode or re.search(r"(?m)^Error:", result.stdout):
        raise RuntimeError(result.stdout)
    return result.stdout


def check():
    version = require(["coqc", "--version"], HERE)
    if not re.search(r"version 8\.20\.1\b", version):
        raise RuntimeError("Coq 8.20.1 required")
    expected_project = ["-Q ../montague_ptq MontaguePTQ", "-Q . MontagueGallin",
                        *(unit + ".v" for unit in UNITS)]
    if (HERE / "_CoqProject").read_text().splitlines() != expected_project:
        raise RuntimeError("_CoqProject and checker compile order differ")
    source_checkpoint = json.loads((PTQ / "verification.json").read_text())
    dependencies = {}
    for unit in DEPENDENCIES:
        filename = unit + ".v"
        sha = digest(PTQ / filename)
        if sha != source_checkpoint["files"][filename]["sha256"]:
            raise RuntimeError(f"Source PTQ checkpoint changed: {filename}")
        dependencies[filename] = sha
    files, names, audited = {}, [], []
    for unit in UNITS:
        source = HERE / (unit + ".v")
        clean = verify.strip_comments(source.read_text())
        if re.search(r"\b(Admitted|Abort|Axiom|Parameter|Parameters|Conjecture|"
                     r"Classical_Prop|FunctionalExtensionality|PropExtensionality|"
                     r"ProofIrrelevance|Eqdep)\b|Unset\s+(Guard|Positivity|Universe)\s+Checking", clean):
            raise RuntimeError(f"Unsafe shortcut or new global assumption: {source.name}")
        declarations, warnings = verify.parse(source)
        proofs = [d for d in declarations if d["kind"] == "theorem"]
        if warnings or any(d.get("status") != "proved" for d in proofs):
            raise RuntimeError(f"Incomplete declarations: {source.name}")
        qualify = lambda d: ".".join(["MontagueGallin", unit, *d["modpath"], d["name"]])
        statements = [qualify(d) for d in proofs]
        inventory = [qualify(d) for d in declarations if d["kind"] in ("theorem", "definition")]
        names.extend(statements)
        audited.extend(inventory)
        files[source.name] = {"sha256": digest(source), "proved_statements": statements,
                              "audited_declarations": inventory}
    with tempfile.TemporaryDirectory(prefix="montague-gallin-") as directory:
        temp = Path(directory)
        source_dir, target_dir = temp / "ptq", temp / "gallin"
        source_dir.mkdir()
        target_dir.mkdir()
        flags = ["-Q", str(source_dir), "MontaguePTQ", "-Q", str(target_dir), "MontagueGallin"]
        inputs = [(PTQ / (u + ".v"), source_dir) for u in DEPENDENCIES]
        inputs += [(HERE / (u + ".v"), target_dir) for u in UNITS]
        for source, folder in inputs:
            destination = folder / source.name
            shutil.copy2(source, destination)
            require(["coqc", *flags, str(destination)], temp)
            print(f"Compiled {source.relative_to(ROOT)}", flush=True)
        require(["coqchk", "-silent", *flags, *("MontagueGallin." + u for u in UNITS)], temp)
        print("Kernel recheck passed", flush=True)
        audit = require(["coqtop", "-quiet", *flags], temp,
                        PRELUDE + "\n".join(f"Print Assumptions {name}." for name in audited))
        if "Axioms:" in audit or audit.count("Closed under the global context") != len(audited):
            raise RuntimeError("Global assumption audit failed:\n" + audit)
        signature_file = temp / "Signatures.v"
        signature_file.write_text(PRELUDE + SIGNATURES)
        require(["coqc", *flags, str(signature_file)], temp)
        print("Exact theorem signatures passed", flush=True)
        for name, (fixture, diagnostic) in NEGATIVE.items():
            path = temp / "Rejected.v"
            path.write_text(PRELUDE + fixture + "\n")
            result = run(["coqc", *flags, str(path)], temp)
            if result.returncode == 0 or diagnostic not in result.stdout:
                raise RuntimeError(f"Negative fixture failed for the wrong reason: {name}\n{result.stdout}")
            print(f"Rejected invalid fixture: {name}", flush=True)
    return {
        "schema_version": 1, "checkpoint": 1, "coq_version": "8.20.1",
        "scope": "source-first PTQ interpretation preserved in explicit-index Ty2 presentation",
        "files": files, "ptq_dependencies": dependencies,
        "proved_statement_count": len(names), "kernel_rechecked": True,
        "global_dependencies_by_statement": {name: [] for name in names},
        "global_dependencies_by_declaration": {name: [] for name in audited},
        "explicit_foundational_inputs": ["BooleanTruth and FunExt in the source model"],
        "source_map_sha256": digest(HERE / "SOURCE_MAP.md"),
        "checker_sha256": digest(HERE / "check.py"),
        "coverage": {
            "all_source_ptq_term_constructors": True,
            "all_source_bound_and_free_assignments": True,
            "index_dependent_constants": True, "primitive_equality": True,
            "full_internal_function_spaces": True, "ptq_tense_extension": True,
            "english_tree_translation_composed": True,
            "admissible_temperature_countermodel_transported": True,
            "consequence_on_constructed_model_image": True,
            "all_independent_ty2_models": False,
            "elimination_of_connectives_into_gallin_minimal_syntax": False,
            "reverse_translation": False, "henkin_completeness": False,
            "gallin_axiomatic_calculus": False,
        },
        "negative_fixtures_rejected": sorted(NEGATIVE),
        "source_review": "AI-assisted primary-source consultation; no independent human review claimed",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--record", action="store_true")
    args = parser.parse_args()
    report = check()
    checkpoint = HERE / "verification.json"
    if args.record:
        checkpoint.write_text(json.dumps(report, indent=2) + "\n")
    elif json.loads(checkpoint.read_text()) != report:
        raise RuntimeError("Gallin checkpoint drift. Inspect the change before explicitly recording a new checkpoint.")
    print(f"PASS: {report['proved_statement_count']} checked statements; "
          f"{len(NEGATIVE)} invalid claims rejected. Explicit model assumptions remain required.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        sys.exit(str(error))
