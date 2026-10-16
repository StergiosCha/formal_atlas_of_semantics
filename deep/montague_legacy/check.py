#!/usr/bin/env python3
"""Isolated legacy and guarded-observation bridge checks, with separate audits.

Does not relax the axiom-closed montague_core checker. Imports an unchanged,
hash-pinned PTQ_deep2.v and rejects all dependencies except its used parameters.
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
CORE = HERE.parent / "montague_core"
LEGACY = HERE.parent / "PTQ_deep2.v"
LEGACY_SHA256 = "ee13df1359e47ca5856a3a35eacb9107beba145253a2f07c8fb39894477cd926"
UNITS = ("IndexSyntax", "IndexModels", "LegacyTranslation", "LegacyExamples",
         "ObservationBridge", "ObservationExamples")
CORE_UNITS = ("Syntax", "Models", "Calculus", "BooleanModels", "BooleanFinite",
              "Ty2Syntax", "Ty2Models", "Ty2Calculus")
sys.path.insert(0, str(ROOT / "atlas_data"))
import verify

LEGACY_PARAMETERS = {
    "Entity", "World", "Time", "time_lt", "john_e", "bill_e", "mary_e", "ninety_e",
    "walk_den", "run_den", "talk_den", "rise_den", "change_den", "man_den",
    "woman_den", "unicorn_den", "park_den", "fish_den", "price_den", "temperature_den",
    "find_den", "lose_den", "eat_den", "love_den", "seek_den", "try_to_den",
    "wish_to_den", "necessarily_den", "allegedly_den",
}
ALLOWED = {"PTQ_deep2." + name for name in LEGACY_PARAMETERS}
PRELUDE = """From Coq Require Import List.
From MontagueProof Require Import Models Calculus BooleanModels BooleanFinite Ty2Syntax Ty2Models Ty2Calculus.
From MontagueLegacy Require Import IndexSyntax IndexModels LegacyTranslation LegacyExamples.
From MontagueLegacy Require Import ObservationBridge ObservationExamples.
Import ListNotations.
"""
NEGATIVE = {
    "necessity_is_not_quantification_over_all_indices": ("""
Example bad :
  compile_legacy (Old.nec_ legacy_atom) (pz,tt)
    (@PVar legacy_symbol [parr pi pt;pi] pi (pvs pz)) =
  PAll (@PApp legacy_symbol [pi;parr pi pt;pi] pi pt (PVar (pvs pz)) (PVar pz)).
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "no_tense_does_not_license_time_erasure": ("""
Example bad (w : Old.World) (t0 t1 : Old.Time) :
  Old.eval legacy_atom (at_time t0) (w,t1).
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "future_order_cannot_be_reversed": (r"""
Example bad (w : Old.World) (t0 t1 : Old.Time) (F : Old.time_lt t0 t1) :
  exists t', Old.time_lt t' t0 /\ Old.eval legacy_atom (at_time t1) (w,t').
Proof. exists t1; split; [exact F | reflexivity]. Qed.
""", "expected to have type"),
    "prop_is_not_boolean_truth": ("""
Definition bad (i : Old.Index) : bool :=
  target_eval (legacy_as_index_function legacy_reflexive) empty_target_env i.
""", "expected to have type"),
    "general_preservation_keeps_funext": ("""
Definition bad : forall G a (t : Old.IL G a) env i,
  target_eval (legacy_as_index_function t) (canonical_env G env) i =
  legacy_lift a (Old.eval t env i) := legacy_open_preservation.
""", "expected to have type"),
    "worlds_and_times_are_distinct_sorts": ("""
Definition bad : ptm legacy_symbol [pw] ptime := @PVar legacy_symbol [pw] pw pz.
""", "expected to have type"),
    "legacy_beta_cannot_erase_the_index": ("""
Example bad (c : Old.Index -> Old.Entity) (i j : Old.Index) :
  Old.eval legacy_frozen (@Old.env_cons (Old.ty_s Old.ty_e) [] c tt) i j =
  Old.eval legacy_recomputed (@Old.env_cons (Old.ty_s Old.ty_e) [] c tt) i j.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "observation_guard_rejects_arbitrary_truth_quantification": ("""
Example bad : observable (@WAll observed_word [] wt (WImp (WVar wz) wfalsity)).
Proof. apply observe_all; [constructor | observation_certificate]. Qed.
""", "Unable to unify"),
    "observation_guard_rejects_predicate_quantification": ("""
Example bad : observable (@WAll observed_word [] (warr we wt) (WApp (WVar wz) ojohn)).
Proof. apply observe_all; [constructor | observation_certificate]. Qed.
""", "Unable to unify"),
    "mismatched_lexicons_do_not_preserve_atomic_truth": ("""
Example bad : paired_proposition empty_people_tables oman_john.
Proof. exact (proj1 mismatched_lexicons_can_change_the_answer). Qed.
""", "expected to have type"),
    "an_iff_is_not_propositional_identity": ("""
Definition bad (P Q : Prop) (H : P <-> Q) : P = Q := H.
""", "expected to have type"),
    "observation_agreement_requires_the_certificate": ("""
Definition bad (FE : FunExt) F (p : wtm observed_word [] wt) :
  paired_proposition F p <-> paired_boolean FE F p = true := paired_formula_agreement FE F.
""", "expected to have type"),
    "paired_observations_reject_existential_import": ("""
Example bad (FE : FunExt) : some_man_boolean FE empty_people_tables = true.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "paired_observations_reject_local_necessitation": ("""
Example bad (FE : FunExt) : paired_boolean FE varying_tables weather_necessary_o = true.
Proof. reflexivity. Qed.
""", "Unable to unify"),
}


def run(command, *, cwd=None, input=None, timeout=120):
    result = subprocess.run(command, cwd=cwd, input=input, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    return result.returncode, result.stdout


def require(command, **kwargs):
    status, output = run(command, **kwargs)
    if status or re.search(r"\bError:", output):
        raise RuntimeError(f"{' '.join(map(str, command))}\n{output}")
    return output


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(inspect=False):
    expected_project = ["-Q .. LegacyPTQ", "-Q ../montague_core MontagueProof",
                        "-Q . MontagueLegacy", *(unit + ".v" for unit in UNITS)]
    if (HERE / "_CoqProject").read_text().splitlines() != expected_project:
        raise RuntimeError("Local project and checker compile order differ")
    if digest(LEGACY) != LEGACY_SHA256:
        raise RuntimeError("Legacy source changed. Review the bridge before changing its explicit source pin.")
    version = require(["coqc", "--version"])
    if not re.search(r"version 8\.20\.1\b", version):
        raise RuntimeError("Coq 8.20.1 required")
    files, names = {}, []
    for unit in UNITS:
        source = HERE / (unit + ".v")
        declarations, warnings = verify.parse(source)
        proofs = [d for d in declarations if d["kind"] == "theorem"]
        if warnings or any(d.get("status") != "proved" for d in proofs):
            raise RuntimeError(f"Unbalanced or unfinished declarations in {source}")
        clean = verify.strip_comments(source.read_text())
        if re.search(r"\b(Admitted|Abort|Axiom|Parameter|Parameters|Conjecture|"
                     r"Classical_Prop|FunctionalExtensionality|PropExtensionality|"
                     r"ProofIrrelevance|Eqdep)\b|Unset\s+(Guard|Positivity|Universe)\s+Checking", clean):
            raise RuntimeError(f"New assumption or unsafe shortcut in {source}")
        qualified = [".".join(["MontagueLegacy", unit, *d["modpath"], d["name"]]) for d in proofs]
        names.extend(qualified)
        files[source.name] = {"sha256": digest(source), "proved_statements": qualified}
    suite_path = HERE / "OBSERVATION_SUITE.json"
    suite = json.loads(suite_path.read_text())
    cases = suite["cases"]
    if len({case["id"] for case in cases}) != len(cases):
        raise RuntimeError("Duplicate observation case id")
    for case in cases:
        if "MontagueLegacy." + case["proof"] not in names:
            raise RuntimeError(f"Observation case lacks a checked theorem: {case['id']}")
    assumptions = {}
    with tempfile.TemporaryDirectory(prefix="montague-legacy-check-") as directory:
        temporary = Path(directory)
        core, legacy, bridge = (temporary / part for part in ("core", "legacy", "bridge"))
        for folder in (core, legacy, bridge):
            folder.mkdir()
        flags = ["-Q", str(core), "MontagueProof", "-Q", str(legacy), "LegacyPTQ",
                 "-Q", str(bridge), "MontagueLegacy"]
        inputs = [(CORE / (unit + ".v"), core) for unit in CORE_UNITS] + [(LEGACY, legacy)]
        inputs.extend((HERE / (unit + ".v"), bridge) for unit in UNITS)
        for source, folder in inputs:
            destination = folder / source.name
            shutil.copy2(source, destination)
            require(["coqc", *flags, str(destination)], cwd=temporary)
            print(f"Compiled {source.name}", flush=True)
        require(["coqchk", "-silent", *flags, "LegacyPTQ.PTQ_deep2",
                 *("MontagueLegacy." + unit for unit in UNITS)], cwd=temporary)
        print("Kernel recheck passed", flush=True)
        for name in names:
            output = require(["coqtop", "-quiet", *flags], cwd=temporary,
                             input=PRELUDE + f"Print Assumptions {name}.\n")
            if "Closed under the global context" in output:
                dependencies = []
            elif "Axioms:" in output:
                block = output.split("Axioms:", 1)[1]
                dependencies = sorted(set(re.findall(r"(?m)^([A-Za-z_][\w.]*)\s*:", block)))
                if not dependencies:
                    raise RuntimeError(f"Unparsed assumption output for {name}:\n{output}")
            else:
                raise RuntimeError(f"Missing assumption audit for {name}:\n{output}")
            if set(dependencies) - ALLOWED:
                raise RuntimeError(f"Unexpected logical/global dependency in {name}: {dependencies}")
            if name.startswith(("MontagueLegacy.IndexSyntax.", "MontagueLegacy.IndexModels.",
                                "MontagueLegacy.ObservationBridge.", "MontagueLegacy.ObservationExamples.")) and dependencies:
                raise RuntimeError(f"Generic target lemma has global dependencies: {name}")
            assumptions[name] = ["LegacyPTQ." + item for item in dependencies]
        main = assumptions["MontagueLegacy.LegacyTranslation.legacy_interpretation_preservation"]
        if set(main) != {"LegacyPTQ." + item for item in ALLOWED}:
            raise RuntimeError("Main theorem's legacy parameter inventory changed")
        signatures = temporary / "Signatures.v"
        signatures.write_text(PRELUDE + """
Definition actual_legacy_boundary : FunExt -> forall G a (t : Old.IL G a) env i,
  target_eval (legacy_as_index_function t) (canonical_env G env) i =
  legacy_lift a (Old.eval t env i) := @legacy_open_preservation.
Definition actual_legacy_truth_boundary : FunExt -> forall G (p : Old.IL G Old.ty_t) env i,
  target_eval (legacy_as_index_function p) (canonical_env G env) i <-> Old.eval p env i :=
  @legacy_truth_preservation.
Definition equality_without_propositional_extensionality : forall a (x y : Old.Den a),
  (legacy_lift a x = legacy_lift a y) = (x = y) := @legacy_equality.
Definition assignments_are_unrestricted : forall G env,
  assignments_match (canonical_vars G) (canonical_env G env) env := @canonical_assignments_match.
Definition observation_boundary_without_funext : forall symbol target (M : wmodel symbol) T
  (constants : forall a, symbol a -> target (observation_type a))
  (lex : forall a, target a -> pdomain (windividuals M) (worlds M) T a)
  (before : T -> T -> Prop),
  (forall a c, observation_relation a (lex _ (constants a c)) (wlexical M a c)) ->
  forall G a (t : wtm symbol G a), observable t -> forall rho sigma,
  observation_envs rho sigma ->
  observation_relation a (peval lex before (observation_term constants t) rho) (weval M t sigma) :=
  @observation_preservation.
Definition general_truth_coverage_would_imply_classical_truth :
  (forall P : Prop, exists b : bool, P <-> b = true) -> ClassicalTruth :=
  total_truth_reflection_implies_classical_truth.
""")
        require(["coqc", *flags, str(signatures)], cwd=temporary)
        for name, (fixture, diagnostic) in NEGATIVE.items():
            source = temporary / "Rejected.v"
            source.write_text(PRELUDE + fixture)
            status, output = run(["coqc", *flags, str(source)], cwd=temporary)
            if status == 0 or diagnostic not in output:
                raise RuntimeError(f"Negative fixture {name} failed for the wrong reason:\n{output}")
            print(f"Rejected invalid fixture: {name}", flush=True)
        if inspect:
            session = temporary / "Inspect.v"
            session.write_text(PRELUDE)
            print("Opening Coq on the isolated checked build. Quit with Ctrl-D. Edits here are temporary.", flush=True)
            subprocess.run(["coqtop", "-quiet", *flags, "-load-vernac-source", str(session)],
                           cwd=temporary, check=True)
    return {
        "schema_version": 1, "coq_version": "8.20.1", "checkpoint": 7,
        "scope": "actual legacy IL preservation and a guarded Prop/Boolean observation relation",
        "legacy_source": {"path": "deep/PTQ_deep2.v", "sha256": digest(LEGACY), "modified": False},
        "core_dependencies": {unit + ".v": digest(CORE / (unit + ".v")) for unit in CORE_UNITS},
        "files": files, "proved_statement_count": len(names), "kernel_rechecked": True,
        "global_dependencies_by_statement": assumptions,
        "explicit_preservation_premises": ["FunExt"],
        "additional_logical_axioms_used": [],
        "truth": "Coq Prop, unchanged from legacy, not Boolean equivalence",
        "index": "World * Time; necessity fixes time, tense fixes world, up varies both",
        "coverage": {"all_legacy_il_constructors": True, "all_legacy_assignments": True,
                     "primitive_equality": True, "tense": True,
                     "english_source_adequacy": False, "gallin_equivalence": False,
                     "full_legacy_boolean_bridge": False, "target_proof_calculus": False,
                     "henkin_completeness": False},
        "observation_bridge": {
            "existing_evaluators": ["MontagueProof.Ty2Models.weval", "MontagueLegacy.IndexModels.peval"],
            "certificate": "actual Ty2 syntax; quantification at e or s, plus separately justified encoded falsity",
            "higher_order_composition": "allowed only under related lexical values and assignments",
            "truth_relation": "Prop denotation iff Boolean denotation equals true, not propositional equality",
            "preservation_requires_funext": False,
            "lexical_relation_required": True,
            "related_assignments_required": True,
            "model_quantifier_reflection_required": True,
            "finite_examples_require_funext_for_model_construction": True,
            "derivation_semantic_transfer_requires_funext": True,
            "unrestricted_proposition_or_predicate_quantification": False,
            "unrestricted_equality": False,
            "tense_comparison": False,
            "complete_legacy_translation_composed_with_observations": False,
            "scope_of_inference_agreement": "pointwise under related interpretations; not equality of all model classes",
        },
        "observation_suite": {"sha256": digest(suite_path), "cases": cases},
        "negative_fixtures_rejected": sorted(NEGATIVE), "source_review": "not independently reviewed",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--record", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--inspect", action="store_true", help="open coqtop on the fresh isolated build after checks")
    args = parser.parse_args()
    report = check(inspect=args.inspect)
    path = HERE / "verification.json"
    if args.record:
        path.write_text(json.dumps(report, indent=2) + "\n")
    elif args.check and json.loads(path.read_text()) != report:
        raise RuntimeError("Legacy checkpoint drift. Review changes before running --record.")
    print(f"PASS: {report['proved_statement_count']} new checked statements; legacy parameters separately recorded.")
    print("Legacy preservation has explicit FunExt; guarded observation preservation does not.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        sys.exit(str(error))
