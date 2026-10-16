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

UNITS = ("Types", "Target", "Translation", "Examples", "Independent", "Correspondence", "ModelExamples",
         "Minimal", "MinimalCorrespondence", "Untensed", "UntensedTranslation", "UntensedModels", "UntensedExamples")
DEPENDENCIES = ("Syntax", "Models", "Grammar", "Translation", "Meaning", "Postulates", "Examples",
                "Named", "PostulateFormulas")
PRELUDE = """From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Postulates Examples Named PostulateFormulas.
From MontagueGallin Require Import Types Target Translation Examples Independent Correspondence ModelExamples
  Minimal MinimalCorrespondence Untensed UntensedTranslation UntensedModels UntensedExamples.
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
Definition independent_target_can_reconstruct_a_source : forall F, coherent_model F -> model :=
  @reconstruct_model.
Definition target_roundtrip_covers_every_target_term : forall F (N : coherent_model F)
  (theta : coherent_assignment F) G a (p : target_term G a) rho,
  coherent_eval N theta p rho =
  target_eval (reconstruct_model N) (reconstruct_assignment N theta) p rho :=
  @target_roundtrip_interpretation.
Definition independently_stated_postulates_characterize_admissibility :
  forall F (N : coherent_model F), target_admissible N <-> admissible (reconstruct_model N) :=
  @admissible_model_correspondence.
Definition all_coherent_models_not_just_the_constructed_image : forall ps q,
  admissible_target_consequence ps q <-> source_consequence admissible ps q :=
  @admissible_consequence_correspondence.
Definition independent_satisfiability : forall ps,
  source_satisfiable ps <-> target_satisfiable ps := @admissible_satisfiability_correspondence.
Definition standard_carriers_do_not_require_a_ptq_frame : forall S (N : standard_model S),
  Type := fun S N => standard_indices N.
Definition minimal_preservation_covers_every_rich_target_term :
  forall (S P : gty -> Type) (E I : Type) (B : BooleanTruth)
    (lex : forall a, S a -> value_domain E I a)
    (free : forall a, P a -> value_domain E I a) (FE : FunExt)
    G a (p : gtm S P G a) rho,
    ceval B lex free (eliminate p) rho = geval B lex free p rho :=
  @elimination_preserves_interpretation.
Definition minimal_translation_covers_open_source_terms : forall M G a (p : tm G a) rho sigma i,
  core_eval (embed_model M) (target_free sigma) (minimal_translate p) (canonical_env rho) i =
  lift_value (carrier M) a (eval M p rho sigma i) := @minimal_open_preservation.
Definition minimal_syntax_has_an_exact_retraction : forall S P G a (p : ctm S P G a),
  eliminate (include_core p) = p := @eliminate_core_identity.
Definition minimal_target_postulates_still_characterize_admissibility : forall F (N : coherent_model F),
  core_admissible N <-> admissible (reconstruct_model N) := @minimal_admissible_model_correspondence.
Definition minimal_entailment_ends_in_actual_core_formulas : forall (ps : list (tm [] t)) (q : tm [] t),
  core_consequence (map minimal_translate ps) (minimal_translate q) <->
  source_consequence admissible ps q := @minimal_consequence_correspondence.
Definition minimal_satisfiability_ends_in_actual_core_formulas : forall ps,
  source_satisfiable ps <-> core_satisfiable (map minimal_translate ps) :=
  @minimal_satisfiability_correspondence.
Definition untensed_reconstruction_accepts_every_standard_model :
  standard_model source_symbol -> il_model := il_reconstruct.
Definition untensed_indices_are_not_replaced_by_products : forall N,
  il_indices (il_reconstruct N) = standard_indices N := fun N => eq_refl.
Definition untensed_backwards_covers_open_terms_and_all_models : forall
  (N : standard_model source_symbol) theta G a (p : itm G a)
  (rho : il_env (il_reconstruct N) G) i,
  core_standard_eval N theta (il_minimal_translate p) (il_canonical_env rho) i =
  il_lift (standard_entities N) (standard_indices N) a
    (ieval (il_reconstruct N) p rho (il_reconstruct_assignment theta) i) :=
  @untensed_backward_preservation.
Definition untensed_theories_are_not_restricted_to_finite_lists :
  forall (Gamma : il_formula -> Prop) (q : il_formula),
  il_standard_consequence Gamma q <->
  ty2_standard_consequence (translated_il_theory Gamma) (il_minimal_translate q) :=
  @untensed_standard_consequence.
Definition untensed_satisfiability_is_bidirectional : forall (Gamma : il_formula -> Prop),
  il_standard_satisfiable Gamma <-> ty2_standard_satisfiable (translated_il_theory Gamma) :=
  @untensed_standard_satisfiability.
Definition untensed_source_is_connected_to_existing_ptq : forall M G a (p : itm G a) rho sigma i,
  il_lift (entity (carrier M)) (index (carrier M)) a
    (ieval (forget_ptq_time M) p (forget_ptq_env rho) (forget_ptq_free sigma) i) =
  lift_value (carrier M) a (eval M (embed_il p) rho sigma i) := @ptq_untensed_interpretation.
Definition untensed_source_does_not_silently_erase_tense : forall G (p : tm G t),
  ~ exists q : itm G t, embed_il q = Will p := @no_untensed_representation_of_future.
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
    "unrestricted_standard_model_is_not_temporally_coherent": (
        "Definition bad : forall S, standard_model S -> model := @reconstruct_model.",
        "expected to have type"),
    "source_admissibility_cannot_be_dropped_from_embedding": (
        "Definition bad : forall M, target_admissible (embed_model M) := @embed_preserves_admissibility.",
        "expected to have type"),
    "target_postulates_cannot_be_dropped_from_reconstruction": (
        "Definition bad : forall F (N : coherent_model F), admissible (reconstruct_model N) := "
        "@admissible_model_correspondence.", "expected to have type"),
    "coherence_laws_cannot_be_omitted": (
        "Definition bad (F : frame) (B : BooleanTruth) (FE : FunExt) "
        "(L : forall a, source_symbol a -> gdomain F a) : coherent_model F := "
        "{| coherent_truth := B; coherent_extensionality := FE; coherent_lex := L |}.",
        "unresolved implicit arguments"),
    "countermodel_predictions_do_not_agree_without_coherence": (
        "Definition bad B FE : eval (one_moment_source B FE) future_tautology (empty_env _) "
        "(fun a _ => one_moment_zero a) (tt,tt) = true := source_future_tautology_false B FE.",
        "expected to have type"),
    "model_roundtrip_is_not_a_reverse_syntax_translation": (
        "Definition bad : forall G a, target_term G a -> tm [] t := @reconstruct_model.",
        "expected to have type"),
    "rich_connectives_are_not_minimal_constructors": (
        "Definition bad : core_term [] gt := GNeg (GEq (GCon (IndexedConstant e 0)) "
        "(GCon (IndexedConstant e 0))).", "expected to have type"),
    "minimal_truth_is_not_minimal_falsity": (
        "Example bad : @ctrue source_symbol source_parameter [] = cfalse. "
        "Proof. reflexivity. Qed.", "Unable to unify"),
    "universal_abbreviation_is_not_existential_abbreviation": (
        "Example bad : @call source_symbol source_parameter [] gt (CVar gz) = cex (CVar gz). "
        "Proof. reflexivity. Qed.", "Unable to unify"),
    "minimal_translation_cannot_discard_bound_variables": (
        "Example bad : eliminate (@GLam source_symbol source_parameter [] gt gt (GVar gz)) = "
        "CLam ctrue. Proof. reflexivity. Qed.", "Unable to unify"),
    "minimal_reconstruction_still_requires_postulates": (
        "Definition bad : forall F (N : coherent_model F), admissible (reconstruct_model N) := "
        "@minimal_admissible_model_correspondence.", "expected to have type"),
    "minimal_boolean_universal_is_not_true": (
        "Definition bad F (N : coherent_model F) theta : "
        "core_eval N theta (@call source_symbol source_parameter [] gt (CVar gz)) (gempty F) = true := "
        "proj1 (minimal_boolean_quantifiers_differ N theta).", "expected to have type"),
    "untensed_syntax_does_not_accept_future": (
        "Definition bad : itm [] t := Will (@Con [] t 0).", "expected to have type"),
    "untensed_reconstruction_is_not_full_ptq_reconstruction": (
        "Definition bad : standard_model source_symbol -> model := il_reconstruct.",
        "expected to have type"),
    "untensed_theorem_does_not_accept_arbitrary_tensed_formulas": (
        "Definition bad : forall p : tm [] t, is_untensed p = true := @embedded_il_is_untensed.",
        "expected to have type"),
    "untensed_roundtrip_does_not_recover_arbitrary_temporal_terms": (
        "Definition bad B FE : let N := plain_model B FE true in "
        "core_standard_eval (il_target (il_reconstruct N)) plain_assignment "
        "(@CCon source_symbol source_parameter [] _ FutureRelation) "
        "(value_empty bool bool) false false = true := "
        "proj2 (untensed_roundtrip_does_not_preserve_temporal_terms B FE).",
        "expected to have type"),
    "untensed_necessity_is_not_current_index_truth": (
        "Definition bad B FE : core_standard_eval (plain_model B FE true) plain_assignment "
        "(il_minimal_translate (IBox (@ICon [] t 0))) (value_empty bool bool) true = true := "
        "proj2 (arbitrary_index_necessity_sees_other_indices B FE true).", "expected to have type"),
    "untensed_index_domain_is_not_silently_a_product": (
        "Example bad B FE : standard_indices (plain_model B FE true) = (bool * bool)%type. "
        "Proof. reflexivity. Qed.", "Unable to unify"),
    "untensed_validity_correspondence_is_not_universal_validity": (
        "Definition bad : forall q, il_standard_consequence (fun _ => False) q := "
        "@untensed_standard_validity.", "expected to have type"),
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
        "schema_version": 1, "checkpoint": 4, "coq_version": "8.20.1",
        "scope": "Untensed IL and minimal Ty2 over arbitrary inhabited index domains, plus the retained coherent tensed PTQ correspondence",
        "files": files, "ptq_dependencies": dependencies,
        "proved_statement_count": len(names), "kernel_rechecked": True,
        "global_dependencies_by_statement": {name: [] for name in names},
        "global_dependencies_by_declaration": {name: [] for name in audited},
        "explicit_foundational_inputs": ["BooleanTruth and FunExt in source and target models"],
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
            "independent_standard_model_record": True,
            "general_entity_and_index_domains": True,
            "independent_temporally_coherent_model_correspondence": True,
            "all_target_terms_preserved_by_model_roundtrip": True,
            "translated_nine_postulate_families_characterize_admissibility": True,
            "admissible_consequence_and_satisfiability_correspondence": True,
            "countermodel_when_temporal_coherence_is_omitted": True,
            "all_independent_ty2_models": False,
            "elimination_of_connectives_into_gallin_minimal_syntax": True,
            "minimal_independent_evaluator": True,
            "minimal_elimination_all_signatures_carriers_environments": True,
            "minimal_english_countermodel_and_admissible_correspondences": True,
            "untensed_il_independent_syntax_and_evaluator": True,
            "untensed_preservation_all_open_terms": True,
            "untensed_source_compatibility_with_existing_ptq": True,
            "untensed_all_standard_models_over_arbitrary_entity_index_carriers": True,
            "untensed_consequence_and_satisfiability_arbitrary_theories": True,
            "untensed_minimal_target_syntax": True,
            "untensed_needs_temporal_coherence_or_ptq_postulates": False,
            "reverse_translation": False, "henkin_completeness": False,
            "gallin_axiomatic_calculus": False,
        },
        "model_class_boundary": {
            "covered": "all independent coherent valuations on all declared inhabited PTQ world-time frames",
            "temporal_relations": "same world and strictly later/earlier time",
            "admissibility": "nine source meaning-postulate families evaluated as translated target formulas",
            "unrestricted_standard_target_models": "defined but not included in the full tensed correspondence",
            "arbitrary_index_isomorphisms": False,
            "proof_system_correspondence": False,
        },
        "untensed_model_class_boundary": {
            "covered": "all independent standard models of the implemented target signature on arbitrary inhabited entity and index types",
            "source": "explicit untensed IL syntax embedded in the actual PTQ syntax; no Will or Has constructors",
            "function_spaces": "full internal Rocq function spaces, not external set equality or Henkin subdomains",
            "theories": "arbitrary predicates on formulas, not only finite premise lists",
            "postulates": "none imposed by the correspondence; object-language assumptions can be included in the theory",
            "temporal_symbols": "arbitrary and unused by translations; not recovered by the source-to-target round trip",
            "target_formulas": "minimal terms of type s -> t, applied to the arbitrary evaluation index",
            "full_tensed_or_proof_system_correspondence": False,
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
