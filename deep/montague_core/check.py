#!/usr/bin/env python3
"""Fresh isolated Coq build, kernel recheck, assumptions and negative fixtures.

No provider calls, PDFs or atlas grade changes. The report is deterministic.
Closed global context does not remove explicit theorem or model premises.
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
sys.path.insert(0, str(ROOT / "atlas_data"))
import verify  # Reuse the repository's Coq declaration parser, not its writer.

UNITS = ("Syntax", "Algebra", "Models", "Calculus", "Structural", "Contexts",
         "Examples", "StructuralExamples", "BooleanModels", "BooleanFinite",
         "BooleanEquality", "BooleanExamples", "Ty2Syntax", "Ty2Models",
         "Ty2Calculus", "Ty2Embedding", "Ty2Examples", "ILSyntax",
         "ILTranslation", "ILExamples")
PRELUDE = """From Coq Require Import List.
From MontagueProof Require Import Syntax Algebra Models Calculus Structural
  Contexts Examples StructuralExamples BooleanModels BooleanFinite BooleanEquality BooleanExamples.
From MontagueProof Require Import Ty2Syntax Ty2Models Ty2Calculus Ty2Embedding Ty2Examples.
From MontagueProof Require Import ILSyntax ILTranslation ILExamples.
Import ListNotations.
"""
NEGATIVE = {
    "classical_rule_requires_classical_mode": (
        """Example bad : derives constructive [neg (neg (@man_john []))] man_john.
Proof. apply d_double_negation; [reflexivity | apply d_assume; cbn; auto]. Qed.
""", "Unable to unify"),
    "capture_is_not_substitution": (
        """Example bad : instantiate (@Var word [entity] entity vz)
  (@Lam word [entity; entity] entity entity (Var (vs vz))) =
  @Lam word [entity] entity entity (Var vz).
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "one_name_cannot_be_generalized": (
        """Example bad : derives constructive [@man_john []] (All (App man (Var vz))).
Proof. apply d_all_intro. apply d_assume. cbn. auto. Qed.
""", "incomplete proof"),
    "classical_soundness_needs_its_premise": (
        """Definition bad (FE : FunExt) : forall symbol G H (p : tm symbol G truth),
  derives classical H p -> consequence H p := classical_sound FE.
""", "expected to have type"),
    "interleaved_lookup_must_shift": (
        """Example bad : lookup (context_var entity x_is_man)
  (@App word [entity; entity] entity truth man (Var vz)).
Proof. exact (lookup_var entity
  (lookup_here (context_var entity context_empty) man_x)). Qed.
""", "expected to have type"),
    "flattening_is_not_context_identity": (
        """Example bad : before_variable = after_variable.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "weakening_must_shift_conclusion": (
        """Example bad : derives constructive
  [@App word [truth; entity] entity truth man (Var (vs vz))]
  (All (@App word [entity; truth; entity] entity truth man (Var vz))).
Proof. exact (derivation_weakening truth split_fresh_variable). Qed.
""", "expected to have type"),
    "substitution_must_transform_assumptions": (
        """Example bad : derives constructive [@walk_john []]
  (All (@man_john [entity])).
Proof. exact (derivation_instantiation john split_fresh_variable). Qed.
""", "expected to have type"),
    "constant_true_is_not_a_universal_quantifier": (
        """Definition bad_quantifiers : BooleanQuantifiers unit.
Proof.
  refine {| bforall := fun _ _ => true |}.
  intros a p; split; auto. intros _ x. reflexivity.
Defined.
""", "Unable to unify"),
    "one_predicate_is_not_full_quantification": (
        """Example bad (FE : FunExt) : beval (bool_two_people FE)
  all_predicates_hold_of_john (bempty_env _) = true.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "boolean_countermodel_rejects_existential_import": (
        """Example bad (FE : FunExt) : beval (bool_no_men FE)
  (@a_man_walks []) (bempty_env _) = true.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "distinct_predicates_are_not_leibniz_equal": (
        """Example bad (FE : FunExt) : beval (bool_two_people FE)
  (leibniz_equal (@man []) walk) (bempty_env _) = true.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "decision_construction_keeps_its_premise": (
        """Definition bad : forall E : Type, BooleanQuantifiers E := decision_quantifiers.
""", "expected to have type"),
    "worlds_are_not_entities": (
        """Definition bad : wtm world_word [] we := @actual [].
""", "expected to have type"),
    "actual_truth_does_not_imply_necessity": (
        """Example bad (FE : FunExt) : weval (two_worlds FE)
  (necessarily (@weather [])) (wempty_env _) = true.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "local_assumptions_do_not_authorize_necessitation": (
        """Example bad : wderives constructive [at_world (@weather []) actual]
  (necessarily weather).
Proof. apply wd_all_intro. apply wd_assume. cbn. auto. Qed.
""", "incomplete proof"),
    "actual_agreement_is_not_concept_identity": (
        """Example bad (FE : FunExt) :
  weval (two_worlds FE) (@rigid_concept []) (wempty_env _) =
  weval (two_worlds FE) (@person_concept []) (wempty_env _).
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "freezing_does_not_re_evaluate_at_another_world": (
        """Example bad (FE : FunExt) :
  weval (two_worlds FE) (at_world frozen_concept alternative) (wempty_env _) =
  weval (two_worlds FE) (at_world (@person_concept []) alternative) (wempty_env _).
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "world_substitution_must_avoid_capture": (
        """Example bad : winstantiate (@WVar world_word [ws] ws wz)
  (@WLam world_word [ws; ws] ws ws (WVar (wvs wz))) =
  @WLam world_word [ws] ws ws (WVar wz).
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "il_translation_must_shift_assigned_variables": (
        """Example bad :
  explicit_world il_constants (@ILam il_word [] ie (intens ie) (IUp (IVar iz)))
    (@ivar_embed []) (WConst IActual) = WLam (WLam (WVar wz)).
Proof. reflexivity. Qed.
""", "expected to have type"),
    "il_index_sensitive_substitution_is_not_beta": (
        """Example bad (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) il_frozen (iempty_env _) true false =
  ieval il_constants (il_two_worlds FE) il_recomputed (iempty_env _) true false.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "il_up_down_is_not_an_unconditional_inverse": (
        """Example bad (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) (IUp (IDown il_nonrigid_intension))
    (iempty_env _) true false =
  ieval il_constants (il_two_worlds FE) il_nonrigid_intension (iempty_env _) true false.
Proof. reflexivity. Qed.
""", "Unable to unify"),
    "il_world_binder_cannot_reassign_a_variable": (
        """Example bad (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) (@IUp il_word [ie] ie (IVar iz))
    (@iextend il_target (il_two_worlds FE) [] ie (iempty_env _) true) true false = false.
Proof. reflexivity. Qed.
""", "Unable to unify"),
}


def run(command, *, cwd=None, input=None, timeout=90):
    result = subprocess.run(command, cwd=cwd, input=input, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=timeout)
    return result.returncode, result.stdout


def require_success(command, **kwargs):
    status, output = run(command, **kwargs)
    if status or re.search(r"\bError:", output):
        raise RuntimeError(f"{' '.join(map(str, command))}\n{output}")
    return output


def check():
    for executable in ("coqc", "coqtop", "coqchk"):
        if not shutil.which(executable):
            raise RuntimeError(f"Missing required executable: {executable}")
    version = require_success(["coqc", "--version"])
    if not re.search(r"version 8\.20\.1\b", version):
        raise RuntimeError(f"This checkpoint requires Coq 8.20.1, found:\n{version}")
    expected_project = ["-Q . MontagueProof", *(unit + ".v" for unit in UNITS)]
    if (HERE / "_CoqProject").read_text().splitlines() != expected_project:
        raise RuntimeError("Local _CoqProject and checker compile order differ")

    files = {}
    names = []
    for unit in UNITS:
        source = HERE / (unit + ".v")
        declarations, warnings = verify.parse(source)
        if warnings:
            raise RuntimeError(f"Unbalanced Coq scopes in {source}: {warnings}")
        proofs = [d for d in declarations if d["kind"] == "theorem"]
        if any(d.get("status") != "proved" for d in proofs):
            raise RuntimeError(f"Unfinished theorem in {source}")
        forbidden = re.search(
            r"\b(Admitted|Abort|Axiom|Parameter|Parameters|Conjecture)\b|"
            r"Unset\s+(Guard|Positivity|Universe)\s+Checking|\bClassical_Prop\b|"
            r"\bFunctionalExtensionality\b|\bProofIrrelevance\b|\bEqdep\b",
            verify.strip_comments(source.read_text()))
        if forbidden:
            raise RuntimeError(f"Forbidden shortcut in {source}: {forbidden.group()}")
        qualified = [".".join(["MontagueProof", unit, *d["modpath"], d["name"]])
                     for d in proofs]
        names.extend(qualified)
        files[source.name] = {
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "proved_statements": qualified,
        }

    with tempfile.TemporaryDirectory(prefix="montague-core-check-") as directory:
        temporary = Path(directory)
        flags = ["-Q", str(temporary), "MontagueProof"]
        for unit in UNITS:
            source = temporary / (unit + ".v")
            shutil.copy2(HERE / source.name, source)
            require_success(["coqc", *flags, str(source)], cwd=temporary)
            print(f"Compiled {unit}.v", flush=True)
        require_success(["coqchk", "-silent", *flags,
                         *("MontagueProof." + u for u in UNITS)],
                        cwd=temporary, timeout=180)
        print("Kernel recheck passed", flush=True)
        query = PRELUDE + "\n".join(f"Print Assumptions {name}." for name in names) + "\n"
        output = require_success(["coqtop", "-quiet", *flags], cwd=temporary, input=query)
        if "Axioms:" in output or output.count("Closed under the global context") != len(names):
            raise RuntimeError(f"Unexpected assumption audit:\n{output}")

        # Check the stated assumption boundary against the actual theorem types.
        signatures = temporary / "Signatures.v"
        signatures.write_text(PRELUDE + """
Definition constructive_boundary (FE : FunExt) :
  forall symbol G H (p : tm symbol G truth),
  derives constructive H p -> consequence H p := constructive_sound FE.
Definition classical_boundary (FE : FunExt) (CL : ClassicalTruth) :
  forall symbol G H (p : tm symbol G truth),
  derives classical H p -> consequence H p := classical_sound FE CL.
Definition renaming_without_semantic_premises :
  forall symbol L G H (p : tm symbol G truth),
  derives L H p -> forall D (r : ren G D),
  derives L (map (fun q => rename q r) H) (rename p r) := @derivation_renaming.
Definition substitution_without_semantic_premises :
  forall symbol L G H (p : tm symbol G truth),
  derives L H p -> forall D (s : sub symbol G D),
  derives L (map (fun q => subst q s) H) (subst p s) := @derivation_substitution.
Definition conversion_without_semantic_premises :
  forall symbol G a (t u : tm symbol G a), beta t u ->
  forall D (s : sub symbol G D), beta (subst t s) (subst u s) := @beta_substitution.
Definition context_bridge_without_semantic_premises :
  forall symbol L G (C : mixed symbol G) p,
  mixed_derives L C p <-> derives L (hypotheses C) p := @mixed_split_equivalence.
Definition lookup_shift_boundary :
  lookup (context_var entity x_is_man) (weaken man_x) :=
  lookup_var entity (lookup_here (context_var entity context_empty) man_x).
Definition boolean_soundness_boundary (FE : FunExt) :
  forall symbol G H (p : tm symbol G truth),
  derives classical H p -> bconsequence H p := classical_boolean_sound FE.
Definition finite_models_without_classical_decision :
  forall symbol E, FunExt -> finite E ->
  (forall a, symbol a -> bdomain E a) -> bmodel symbol := @finite_model.
Definition arbitrary_quantifiers_require_classical_decision :
  ClassicalDecision -> forall E : Type, BooleanQuantifiers E := decision_quantifiers.
Definition finite_equality_boundary : forall symbol E (FE : FunExt) (F : finite E)
  (lex : forall a, symbol a -> bdomain E a) G a (u v : tm symbol G a) rho,
  beval (finite_model FE F lex) (leibniz_equal u v) rho = true <->
  beval (finite_model FE F lex) u rho = beval (finite_model FE F lex) v rho :=
  @finite_leibniz_equality.
Definition world_soundness_boundary (FE : FunExt) :
  forall symbol L G H (p : wtm symbol G wt),
  wderives L H p -> wconsequence H p := @world_derivation_sound FE.
Definition core_embedding_boundary (FE : FunExt) : forall symbol target
  (constants : forall a, symbol a -> target (embed_type a)) L G H (p : tm symbol G truth),
  derives L H p ->
  wconsequence (map (embed_term constants) H) (embed_term constants p) :=
  @core_derivation_world_sound FE.
Definition finite_world_model_boundary : forall symbol E W,
  FunExt -> finite E -> finite W ->
  (forall a, symbol a -> wdomain E W a) -> wmodel symbol := @world_finite_model.
Definition arbitrary_world_model_boundary : forall symbol E W,
  ClassicalDecision -> inhabited E -> inhabited W ->
  (forall a, symbol a -> wdomain E W a) -> wmodel symbol := @world_decision_model.
Definition il_preservation_boundary : forall symbol target
  (constants : forall a, symbol a -> target (world_type a)) (M : wmodel target),
  FunExt -> forall G a (t : itm symbol G a) D (r : ivmap G D)
  (w : wtm target D ws) (rho : wenv M D) (sigma : ienv M G),
  (forall b v, rho _ (r b v) = sigma b v) ->
  weval M (explicit_world constants t r w) rho =
  ieval constants M t sigma (weval M w rho) := @explicit_world_preservation.
Definition il_cancellation_without_extensionality : forall symbol target
  (constants : forall a, symbol a -> target (world_type a)) (M : wmodel target)
  G a (t : itm symbol G a) rho w,
  ieval constants M (IDown (IUp t)) rho w = ieval constants M t rho w :=
  @down_up_cancellation.
Definition il_reverse_cancellation_keeps_rigidity : forall symbol target
  (constants : forall a, symbol a -> target (world_type a)) (M : wmodel target),
  FunExt -> forall G a (t : itm symbol G (intens a)),
  index_rigid constants M t -> forall rho w,
  ieval constants M (IUp (IDown t)) rho w = ieval constants M t rho w :=
  @up_down_for_rigid_intensions.
""")
        require_success(["coqc", *flags, str(signatures)], cwd=temporary)
        for name, (fixture, diagnostic) in NEGATIVE.items():
            source = temporary / "Rejected.v"
            source.write_text(PRELUDE + fixture)
            status, output = run(["coqc", *flags, str(source)], cwd=temporary)
            if status == 0 or diagnostic not in output:
                raise RuntimeError(f"Negative fixture {name} failed for the wrong reason:\n{output}")
            print(f"Rejected invalid fixture: {name}", flush=True)

    return {
        "schema_version": 1,
        "coq_version": "8.20.1",
        "scope": "extensional C, selected Ty2 and world-only IL interpretation preservation; not full PTQ, legacy IL adequacy or Henkin completeness",
        "files": files,
        "proved_statement_count": len(names),
        "kernel_rechecked": True,
        "global_axiom_dependencies": [],
        "explicit_soundness_premises": {
            "constructive": ["FunExt"],
            "classical": ["FunExt", "ClassicalTruth"],
        },
        "boolean_model_boundary": {
            "truth_domain": "bool",
            "arrow_domains": "full Coq function spaces; not external set-model adequacy",
            "soundness": ["FunExt", "model includes total quantifiers with reflection proofs"],
            "finite_model_construction": ["FunExt", "finite inhabited entity-domain data"],
            "arbitrary_entity_domain_construction": ["ClassicalDecision", "inhabited entity domain"],
            "finite_leibniz_equality": ["FunExt", "finite model construction"],
            "henkin_models_implemented": False,
            "possible_worlds_in_boolean_core": False,
            "prop_boolean_adequacy_proved": False,
        },
        "world_layer": {
            "possible_worlds_implemented": True,
            "truth_domain": "bool",
            "entity_domains": "constant across worlds",
            "necessity": "quantification over all worlds; no accessibility relation",
            "soundness": ["FunExt", "reflected total model quantifiers"],
            "core_bridge": "term interpretation and semantic consequence preservation",
            "core_derivation_translation_proved": False,
            "conservativity_proved": False,
            "legacy_il_translation_proved": False,
            "tense_implemented": False,
            "henkin_completeness_proved": False,
        },
        "structural_results_require_semantic_premises": False,
        "il_translation": {
            "source": "specified world-only Boolean IL fragment with rigid typed constants",
            "target": "selected Ty2 with explicit world terms",
            "preservation": "all typed terms under related environments and interpreted current-world term",
            "premises": ["FunExt", "shared full internal domains and reflected model quantifiers"],
            "source_evaluator_independent_of_translation": True,
            "down_up_cancellation": "unconditional",
            "up_down_cancellation": "proved for index-rigid intensions, given FunExt",
            "unrestricted_il_beta_rule": False,
            "legacy_ptq_bridge_proved": False,
            "gallin_equivalence_proved": False,
            "reverse_translation_proved": False,
            "source_proof_calculus_implemented": False,
            "tense_or_primitive_equality_implemented": False,
        },
        "context_bridge_scope": "intrinsic interleaved and split C judgments; not named-source adequacy",
        "negative_fixtures_rejected": sorted(NEGATIVE),
        "source_review": "not independently reviewed",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--record", action="store_true", help="write the verified checkpoint")
    mode.add_argument("--check", action="store_true", help="compare against the checkpoint")
    args = parser.parse_args()
    report = check()
    checkpoint = HERE / "verification.json"
    if args.record:
        checkpoint.write_text(json.dumps(report, indent=2) + "\n")
    elif args.check and json.loads(checkpoint.read_text()) != report:
        raise RuntimeError("Checkpoint drift. Review the changes, then run check.py --record.")
    print(f"PASS: {report['proved_statement_count']} checked statements; no global axiom dependencies.")
    print("General soundness still has the explicit premises recorded in verification.json.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        sys.exit(str(error))
