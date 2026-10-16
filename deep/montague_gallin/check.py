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
         "Minimal", "MinimalCorrespondence", "Untensed", "UntensedTranslation", "UntensedModels", "UntensedExamples",
         "Substitution", "Calculus", "CalculusConnections", "CalculusExamples",
         "ILCore", "ILCalculus", "ILCalculusExamples", "ILProofTranslation",
         "SyntaxAlgebra", "ILCompileSyntax", "ILFullProofTranslation", "ProofDischarge", "FullCompilerExamples")
DEPENDENCIES = ("Syntax", "Models", "Grammar", "Translation", "Meaning", "Postulates", "Examples",
                "Named", "PostulateFormulas")
PRELUDE = """From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Postulates Examples Named PostulateFormulas.
From MontagueGallin Require Import Types Target Translation Examples Independent Correspondence ModelExamples
  Minimal MinimalCorrespondence Untensed UntensedTranslation UntensedModels UntensedExamples
  Substitution Calculus CalculusConnections CalculusExamples
  ILCore ILCalculus ILCalculusExamples ILProofTranslation
  SyntaxAlgebra ILCompileSyntax ILFullProofTranslation ProofDischarge FullCompilerExamples.
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
Definition substitution_sound_for_every_open_body : forall (S P : gty -> Type) E I
  (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  G a b (p : ctm S P (a :: G) b) (q : ctm S P G a) rho,
  ceval B lex theta (CApp (CLam p) q) rho = ceval B lex theta (subst0 p q) rho :=
  @beta_interpretation.
Definition replacement_requires_all_hole_environments : forall (S P : gty -> Type) E I
  (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  D a G b (C : ccontext S P D a G b) (p q : ctm S P D a),
  (forall rho, ceval B lex theta p rho = ceval B lex theta q rho) ->
  forall tau, ceval B lex theta (plug C p) tau = ceval B lex theta (plug C q) tau :=
  @replacement_preserves_global_equality.
Definition soundness_is_for_explicit_derivation_trees : forall (S P : gty -> Type) E I
  (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  G (p : ctm S P G gt), Derivation p -> forall rho, ceval B lex theta p rho = true :=
  @ty2_derivations_sound.
Definition derivation_to_il_is_soundness_not_a_reverse_proof_translation : forall p,
  Derivation (il_proof_formula p) -> il_standard_consequence (fun _ => False) p :=
  @derived_il_translation_is_valid.
Definition checked_object_proof_example : Derivation (il_proof_formula il_constant_reflexivity) :=
  il_constant_reflexivity_proof.
Definition consistency_still_records_foundational_inputs : forall (B : BooleanTruth) (FE : FunExt) S P G,
  Derivation (@cfalse S P G) -> False := @ty2_no_derivation_of_false.
Definition source_modal_closure_guarantees_all_indices : forall M sigma G a (p : ltm G a),
  ModallyClosed p -> forall rho i j, lval M p rho sigma i = lval M p rho sigma j :=
  @modally_closed_is_index_independent.
Definition source_axioms_have_all_models_soundness : forall M sigma G (p : ltm G t),
  ILAxiom p -> forall rho i, lval M p rho sigma i = true := @il_axioms_sound.
Definition source_rules_have_all_environments_and_indices_soundness : forall M sigma G (p : ltm G t),
  ILDerivation p -> forall rho i, lval M p rho sigma i = true := @il_derivations_sound.
Definition source_assumptions_use_finite_implication_theorems : forall G (Gamma : ltm G t -> Prop) p,
  ILFrom Gamma p -> forall M sigma rho i,
  (forall q, Gamma q -> lval M q rho sigma i = true) -> lval M p rho sigma i = true :=
  @il_from_assumptions_sound.
Definition modal_beta_cannot_drop_the_side_condition : forall (B : BooleanTruth) (FE : FunExt),
  ILDerivation forbidden_modal_beta -> False := @forbidden_modal_beta_has_no_derivation.
Definition axiom_five_cannot_drop_variable_or_rigidity_conditions : forall B FE,
  lval (modal_test_model B FE) (il_axiom5 (@LCon [] (intens t) 0) (LUp lfalse))
    (il_empty _) (modal_test_assignment B FE) false = false :=
  @axiom_five_cannot_accept_arbitrary_intension_terms.
Definition assumptions_correspond_semantically_in_target : forall Gamma p, ILFrom Gamma p ->
  ty2_standard_consequence (translated_il_theory (included_il_theory Gamma))
    (il_minimal_translate (include_il p)) := @il_assumptions_imply_translated_consequence.
Definition proof_compiler_reuses_the_existing_formula_translation : forall G a (p : ltm G a),
  il_minimal_translate (include_il p) = CLam (il_at p) := @il_at_is_existing_translation_body.
Definition restricted_proof_inputs_really_are_source_proofs : forall G (p : ltm G t),
  ILPointwiseProof p -> ILDerivation p := @pointwise_proof_is_source_derivation.
Definition restricted_proof_compiler_outputs_trees_without_semantic_inputs : forall G (p : ltm G t),
  ILPointwiseProof p -> Derivation (il_at p) := @compile_pointwise_proof.
Definition general_compiler_agrees_syntactically_with_established_translation :
  forall G a (p : ltm G a) D (r : variable_map G D) (i : gvar D gs),
  lcompile p (variable_values r) (CVar i) =
  eliminate (compile (embed_il (include_il p)) r (GVar i)) := @lcompile_agrees_with_existing.
Definition all_source_axioms_produce_target_proofs : forall G (p : ltm G t), ILAxiom p ->
  forall D (r : variable_map G D) i, Derivation (lcompile p (variable_values r) i) :=
  @compile_all_axioms.
Definition every_source_derivation_produces_target_proof : forall G (p : ltm G t),
  ILDerivation p -> Derivation (il_at p) := @compile_il_proof.
Definition arbitrary_variable_mappings_and_index_terms : forall G (p : ltm G t),
  ILDerivation p -> forall D (r : variable_map G D)
  (i : ctm source_symbol source_parameter D gs), Derivation (lcompile p (variable_values r) i) :=
  @compile_il_general.
Definition discharged_proofs_translate_without_semantic_inputs : forall G (Gamma : ltm G t -> Prop) p,
  ILFrom Gamma p -> Ty2From (compiled_premises Gamma) (il_at p) := @compile_il_from.
Definition discharge_preserves_implication_structure : forall G (ps : list (ltm G t)) p,
  il_at (il_implication_chain ps p) = ty2_implication_chain (map (@il_at G t) ps) (il_at p) :=
  @compile_implication_chain.
Definition full_translation_does_not_make_forbidden_beta_derivable :
  forall (B : BooleanTruth) (FE : FunExt), Derivation (il_at forbidden_modal_beta) -> False :=
  @forbidden_modal_beta_has_no_target_derivation.
Definition nested_lambda_and_intension_example : Derivation (il_at nested_scope_formula) :=
  nested_scope_target_proof.
Definition capture_avoiding_exchange_example : Derivation (il_at exchange_formula) := exchange_target_proof.
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
    "host_equality_is_not_an_object_derivation": (
        "Definition bad : Derivation (@CEq no_symbols no_symbols [] gt ctrue ctrue) := eq_refl.",
        "expected to have type"),
    "semantic_soundness_is_not_completeness": (
        "Definition bad (S P : gty -> Type) E I (B : BooleanTruth) (FE : FunExt) "
        "(lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a) : "
        "forall G (p : ctm S P G gt), (forall rho, ceval B lex theta p rho = true) -> Derivation p := "
        "@ty2_derivations_sound S P E I B FE lex theta.", "expected to have type"),
    "beta_substitution_cannot_capture_outer_variable": (
        "Example bad : subst0 (@CLam no_symbols no_symbols [gt; gt] gt gt (CVar (gvs gz))) "
        "(CVar gz) = @CLam no_symbols no_symbols [gt] gt gt (CVar gz). "
        "Proof. reflexivity. Qed.", "Unable to unify"),
    "pointwise_equality_is_not_a_derivation_for_replacement": (
        "Definition bad B : Derivation (@CEq no_symbols no_symbols [gt] gt (CVar gz) ctrue) := "
        "proj1 (pointwise_equality_cannot_justify_lambda_replacement B).", "expected to have type"),
    "axiom_one_requires_a_variable_not_a_compound_term": (
        "Definition bad : Derivation (@axiom1 no_symbols no_symbols [] (CLam (CVar gz))) := "
        "ByAxiom (A1 (CLam (CVar gz))).", "expected to have type"),
    "local_equality_does_not_make_lambda_functions_equal": (
        "Definition bad B : ceval B no_valuation no_valuation "
        "(@CLam no_symbols no_symbols [] gt gt (CVar gz)) (value_empty bool bool) = "
        "ceval B no_valuation no_valuation (@CLam no_symbols no_symbols [] gt gt ctrue) "
        "(value_empty bool bool) := proj2 (pointwise_equality_cannot_justify_lambda_replacement B).",
        "expected to have type"),
    "relative_consistency_does_not_supply_its_own_foundations": (
        "Definition bad : forall S P G, Derivation (@cfalse S P G) -> False := "
        "@ty2_no_derivation_of_false.", "expected to have type"),
    "source_primitive_syntax_has_no_primitive_box": (
        "Definition bad : ltm [] t := IBox (@ICon [] t 0).", "expected to have type"),
    "source_constant_is_not_modally_closed": (
        "Definition bad : ModallyClosed (@LCon [] t 0) := MCUp (@LCon [] t 0).",
        "expected to have type"),
    "source_modal_beta_requires_a_side_condition": (
        "Definition bad : ILAxiom forbidden_modal_beta := IL_AS47 (LVar vz) (LCon 0).",
        "expected to have type"),
    "source_axiom_five_requires_variables": (
        "Definition bad := IL_A5 (@LCon [] (intens t) 0) (LCon 1).",
        "expected to have type"),
    "source_proof_is_not_a_host_equality": (
        "Definition bad : ILDerivation (LEq (@LCon [] t 0) (LCon 0)) := eq_refl.",
        "expected to have type"),
    "source_hypothesis_discharge_is_not_an_unconditional_theorem": (
        "Definition bad G (Gamma : ltm G t -> Prop) p : ILFrom Gamma p -> ILDerivation p := fun H => H.",
        "expected to have type"),
    "source_beta_exchange_cannot_capture_outer_variable": (
        "Example bad : lrename (@LVar [t; t] t (vs vz)) lswap = LVar (vs vz). "
        "Proof. reflexivity. Qed.", "Unable to unify"),
    "source_invalid_modal_beta_has_no_proof": (
        "Definition bad B FE : ILDerivation forbidden_modal_beta := "
        "forbidden_modal_beta_has_no_derivation B FE.", "expected to have type"),
    "restricted_proof_translation_is_not_the_general_case": (
        "Definition bad : forall G (p : ltm G t), ILDerivation p -> Derivation (il_at p) := "
        "@compile_pointwise_proof.", "expected to have type"),
    "source_semantic_translation_is_not_a_target_derivation": (
        "Definition bad (p : ltm [] t) (H : ILDerivation p) : Derivation (il_at p) := "
        "il_derivation_implies_translated_validity H.", "expected to have type"),
    "full_compiler_does_not_accept_semantic_truth_as_a_source_proof": (
        "Definition bad (p : ltm [] t) (H : il_standard_consequence (fun _ => False) (include_il p)) : "
        "Derivation (il_at p) := compile_il_proof H.", "expected to have type"),
    "full_compiler_cannot_omit_source_proof": (
        "Definition bad : forall G (p : ltm G t), Derivation (il_at p) := @compile_il_proof.",
        "expected to have type"),
    "full_compiler_is_not_a_reverse_proof_translation": (
        "Definition bad : forall G (p : ltm G t), Derivation (il_at p) -> ILDerivation p := "
        "@compile_il_proof.", "expected to have type"),
    "full_compiler_cannot_prove_an_unrestricted_modal_beta_instance": (
        "Definition bad : Derivation (il_at forbidden_modal_beta) := "
        "compile_il_proof (ILByAxiom (IL_AS47 (LVar vz) (MCUp (@LCon [] t 0)))).",
        "expected to have type"),
    "discharge_compiler_does_not_discard_the_hypotheses": (
        "Definition bad : forall G (Gamma : ltm G t -> Prop) p, ILFrom Gamma p -> Derivation (il_at p) := "
        "@compile_il_from.", "expected to have type"),
    "discharge_does_not_broaden_local_hypotheses_to_global_theorems": (
        "Definition bad (S P : gty -> Type) G (Gamma : ctm S P G gt -> Prop) p : "
        "Ty2From Gamma p -> Derivation p := fun H => H.", "expected to have type"),
    "syntactic_modal_closure_is_still_required": (
        "Definition bad : forall G a (p : ltm G a) D (r : lvalues G D) i j, "
        "lcompile p r i = lcompile p r j := @lcompile_modal_closed.", "expected to have type"),
    "full_index_body_is_not_a_closed_proposition": (
        "Definition bad : ctm source_symbol source_parameter [] gt := il_at nested_scope_formula.",
        "expected to have type"),
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
        "schema_version": 1, "checkpoint": 7, "coq_version": "8.20.1",
        "scope": "Every implemented IL derivation compiles to an unchanged Ty2 derivation; all source axioms, R1-R8 and finite implication discharge",
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
            "gallin_axiomatic_calculus": True,
            "ty2_capture_avoiding_substitution": True,
            "ty2_four_source_axiom_families": True,
            "ty2_single_occurrence_replacement_under_binders": True,
            "ty2_explicit_derivation_trees": True,
            "ty2_standard_model_soundness": True,
            "ty2_derived_translation_implies_il_validity": True,
            "ty2_completeness": False,
            "source_il_primitive_syntax": True,
            "source_il_modally_closed_terms_and_rigidity": True,
            "source_il_alternative_AS41_AS47_R1_R8_calculus": True,
            "source_il_all_derivations_standard_soundness": True,
            "source_il_finite_implication_discharge_soundness": True,
            "source_il_side_condition_countermodels": True,
            "source_il_restricted_pointwise_proof_translation": True,
            "source_il_general_proof_translation": True,
            "source_il_all_axioms_and_R1_R8_compiled": True,
            "source_il_discharged_proofs_compiled": True,
            "proof_compiler_has_semantic_or_completeness_inputs": False,
            "proof_compiler_syntactically_matches_existing_translation": True,
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
        "proof_calculus_boundary": {
            "source": "Gallin p. 60, A1-A3, AS4 and R, in a typed locally indexed presentation",
            "axiom_instances": "A1-A3 use contextual or named variables; AS4 uses capture-avoiding term substitution",
            "inference_rules": "axiom introduction and one-occurrence replacement only; equality reasoning is derived",
            "assumptions": "theorem calculus, not local-hypothesis consequence; R uses equality valid for all hole environments",
            "soundness": "all derivations, signatures, assignments and environments in the full internal Boolean/function-space semantics",
            "source_connection": "a derivation of the actual translated IL formula implies its standard semantic validity",
            "not_claimed": ["completeness", "Henkin soundness/completeness", "IL+D to Ty2+D proof translation",
                            "named/indexed calculus equivalence", "unrestricted local-assumption rule"],
        },
        "source_proof_calculus_boundary": {
            "source": "Gallin pp. 19-20: A1-A3, AS4.1-AS4.7, A5, AS6 and R1-R8",
            "syntax": "primitive IL with derived logical macros and locally indexed binders",
            "modal_beta": "AS4.7 requires the syntactic ModallyClosed predicate from p. 14",
            "axiom_five": "variables only; validity is separately proved for modally closed intensions",
            "hypotheses": "finite nested implication theorem as in p. 20, not unrestricted local replacement",
            "soundness": "all implemented ILDerivation trees, models, assignments, environments and indices",
            "proof_compiler": "every ILDerivation to actual Ty2 Derivation, with no semantic or completeness inputs",
            "compiled_fragment": "all ILAxiom constructors and all R1-R8; arbitrary contexts and primitive IL terms",
            "hypothesis_compiler": "ILFrom Gamma p to Ty2From of translated premises and conclusion",
            "not_yet_compiled": "none within the implemented ILDerivation and ILFrom datatypes",
            "not_claimed": ["reverse proof translation", "description principles D", "Theorem 8.3",
                            "Henkin completeness", "equivalence to a separately encoded named calculus"],
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
