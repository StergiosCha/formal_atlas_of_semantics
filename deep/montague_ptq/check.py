#!/usr/bin/env python3
"""Isolated source-first PTQ build, kernel check and assumption audit.

No source PDF is required to reproduce the proofs. Its hash and page map are
recorded in SOURCE_MAP.md. This checker does not amend the frozen checkpoints.
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
import verify

UNITS = ("Syntax", "Models", "Grammar", "Translation", "Meaning", "Postulates", "Examples", "Named", "PostulateFormulas", "Surface", "Catalogue", "Reductions", "Scope", "FreshNames", "ReadingForms", "SurfaceInvariant", "VacuousInsertion", "SurfaceAmendment", "SurfaceAmendmentSafety", "ReadingClassification", "AdditionalReadings", "PronounSupport", "GrammarRenaming", "ReadingNormalization", "RenamingNormalization", "SurfaceInverse", "SearchRank")
PRELUDE = "From Coq Require Import List Bool.\nFrom MontaguePTQ Require Import " + " ".join(UNITS) + ".\nImport ListNotations.\n"
NEGATIVE = {
    "iv_does_not_return_an_extra_intension": "Example bad : category_type IV = arr ic (intens t). Proof. reflexivity. Qed.\n",
    "sentences_are_not_proposition_intensions": "Example bad : category_type ct = intens t. Proof. reflexivity. Qed.\n",
    "two_english_categories_are_not_identical": "Example bad : IV = CN. Proof. reflexivity. Qed.\n",
    "truth_is_not_coq_prop": "Definition bad (M : model) : domain (carrier M) t := True.\n",
    "classical_truth_is_not_supplied_silently": "Definition bad : BooleanTruth := decision_truth.\n",
    "model_construction_keeps_extensionality": "Definition bad (B : BooleanTruth) : model := sample_model B.\n",
    "necessity_now_is_not_ptq_box": "Example bad B FE : eval (sample_model B FE) (Box (@Con [] t 0)) (empty_env _) (sample_assignment B FE) (tt,false) = true. Proof. exact (proj2 (necessity_now_is_not_ptq_necessity B FE)). Qed.\n",
    "every_is_not_existential": "Example bad : translate_closed every_man_walks = translate_closed a_man_walks. Proof. reflexivity. Qed.\n",
    "relative_clause_cannot_capture_noun_pronouns": "Example bad : translate_closed relative_with_collision = wrongly_captured_relative. Proof. reflexivity. Qed.\n",
    "the_two_unicorn_translations_differ": "Example bad : translate_closed seeks_unicorn_dicto = translate_closed seeks_unicorn_re. Proof. reflexivity. Qed.\n",
    "source_reduction_keeps_model_postulates": "Definition bad : forall M sigma i, eval M (translate_closed every_man_walks) (empty_env M) sigma i = true <-> forall u, word_value M (lcn man) i (fun _ => u) = true -> word_value M (liv walk) i (fun _ => u) = true := every_man_source_reduction.\n",
    "named_shadowing_does_not_bind_the_outer_variable": "Example bad : embed_named (NL e 0 (NL e 0 (NV e 0))) = @Lam [] e (arr e e) (Lam (Var (vs vz))). Proof. reflexivity. Qed.\n",
    "missing_surface_occurrence_is_not_silently_a_noop": "Example bad : surface (s14 some_unicorn 9 bill_walks) = surface bill_walks. Proof. reflexivity. Qed.\n",
    "first_verb_rule_does_not_inflect_both_conjuncts": "Example bad : surface (joint_control try_to wish_to) = Some printed_try_wish. Proof. reflexivity. Qed.\n",
    "seeking_paraphrase_keeps_postulate_nine": "Definition bad : forall M sigma i, eval M (translate_closed seeks_unicorn_dicto) (empty_env M) sigma i = eval M (translate_closed tries_unicorn_dicto) (empty_env M) sigma i := seeking_trying_dicto_equal.\n",
    "referential_witness_theorem_does_not_cover_dicto_cases": "Definition bad : forall M r i, Forall (fun u : tree ct => denote M u r i = true -> exists x, word_value M (lcn unicorn) i x = true) dicto_cases := @referential_analyses_have_witnesses.\n",
    "entity_reduction_keeps_ordinary_noun_restriction": "Definition bad : forall M, admissible M -> forall c P i, dvalue M a_or_an (word_value M (lcn c) i) i P = true <-> exists u, cn_star M c i u = true /\\ P i (rigid M u) = true := indefinite_reduction.\n",
    "quantifier_scopes_are_not_identical_formulas": "Example bad : rf_surface_scope = rf_inverse_scope. Proof. reflexivity. Qed.\n",
    "editorial_freshness_includes_bound_names": "Example bad : editorial_index (names_at (NL ic 0 (NV ic 4)) ic) = 0. Proof. reflexivity. Qed.\n",
    "editorial_even_index_is_not_even_raw_number": "Example bad : editorial_index [0;2] = 1. Proof. reflexivity. Qed.\n",
    "printed_coordination_is_not_generated_by_the_literal_rules": "Definition bad : forall u : tree ct, surface u = Some printed_try_wish := printed_try_wish_has_no_analysis.\n",
    "all_formula_pairs_keep_admissibility": "Definition bad : forall M sigma i, Forall (fun pair => eval M (translate_closed (fst pair)) (empty_env M) sigma i = neval M (snd pair) sigma i) reading_pairs := all_listed_reading_formulas.\n",
    "amended_policy_is_not_the_literal_policy": "Example bad : amended_surface (joint_control try_to wish_to) = surface (joint_control try_to wish_to). Proof. reflexivity. Qed.\n",
    "control_complements_are_not_finite": 'From Coq Require Import Strings.String. Open Scope string_scope.\nExample bad : amended_surface wish_unicorn_dicto = Some ["John";"wishes";"to";"find";"a";"unicorn";"and";"eats";"it"]. Proof. reflexivity. Qed.\n',
    "amendment_does_not_duplicate_negation": 'From Coq Require Import Strings.String. Open Scope string_scope.\nExample bad : amended_surface (s17 negative (s1_name john) (s12 conjunction (s1_word (liv walk)) (s1_word (liv talk)))) = Some ["John";"does";"not";"walk";"and";"does";"not";"talk"]. Proof. reflexivity. Qed.\n',
    "amended_missing_target_is_not_a_noop": "Example bad : amended_surface (s14 some_unicorn 9 bill_walks) = amended_surface bill_walks. Proof. reflexivity. Qed.\n",
    "erasure_preservation_is_not_surface_equality": "Definition bad : forall A (u : tree A), amended_surface u = surface u := @amendment_changes_only_verb_forms.\n",
    "coverage_is_not_every_tree_realizing_every_sentence": "Definition bad : forall text, In text (map fst catalogue ++ [printed_try_wish; printed_wish_try]) -> forall u : tree ct, amended_surface u = Some text := amended_printed_examples_covered.\n",
    "amended_formula_certificate_keeps_admissibility": "Definition bad : forall text us (u : tree ct), In (text,us) amended_catalogue -> In u us -> amended_surface u = Some text /\\ exists p, In (u,p) reading_pairs /\\ forall M sigma i, eval M (translate_closed u) (empty_env M) sigma i = eval M (embed_named p) (empty_env M) sigma i := @amended_catalogue_source_formulas.\n",
    "same_surface_is_not_reading_equivalence": "Definition bad : reading_equivalent belief_external_conjunction belief_unicorn_dicto := eq_refl.\n",
    "original_pair_is_not_exhaustive": "Definition bad B FE : reading_exhaustive (@amended_surface ct) belief_words [belief_unicorn_dicto; belief_unicorn_re] := proj2 (registered_belief_pair_not_exhaustive B FE).\n",
    "revised_registry_coverage_is_not_exhaustiveness": "Definition bad : catalogue_exhaustive (@amended_surface ct) revised_catalogue := revised_catalogue_surface_checks.\n",
    "external_conjunction_is_not_internal_belief": "Example bad : translate_closed belief_external_conjunction = translate_closed belief_unicorn_re. Proof. reflexivity. Qed.\n",
    "belief_separation_keeps_foundational_inputs": "Definition bad : ~ reading_equivalent belief_external_conjunction belief_unicorn_dicto := additional_belief_reading_is_distinct.\n",
    "index_zero_and_index_one_are_not_interchangeable": "Example bad : rename_tree (fun _ => 1) (s1_pronoun 0) = s1_pronoun 0. Proof. reflexivity. Qed.\n",
    "capture_safe_renaming_requires_injectivity": "Definition bad : forall M f A (u : tree A) r i, denote M (rename_tree f u) r i = denote M u (fun n => r (f n)) i := @rename_tree_interpretation.\n",
    "extensional_lifting_does_not_include_seeking": "Definition bad M (A : admissible M) : forall Q x i, word_value M (ltv seek) i Q x = Q i (fun j y => word_value M (ltv seek) j (fun k P => P k y) x) := @extensional_object_lifting M A seek I.\n",
    "support_is_not_always_empty": "Example bad : support (s1_pronoun 7) = []. Proof. reflexivity. Qed.\n",
    "genuine_merge_is_not_erased": "Example bad : normalize_renamings genuine_merge_example = s11 conjunction (s4 (s1_pronoun 0) (s1_word (liv walk))) (s4 (s1_pronoun 1) (s1_word (liv talk))). Proof. reflexivity. Qed.\n",
    "normalization_is_not_always_tree_identity": "Example bad : normalize_renamings (s14 (s1_pronoun 0) 0 bill_walks) = s14 (s1_pronoun 0) 0 bill_walks. Proof. reflexivity. Qed.\n",
    "pure_relabelling_keeps_capture_avoidance": "Example bad : normalize_renamings (s14 (s1_pronoun 1) 0 capture_sensitive_body) = s14 (s1_name john) 1 (s11 conjunction (s4 (s1_pronoun 1) (s1_word (liv walk))) (s4 (s1_pronoun 1) (s1_word (liv talk)))). Proof. reflexivity. Qed.\n",
    "freshening_keeps_its_freshness_premise": "Definition bad : forall b p n k q xs, realize q = Some xs -> tree_equivalent (quantify b p k (rename_tree (swap_index n k) q)) (quantify b p n q) := @freshen_binding_equivalent.\n",
    "normal_form_existence_is_not_catalogue_completeness": "Definition bad : catalogue_exhaustive (@amended_surface ct) revised_catalogue := @every_successful_tree_has_merge_normal_form.\n",
    "inverse_replacement_keeps_freshness_premise": "Definition bad : forall n g out body, In body (restore_pronouns n g out) -> map (replace_pronoun n g) body = out := @replacement_inverse_sound.\n",
    "merge_inverse_excludes_empty_splits": "Example bad : merge_inverses 0 1 [indexed 1 subject_case] = [[indexed 1 subject_case]]. Proof. reflexivity. Qed.\n",
    "merge_inverse_excludes_entire_class_relabelling": "Example bad : merge_inverses 0 1 [indexed 1 subject_case] = [[indexed 0 subject_case]]. Proof. reflexivity. Qed.\n",
    "relative_freshening_keeps_body_freshness": "Definition bad : forall c n k p body, realize p = Some body -> tree_equivalent (s3 c k (rename_tree (swap_index n k) p)) (s3 c n p) := @freshen_relative_equivalent.\n",
    "merge_rank_decrease_requires_a_genuine_merge": "Definition bad : forall n k body, rank_before body (map (rename_pronoun n k) body) := @genuine_merge_strictly_decreases_rank.\n",
    "well_founded_measure_is_not_a_complete_parser": "Definition bad : catalogue_exhaustive (@amended_surface ct) revised_catalogue := inverse_rank_well_founded.\n",
}


def run(cmd, cwd, input=None):
    p = subprocess.run(cmd, cwd=cwd, input=input, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode or re.search(r"(?m)^Error:", p.stdout):
        raise RuntimeError(p.stdout)
    return p.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--record", action="store_true")
    args = parser.parse_args()
    if "version 8.20.1" not in run(["coqc", "--version"], HERE):
        raise RuntimeError("Expected Coq 8.20.1")
    files, names, audit_names = {}, [], []
    expected_project = ['-Q . MontaguePTQ', *(u + '.v' for u in UNITS)]
    if (HERE / '_CoqProject').read_text().splitlines() != expected_project:
        raise RuntimeError('Local project file and checker compile order differ')
    for unit in UNITS:
        path = HERE / (unit + ".v")
        text = verify.strip_comments(path.read_text())
        if re.search(r"\b(Admitted|Abort|Axiom|Parameter|Parameters|Conjecture)\b|"
                     r"Unset\s+(Guard|Positivity|Universe)\s+Checking|"
                     r"\b(Classical_Prop|FunctionalExtensionality|ProofIrrelevance|Eqdep)\b", text):
            raise RuntimeError(f"Forbidden shortcut: {path.name}")
        decls, warnings = verify.parse(path)
        if warnings:
            raise RuntimeError(f'Unbalanced source scopes: {path.name}: {warnings}')
        proved = [d for d in decls if d['kind'] == 'theorem']
        if any(d.get('status') != 'proved' for d in proved):
            raise RuntimeError(f"Incomplete proof: {path.name}")
        qualified = ['.'.join(['MontaguePTQ', unit, *d['modpath'], d['name']]) for d in proved]
        names.extend(qualified)
        audited = ['.'.join(['MontaguePTQ', unit, *d['modpath'], d['name']])
                   for d in decls if d['kind'] in ('theorem', 'definition')]
        audit_names.extend(audited)
        files[path.name] = {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                            "proved_statements": qualified, "audited_declarations": audited}
    with tempfile.TemporaryDirectory(prefix="montague-ptq-") as directory:
        temp = Path(directory)
        flags = ["-Q", str(temp), "MontaguePTQ"]
        for unit in UNITS:
            shutil.copy2(HERE / (unit + '.v'), temp)
            run(["coqc", *flags, str(temp / (unit + '.v'))], temp)
            print(f"Compiled {unit}.v", flush=True)
        run(["coqchk", "-silent", *flags, *("MontaguePTQ." + u for u in UNITS)], temp)
        print("Kernel recheck passed", flush=True)
        audit = run(["coqtop", "-quiet", *flags], temp,
                    PRELUDE + '\n'.join(f'Print Assumptions {n}.' for n in audit_names))
        if 'Axioms:' in audit or audit.count('Closed under the global context') != len(audit_names):
            raise RuntimeError('Assumption audit failed:\n' + audit)
        signatures = temp / 'Signatures.v'
        signatures.write_text(PRELUDE + '''
Definition complete_tree_translation : forall A, tree A -> tm [] (category_type A) := @translate_closed.
Definition complete_semantic_correspondence : forall M A (u : tree A) G
  (r : pronouns G) rho sigma s, represents M r rho sigma s -> forall i,
  eval M (translate u r) rho sigma i = denote M u s i := @translation_interpretation.
Definition full_postulate_model_exists : ClassicalDecision -> FunExt -> exists M, admissible M :=
  source_model_conditions_are_satisfiable.
Definition source_box_boundary : forall M G (p : tm G t) rho sigma i,
  eval M (Box p) rho sigma i = true <-> forall w j, eval M p rho sigma (w,j) = true := @necessity_clause.
Definition named_semantic_correspondence : forall M a (p : ntm a) sigma i,
  eval M (embed_named p) (empty_env M) sigma i = neval M p sigma i := @embed_named_interpretation.
Definition object_postulates_characterize_models : forall M sigma i,
  postulate_family (fun p => eval M (embed_named p) (empty_env M) sigma i = true)
  <-> admissible M := compiled_postulates_exact.
Definition listed_referential_analyses_need_witnesses : forall M r i,
  Forall (fun u : tree ct => denote M u r i = true ->
    exists x, word_value M (lcn unicorn) i x = true) re_cases := @referential_analyses_have_witnesses.
Definition all_twenty_six_source_formula_pairs : forall M, admissible M -> forall sigma i,
  Forall (fun pair => eval M (translate_closed (fst pair)) (empty_env M) sigma i =
    eval M (embed_named (snd pair)) (empty_env M) sigma i) reading_pairs := all_listed_compiled_formulas.
Definition exact_editorial_relative_operation : forall M zeta n phi sigma i,
  eval M (embed_named (editorial_relative zeta n phi)) (empty_env M) sigma i =
  eval M (intrinsic_relative zeta n phi) (empty_env M) sigma i := editorial_intrinsic_relative_agree.
Definition unbounded_generation_refutation : forall u : tree ct,
  surface u <> Some printed_try_wish := printed_try_wish_has_no_analysis.
Definition blanket_source_generation_claim_is_false : ~ section4_generation_claim :=
  section4_generation_claim_refuted.
Definition literal_policy_is_unchanged : forall A (u : tree A),
  policy_surface first_verb_only u = surface u := @first_policy_surface_exact.
Definition amended_registered_examples_have_certified_witnesses : forall text,
  In text (map fst catalogue ++ [printed_try_wish; printed_wish_try]) ->
  exists u p, amended_surface u = Some text /\\ In (u,p) reading_pairs /\\
    forall M, admissible M -> forall sigma i,
      eval M (translate_closed u) (empty_env M) sigma i =
      eval M (embed_named p) (empty_env M) sigma i := amended_printed_examples_covered.
Definition amendment_only_changes_inflection : forall A (u : tree A),
  erase_result (amended_tokens u) = erase_result (realize u) := @amendment_changes_only_verb_forms.
Definition amendment_cannot_repair_a_failed_analysis : forall A (u : tree A),
  amended_surface u = None <-> surface u = None := @amendment_preserves_surface_failure.
Definition old_belief_list_refuted_under_both_policies : forall (B : BooleanTruth) (FE : FunExt),
  ~ reading_exhaustive (@surface ct) belief_words [belief_unicorn_dicto; belief_unicorn_re] /\\
  ~ reading_exhaustive (@amended_surface ct) belief_words [belief_unicorn_dicto; belief_unicorn_re] :=
  registered_belief_pair_not_exhaustive.
Definition revised_source_formulas_all_models : forall text us u,
  In (text,us) revised_catalogue -> In u us ->
  amended_surface u = Some text /\\ exists p, In (u,p) revised_reading_pairs /\\
  forall M, admissible M -> forall sigma i,
    eval M (translate_closed u) (empty_env M) sigma i =
    eval M (embed_named p) (empty_env M) sigma i := revised_catalogue_source_formulas.
Definition revised_registry_has_no_duplicate_readings : forall (B : BooleanTruth) (FE : FunExt),
  Forall (fun entry => readings_irredundant (snd entry)) revised_catalogue :=
  revised_candidates_pairwise_inequivalent.
Definition all_tree_visible_semantic_support : forall A (u : tree A) xs,
  realize u = Some xs -> incl (support u) (visible_indices xs) := @support_is_visible.
Definition all_amended_tree_visible_semantic_support : forall A (u : tree A) xs,
  amended_tokens u = Some xs -> incl (support u) (visible_indices xs) := @amended_support_is_visible.
Definition support_controls_all_interpretations : forall M A (u : tree A) r s,
  agree_on M r s (support u) -> forall i, denote M u r i = denote M u s i :=
  @interpretation_depends_on_support.
Definition safe_grammar_renaming_preserves_meaning : forall M f,
  injective_name_map f -> forall A (u : tree A) r i,
  denote M (rename_tree f u) r i = denote M u (fun n => r (f n)) i := @rename_tree_interpretation.
Definition safe_grammar_renaming_preserves_both_policies : forall f,
  injective_name_map f -> forall policy A (u : tree A),
  plan policy (rename_tree f u) = rename_plan f (plan policy u) := @rename_tree_plan.
Definition lifting_keeps_lexical_scope : forall M, admissible M ->
  forall v, extensional_tv v -> forall Q x i,
  word_value M (ltv v) i Q x = Q i (fun j y => word_value M (ltv v) j (fun k P => P k y) x) :=
  @extensional_object_lifting.
Definition normalization_preserves_every_model_and_both_policies : forall A (u : tree A),
  tree_equivalent (normalize_renamings u) u := @normalize_renamings_equivalent.
Definition all_successful_trees_have_merge_normal_forms : forall A (u : tree A) xs,
  realize u = Some xs -> exists v : tree A, merge_normal v /\\
    tree_size v <= tree_size u /\\ tree_equivalent v u := @every_successful_tree_has_merge_normal_form.
Definition capture_safe_binder_freshening : forall b p n k q xs,
  realize q = Some xs -> ~ In k (visible_indices xs) ->
  tree_equivalent (quantify b p k (rename_tree (swap_index n k) q)) (quantify b p n q) :=
  @freshen_binding_equivalent.
Definition canonical_output_index_preserves_meaning : forall b p n q alpha body out,
  realize p = Some alpha -> realize q = Some body -> f10 n alpha body = Some out ->
  exists q' : tree (binding_type b), tree_size q' = tree_size q /\\
    tree_equivalent (quantify b p (fresh_index out) q') (quantify b p n q) := @canonical_binding_index.
Definition nonbare_local_inverse_covers_every_successful_insertion : forall n alpha body out,
  bare_pronoun alpha = None -> f10 n alpha body = Some out ->
  In (alpha,body) (insertion_inverses n out) := @nonbare_insertion_inverse_complete.
Definition nonbare_local_inverse_is_sound_when_fresh : forall n alpha body out,
  ~ In n (visible_indices out) -> bare_pronoun alpha = None ->
  In (alpha,body) (insertion_inverses n out) -> f10 n alpha body = Some out :=
  @nonbare_insertion_inverse_sound.
Definition bare_local_inverse_covers_every_genuine_merge : forall n k body,
  In n (visible_indices body) -> In k (visible_indices body) ->
  In body (merge_inverses n k (map (rename_pronoun n k) body)) := @genuine_merge_inverse_complete.
Definition canonical_bare_inverse_is_sound_and_proper : forall k out body,
  In body (merge_inverses (fresh_index out) k out) ->
  f10 (fresh_index out) [indexed k subject_case] body = Some out /\\
  In (fresh_index out) (visible_indices body) /\\ In k (visible_indices body) := @canonical_merge_inverse_sound.
Definition relative_binder_freshening_preserves_the_noun : forall c n k p body,
  realize p = Some body -> ~ In k (visible_indices body) ->
  tree_equivalent (s3 c k (rename_tree (swap_index n k) p)) (s3 c n p) := @freshen_relative_equivalent.
Definition search_measure_is_well_founded : well_founded rank_before := inverse_rank_well_founded.
Definition every_genuine_bare_inverse_step_decreases : forall k out body,
  In body (merge_inverses (fresh_index out) k out) -> rank_before body out := @canonical_merge_inverse_rank.
Definition every_nonbare_np_body_step_decreases : forall (p : tree NP) n alpha body out,
  realize p = Some alpha -> bare_pronoun alpha = None ->
  f10 n alpha body = Some out -> rank_before body out := @nonbare_np_body_rank.
''')
        run(['coqc', *flags, str(signatures)], temp)
        for name, fixture in NEGATIVE.items():
            p = temp / 'Invalid.v'
            p.write_text(PRELUDE + fixture)
            result = subprocess.run(["coqc", *flags, str(p)], cwd=temp, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
            if not result.returncode or not re.search(r'Unable to unify|expected to have type', result.stdout):
                raise RuntimeError(f"Invalid fixture was not rejected as intended: {name}\n{result.stdout}")
            print(f"Rejected invalid fixture: {name}", flush=True)
    report = {"coq_version": "8.20.1", "source_sha256": "45ec6a0fa9bdac5c4fe92baf839aa90f60001a99a769a64fa7fa5c13f290b2e8",
              "files": files, "proved_statement_count": len(names), "kernel_rechecked": True,
              "global_axiom_dependencies": [], "negative_fixtures_rejected": sorted(NEGATIVE),
              "explicit_foundations": ["BooleanTruth (entails excluded middle)", "FunExt in model"],
              "scope": {"all_typed_analysis_rule_families": True,
                        "independent_tree_interpretation_theorem": True,
                        "all_nine_semantic_postulate_families": True,
                        "admissible_model_constructed": True,
                        "object_postulate_satisfaction_equivalence": True,
                        "named_source_to_intrinsic_interpretation": True,
                        "surface_operations_with_explicit_preconditions": True,
                        "surface_source_convention_review_complete": False,
                        "surface_counts_policy": "first_verb_only",
                        "section4_matching_surface_sentences": 18,
                        "section4_matching_analysis_witnesses": 24,
                        "section4_coordination_surface_discrepancies": 2,
                        "nonreferential_reading_pairs_separated": 5,
                        "all_section4_listed_analysis_formula_pairs": True,
                        "listed_analysis_formula_pair_count": 26,
                        "quantifier_scope_pair_separated": True,
                        "all_section4_readings_classified": False,
                        "literal_section4_generation_claim": "refuted",
                        "unbounded_ungenerated_printed_examples": 2,
                        "vacuous_noop_insertion_countermodel": True,
                        "exact_editorial_fresh_name_algorithm_correspondence": True,
                        "external_set_model_adequacy": False,
                        "surface_amendment": {
                            "policy": "coordinated_present",
                            "scope": "S4 present head inflection; S17 tense/sign unchanged",
                            "literal_policy_equivalence_all_trees": True,
                            "changes_only_verb_forms_all_trees": True,
                            "realization_failure_preserved_all_trees": True,
                            "registered_surface_sentences": 20,
                            "registered_analysis_formula_pairs": 26,
                            "registered_coverage_and_formula_certificate": True,
                            "all_readings_classified": False,
                            "independent_source_review": False},
                        "reading_classification": {
                            "original_belief_pair_exhaustiveness": "refuted_under_both_policies",
                            "additional_belief_reading": "conjunction_outside_belief",
                            "revised_registered_sentences": 20,
                            "revised_registered_analysis_formula_pairs": 27,
                            "revised_candidates_pairwise_inequivalent": True,
                            "all_tree_visible_semantic_support": True,
                            "all_tree_capture_safe_renaming_both_policies": True,
                            "all_tree_redundant_bare_binding_normalization": True,
                            "normalization_preserves_both_policies_and_all_models": True,
                            "canonical_fresh_binding_index": True,
                            "local_f10_inverse_soundness_and_completeness": True,
                            "relative_binder_capture_safe_freshening": True,
                            "inverse_rank_well_founded": True,
                            "f10_body_inverse_rank_decrease": True,
                            "all_readings_classified": False,
                            "finite_search_report": "reading_exploration.json",
                            "finite_search_completeness_proved": False}},
              "source_review": "primary text consulted; independent review pending"}
    checkpoint = HERE / 'verification.json'
    if args.record:
        checkpoint.write_text(json.dumps(report, indent=2) + '\n')
    elif json.loads(checkpoint.read_text()) != report:
        raise RuntimeError("Verification drift; review before recording")
    print(f"PASS: {len(names)} checked statements; explicit model premises retained.")


if __name__ == '__main__':
    main()
