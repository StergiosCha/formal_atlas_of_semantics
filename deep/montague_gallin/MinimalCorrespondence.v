(* The semantic and admissible-model results now end in Gallin's minimal
   syntax, not in a target with extra primitive logical constructors. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Named Postulates PostulateFormulas Examples.
From MontagueGallin Require Import Types Target Translation Examples Independent Correspondence ModelExamples Minimal.
Import ListNotations.
Set Implicit Arguments.

Definition core_term := ctm source_symbol source_parameter.
Definition minimal_translate {G a} (p : tm G a) := eliminate (translate_intension p).
Definition minimal_english A (u : tree A) := eliminate (english_translation u).

Definition core_standard_eval {S P} (N : standard_model S) (theta : standard_assignment N P)
  G a (p : ctm S P G a) rho := ceval (standard_truth N) (standard_lex N) theta p rho.
Arguments core_standard_eval {S P} N theta {G a} p rho.
Theorem elimination_in_every_standard_model {S P} (N : standard_model S) theta
  G a (p : gtm S P G a) rho :
  core_standard_eval N theta (eliminate p) rho = standard_eval N theta p rho.
Proof. apply elimination_preserves_interpretation; exact (standard_extensionality N). Qed.

Definition core_eval F (N : coherent_model F) (theta : coherent_assignment F)
  G a (p : core_term G a) rho := ceval (coherent_truth N) (@coherent_lex F N) theta p rho.
Arguments core_eval {F} N theta {G a} p rho.
Theorem core_interpretation_agrees F (N : coherent_model F) theta G a
  (p : target_term G a) rho :
  core_eval N theta (eliminate p) rho = coherent_eval N theta p rho.
Proof. apply elimination_preserves_interpretation; exact (coherent_extensionality N). Qed.

Theorem minimal_open_preservation M G a (p : tm G a) rho sigma i :
  core_eval (embed_model M) (target_free sigma) (minimal_translate p) (canonical_env rho) i =
  lift_value (carrier M) a (eval M p rho sigma i).
Proof. unfold minimal_translate; rewrite core_interpretation_agrees.
  apply open_preservation. Qed.
Theorem minimal_backward_preservation F (N : coherent_model F) theta a (p : tm [] a) i :
  core_eval N theta (minimal_translate p) (gempty F) i =
  lift_value F a (eval (reconstruct_model N) p (empty_env _)
    (reconstruct_assignment N theta) i).
Proof. unfold minimal_translate; rewrite core_interpretation_agrees.
  apply backward_preservation. Qed.
Theorem minimal_english_preservation M A (u : tree A) sigma i :
  core_eval (embed_model M) (target_free sigma) (minimal_english u) (gempty (carrier M)) i =
  lift_value (carrier M) (category_type A) (denote M u (fun n => sigma ic (2*n)) i).
Proof. unfold minimal_english; rewrite core_interpretation_agrees.
  apply english_interpretation_preserved. Qed.

Definition core_postulates_at F (N : coherent_model F) theta i :=
  postulate_family (fun p =>
    core_eval N theta (minimal_translate (embed_named p)) (gempty F) i = true).
Definition core_admissible F (N : coherent_model F) :=
  forall theta i, core_postulates_at N theta i.
Theorem core_postulates_agree F (N : coherent_model F) theta i :
  core_postulates_at N theta i <-> target_postulates_at N theta i.
Proof. unfold core_postulates_at, target_postulates_at; apply postulate_family_extensional.
  intro p; unfold minimal_translate; rewrite core_interpretation_agrees; reflexivity. Qed.
Theorem core_admissibility_agrees F (N : coherent_model F) :
  core_admissible N <-> target_admissible N.
Proof. split; intros H theta i; apply core_postulates_agree; apply H. Qed.
Theorem minimal_admissible_model_correspondence F (N : coherent_model F) :
  core_admissible N <-> admissible (reconstruct_model N).
Proof. rewrite core_admissibility_agrees; apply admissible_model_correspondence. Qed.

(* These two predicates take actual minimal target formulas, not source
   syntax. Their correspondence theorems are scoped to translated formulas. *)
Definition core_formula := core_term [] (garr gs gt).
Definition core_consequence (ps : list core_formula) (q : core_formula) :=
  forall F (N : coherent_model F), core_admissible N -> forall theta i,
    (forall p, In p ps -> core_eval N theta p (gempty F) i = true) ->
    core_eval N theta q (gempty F) i = true.
Definition core_satisfiable (ps : list core_formula) :=
  exists F (N : coherent_model F), core_admissible N /\ exists theta i,
    forall p, In p ps -> core_eval N theta p (gempty F) i = true.

Lemma translated_premises_agree F (N : coherent_model F) theta i (ps : list (tm [] t)) :
  (forall p, In p (map minimal_translate ps) -> core_eval N theta p (gempty F) i = true) <->
  (forall p, In p ps -> coherent_eval N theta (translate_intension p) (gempty F) i = true).
Proof.
  split.
  - intros H p Hp; specialize (H (minimal_translate p) (in_map _ _ _ Hp)).
    unfold minimal_translate in H; rewrite core_interpretation_agrees in H; exact H.
  - intros H p Hp; apply in_map_iff in Hp; destruct Hp as [q [E Hq]]; subst p.
    unfold minimal_translate; rewrite core_interpretation_agrees; apply H; exact Hq.
Qed.
Theorem core_consequence_agrees (ps : list (tm [] t)) (q : tm [] t) :
  core_consequence (map minimal_translate ps) (minimal_translate q) <->
  admissible_target_consequence ps q.
Proof.
  split; intros H F N HN theta i HP.
  - assert (Q : core_eval N theta (minimal_translate q) (gempty F) i = true).
    { apply H; [apply core_admissibility_agrees; exact HN |].
      apply translated_premises_agree; exact HP. }
    unfold minimal_translate in Q; rewrite core_interpretation_agrees in Q; exact Q.
  - unfold minimal_translate; rewrite core_interpretation_agrees.
    apply H; [apply core_admissibility_agrees; exact HN |].
    apply translated_premises_agree; exact HP.
Qed.
Theorem minimal_consequence_correspondence (ps : list (tm [] t)) (q : tm [] t) :
  core_consequence (map minimal_translate ps) (minimal_translate q) <->
  source_consequence admissible ps q.
Proof. rewrite core_consequence_agrees; apply admissible_consequence_correspondence. Qed.
Theorem core_satisfiability_agrees (ps : list (tm [] t)) :
  core_satisfiable (map minimal_translate ps) <-> target_satisfiable ps.
Proof.
  split; intros [F [N [HN [theta [i HP]]]]]; exists F, N; split.
  - apply core_admissibility_agrees; exact HN.
  - exists theta, i; apply translated_premises_agree; exact HP.
  - apply core_admissibility_agrees; exact HN.
  - exists theta, i; apply translated_premises_agree; exact HP.
Qed.
Theorem minimal_satisfiability_correspondence ps :
  source_satisfiable ps <-> core_satisfiable (map minimal_translate ps).
Proof. rewrite core_satisfiability_agrees; apply admissible_satisfiability_correspondence. Qed.

Theorem minimal_temperature_countermodel (B : BooleanTruth) (FE : FunExt) :
  let M := sample_model B FE in let N := embed_model M in
  let theta := target_free (sample_assignment B FE) in
  core_admissible N /\
  core_eval N theta (minimal_english temperature_is_ninety) (gempty (carrier M)) (tt,false) = true /\
  core_eval N theta (minimal_english temperature_rises) (gempty (carrier M)) (tt,false) = true /\
  core_eval N theta (minimal_english ninety_rises) (gempty (carrier M)) (tt,false) = false.
Proof.
  cbn zeta; split.
  - apply core_admissibility_agrees; apply (@embed_preserves_admissibility (sample_model B FE)).
    exact (proj1 (temperature_countermodel_transported B FE)).
  - unfold minimal_english; rewrite !core_interpretation_agrees.
    exact (proj2 (temperature_countermodel_transported B FE)).
Qed.
Theorem minimal_temperature_inference_invalid (B : BooleanTruth) (FE : FunExt) :
  ~ core_consequence
    (map minimal_translate [translate_closed temperature_is_ninety; translate_closed temperature_rises])
    (minimal_translate (translate_closed ninety_rises)).
Proof. rewrite core_consequence_agrees; apply target_temperature_inference_invalid; assumption. Qed.

(* Regression: quantifying over t must not confuse forall with exists. *)
Theorem minimal_boolean_quantifiers_differ F (N : coherent_model F) theta :
  core_eval N theta (@call source_symbol source_parameter [] gt (CVar gz)) (gempty F) = false /\
  core_eval N theta (@cex source_symbol source_parameter [] gt (CVar gz)) (gempty F) = true.
Proof.
  unfold core_eval; split.
  - rewrite ceval_all by exact (coherent_extensionality N).
    change (truth (coherent_truth N) (forall x : bool, x = true) = false).
    destruct (truth (coherent_truth N) (forall x : bool, x = true)) eqn:H; auto.
    apply (proj1 (truth_spec (coherent_truth N) _)) in H.
    specialize (H false); discriminate.
  - rewrite ceval_ex by exact (coherent_extensionality N).
    apply (proj2 (truth_spec (coherent_truth N) _)); exists true; reflexivity.
Qed.
