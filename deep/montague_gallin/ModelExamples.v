(* Temporal coherence is necessary, not a cosmetic model annotation.
   A perfectly well-formed unrestricted target model can have reflexive
   future accessibility. No PTQ-coherent interpretation can do that. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Postulates Examples.
From MontagueGallin Require Import Types Target Translation Examples Independent Correspondence.
Import ListNotations.
Set Implicit Arguments.

Theorem coherent_future_is_irreflexive F (N : coherent_model F) i :
  coherent_lex N FutureRelation i i = false.
Proof.
  destruct (coherent_lex N FutureRelation i i) eqn:H; auto.
  apply future_coherence in H; destruct H as [_ [_ H]]; contradiction.
Qed.
Theorem coherent_past_is_irreflexive F (N : coherent_model F) i :
  coherent_lex N PastRelation i i = false.
Proof.
  destruct (coherent_lex N PastRelation i i) eqn:H; auto.
  apply past_coherence in H; destruct H as [_ [_ H]]; contradiction.
Qed.

Fixpoint one_index_zero a : value_domain bool (unit * unit) a :=
  match a with
  | ge => false | gt => false | gs => (tt,tt)
  | garr _ b => fun _ => one_index_zero b
  end.
Definition reflexive_future_lex a (c : source_symbol a) : value_domain bool (unit * unit) a :=
  match c in source_symbol a return value_domain bool (unit * unit) a with
  | IndexedConstant a _ => fun _ => one_index_zero (translate_type a)
  | FutureRelation => fun _ _ => true
  | PastRelation => fun _ _ => false
  end.
Definition reflexive_future_model B FE : standard_model source_symbol :=
  {| standard_entities := bool; standard_indices := (unit * unit)%type;
     entities_inhabited := inhabits false; indices_inhabited := inhabits (tt,tt);
     standard_truth := B; standard_extensionality := FE; standard_lex := reflexive_future_lex |}.
Definition one_index_assignment a (v : source_parameter a) : value_domain bool (unit * unit) a :=
  one_index_zero a.
Theorem arbitrary_standard_future_can_be_reflexive B FE i :
  standard_lex (reflexive_future_model B FE) _ FutureRelation i i = true.
Proof. reflexivity. Qed.
Theorem reflexive_future_cannot_match_a_coherent_model B FE F (N : coherent_model F) i :
  standard_lex (reflexive_future_model B FE) _ FutureRelation (tt,tt) (tt,tt) <>
  coherent_lex N FutureRelation i i.
Proof. rewrite coherent_future_is_irreflexive; discriminate. Qed.

Definition one_moment : frame.
Proof.
  refine {| entity := bool; world := unit; time := unit;
    entity_nonempty := inhabits false; world_nonempty := inhabits tt;
    time_nonempty := inhabits tt; time_le := fun _ _ => True |}.
  - intros; exact I.
  - intros; exact I.
  - intros [] []; reflexivity.
  - intros; left; exact I.
Defined.
Fixpoint one_moment_zero a : domain one_moment a :=
  match a with
  | e => false | t => false
  | arr _ b => fun _ => one_moment_zero b
  | intens b => fun _ => one_moment_zero b
  end.
Definition one_moment_source B FE : model :=
  {| carrier := one_moment; boolean_truth := B; function_extensionality := FE;
     constants := fun a _ _ => one_moment_zero a |}.
Definition future_tautology : tm [] t := Will (Eq (@Con [] e 0) (Con 0)).

Theorem unrestricted_target_future_tautology_true B FE :
  standard_eval (reflexive_future_model B FE) one_index_assignment
    (translate_intension future_tautology) (value_empty bool (unit * unit)) (tt,tt) = true.
Proof.
  cbn; apply truth_spec; exists (tt,tt); cbn; apply truth_spec; reflexivity.
Qed.
Theorem source_future_tautology_false B FE :
  eval (one_moment_source B FE) future_tautology (empty_env _)
    (fun a _ => one_moment_zero a) (tt,tt) = false.
Proof.
  cbn; destruct (truth B _) eqn:H; auto.
  apply truth_spec in H; destruct H as [[] [[_ H] _]]; contradiction.
Qed.
Theorem missing_temporal_coherence_changes_prediction B FE :
  standard_eval (reflexive_future_model B FE) one_index_assignment
    (translate_intension future_tautology) (value_empty bool (unit * unit)) (tt,tt) = true /\
  eval (one_moment_source B FE) future_tautology (empty_env _)
    (fun a _ => one_moment_zero a) (tt,tt) = false.
Proof. split; [apply unrestricted_target_future_tautology_true | apply source_future_tautology_false]. Qed.

Theorem admissible_target_class_is_inhabited (B : BooleanTruth) (FE : FunExt) :
  exists F (N : coherent_model F), target_admissible N.
Proof.
  exists two_times, (embed_model (sample_model B FE)).
  apply (@embed_preserves_admissibility (sample_model B FE)); apply sample_model_admissible.
Qed.
Theorem independent_target_temperature_countermodel B FE :
  let M := sample_model B FE in
  let N := embed_model M in let theta := target_free (sample_assignment B FE) in
  target_admissible N /\
  coherent_eval N theta (english_translation temperature_is_ninety) (gempty two_times) (tt,false) = true /\
  coherent_eval N theta (english_translation temperature_rises) (gempty two_times) (tt,false) = true /\
  coherent_eval N theta (english_translation ninety_rises) (gempty two_times) (tt,false) = false.
Proof.
  cbn zeta; split.
  - apply (@embed_preserves_admissibility (sample_model B FE)); apply sample_model_admissible.
  - exact (proj2 (temperature_countermodel_transported B FE)).
Qed.

Theorem target_temperature_inference_invalid (B : BooleanTruth) (FE : FunExt) :
  ~ admissible_target_consequence
    [translate_closed temperature_is_ninety; translate_closed temperature_rises]
    (translate_closed ninety_rises).
Proof.
  intro H; destruct (independent_target_temperature_countermodel B FE) as [HN [HP [HQ HR]]].
  specialize (H two_times (embed_model (sample_model B FE)) HN
    (target_free (sample_assignment B FE)) (tt,false)).
  assert (HC : coherent_eval (embed_model (sample_model B FE))
    (target_free (sample_assignment B FE)) (english_translation ninety_rises)
    (gempty two_times) (tt,false) = true).
  { apply H; intros p [K | [K | K]]; subst; auto; contradiction. }
  congruence.
Qed.
