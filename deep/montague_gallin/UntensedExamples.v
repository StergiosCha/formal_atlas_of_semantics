(* Regression models on a bare Boolean index carrier. No product, time
   order, temporal coherence, or PTQ meaning postulates are supplied. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Independent Minimal MinimalCorrespondence
  Untensed UntensedTranslation UntensedModels.
Import ListNotations.
Set Implicit Arguments.

Fixpoint plain_value (a : ty) : idomain bool bool a :=
  match a with
  | e | t => false
  | arr a b => fun _ => plain_value b
  | intens a => fun _ => plain_value a
  end.
Definition plain_constant (a : ty) (i : bool) : idomain bool bool a :=
  match a with
  | t => i
  | e => false
  | arr a b => fun _ => plain_value b
  | intens a => fun _ => plain_value a
  end.
Definition plain_lex (temporal : bool) a (c : source_symbol a) : value_domain bool bool a :=
  match c in source_symbol a return value_domain bool bool a with
  | IndexedConstant a _ => fun i => il_lift bool bool a (plain_constant a i)
  | FutureRelation | PastRelation => fun _ _ => temporal
  end.
Definition plain_model B FE temporal : standard_model source_symbol :=
  {| standard_entities := bool; standard_indices := bool;
     entities_inhabited := inhabits false; indices_inhabited := inhabits false;
     standard_truth := B; standard_extensionality := FE; standard_lex := plain_lex temporal |}.
Definition plain_assignment a (v : source_parameter a) : value_domain bool bool a :=
  match v in source_parameter a return value_domain bool bool a with
  | SourceFree b _ => il_lift bool bool b (plain_value b)
  end.

Example indices_need_no_world_time_product B FE temporal :
  standard_indices (plain_model B FE temporal) = bool.
Proof. reflexivity. Qed.
Theorem arbitrary_index_constant_can_vary B FE temporal :
  core_standard_eval (plain_model B FE temporal) plain_assignment
    (il_minimal_translate (@ICon [] t 0)) (value_empty bool bool) false = false /\
  core_standard_eval (plain_model B FE temporal) plain_assignment
    (il_minimal_translate (@ICon [] t 0)) (value_empty bool bool) true = true.
Proof. split; reflexivity. Qed.

Theorem arbitrary_index_necessity_sees_other_indices B FE temporal :
  let N := plain_model B FE temporal in
  core_standard_eval N plain_assignment (il_minimal_translate (@ICon [] t 0))
    (value_empty bool bool) true = true /\
  core_standard_eval N plain_assignment (il_minimal_translate (IBox (@ICon [] t 0)))
    (value_empty bool bool) true = false.
Proof.
  cbn zeta; split; [reflexivity |].
  change (core_standard_eval (plain_model B FE temporal) plain_assignment
    (il_minimal_translate (IBox (@ICon [] t 0)))
    (il_canonical_env (il_empty (il_reconstruct (plain_model B FE temporal)))) true = false).
  rewrite untensed_backward_preservation.
  change (truth B (forall i : bool, i = true) = false).
  destruct (truth B (forall i : bool, i = true)) eqn:H; auto.
  apply (proj1 (truth_spec B _)) in H; specialize (H false); discriminate.
Qed.

Theorem untensed_terms_ignore_temporal_values B FE G a (p : itm G a)
  (rho : il_env (il_reconstruct (plain_model B FE false)) G) i :
  core_standard_eval (plain_model B FE false) plain_assignment
    (il_minimal_translate p) (il_canonical_env rho) i =
  core_standard_eval (plain_model B FE true) plain_assignment
    (il_minimal_translate p) (il_canonical_env rho) i.
Proof.
  transitivity (il_lift bool bool a (ieval (il_reconstruct (plain_model B FE false)) p rho
    (@il_reconstruct_assignment (plain_model B FE false) plain_assignment) i)).
  - exact (@untensed_backward_preservation (plain_model B FE false) plain_assignment G a p rho i).
  - symmetry; exact (@untensed_backward_preservation (plain_model B FE true) plain_assignment G a p rho i).
Qed.

(* The shared target language also contains terms outside the translated
   fragment. Their temporal meanings are not recovered by this round trip. *)
Theorem untensed_roundtrip_does_not_preserve_temporal_terms B FE :
  let N := plain_model B FE true in
  core_standard_eval N plain_assignment (@CCon source_symbol source_parameter [] _ FutureRelation)
    (value_empty bool bool) false false = true /\
  core_standard_eval (il_target (il_reconstruct N)) plain_assignment
    (@CCon source_symbol source_parameter [] _ FutureRelation)
    (value_empty bool bool) false false = false.
Proof. split; reflexivity. Qed.

Theorem arbitrary_index_model_classes_are_nonempty (B : BooleanTruth) (FE : FunExt) :
  il_standard_satisfiable (fun _ => False) /\
  ty2_standard_satisfiable (translated_il_theory (fun _ => False)).
Proof.
  assert (H : il_standard_satisfiable (fun _ => False)).
  { exists (il_reconstruct (plain_model B FE true)),
      (@il_reconstruct_assignment (plain_model B FE true) plain_assignment), false.
    intros p HP; contradiction. }
  split; [exact H | apply untensed_standard_satisfiability; exact H].
Qed.

Theorem no_untensed_representation_of_future G (p : tm G t) :
  ~ exists q : itm G t, embed_il q = Will p.
Proof.
  intros [q H]; pose proof (embedded_il_is_untensed q) as K.
  rewrite H in K; discriminate.
Qed.
Theorem no_untensed_representation_of_past G (p : tm G t) :
  ~ exists q : itm G t, embed_il q = Has p.
Proof.
  intros [q H]; pose proof (embedded_il_is_untensed q) as K.
  rewrite H in K; discriminate.
Qed.
