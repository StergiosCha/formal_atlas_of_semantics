(* Application of the general translation to existing English analyses.
   These are checks on the translation, not new discoveries about English. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Postulates Examples.
From MontagueGallin Require Import Types Target Translation.
Import ListNotations.
Set Implicit Arguments.

Definition english_translation A (u : tree A) :=
  translate_intension (translate_closed u).
Theorem english_interpretation_preserved M A (u : tree A) sigma i :
  target_eval M sigma (english_translation u) (gempty (carrier M)) i =
  lift_value (carrier M) (category_type A)
    (denote M u (fun n => sigma ic (2*n)) i).
Proof. unfold english_translation; rewrite closed_preservation, closed_translation_interpretation; reflexivity. Qed.

Theorem temperature_countermodel_transported B FE :
  let M := sample_model B FE in
  let sigma := sample_assignment B FE in
  admissible M /\
  target_eval M sigma (english_translation temperature_is_ninety) (gempty (carrier M)) (tt,false) = true /\
  target_eval M sigma (english_translation temperature_rises) (gempty (carrier M)) (tt,false) = true /\
  target_eval M sigma (english_translation ninety_rises) (gempty (carrier M)) (tt,false) = false.
Proof.
  cbn zeta; unfold english_translation; rewrite !closed_preservation.
  exact (MontaguePTQ.Examples.temperature_countermodel B FE).
Qed.

Definition source_consequence (restriction : model -> Prop) (ps : list (tm [] t)) (q : tm [] t) :=
  forall M, restriction M -> forall sigma i,
    (forall p, In p ps -> eval M p (empty_env M) sigma i = true) ->
    eval M q (empty_env M) sigma i = true.
(* Quantifies over the same source models and their constructed targets.
   It intentionally does NOT quantify over arbitrary Henkin/Ty2 models. *)
Definition image_consequence (restriction : model -> Prop) (ps : list (tm [] t)) (q : tm [] t) :=
  forall M, restriction M -> forall sigma i,
    (forall p, In p ps -> target_eval M sigma (translate_intension p) (gempty (carrier M)) i = true) ->
    target_eval M sigma (translate_intension q) (gempty (carrier M)) i = true.
Theorem consequence_on_model_image restriction ps q :
  image_consequence restriction ps q <-> source_consequence restriction ps q.
Proof.
  unfold image_consequence, source_consequence; split; intros H M HM sigma i HP.
  - assert (HQ : target_eval M sigma (translate_intension q) (gempty (carrier M)) i = true).
    { apply H; auto; intros p Hp; rewrite closed_preservation; apply HP; exact Hp. }
    rewrite closed_preservation in HQ; exact HQ.
  - rewrite closed_preservation; apply H; auto.
    intros p Hp; specialize (HP p Hp); rewrite closed_preservation in HP; exact HP.
Qed.
Corollary admissible_consequence_on_model_image ps q :
  image_consequence admissible ps q <-> source_consequence admissible ps q.
Proof. apply consequence_on_model_image. Qed.

Theorem translated_constant_is_not_frozen B FE :
  let M := sample_model B FE in
  let sigma := sample_assignment B FE in
  let p := translate_intension (@Con [] t 0) in
  target_eval M sigma p (gempty (carrier M)) (tt,false) = true /\
  target_eval M sigma p (gempty (carrier M)) (tt,true) = false.
Proof. cbn zeta; rewrite !closed_preservation; split; reflexivity. Qed.
Theorem translated_necessity_keeps_both_coordinates B FE :
  let M := sample_model B FE in
  let sigma := sample_assignment B FE in
  (forall w, target_eval M sigma (translate_intension (@Con [] t 0)) (gempty (carrier M)) (w,false) = true) /\
  target_eval M sigma (translate_intension (Box (@Con [] t 0))) (gempty (carrier M)) (tt,false) = false.
Proof.
  cbn zeta; split.
  - intro w; rewrite closed_preservation; reflexivity.
  - rewrite closed_preservation; exact (proj2 (necessity_now_is_not_ptq_necessity B FE)).
Qed.

Example constant_translation_uses_index :
  translate_intension (@Con [] e 7) =
  GLam (GApp (GCon (IndexedConstant e 7)) (GVar gz)).
Proof. reflexivity. Qed.
Example free_variable_translation_does_not_use_index :
  translate_intension (@Free [] e 7) = GLam (GFree (SourceFree e 7)).
Proof. reflexivity. Qed.
Example index_under_lambda_is_shifted :
  translate_intension (@Lam [] e e (Con 0)) =
  GLam (GLam (GApp (GCon (IndexedConstant e 0)) (GVar (gvs gz)))).
Proof. reflexivity. Qed.
Example source_variable_under_intension_is_shifted :
  translate_intension (@Lam [] e (intens e) (Up (Var vz))) =
  GLam (GLam (GLam (GVar (gvs gz)))).
Proof. reflexivity. Qed.
Example source_iv_type_survives :
  translate_type ivty = garr (garr gs ge) gt.
Proof. reflexivity. Qed.
