(* Structural metatheory of the object calculus, without semantic premises. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax Algebra Calculus.
Import ListNotations.
Set Implicit Arguments.

Theorem beta_renaming : forall symbol G a (t u : tm symbol G a),
  beta t u -> forall D (r : ren G D), beta (rename t r) (rename u r).
Proof.
  intros symbol G a t u B; induction B; intros D r; cbn.
  - apply beta_refl.
  - apply beta_sym; auto.
  - eapply beta_trans; eauto.
  - rewrite rename_instantiate; apply beta_step.
  - apply beta_lam; auto.
  - apply beta_app; auto.
  - apply beta_imp; auto.
  - apply beta_all; auto.
Qed.

Theorem beta_substitution : forall symbol G a (t u : tm symbol G a),
  beta t u -> forall D (s : sub symbol G D), beta (subst t s) (subst u s).
Proof.
  intros symbol G a t u B; induction B; intros D theta; cbn.
  - apply beta_refl.
  - apply beta_sym; auto.
  - eapply beta_trans; eauto.
  - rewrite subst_instantiate; apply beta_step.
  - apply beta_lam; auto.
  - apply beta_app; auto.
  - apply beta_imp; auto.
  - apply beta_all; auto.
Qed.

Theorem derivation_renaming : forall symbol L G H (p : tm symbol G truth),
  derives L H p -> forall D (r : ren G D),
  derives L (map (fun q => rename q r) H) (rename p r).
Proof.
  intros symbol L G H p Proof; induction Proof; intros D r; cbn.
  - apply d_assume; apply in_map_iff; exists p; split; [reflexivity | assumption].
  - apply d_imp_intro; apply IHProof.
  - eapply d_imp_elim; [apply IHProof1 | apply IHProof2].
  - apply d_all_intro.
    rewrite <- map_rename_weaken; apply IHProof.
  - rewrite rename_instantiate; apply d_all_elim; apply IHProof.
  - eapply d_conversion; [apply IHProof | apply beta_renaming; eassumption].
  - apply d_double_negation; [assumption | apply IHProof].
Qed.

Theorem derivation_weakening : forall symbol L G H (p : tm symbol G truth) a,
  derives L H p ->
  derives L (map (@weaken symbol G a truth) H) (weaken p).
Proof. intros; apply derivation_renaming; assumption. Qed.

Theorem derivation_substitution : forall symbol L G H (p : tm symbol G truth),
  derives L H p -> forall D (s : sub symbol G D),
  derives L (map (fun q => subst q s) H) (subst p s).
Proof.
  intros symbol L G H p Proof; induction Proof; intros D theta; cbn.
  - apply d_assume; apply in_map_iff; exists p; split; [reflexivity | assumption].
  - apply d_imp_intro; apply IHProof.
  - eapply d_imp_elim; [apply IHProof1 | apply IHProof2].
  - apply d_all_intro.
    rewrite <- map_subst_weaken; apply IHProof.
  - rewrite subst_instantiate; apply d_all_elim; apply IHProof.
  - eapply d_conversion; [apply IHProof | apply beta_substitution; eassumption].
  - apply d_double_negation; [assumption | apply IHProof].
Qed.

Theorem derivation_instantiation : forall symbol L G a (H : list (tm symbol (a :: G) truth))
  (p : tm symbol (a :: G) truth) (u : tm symbol G a),
  derives L H p ->
  derives L (map (fun q => instantiate u q) H) (instantiate u p).
Proof. intros; apply derivation_substitution; assumption. Qed.
