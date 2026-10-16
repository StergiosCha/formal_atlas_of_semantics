(* Reuse the existing PTQ compiler on embedded untensed syntax. Prove it
   correct against an independent evaluator on arbitrary index domains.
   The lexical hypotheses mention no future or past relation. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Minimal Untensed.
Import ListNotations.
Set Implicit Arguments.

Definition il_matches M G D (r : variable_map G D)
  (rho : value_env (il_entities M) (il_indices M) D) (tau : il_env M G) :=
  forall a v, rho _ (r a v) = il_lift (il_entities M) (il_indices M) a (tau a v).
Lemma il_shifted_environments M G D a (r : variable_map G D) rho (tau : il_env M G) x :
  il_matches r rho tau -> il_matches (@shift_map G D a r) (value_extend rho x) tau.
Proof. intros H b v; apply H. Qed.
Lemma il_lifted_environments M G D a (r : variable_map G D) rho (tau : il_env M G) x :
  il_matches r rho tau -> il_matches (@lift_map G D a r) (value_extend rho x)
    (il_extend tau (il_lower (il_entities M) (il_indices M) a x)).
Proof.
  intros H; unfold il_matches; apply var_cases; cbn.
  - symmetry; apply il_lift_lower.
  - intros; apply H.
Qed.

Section Preservation.
Variable M : il_model.
Variable sigma : il_free_env M.
Local Notation E := (il_entities M).
Local Notation J := (il_indices M).
Local Notation B := (il_truth M).
Local Notation FE := (il_extensionality M).
Variable lex : forall a, source_symbol a -> value_domain E J a.
Variable theta : forall a, source_parameter a -> value_domain E J a.
Hypothesis HC : forall a n i, @lex _ (IndexedConstant a n) i = il_lift E J a (il_constants M a n i).
Hypothesis HF : forall a n, @theta _ (SourceFree a n) = il_lift E J a (sigma a n).
Local Notation V := (geval B lex theta).
Lemma il_target_weaken G a b (p : target_term G b) rho x :
  V (@gweaken _ _ G a b p) (value_extend rho x) = V p rho.
Proof. apply geval_weaken; exact FE. Qed.

Theorem untensed_interpretation_preservation G a (p : itm G a) : forall D
  (r : variable_map G D) (i : target_term D gs) rho tau,
  il_matches r rho tau ->
  V (compile (embed_il p) r i) rho = il_lift E J a (ieval M p tau sigma (V i rho)).
Proof.
  induction p; intros D r i rho tau H; cbn [embed_il compile].
  - apply H.
  - apply HF.
  - apply HC.
  - match goal with |- _ = ?rhs => change ((fun x => V (compile (embed_il p) (lift_map r) (gweaken i)) (value_extend rho x)) = rhs) end.
    rewrite il_lift_lambda; apply FE; intro x.
    rewrite IHp with (tau := il_extend tau (il_lower E J a x));
      [rewrite il_target_weaken; reflexivity | apply il_lifted_environments; exact H].
  - match goal with |- _ = ?rhs => change (V (compile (embed_il p1) r i) rho (V (compile (embed_il p2) r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
    apply il_lift_application.
  - match goal with |- _ = ?rhs => change (truth B (V (compile (embed_il p1) r i) rho = V (compile (embed_il p2) r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
    apply truth_congr; split; intro K.
    + apply (f_equal (il_lower E J a)) in K; rewrite !il_lower_lift in K; exact K.
    + exact (f_equal (il_lift E J a) K).
  - match goal with |- _ = ?rhs => change (negb (V (compile (embed_il p) r i) rho) = rhs) end.
    rewrite IHp with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (andb (V (compile (embed_il p1) r i) rho) (V (compile (embed_il p2) r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (orb (V (compile (embed_il p1) r i) rho) (V (compile (embed_il p2) r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (orb (negb (V (compile (embed_il p1) r i) rho)) (V (compile (embed_il p2) r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (Bool.eqb (V (compile (embed_il p1) r i) rho) (V (compile (embed_il p2) r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (truth B (forall x, V (compile (embed_il p) (lift_map r) (gweaken i)) (value_extend rho x) = true) = rhs) end.
    assert (K : forall x, V (compile (embed_il p) (lift_map r) (gweaken i)) (value_extend rho x) =
      ieval M p (il_extend tau (il_lower E J a x)) sigma (V i rho)).
    { intro x; rewrite IHp with (tau := il_extend tau (il_lower E J a x));
        [rewrite il_target_weaken; reflexivity | apply il_lifted_environments; exact H]. }
    apply truth_congr; setoid_rewrite K; split; intros Q x.
    + specialize (Q (il_lift E J a x)); rewrite il_lower_lift in Q; exact Q.
    + apply Q.
  - match goal with |- _ = ?rhs => change (truth B (exists x, V (compile (embed_il p) (lift_map r) (gweaken i)) (value_extend rho x) = true) = rhs) end.
    assert (K : forall x, V (compile (embed_il p) (lift_map r) (gweaken i)) (value_extend rho x) =
      ieval M p (il_extend tau (il_lower E J a x)) sigma (V i rho)).
    { intro x; rewrite IHp with (tau := il_extend tau (il_lower E J a x));
        [rewrite il_target_weaken; reflexivity | apply il_lifted_environments; exact H]. }
    apply truth_congr; setoid_rewrite K; split; intros [x Q].
    + exists (il_lower E J a x); exact Q.
    + exists (il_lift E J a x); rewrite il_lower_lift; exact Q.
  - match goal with |- _ = ?rhs => change (truth B (forall j, V (compile (embed_il p) (shift_map r) (GVar gz)) (value_extend rho j) = true) = rhs) end.
    apply truth_congr.
    assert (K : forall j, V (compile (embed_il p) (shift_map r) (GVar gz)) (value_extend rho j) =
      ieval M p tau sigma j).
    { intro j; apply IHp; apply il_shifted_environments; exact H. }
    cbn [ieval]; setoid_rewrite K; reflexivity.
  - match goal with |- _ = ?rhs => change ((fun j => V (compile (embed_il p) (shift_map r) (GVar gz)) (value_extend rho j)) = rhs) end.
    rewrite il_lift_intension; apply FE; intro j; apply IHp.
    apply il_shifted_environments; exact H.
  - match goal with |- _ = ?rhs => change (V (compile (embed_il p) r i) rho (V i rho) = rhs) end.
    rewrite IHp with (tau := tau); auto.
    rewrite il_lift_intension; reflexivity.
Qed.

Fixpoint il_canonical_env G : il_env M G -> value_env E J (map translate_type G) :=
  match G return il_env M G -> value_env E J (map translate_type G) with
  | [] => fun _ => value_empty E J
  | a :: G => fun rho => value_extend
      (@il_canonical_env G (fun b v => rho b (vs v))) (il_lift E J a (rho a vz))
  end.
Lemma il_canonical_environments_match G (rho : il_env M G) :
  il_matches (@canonical_map G) (il_canonical_env rho) rho.
Proof.
  induction G as [|a G IH].
  - intros b v; inversion v.
  - unfold il_matches; apply var_cases; cbn; [reflexivity | intros; apply IH].
Qed.

Theorem untensed_open_preservation G a (p : itm G a) rho i :
  V (translate_intension (embed_il p)) (il_canonical_env rho) i =
  il_lift E J a (ieval M p rho sigma i).
Proof.
  unfold translate_intension; cbn [geval].
  apply untensed_interpretation_preservation; apply il_shifted_environments.
  apply il_canonical_environments_match.
Qed.
Theorem untensed_minimal_preservation G a (p : itm G a) rho i :
  ceval B lex theta (eliminate (translate_intension (embed_il p))) (il_canonical_env rho) i =
  il_lift E J a (ieval M p rho sigma i).
Proof. rewrite elimination_preserves_interpretation by exact FE.
  apply untensed_open_preservation. Qed.
End Preservation.

(* Actual PTQ compatibility, compared through the already proved inverse
   domain transports rather than by identifying two different recursors. *)
Theorem ptq_untensed_interpretation M G a (p : itm G a) rho sigma i :
  il_lift (entity (carrier M)) (index (carrier M)) a
    (ieval (forget_ptq_time M) p (forget_ptq_env rho) (forget_ptq_free sigma) i) =
  lift_value (carrier M) a (eval M (embed_il p) rho sigma i).
Proof.
  transitivity (target_eval M sigma (translate_intension (embed_il p)) (canonical_env rho) i).
  - symmetry; unfold target_eval, translate_intension; cbn [geval].
    apply (@untensed_interpretation_preservation (forget_ptq_time M) (forget_ptq_free sigma)
      (target_lex M) (target_free sigma)).
    + intros; symmetry; apply il_lift_lower.
    + intros; symmetry; apply il_lift_lower.
    + apply il_shifted_environments; intros b v.
      unfold forget_ptq_env; rewrite il_lift_lower; apply canonical_environments_match.
  - apply open_preservation.
Qed.
