(* Source pp. 29-31: selected truth-condition reductions. Starred lexical
   extensions are defined, not supplied as fresh uninterpreted predicates. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Catalogue.
Import ListNotations.
Set Implicit Arguments.

Definition rigid M (u : entity (carrier M)) : domain (carrier M) ic := fun _ => u.
Definition cn_star M c i u := word_value M (lcn c) i (rigid M u).
Definition iv_star M v i u := word_value M (liv v) i (rigid M u).
Definition tv_star M v i u z := word_value M (ltv v) i
  (fun j P => P j (rigid M z)) (rigid M u).

Lemma iv_extensional_reduction M (A : admissible M) v (O : ordinary_iv v) x i :
  word_value M (liv v) i x = iv_star M v i (x i).
Proof.
  destruct (postulate3 A v O) as [P H]; unfold iv_star; rewrite !H; reflexivity.
Qed.

Lemma tv_extensional_reduction M (A : admissible M) v (O : extensional_tv v) Q x i :
  word_value M (ltv v) i Q x =
  Q i (fun j y => tv_star M v j (x j) (y j)).
Proof.
  destruct (postulate4 A v O) as [S H]; rewrite H.
  f_equal; apply (function_extensionality M); intro j.
  apply (function_extensionality M); intro y.
  unfold tv_star; rewrite H; reflexivity.
Qed.

Lemma indefinite_reduction M (A : admissible M) c (O : ordinary_cn c) P i :
  dvalue M a_or_an (word_value M (lcn c) i) i P = true <->
  exists u, cn_star M c i u = true /\ P i (rigid M u) = true.
Proof.
  cbn [dvalue]; rewrite truth_spec; split.
  - intros [x H]; apply andb_true_iff in H; destruct H as [C V].
    destruct (postulate2 A c O i x C) as [u E]; subst x; exists u; auto.
  - intros [u [C V]]; exists (rigid M u); apply andb_true_iff; auto.
Qed.

Lemma universal_reduction M (A : admissible M) c (O : ordinary_cn c) P i :
  dvalue M every (word_value M (lcn c) i) i P = true <->
  forall u, cn_star M c i u = true -> P i (rigid M u) = true.
Proof.
  cbn [dvalue]; rewrite truth_spec; split.
  - intros H u; apply (proj1 (boolean_implication _ _) (H (rigid M u))).
  - intros H x; apply boolean_implication; intro C.
    destruct (postulate2 A c O i x C) as [u E]; subst x; apply H; exact C.
Qed.

Lemma eqb_truth_iff B b P : Bool.eqb b (truth B P) = true <-> (b = true <-> P).
Proof.
  rewrite Bool.eqb_true_iff; split; intro H.
  - rewrite H; apply truth_spec.
  - apply bool_ext; rewrite truth_spec; exact H.
Qed.

Lemma definite_reduction M (A : admissible M) c (O : ordinary_cn c) P i :
  dvalue M the (word_value M (lcn c) i) i P = true <->
  exists u, (forall v, cn_star M c i v = true <-> v = u) /\
    P i (rigid M u) = true.
Proof.
  cbn [dvalue]; rewrite truth_spec.
  setoid_rewrite andb_true_iff; setoid_rewrite truth_spec.
  setoid_rewrite eqb_truth_iff.
  split.
  - intros [y [U V]].
    pose proof (proj2 (U y) eq_refl) as C.
    destruct (postulate2 A c O i y C) as [u E]; subst y.
    exists u; split; auto. intro v; unfold cn_star; rewrite U.
    split; intro E.
    + exact (f_equal (fun f => f i) E).
    + subst v; reflexivity.
  - intros [u [U V]]; exists (rigid M u); split; auto. intro x; split.
    + intro C; destruct (postulate2 A c O i x C) as [v E]; subst x.
      assert (v = u) by (apply (proj1 (U v)); exact C).
      subst v; reflexivity.
    + intro E; subst x; apply (proj2 (U u)); reflexivity.
Qed.

Theorem the_man_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed the_man_walks) (empty_env M) sigma i = true <->
  exists u, (forall v, cn_star M man i v = true <-> v = u) /\
    iv_star M walk i u = true.
Proof.
  rewrite closed_translation_interpretation.
  apply (definite_reduction A man I).
Qed.

Theorem bill_walks_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed bill_walks) (empty_env M) sigma i =
  iv_star M walk i (constants M e (name_code bill) i).
Proof. rewrite bill_walks_interpretation; apply (@iv_extensional_reduction M A walk I). Qed.

Theorem john_finds_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed finds_unicorn) (empty_env M) sigma i = true <->
  exists u, cn_star M unicorn i u = true /\
    tv_star M find i (constants M e (name_code john) i) u = true.
Proof.
  rewrite closed_translation_interpretation.
  change (word_value M (ltv find) i
    (fun j => dvalue M a_or_an (word_value M (lcn unicorn) j) j)
    (fun j => constants M e (name_code john) j) = true <->
    exists u, cn_star M unicorn i u = true /\
      tv_star M find i (constants M e (name_code john) i) u = true).
  rewrite (@tv_extensional_reduction M A find I).
  apply (indefinite_reduction A unicorn I).
Qed.

(* The extensionality analogue of postulate 4 for be requires no lexical
   postulate: its relation is equality, by its translated definition. *)
Theorem be_extensional_without_postulates M sigma :
  exists S : index (carrier M) -> entity (carrier M) -> entity (carrier M) -> bool,
  forall Q x i, eval M (@translate_be []) (empty_env M) sigma i Q x =
    Q i (fun j y => S j (x j) (y j)).
Proof. exists (fun _ u v => truth (boolean_truth M) (u = v)); reflexivity. Qed.

Theorem identity_source_reduction M sigma i :
  eval M (translate_closed bill_is_mary) (empty_env M) sigma i = true <->
  constants M e (name_code bill) i = constants M e (name_code mary) i.
Proof. rewrite closed_translation_interpretation; apply truth_spec. Qed.

Theorem predication_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed bill_is_man) (empty_env M) sigma i = true <->
  cn_star M man i (constants M e (name_code bill) i) = true.
Proof.
  rewrite closed_translation_interpretation.
  change (dvalue M a_or_an (word_value M (lcn man) i) i
    (fun j y => truth (boolean_truth M) (constants M e (name_code bill) j = y j)) = true <->
    cn_star M man i (constants M e (name_code bill) i) = true).
  rewrite (indefinite_reduction A man I); split.
  - intros [u [C E]]; apply truth_spec in E.
    change (constants M e (name_code bill) i = u) in E.
    rewrite <- E in C; exact C.
  - intro C; exists (constants M e (name_code bill) i); split; auto.
    apply truth_spec; reflexivity.
Qed.

Theorem price_concept_truth_condition M sigma i :
  eval M (translate_closed a_price_rises) (empty_env M) sigma i = true <->
  exists x : domain (carrier M) ic,
    word_value M (lcn price) i x = true /\ word_value M (liv rise) i x = true.
Proof.
  rewrite closed_translation_interpretation.
  cbn [a_price_rises denote dvalue]; rewrite truth_spec.
  setoid_rewrite andb_true_iff; reflexivity.
Qed.

Theorem seeking_trying_dicto_equal M (A : admissible M) sigma i :
  eval M (translate_closed seeks_unicorn_dicto) (empty_env M) sigma i =
  eval M (translate_closed tries_unicorn_dicto) (empty_env M) sigma i.
Proof. rewrite !closed_translation_interpretation; apply (postulate9 A). Qed.

Theorem seeking_trying_re_equal M (A : admissible M) sigma i :
  eval M (translate_closed seeks_unicorn_re) (empty_env M) sigma i =
  eval M (translate_closed tries_unicorn_re) (empty_env M) sigma i.
Proof.
  rewrite !closed_translation_interpretation.
  cbn [seeks_unicorn_re tries_unicorn_re some_unicorn denote dvalue].
  pose proof (postulate9 A) as E; unfold mp9, word_value in E.
  apply truth_congr; split; intros [x H]; exists x;
    apply andb_true_iff in H; destruct H as [C V]; apply andb_true_iff; split; auto.
  - rewrite <- E; exact V.
  - rewrite E; exact V.
Qed.
