(* Object-language postulates, PTQ p. 28; formulas 2 and 9 are closed.
   Relations use subject-first curried coordinates. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Postulates Named.
Import ListNotations.
Set Implicit Arguments.

Definition nword {A} (w : lexeme A) : ntm (category_type A) := NC _ (lexical_code w).
Definition nx := NV ic 1.
Definition ny := NV ic 3.
Definition nu := NV e 0.
Definition prop_e := intens (arr e t).
Definition rel_e := intens (arr e (arr e t)).
Definition prop_ic := intens ivty.
Definition prop_np := intens npty.
Definition prop_e_iav := intens (arr e (category_type IAV)).
Definition nM := NV prop_e 0.
Definition nS := NV rel_e 0.
Definition nP := NV prop_ic 0.
Definition nQ := NV prop_np 0.
Definition nR := NV prop_ic 1.
Definition np := NV (intens t) 0.
Definition nG := NV prop_e_iav 0.

Definition formula1 n := NEx e 0 (NBox (NE nu (NC e (name_code n)))).
Definition formula2 c := NAll ic 1 (NBox
  (NI (NA (nword (lcn c)) nx) (NEx e 0 (NE nx (NU nu))))).
Definition formula3 v := NEx prop_e 0 (NAll ic 1 (NBox
  (NB (NA (nword (liv v)) nx) (NA (ND nM) (ND nx))))).
Definition formula4 v := NEx rel_e 0 (NAll ic 1 (NAll prop_np 0 (NBox
  (NB (NA (NA (nword (ltv v)) nQ) nx)
    (NA (ND nQ) (NU (NL ic 3 (NA (NA (ND nS) (ND nx)) (ND ny))))))))).

Definition formula5 v := NAll prop_np 0 (NEx prop_e 0 (NAll ic 1 (NBox
  (NB (NA (NA (nword (ltv v)) nQ) nx) (NA (ND nM) (ND nx)))))).
Definition formula6 v := NAll (intens t) 0 (NEx prop_e 0 (NAll ic 1 (NBox
  (NB (NA (NA (nword (latt v)) np) nx) (NA (ND nM) (ND nx)))))).
Definition formula7 v := NAll prop_ic 0 (NEx prop_e 0 (NAll ic 1 (NBox
  (NB (NA (NA (nword (lcontrol v)) nP) nx) (NA (ND nM) (ND nx)))))).
Definition formula8 := NEx prop_e_iav 0 (NAll prop_np 0 (NAll prop_ic 1 (NAll ic 1 (NBox
  (NB (NA (NA (NA (nword (lprep in_)) nQ) nR) nx)
    (NA (ND nQ) (NU (NL ic 3 (NA (NA (NA (ND nG) (ND ny)) nR) nx))))))))).
Definition formula9 := NAll ic 1 (NAll prop_np 0 (NBox
  (NB (NA (NA (nword (ltv seek)) nQ) nx)
    (NA (NA (nword (lcontrol try_to)) (NU (NA (nword (ltv find)) nQ))) nx)))).

Ltac unfold_postulate := cbn [formula1 formula2 formula3 formula4 formula5 formula6
  formula7 formula8 formula9 nword nx ny nu nM nS nP nQ nR np nG
  prop_e rel_e prop_ic prop_np prop_e_iav neval put ty_eq_dec];
  repeat (setoid_rewrite truth_spec || setoid_rewrite Bool.eqb_true_iff ||
          setoid_rewrite boolean_implication).

Lemma formula1_exact M n sigma i : neval M (formula1 n) sigma i = true <->
  exists u, forall j, constants M e (name_code n) j = u.
Proof. unfold_postulate; split; intros [u H]; exists u; intro j; symmetry; apply H. Qed.
Lemma formula2_exact M c sigma i : neval M (formula2 c) sigma i = true <->
  forall j x, word_value M (lcn c) j x = true -> exists u, x = (fun _ => u).
Proof. unfold_postulate; unfold word_value; firstorder. Qed.
Lemma formula3_exact M v sigma i : neval M (formula3 v) sigma i = true <->
  exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x j, word_value M (liv v) j x = P j (x j).
Proof. unfold_postulate; reflexivity. Qed.
Lemma formula4_exact M v sigma i : neval M (formula4 v) sigma i = true <->
  exists S : index (carrier M) -> entity (carrier M) -> entity (carrier M) -> bool,
  forall x Q j, word_value M (ltv v) j Q x = Q j (fun k y => S k (x k) (y k)).
Proof. unfold_postulate; reflexivity. Qed.
Lemma formula5_exact M v sigma i : neval M (formula5 v) sigma i = true <->
  forall Q, exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x j, word_value M (ltv v) j Q x = P j (x j).
Proof. unfold_postulate; reflexivity. Qed.
Lemma formula6_exact M v sigma i : neval M (formula6 v) sigma i = true <->
  forall p, exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x j, word_value M (latt v) j p x = P j (x j).
Proof. unfold_postulate; reflexivity. Qed.
Lemma formula7_exact M v sigma i : neval M (formula7 v) sigma i = true <->
  forall Q, exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x j, word_value M (lcontrol v) j Q x = P j (x j).
Proof. unfold_postulate; reflexivity. Qed.
Lemma formula8_exact M sigma i : neval M formula8 sigma i = true <-> mp8 M.
Proof. unfold_postulate; reflexivity. Qed.
Lemma formula9_exact M sigma i : neval M formula9 sigma i = true <-> mp9 M.
Proof. unfold_postulate; reflexivity. Qed.

Definition postulate_family (holds : ntm t -> Prop) :=
  (forall n, holds (formula1 n)) /\
  (forall c, ordinary_cn c -> holds (formula2 c)) /\
  (forall v, ordinary_iv v -> holds (formula3 v)) /\
  (forall v, extensional_tv v -> holds (formula4 v)) /\
  (forall v, intensional_tv v -> holds (formula5 v)) /\
  (forall v, holds (formula6 v)) /\
  (forall v, holds (formula7 v)) /\ holds formula8 /\ holds formula9.

Theorem object_postulates_exact M sigma i :
  postulate_family (fun p => neval M p sigma i = true) <-> admissible M.
Proof.
  unfold postulate_family; cbn beta.
  setoid_rewrite formula1_exact; setoid_rewrite formula2_exact;
  setoid_rewrite formula3_exact; setoid_rewrite formula4_exact;
  setoid_rewrite formula5_exact; setoid_rewrite formula6_exact;
  setoid_rewrite formula7_exact; rewrite formula8_exact, formula9_exact.
  split.
  - intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]; constructor; assumption.
  - intros [H1 H2 H3 H4 H5 H6 H7 H8 H9]; repeat split; assumption.
Qed.

Theorem compiled_postulates_exact M sigma i :
  postulate_family (fun p => eval M (embed_named p) (empty_env M) sigma i = true)
  <-> admissible M.
Proof.
  unfold postulate_family; setoid_rewrite embed_named_interpretation.
  apply object_postulates_exact.
Qed.
