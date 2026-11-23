(** Cooper (2023), From Perception to Communication, p. 59 (51)-(52)
    and Appendix A5, p. 403. The legacy value language represents a
    finite set by a well-formed labelled collection of its members. *)
From Coq Require Import List String.
Require Import TTR_base TTR_types.
Open Scope string_scope.

Theorem set_witness_iff M X T :
  witnesses M X (TSet T) <->
  exists ls, X = VLSet ls /\ wf_labelled_set ls = true /\
    forall l v, ls_lookup ls l = Some v -> witnesses M v T.
Proof.
  split.
  - intro H. inversion H; subst. eauto.
  - intros [ls [-> [well_formed members]]]. now apply wit_set.
Qed.

(** The elimination rule applies even to raw fields accessed before any
    lookup. Thus a repeated label cannot conceal an ill-typed member. *)
Local Lemma has_stored_label f ls :
  In f (ls_to_list ls) -> has_label (field_label f) ls = true.
Proof.
  induction ls as [|head tail IH]; simpl.
  - contradiction.
  - intros [<- | found].
    + now rewrite String.eqb_refl.
    + destruct (String.eqb (field_label head) (field_label f)); auto.
Qed.

Local Lemma lookup_stored_field ls f :
  wf_labelled_set ls = true -> In f (ls_to_list ls) ->
  ls_lookup ls (field_label f) = Some (field_value f).
Proof.
  induction ls as [|head tail IH]; simpl.
  - contradiction.
  - intros wf [<- | found].
    + now rewrite String.eqb_refl.
    + apply Bool.andb_true_iff in wf as [fresh wf].
      apply Bool.negb_true_iff in fresh.
      destruct (String.eqb (field_label head) (field_label f)) eqn:same.
      * apply String.eqb_eq in same.
        pose proof (has_stored_label f tail found) as present.
        rewrite same in fresh. congruence.
      * now apply IH.
Qed.

Theorem set_member_elim M ls T f :
  witnesses M (VLSet ls) (TSet T) ->
  In f (ls_to_list ls) -> witnesses M (field_value f) T.
Proof.
  intros H stored. apply set_witness_iff in H as [entries [shape [wf members]]].
  injection shape as same. subst entries.
  apply (members (field_label f)). now apply lookup_stored_field.
Qed.

(** Prior to the correction this term classified every labelled collection
    at every set type, including singleton collections at set(absurd). *)
Fail Check (fun (M : TTRModel) (T : TTRType) (ls : LabelledSet) =>
  wit_set M T ls True I).

Example empty_set M T : witnesses M (VLSet LSNil) (TSet T).
Proof. apply wit_set; [reflexivity | intros l v H; discriminate]. Qed.

Example raw_value_is_not_a_set M T : ~ witnesses M (VNat 1) (TSet T).
Proof. intro H. inversion H. Qed.

Definition numbers_model : TTRModel :=
  mkModel (fun _ v => v = VNat 1) (fun _ _ _ => False)
    (mkPredSig nil (fun _ => nil)).
Definition unit_number := TBasic "one".
Definition two_fields (second : Val) :=
  LSCons (FPair "first" (VNat 1)) (LSCons (FTriple "second" second 0) LSNil).

Example two_labels_one_member :
  witnesses numbers_model (VLSet (two_fields (VNat 1))) (TSet unit_number).
Proof.
  apply wit_set_proper; [reflexivity |].
  intros l v H.
  cbn [two_fields ls_lookup field_label field_value] in H.
  destruct (String.eqb "first" l) in H;
    [ | destruct (String.eqb "second" l) in H ]; inversion H; now apply wit_basic.
Qed.

Example mixed_set_rejected :
  ~ witnesses numbers_model (VLSet (two_fields (VBool true))) (TSet unit_number).
Proof.
  intro H.
  pose proof (set_member_elim _ _ _ (FTriple "second" (VBool true) 0)
    H (or_intror (or_introl eq_refl))) as bad.
  inversion bad; discriminate.
Qed.

Example duplicate_label_rejected M T first second :
  ~ witnesses M
    (VLSet (LSCons (FPair "x" first) (LSCons (FPair "x" second) LSNil)))
    (TSet T).
Proof. intro H. inversion H; subst; discriminate. Qed.

Definition singleton_value (v : Val) := VLSet (LSCons (FPair "x" v) LSNil).

Example nested_empty_set M : witnesses M (singleton_value (VLSet LSNil))
    (TSet (TSet TAbsurd)).
Proof.
  apply wit_set; [reflexivity |].
  intros l v H. cbn [ls_lookup field_label field_value] in H.
  destruct (String.eqb "x" l) in H; inversion H. apply empty_set.
Qed.

Example nested_bad_member M :
  ~ witnesses M (singleton_value (singleton_value (VNat 1))) (TSet (TSet TAbsurd)).
Proof.
  intro H.
  pose proof (set_member_elim _ _ _ _ H (or_introl eq_refl)) as inner.
  pose proof (set_member_elim _ _ _ _ inner (or_introl eq_refl)) as absurd.
  inversion absurd.
Qed.
