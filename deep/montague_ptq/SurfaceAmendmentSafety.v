(* The amendment changes only verb forms, not lexical identity, token order,
   pronoun indices, or success/failure of realization. These are all-tree
   properties. They do not assert exhaustive semantic reading classification. *)
From Coq Require Import List Bool Strings.String.
From MontaguePTQ Require Import Syntax Grammar Surface SurfaceInvariant SurfaceAmendment.
Import ListNotations.
Set Implicit Arguments.

Definition erase_verb_form u := match u with
  | verb v _ => verb v infinitive | _ => u end.
Definition erase_forms := map erase_verb_form.
Definition erase_result := option_map erase_forms.
Definition inflect_result f xs := match xs with
  | Some us => inflect_first f us | None => None end.

Lemma erase_forms_idempotent xs : erase_forms (erase_forms xs) = erase_forms xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [erase_forms map erase_verb_form] in *; congruence.
Qed.
Lemma erase_result_idempotent xs : erase_result (erase_result xs) = erase_result xs.
Proof. destruct xs; [unfold erase_result; cbn [option_map]; rewrite erase_forms_idempotent|]; reflexivity. Qed.

Lemma erase_forms_append xs ys : erase_forms (xs ++ ys) = erase_forms xs ++ erase_forms ys.
Proof. apply map_app. Qed.
Lemma erase_forms_replace n g xs :
  erase_forms (map (replace_pronoun n g) xs) = map (replace_pronoun n g) (erase_forms xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  cbn [erase_forms map]; rewrite IH; f_equal; destruct u; cbn;
    try reflexivity; destruct (Nat.eqb n n0); reflexivity.
Qed.
Lemma erase_forms_rename n k xs :
  erase_forms (map (rename_pronoun n k) xs) = map (rename_pronoun n k) (erase_forms xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  cbn [erase_forms map]; rewrite IH; f_equal; destruct u; cbn;
    try reflexivity; destruct (Nat.eqb n n0); reflexivity.
Qed.
Lemma erase_forms_gender xs : first_gender (erase_forms xs) = first_gender xs.
Proof. induction xs as [|u xs IH]; [reflexivity|]; destruct u; cbn; auto. Qed.
Lemma erase_forms_bare xs : bare_pronoun (erase_forms xs) = bare_pronoun xs.
Proof.
  destruct xs as [|u xs]; [reflexivity|].
  destruct u; destruct xs; cbn; try reflexivity; destruct c; reflexivity.
Qed.
Lemma erase_forms_object xs : erase_forms (object_form xs) = object_form (erase_forms xs).
Proof.
  destruct xs as [|u xs]; [reflexivity|].
  destruct u; destruct xs; cbn; try reflexivity; destruct c; reflexivity.
Qed.

Lemma erase_forms_insert n alpha g xs :
  erase_result (insert_first n alpha g xs) = insert_first n (erase_forms alpha) g (erase_forms xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  destruct u; cbn [insert_first erase_forms map erase_verb_form];
    try (rewrite <- IH; destruct (insert_first n alpha g xs); reflexivity).
  destruct (Nat.eqb n n0).
  - cbn [erase_result option_map]; rewrite erase_forms_append, erase_forms_replace; reflexivity.
  - rewrite <- IH; destruct (insert_first n alpha g xs); reflexivity.
Qed.

Lemma erase_forms_f10 n alpha xs :
  erase_result (f10 n alpha xs) = f10 n (erase_forms alpha) (erase_forms xs).
Proof.
  unfold f10; rewrite erase_forms_bare, erase_forms_gender.
  destruct (bare_pronoun alpha); [cbn [erase_result option_map]; rewrite erase_forms_rename; reflexivity|].
  destruct (first_gender alpha); [apply erase_forms_insert|reflexivity].
Qed.

Lemma erase_forms_inflect f xs :
  erase_result (inflect_first f xs) = erase_result (inflect_first f (erase_forms xs)).
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  destruct u; cbn [inflect_first erase_forms map erase_verb_form];
    try (destruct (inflect_first f xs), (inflect_first f (erase_forms xs));
      cbn [erase_result option_map erase_forms map erase_verb_form] in *; congruence).
  cbn [erase_result option_map erase_forms map erase_verb_form].
  rewrite erase_forms_idempotent; reflexivity.
Qed.

Lemma erase_result_inflect f xs :
  erase_result (inflect_result f xs) = erase_result (inflect_result f (erase_result xs)).
Proof. destruct xs; [apply erase_forms_inflect|reflexivity]. Qed.

Lemma erase_result_first xs :
  erase_result (first_present xs) = erase_result (first_present (erase_result xs)).
Proof. apply erase_result_inflect. Qed.

Lemma erase_result_combine f :
  (forall xs ys, erase_result (f xs ys) = f (erase_forms xs) (erase_forms ys)) ->
  forall a b, erase_result (combine f a b) = combine f (erase_result a) (erase_result b).
Proof. intros H [xs|] [ys|]; try reflexivity; apply H. Qed.

Lemma erase_result_concat a b :
  erase_result (combine concat_tokens a b) = combine concat_tokens (erase_result a) (erase_result b).
Proof.
  apply erase_result_combine; intros; cbn [concat_tokens erase_result option_map].
  rewrite erase_forms_append; reflexivity.
Qed.
Lemma erase_result_reverse a b :
  erase_result (combine (fun x y => concat_tokens y x) a b) =
  combine (fun x y => concat_tokens y x) (erase_result a) (erase_result b).
Proof.
  apply erase_result_combine; intros; cbn [concat_tokens erase_result option_map].
  rewrite erase_forms_append; reflexivity.
Qed.
Lemma erase_result_object a b :
  erase_result (combine (fun x y => concat_tokens x (object_form y)) a b) =
  combine (fun x y => concat_tokens x (object_form y)) (erase_result a) (erase_result b).
Proof.
  apply erase_result_combine; intros; cbn [concat_tokens erase_result option_map].
  rewrite erase_forms_append, erase_forms_object; reflexivity.
Qed.
Lemma erase_result_join j a b :
  erase_result (combine (join_tokens j) a b) = combine (join_tokens j) (erase_result a) (erase_result b).
Proof.
  apply erase_result_combine; intros; cbn [join_tokens erase_result option_map].
  repeat rewrite erase_forms_append; reflexivity.
Qed.
Lemma erase_result_f10 n a b :
  erase_result (combine (f10 n) a b) = combine (f10 n) (erase_result a) (erase_result b).
Proof. apply erase_result_combine; apply erase_forms_f10. Qed.

Lemma erase_result_subject f a b :
  erase_result (combine (subject_verb f) a b) =
  erase_result (combine (subject_verb f) (erase_result a) (erase_result b)).
Proof.
  assert (C : forall x y, combine (subject_verb f) x y =
    combine concat_tokens x (inflect_result f y)).
  { intros [xs|] [ys|]; cbn [combine subject_verb inflect_result];
      try reflexivity; destruct (inflect_first f ys); reflexivity. }
  repeat rewrite C; repeat rewrite erase_result_concat.
  rewrite erase_result_inflect.
  rewrite erase_result_idempotent; reflexivity.
Qed.

Lemma erase_result_determiner d a :
  erase_result (match a with Some cs => Some (literal
    (match d with every => "every" | the => "the" | a_or_an => "a" end) :: cs)
    | None => None end) =
  match erase_result a with Some cs => Some (literal
    (match d with every => "every" | the => "the" | a_or_an => "a" end) :: cs)
    | None => None end.
Proof. destruct a; reflexivity. Qed.

Lemma erase_result_relative n a b :
  erase_result (combine (fun cs ps => match first_gender cs with
    | Some g => Some (cs ++ [literal "such"; literal "that"] ++ map (replace_pronoun n g) ps)
    | None => None end) a b) =
  combine (fun cs ps => match first_gender cs with
    | Some g => Some (cs ++ [literal "such"; literal "that"] ++ map (replace_pronoun n g) ps)
    | None => None end) (erase_result a) (erase_result b).
Proof.
  apply erase_result_combine; intros; rewrite erase_forms_gender.
  destruct (first_gender xs); [|reflexivity].
  cbn [erase_result option_map]; repeat rewrite erase_forms_append.
  rewrite erase_forms_replace; reflexivity.
Qed.

Lemma iv_present_keeps_erasure (u : tree IV) :
  erase_result (first_present (realize u)) = erase_result (realize u).
Proof.
  destruct (realize u) as [xs|] eqn:E; [|reflexivity].
  pose proof (proj2 (@realized_sequence_invariant IV u xs E) iv_verb_category) as V.
  destruct V as [v [rest V]]; subst xs; reflexivity.
Qed.

Lemma erase_first_congr a b : erase_result a = erase_result b ->
  erase_result (first_present a) = erase_result (first_present b).
Proof. intro H; rewrite (erase_result_first a), (erase_result_first b), H; reflexivity. Qed.
Lemma erase_subject_congr f a b x y :
  erase_result a = erase_result x -> erase_result b = erase_result y ->
  erase_result (combine (subject_verb f) a b) = erase_result (combine (subject_verb f) x y).
Proof.
  intros H K; rewrite (erase_result_subject f a b), (erase_result_subject f x y), H, K; reflexivity.
Qed.

Theorem all_tree_amendment_erasure A (u : tree A) :
  erase_result (plain_tokens (plan coordinated_present u)) = erase_result (realize u) /\
  erase_result (present_tokens (plan coordinated_present u)) =
    erase_result (first_present (realize u)).
Proof.
  induction u;
    cbn [plan ordinary_plan coordinated_plan plain_tokens present_tokens realize];
    repeat match goal with
      | H : _ /\ _ |- _ =>
          let L := fresh "P" in let R := fresh "F" in destruct H as [L R]
      end.
  all: try (split; reflexivity).
  all: split; try apply erase_first_congr.
  all: try (apply erase_subject_congr; assumption).
  all: try (repeat rewrite <- subject_first_plan;
    repeat first [rewrite erase_result_determiner | rewrite erase_result_relative |
      rewrite erase_result_concat | rewrite erase_result_object | rewrite erase_result_join |
      rewrite erase_result_f10 | rewrite erase_result_reverse]; congruence).
  all: try (rewrite (erase_result_determiner d (plain_tokens (plan coordinated_present u))),
    (erase_result_determiner d (realize u)), P; reflexivity).
  - pose proof (iv_present_keeps_erasure (s10 u1 u2)) as K.
    cbn [realize] in K; rewrite K.
    repeat rewrite erase_result_reverse.
    rewrite P0, F, iv_present_keeps_erasure; reflexivity.
  - pose proof (iv_present_keeps_erasure (s12 j u1 u2)) as K.
    cbn [realize] in K; rewrite K.
    repeat rewrite erase_result_join.
    rewrite F, F0; repeat rewrite iv_present_keeps_erasure; reflexivity.
  - pose proof (iv_present_keeps_erasure (s16 u1 n u2)) as K.
    cbn [realize] in K; rewrite K.
    repeat rewrite erase_result_f10.
    rewrite P0, F, iv_present_keeps_erasure; reflexivity.
Qed.

Corollary amendment_changes_only_verb_forms A (u : tree A) :
  erase_result (amended_tokens u) = erase_result (realize u).
Proof. exact (proj1 (all_tree_amendment_erasure u)). Qed.

Corollary amendment_preserves_failure A (u : tree A) :
  amended_tokens u = None <-> realize u = None.
Proof.
  pose proof (amendment_changes_only_verb_forms u) as H.
  destruct (amended_tokens u), (realize u); cbn [erase_result option_map] in H;
    try discriminate; split; intros; try discriminate; reflexivity.
Qed.

Corollary amendment_preserves_surface_failure A (u : tree A) :
  amended_surface u = None <-> surface u = None.
Proof.
  change (option_map words (amended_tokens u) = None <-> option_map words (realize u) = None).
  pose proof (amendment_preserves_failure u) as H.
  destruct (amended_tokens u), (realize u); cbn [option_map] in *;
    intuition discriminate.
Qed.

Corollary amendment_preserves_token_identity A (u : tree A) before after :
  realize u = Some before -> amended_tokens u = Some after ->
  erase_forms before = erase_forms after /\ List.length before = List.length after.
Proof.
  intros B C; pose proof (amendment_changes_only_verb_forms u) as H.
  rewrite B, C in H; cbn [erase_result option_map] in H; inversion H as [E].
  split; [reflexivity|].
  apply (f_equal (@List.length token)) in E.
  unfold erase_forms in E; repeat rewrite length_map in E; symmetry; exact E.
Qed.
