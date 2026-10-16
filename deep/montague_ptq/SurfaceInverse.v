(* Finite inversion certificates for F10. These certify local operations;
   they do not by themselves certify the whole inverse grammar search. *)
From Coq Require Import List Bool Arith Lia.
From Coq Require Import Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Meaning Surface PronounSupport
  SurfaceAmendment GrammarRenaming RenamingNormalization.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Fixpoint next_index ns := match ns with [] => 0 | n::rest => Nat.max (S n) (next_index rest) end.
Definition fresh_index xs := next_index (visible_indices xs).
Lemma next_index_bound n ns : In n ns -> n < next_index ns.
Proof.
  induction ns as [|m ns IH]; [cbn; contradiction|].
  change (m = n \/ In n ns -> n < Nat.max (S m) (next_index ns)).
  intros [E|N];
    [subst m; pose proof (Nat.le_max_l (S n) (next_index ns))|
      specialize (IH N); pose proof (Nat.le_max_r (S m) (next_index ns))]; lia.
Qed.

Theorem fresh_index_not_visible xs : ~ In (fresh_index xs) (visible_indices xs).
Proof. intro H; apply next_index_bound in H; unfold fresh_index in H; lia. Qed.

(* Reverse the bare-pronoun branch by splitting an output index class.
   The two presence tests retain precisely nonempty, proper splits. *)
Fixpoint split_index n k out : list (list token) := match out with
  | [] => [[]]
  | u::rest => let tails := split_index n k rest in
      map (cons u) tails ++ match u with
        | indexed m c => if Nat.eqb k m then map (cons (indexed n c)) tails else []
        | _ => [] end
  end.
Definition index_present n xs := existsb (Nat.eqb n) (visible_indices xs).
Lemma index_present_spec n xs : index_present n xs = true <-> In n (visible_indices xs).
Proof.
  unfold index_present; rewrite existsb_exists; split.
  - intros [m [I E]]; apply Nat.eqb_eq in E; subst m; exact I.
  - intro I; exists n; split; [exact I|apply Nat.eqb_refl].
Qed.
Definition merge_inverses n k out :=
  filter (fun body => andb (index_present n body) (index_present k body)) (split_index n k out).

Theorem split_index_complete n k body :
  In body (split_index n k (map (rename_pronoun n k) body)).
Proof.
  induction body as [|u body IH]; [cbn; auto|].
  destruct u; cbn [map rename_pronoun];
    try (cbn [split_index]; apply in_or_app; left; apply in_map; exact IH).
  destruct (Nat.eqb n n0) eqn:E; cbn [split_index].
  - apply Nat.eqb_eq in E; subst n0; rewrite Nat.eqb_refl;
      apply in_or_app; right; apply in_map; exact IH.
  - apply in_or_app; left; apply in_map; exact IH.
Qed.
Theorem split_index_sound n k out body :
  ~ In n (visible_indices out) -> In body (split_index n k out) ->
  map (rename_pronoun n k) body = out.
Proof.
  revert body; induction out as [|u out IH]; intros body N H; cbn in H.
  - destruct H as [H|H]; [subst body; reflexivity|contradiction].
  - assert (T : ~ In n (visible_indices out)).
    { intro K; apply N; rewrite visible_indices_cons; apply in_or_app; auto. }
    apply in_app_or in H; destruct H as [H|H].
    + apply in_map_iff in H; destruct H as [rest [E H]]; subst body; cbn [map].
      rewrite (IH rest T H); f_equal; destruct u; try reflexivity.
      cbn [rename_pronoun]; destruct (Nat.eqb n n0) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E; subst n0; exfalso; apply N; cbn; auto.
    + destruct u; try contradiction; destruct (Nat.eqb k n0) eqn:K; [|contradiction].
      apply Nat.eqb_eq in K; subst n0.
      apply in_map_iff in H; destruct H as [rest [E H]]; subst body; cbn [map rename_pronoun].
      rewrite Nat.eqb_refl, (IH rest T H); reflexivity.
Qed.
Theorem genuine_merge_inverse_complete n k body :
  In n (visible_indices body) -> In k (visible_indices body) ->
  In body (merge_inverses n k (map (rename_pronoun n k) body)).
Proof.
  intros N K; unfold merge_inverses; apply filter_In; split; [apply split_index_complete|].
  apply andb_true_iff; split; apply index_present_spec; assumption.
Qed.
Theorem genuine_merge_inverse_sound n k out body :
  ~ In n (visible_indices out) -> In body (merge_inverses n k out) ->
  f10 n [indexed k subject_case] body = Some out /\
  In n (visible_indices body) /\ In k (visible_indices body).
Proof.
  intros N H; apply filter_In in H; destruct H as [H P]; apply andb_true_iff in P.
  destruct P as [P Q]; apply index_present_spec in P; apply index_present_spec in Q.
  split; [cbn [f10 bare_pronoun]; f_equal; eapply split_index_sound; eassumption|auto].
Qed.
Theorem canonical_merge_inverse_sound k out body :
  In body (merge_inverses (fresh_index out) k out) ->
  f10 (fresh_index out) [indexed k subject_case] body = Some out /\
  In (fresh_index out) (visible_indices body) /\ In k (visible_indices body).
Proof. apply genuine_merge_inverse_sound; apply fresh_index_not_visible. Qed.

Lemma f10_surviving_indices n alpha body out : f10 n alpha body = Some out ->
  forall m, In m (visible_indices body) -> m <> n -> In m (visible_indices out).
Proof.
  unfold f10; destruct (bare_pronoun alpha) as [k|].
  - intro H; injection H as H; subst out; rewrite visible_indices_rename.
    intros m I N; apply in_map_iff; exists m; split; [|exact I].
    assert (E : Nat.eqb n m = false) by (apply Nat.eqb_neq; congruence); rewrite E; reflexivity.
  - destruct (first_gender alpha) as [g|]; [|discriminate].
    intro H; exact (proj2 (@visible_insert_support n alpha g body out H)).
Qed.
Lemma output_fresh_for_body n alpha body out : f10 n alpha body = Some out ->
  fresh_index out = n \/ ~ In (fresh_index out) (visible_indices body).
Proof.
  intro H; destruct (Nat.eq_dec (fresh_index out) n) as [E|E]; [auto|right].
  intro I; apply (fresh_index_not_visible out); eapply f10_surviving_indices; eassumption.
Qed.

Theorem canonical_binding_index b p n q alpha body out :
  realize p = Some alpha -> realize q = Some body -> f10 n alpha body = Some out ->
  exists q' : tree (binding_type b), tree_size q' = tree_size q /\
    tree_equivalent (quantify b p (fresh_index out) q') (quantify b p n q).
Proof.
  intros P Q H; destruct (@output_fresh_for_body n alpha body out H) as [E|E].
  - exists q; rewrite E; split; [reflexivity|apply tree_equivalent_refl].
  - exists (rename_tree (swap_index n (fresh_index out)) q); split;
      [apply rename_tree_size|eapply freshen_binding_equivalent; eassumption].
Qed.

Fixpoint splits {A} (xs : list A) : list (list A * list A) := match xs with
  | [] => [([],[])]
  | x::rest => ([],x::rest)::map (fun pair => (x::fst pair,snd pair)) (splits rest)
  end.
Lemma split_at_append A (left right : list A) : In (left,right) (splits (left ++ right)).
Proof.
  induction left as [|x left IH]; [cbn; destruct right; cbn; auto|].
  cbn; right; apply in_map_iff; exists (left,right); auto.
Qed.
Lemma split_sound A (xs left right : list A) : In (left,right) (splits xs) -> xs = left ++ right.
Proof.
  revert left right; induction xs as [|x xs IH]; intros left right H; cbn in H.
  - destruct H as [H|H]; [inversion H; reflexivity|contradiction].
  - destruct H as [H|H]; [inversion H; reflexivity|].
    apply in_map_iff in H; destruct H as [[l r] [E H]]; inversion E; subst;
      cbn; f_equal; eapply IH; exact H.
Qed.
Definition gender_eq_dec : forall g h : gender, {g=h}+{g<>h}.
Proof. decide equality. Defined.

Fixpoint restore_pronouns n g xs : list (list token) := match xs with
  | [] => [[]]
  | u::rest => let tails := restore_pronouns n g rest in
      map (cons u) tails ++ match u with
        | plain h c => if gender_eq_dec g h then map (cons (indexed n c)) tails else []
        | _ => [] end
  end.
Lemma restore_keeps_input n g xs : In xs (restore_pronouns n g xs).
Proof.
  induction xs as [|u xs IH]; [cbn; auto|]; cbn; apply in_or_app; left;
    apply in_map; exact IH.
Qed.
Theorem replacement_inverse_complete n g body :
  In body (restore_pronouns n g (map (replace_pronoun n g) body)).
Proof.
  induction body as [|u body IH]; [cbn; auto|].
  destruct u; cbn [map replace_pronoun];
    try (cbn [restore_pronouns]; apply in_or_app; left; apply in_map; exact IH).
  destruct (Nat.eqb n n0) eqn:E; cbn [restore_pronouns].
  - apply Nat.eqb_eq in E; subst n0; destruct (gender_eq_dec g g); [|contradiction].
    apply in_or_app; right; apply in_map; exact IH.
  - apply in_or_app; left; apply in_map; exact IH.
Qed.
Theorem replacement_inverse_sound n g out body :
  ~ In n (visible_indices out) -> In body (restore_pronouns n g out) ->
  map (replace_pronoun n g) body = out.
Proof.
  revert body; induction out as [|u out IH]; intros body N H; cbn in H.
  - destruct H as [H|H]; [subst body; reflexivity|contradiction].
  - assert (T : ~ In n (visible_indices out)).
    { intro K; apply N; rewrite visible_indices_cons; apply in_or_app; auto. }
    apply in_app_or in H; destruct H as [H|H].
    + apply in_map_iff in H; destruct H as [rest [E H]]; subst body; cbn [map].
      rewrite (IH rest T H); f_equal; destruct u; try reflexivity.
      cbn [replace_pronoun]; destruct (Nat.eqb n n0) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E; subst n0; exfalso; apply N; cbn; auto.
    + destruct u; try contradiction; destruct (gender_eq_dec g g0); [subst g0|contradiction].
      apply in_map_iff in H; destruct H as [rest [E H]]; subst body; cbn [map replace_pronoun].
      rewrite Nat.eqb_refl, (IH rest T H); reflexivity.
Qed.

Theorem first_insertion_decomposition n alpha g body out :
  insert_first n alpha g body = Some out -> exists before after c,
    body = before ++ indexed n c :: after /\
    ~ In n (visible_indices before) /\ out = before ++ alpha ++ map (replace_pronoun n g) after.
Proof.
  revert out; induction body as [|u body IH]; intros out H; [discriminate|].
  cbn [insert_first] in H.
  destruct (match u with indexed m _ => Nat.eqb n m | _ => false end) eqn:E.
  - destruct u; try discriminate; apply Nat.eqb_eq in E; subst n0; injection H as H; subst out.
    exists [], body, c; cbn; auto.
  - destruct (insert_first n alpha g body) as [tail|] eqn:R; [|discriminate].
    injection H as H; subst out; destruct (IH tail eq_refl) as [before [after [c [B [N O]]]]].
    exists (u::before), after, c; subst body tail; split; [reflexivity|]; split; [|reflexivity].
    rewrite visible_indices_cons; intro I; apply in_app_or in I; destruct I as [I|I]; [|contradiction].
    destruct u; cbn [visible_indices flat_map app In] in I; try contradiction.
    destruct I as [I|I]; [subst n0; rewrite Nat.eqb_refl in E; discriminate|contradiction].
Qed.

Definition insertion_inverses n out : list (list token * list token) :=
  flat_map (fun outer => let before := fst outer in
    flat_map (fun inner => let alpha := fst inner in let after := snd inner in
      match first_gender alpha with
      | None => []
      | Some g => flat_map (fun tail =>
          [(alpha, before ++ indexed n subject_case :: tail);
           (alpha, before ++ indexed n object_case :: tail)]) (restore_pronouns n g after)
      end) (splits (snd outer))) (splits out).

Theorem nonbare_insertion_inverse_complete n alpha body out :
  bare_pronoun alpha = None -> f10 n alpha body = Some out ->
  In (alpha,body) (insertion_inverses n out).
Proof.
  intros B H; unfold f10 in H; rewrite B in H; destruct (first_gender alpha) as [g|] eqn:G; [|discriminate].
  destruct (@first_insertion_decomposition n alpha g body out H) as [before [after [c [E [N O]]]]].
  subst body out; unfold insertion_inverses.
  apply in_flat_map; exists (before, alpha ++ map (replace_pronoun n g) after); split; [apply split_at_append|].
  cbn [fst snd]; apply in_flat_map; exists (alpha, map (replace_pronoun n g) after); split; [apply split_at_append|].
  cbn [fst snd]; rewrite G; apply in_flat_map; exists after; split; [apply replacement_inverse_complete|].
  destruct c; cbn; auto.
Qed.

Lemma insert_first_at_split n alpha g before after c :
  ~ In n (visible_indices before) ->
  insert_first n alpha g (before ++ indexed n c :: after) =
    Some (before ++ alpha ++ map (replace_pronoun n g) after).
Proof.
  induction before as [|u before IH]; intro N.
  - cbn [app insert_first]; rewrite Nat.eqb_refl; reflexivity.
  - assert (T : ~ In n (visible_indices before)).
    { intro K; apply N; rewrite visible_indices_cons; apply in_or_app; auto. }
    cbn [app insert_first]; rewrite (IH T).
    destruct u; try reflexivity; destruct (Nat.eqb n n0) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E; subst n0; exfalso; apply N; cbn; auto.
Qed.
Theorem nonbare_insertion_inverse_sound n alpha body out :
  ~ In n (visible_indices out) -> bare_pronoun alpha = None ->
  In (alpha,body) (insertion_inverses n out) -> f10 n alpha body = Some out.
Proof.
  intros N B H; unfold insertion_inverses in H.
  apply in_flat_map in H; destruct H as [[before rest] [O H]]; cbn [fst snd] in H.
  apply in_flat_map in H; destruct H as [[a after] [I H]]; cbn [fst snd] in H.
  destruct (first_gender a) as [g|] eqn:G; [|contradiction].
  apply in_flat_map in H; destruct H as [tail [T H]].
  apply split_sound in O; apply split_sound in I; subst rest out.
  assert (P : ~ In n (visible_indices before)).
  { intro K; apply N; rewrite visible_indices_append; apply in_or_app; auto. }
  assert (S : ~ In n (visible_indices after)).
  { intro K; apply N; repeat rewrite visible_indices_append.
    apply in_or_app; right; apply in_or_app; right; exact K. }
  pose proof (@replacement_inverse_sound n g after tail S T) as R.
  cbn in H; destruct H as [E|[E|H]]; [| |contradiction]; inversion E; subst a body;
    unfold f10; rewrite B,G,insert_first_at_split by exact P; rewrite R; reflexivity.
Qed.

Example restore_all_coindexed_positions :
  In ([name mary], [indexed 0 subject_case; verb (vtv love) present; indexed 0 object_case])
    (insertion_inverses 0 [name mary; verb (vtv love) present; plain feminine object_case]).
Proof. apply nonbare_insertion_inverse_complete; reflexivity. Qed.
Example merge_cannot_use_an_empty_split :
  ~ In [indexed 1 subject_case; indexed 1 object_case]
    (merge_inverses 0 1 [indexed 1 subject_case; indexed 1 object_case]).
Proof. cbn; intuition discriminate. Qed.
Example merge_cannot_rename_the_entire_class :
  ~ In [indexed 0 subject_case; indexed 0 object_case]
    (merge_inverses 0 1 [indexed 1 subject_case; indexed 1 object_case]).
Proof. cbn; intuition discriminate. Qed.
Example merge_keeps_both_case_sensitive_splits :
  merge_inverses 0 1 [indexed 1 subject_case; indexed 1 object_case] =
    [[indexed 1 subject_case; indexed 0 object_case];
     [indexed 0 subject_case; indexed 1 object_case]].
Proof. reflexivity. Qed.

(* S3 has its own binder. Freshening changes the relative sentence and its
   bound index, never the noun's free indices. *)
Theorem freshen_relative_equivalent (c : tree CN) n k (p : tree ct) body :
  realize p = Some body -> ~ In k (visible_indices body) ->
  tree_equivalent (s3 c k (rename_tree (swap_index n k) p)) (s3 c n p).
Proof.
  intros R K; split.
  - intro policy; cbn [plan]; rewrite (rename_tree_plan (swap_index_injective n k)).
    cbn [rename_plan plain_tokens];
      destruct (plain_tokens (plan policy c)) as [cs|] eqn:C;
      destruct (plain_tokens (plan policy p)) as [ps|] eqn:P;
      cbn [combine rename_result option_map]; try reflexivity.
    destruct (first_gender cs) as [g|]; [|reflexivity].
    rewrite replace_swap_fresh; [reflexivity|].
    rewrite (proj1 (@plan_indices policy ct p body R) ps P); exact K.
  - intros M r i; cbn [denote]; apply (function_extensionality M); intro x.
    rewrite (@freshen_body_meaning M ct p n k body R K r x i); reflexivity.
Qed.

Definition relative_output n cs ps := match first_gender cs with
  | Some g => Some (cs ++ [literal "such"%string; literal "that"%string] ++
      map (replace_pronoun n g) ps)
  | None => None end.
Lemma relative_output_surviving_indices n cs body out :
  relative_output n cs body = Some out -> forall m,
  In m (visible_indices body) -> m <> n -> In m (visible_indices out).
Proof.
  unfold relative_output; destruct (first_gender cs) as [g|]; [|discriminate].
  intro H; injection H as H; subst out; intros m I N.
  repeat rewrite visible_indices_append; cbn [visible_indices flat_map app].
  apply in_or_app; right; rewrite visible_indices_replace; apply in_in_remove; assumption.
Qed.
Theorem canonical_relative_index c n p cs body out :
  realize c = Some cs -> realize p = Some body -> relative_output n cs body = Some out ->
  exists p' : tree ct, tree_size p' = tree_size p /\
    tree_equivalent (s3 c (fresh_index out) p') (s3 c n p).
Proof.
  intros C P O; destruct (Nat.eq_dec (fresh_index out) n) as [E|E].
  - exists p; rewrite E; split; [reflexivity|apply tree_equivalent_refl].
  - exists (rename_tree (swap_index n (fresh_index out)) p); split; [apply rename_tree_size|].
    eapply freshen_relative_equivalent; [exact P|].
    intro I; apply (fresh_index_not_visible out); eapply relative_output_surviving_indices; eassumption.
Qed.

Definition noun_with_retained_index :=
  s3 (s1_word (lcn man)) 2 (s4 (s1_pronoun 1) (s1_word (liv talk))).
Example noun_retains_a_free_index : support noun_with_retained_index = [1].
Proof. reflexivity. Qed.
Example relative_freshening_leaves_the_noun_untouched :
  tree_equivalent
    (s3 noun_with_retained_index 1
      (rename_tree (swap_index 0 1) (s4 (s1_pronoun 0) (s1_word (liv walk)))))
    (s3 noun_with_retained_index 0
      (s4 (s1_pronoun 0) (s1_word (liv walk)))).
Proof. eapply freshen_relative_equivalent; [reflexivity|cbn; intuition discriminate]. Qed.
