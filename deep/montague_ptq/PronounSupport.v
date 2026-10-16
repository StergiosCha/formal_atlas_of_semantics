(* Finite semantic support, including elimination of unused bare-pronoun
   renaming dependencies. This is needed to quotient zero-width derivations. *)
From Coq Require Import List Bool Arith Eqdep_dec Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Meaning Surface SurfaceInvariant
  SurfaceAmendment SurfaceAmendmentSafety.
Import ListNotations.
Set Implicit Arguments.

Definition category_eq_dec : forall A B : cat, {A = B} + {A <> B}.
Proof. decide equality. Defined.
Definition tree_pronoun {A} (u : tree A) := match u with
  | s1_pronoun n => Some n | _ => None end.
Lemma tree_pronoun_packed A (u : tree A) n :
  tree_pronoun u = Some n -> existT tree A u = existT tree NP (s1_pronoun n).
Proof. destruct u; cbn; intro H; try discriminate; inversion H; reflexivity. Qed.
Lemma tree_pronoun_exact (u : tree NP) n : tree_pronoun u = Some n -> u = s1_pronoun n.
Proof.
  intro H; pose proof (@tree_pronoun_packed NP u n H) as E.
  exact (@Eqdep_dec.inj_pair2_eq_dec cat category_eq_dec tree NP u (s1_pronoun n) E).
Qed.

Definition rename_support k n xs :=
  if in_dec Nat.eq_dec n xs then k :: remove Nat.eq_dec n xs else xs.
Definition binder_support {A} (p : tree NP) n (q : tree A)
  (fp fq : list nat) :=
  match tree_pronoun p with
  | Some k => rename_support k n fq
  | None => fp ++ remove Nat.eq_dec n fq
  end.

Fixpoint support {A} (u : tree A) : list nat := match u with
  | s1_word _ | s1_name _ | s1_be | s1_necessarily => []
  | s1_pronoun n => [n]
  | s2 _ c => support c
  | s3 c n p => support c ++ remove Nat.eq_dec n (support p)
  | s4 p q | s5 p q | s6 p q | s7 p q | s8 p q | s9 p q | s10 p q
  | s11 _ p q | s12 _ p q | s13 p q | s17 _ p q => support p ++ support q
  | s14 p n q | s15 p n q | s16 p n q => binder_support p n q (support p) (support q)
  end.

Definition visible_indices xs := flat_map (fun u => match u with
  | indexed n _ => [n] | _ => [] end) xs.
Lemma visible_indices_append xs ys : visible_indices (xs ++ ys) =
  visible_indices xs ++ visible_indices ys.
Proof. apply flat_map_app. Qed.
Lemma visible_indices_cons u xs : visible_indices (u::xs) =
  visible_indices [u] ++ visible_indices xs.
Proof. destruct u; reflexivity. Qed.
Lemma visible_indices_replace n g xs :
  visible_indices (map (replace_pronoun n g) xs) = remove Nat.eq_dec n (visible_indices xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  destruct u; cbn [map replace_pronoun visible_indices flat_map]; try exact IH.
  destruct (Nat.eqb n n0) eqn:E; cbn [visible_indices flat_map app remove];
    destruct (Nat.eq_dec n n0); try (apply Nat.eqb_eq in E; congruence);
    try (apply Nat.eqb_neq in E; congruence).
  all: first [exact IH | f_equal; exact IH].
Qed.
Lemma visible_indices_rename n k xs :
  visible_indices (map (rename_pronoun n k) xs) =
  map (fun m => if Nat.eqb n m then k else m) (visible_indices xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  destruct u; cbn [map rename_pronoun visible_indices flat_map]; try exact IH.
  destruct (Nat.eqb n n0) eqn:E; cbn [visible_indices flat_map app map];
    unfold visible_indices in IH; rewrite E, IH; reflexivity.
Qed.
Lemma visible_indices_object xs : visible_indices (object_form xs) = visible_indices xs.
Proof.
  destruct xs as [|u xs]; [reflexivity|]; destruct u; destruct xs;
    cbn; try reflexivity; destruct c; reflexivity.
Qed.
Lemma visible_indices_inflect f xs out :
  inflect_first f xs = Some out -> visible_indices out = visible_indices xs.
Proof.
  revert out; induction xs as [|u xs IH]; intros out H; [discriminate|].
  destruct u; cbn [inflect_first] in H;
    try (destruct (inflect_first f xs) as [tail|] eqn:E; [|discriminate];
      inversion H; subst out; cbn [visible_indices flat_map app];
      unfold visible_indices in IH; rewrite (IH tail eq_refl); reflexivity).
  inversion H; reflexivity.
Qed.

Lemma visible_insert_support n alpha g xs out : insert_first n alpha g xs = Some out ->
  incl (visible_indices alpha) (visible_indices out) /\
  (forall m, In m (visible_indices xs) -> m <> n -> In m (visible_indices out)).
Proof.
  revert out; induction xs as [|u xs IH]; intros out H; [discriminate|].
  cbn [insert_first] in H.
  destruct (match u with indexed m _ => Nat.eqb n m | _ => false end) eqn:E.
  - destruct u; try discriminate; apply Nat.eqb_eq in E; subst n0.
    inversion H; subst out; rewrite visible_indices_append, visible_indices_replace.
    split; intros m I; [apply in_or_app; auto|].
    cbn [visible_indices flat_map app In] in I; intro N; destruct I as [I|I]; [congruence|].
    apply in_or_app; right; apply in_in_remove; [congruence|exact I].
  - destruct (insert_first n alpha g xs) as [tail|] eqn:T; [|discriminate].
    inversion H; subst out; destruct (IH tail eq_refl) as [A X].
    rewrite (visible_indices_cons u tail), (visible_indices_cons u xs); split.
    + intros m I; apply in_or_app; right; apply A; exact I.
    + intros m I N; apply in_app_or in I; apply in_or_app; destruct I; auto.
Qed.

Lemma bare_join_never j xs ys : bare_pronoun (xs ++ [literal j] ++ ys) = None.
Proof.
  destruct xs as [|u [|v xs]]; cbn [app bare_pronoun];
    try destruct u; try destruct c; reflexivity.
Qed.
Lemma realized_np_bare A (u : tree A) : A = NP -> forall xs,
  realize u = Some xs -> bare_pronoun xs = tree_pronoun u.
Proof.
  destruct u; intro E; try discriminate; intros xs H; cbn [realize] in H.
  - destruct l; discriminate.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - destruct (realize u) as [cs|]; [|discriminate]; inversion H; reflexivity.
  - unfold combine in H; destruct (realize u1), (realize u2); try discriminate.
    inversion H; apply bare_join_never.
Qed.

Lemma support_of_f10 A (p : tree NP) n (q : tree A) alpha body out :
  realize p = Some alpha -> incl (support p) (visible_indices alpha) ->
  incl (support q) (visible_indices body) -> f10 n alpha body = Some out ->
  incl (binder_support p n q (support p) (support q)) (visible_indices out).
Proof.
  intros P SP SQ H; unfold binder_support, f10 in *.
  rewrite (@realized_np_bare NP p eq_refl alpha P) in H.
  destruct (tree_pronoun p) as [k|] eqn:K.
  - inversion H; subst out; rewrite visible_indices_rename.
    unfold rename_support; destruct (in_dec Nat.eq_dec n (support q)) as [N|N]; intros m I.
    + destruct I as [I|I].
      * subst m; apply in_map_iff; exists n; split; [rewrite Nat.eqb_refl; reflexivity|apply SQ; exact N].
      * apply in_remove in I; destruct I as [I D].
        apply in_map_iff; exists m; split.
        -- assert (F : Nat.eqb n m = false) by (apply Nat.eqb_neq; congruence).
           rewrite F; reflexivity.
        -- apply SQ; exact I.
    + apply in_map_iff; exists m; split.
      * assert (D : n <> m) by (intro E; subst m; contradiction).
        apply Nat.eqb_neq in D; rewrite D; reflexivity.
      * apply SQ; exact I.
  - destruct (first_gender alpha) as [g|]; [|discriminate].
    destruct (@visible_insert_support n alpha g body out H) as [PA PB].
    intros m I; apply in_app_or in I; destruct I as [I|I].
    + apply PA; apply SP; exact I.
    + apply in_remove in I; destruct I as [I D]; apply PB; [apply SQ; exact I|congruence].
Qed.

Ltac support_children H :=
  repeat match type of H with
    | context [realize ?u] => let xs := fresh "part" in let E := fresh "realized" in
        destruct (realize u) as [xs|] eqn:E; cbn [combine concat_tokens join_tokens] in H; try discriminate
  end;
  repeat match goal with
    | IH : forall xs, Some ?p = Some xs -> _ |- _ =>
        let R := fresh "child" in pose proof (IH p eq_refl) as R; clear IH
  end.

Theorem support_is_visible A (u : tree A) : forall xs,
  realize u = Some xs -> incl (support u) (visible_indices xs).
Proof.
  induction u; intros xs H; cbn [realize support] in *.
  - intros m I; contradiction.
  - intros m I; contradiction.
  - inversion H; subst; intros m I; exact I.
  - intros m I; contradiction.
  - intros m I; contradiction.
  - support_children H; inversion H; subst; exact child.
  - support_children H; destruct (first_gender part) as [g|]; [|discriminate].
    inversion H; subst; repeat rewrite visible_indices_append.
    cbn [visible_indices flat_map app]; rewrite visible_indices_replace.
    intros m I; apply in_app_or in I; apply in_or_app; destruct I as [I|I].
    + left; apply child0; exact I.
    + right; apply in_remove in I; destruct I as [I N]; apply in_in_remove; [congruence|apply child; exact I].
  - support_children H; unfold subject_verb in H.
    destruct (inflect_first present part0) as [out|] eqn:E; [|discriminate].
    inversion H; subst; rewrite visible_indices_append, (@visible_indices_inflect present part0 out E).
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; rewrite visible_indices_append, visible_indices_object.
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; rewrite visible_indices_append, visible_indices_object.
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; rewrite visible_indices_append.
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; rewrite visible_indices_append.
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; rewrite visible_indices_append.
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; rewrite visible_indices_append.
    apply incl_app; [eapply incl_appr|eapply incl_appl]; eassumption.
  - support_children H; inversion H; subst; repeat rewrite visible_indices_append.
    cbn [visible_indices flat_map app]; apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; repeat rewrite visible_indices_append.
    cbn [visible_indices flat_map app]; apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; inversion H; subst; repeat rewrite visible_indices_append.
    cbn [visible_indices flat_map app]; apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
  - support_children H; eapply support_of_f10; eassumption.
  - support_children H; eapply support_of_f10; eassumption.
  - support_children H; eapply support_of_f10; eassumption.
  - support_children H; unfold subject_verb in H.
    match goal with k : tense_sign |- _ =>
      destruct (inflect_first (sign_form k) part0) as [out|] eqn:E; [|discriminate];
      inversion H; subst; rewrite visible_indices_append, (@visible_indices_inflect (sign_form k) part0 out E)
    end.
    apply incl_app; [eapply incl_appl|eapply incl_appr]; eassumption.
Qed.

Definition agree_on M (r s : pvalues M) xs := forall n, In n xs -> r n = s n.
Arguments agree_on M r s xs : clear implicits.
Lemma agree_on_left M r s xs ys : agree_on M r s (xs ++ ys) -> agree_on M r s xs.
Proof. intros H n N; apply H; apply in_or_app; auto. Qed.
Arguments agree_on_left {M r s xs ys} _.
Lemma agree_on_right M r s xs ys : agree_on M r s (xs ++ ys) -> agree_on M r s ys.
Proof. intros H n N; apply H; apply in_or_app; auto. Qed.
Arguments agree_on_right {M r s xs ys} _.
Lemma agree_on_update M r s n x xs :
  agree_on M r s (remove Nat.eq_dec n xs) ->
  agree_on M (update r n x) (update s n x) xs.
Proof.
  intros H m I; unfold update; destruct (Nat.eqb m n) eqn:E; [reflexivity|].
  apply H; apply in_in_remove; [apply Nat.eqb_neq in E; congruence|exact I].
Qed.
Arguments agree_on_update {M r s n} x {xs} _.
Lemma agree_on_rename M r s k n xs : agree_on M r s (rename_support k n xs) ->
  agree_on M (update r n (r k)) (update s n (s k)) xs.
Proof.
  unfold rename_support; destruct (in_dec Nat.eq_dec n xs) as [N|N]; intros H m I;
    unfold update; destruct (Nat.eqb m n) eqn:E.
  - apply H; left; reflexivity.
  - apply H; right; apply in_in_remove; [apply Nat.eqb_neq in E; congruence|exact I].
  - apply Nat.eqb_eq in E; subst m; contradiction.
  - apply H; exact I.
Qed.
Arguments agree_on_rename {M r s k n xs} _.

Theorem interpretation_depends_on_support M A (u : tree A) :
  forall r s, agree_on M r s (support u) -> forall i, denote M u r i = denote M u s i.
Proof.
  induction u; intros r s H i; cbn [support] in H; cbn [denote].
  - reflexivity.
  - reflexivity.
  - apply (function_extensionality M); intro P; rewrite (H n (or_introl eq_refl)); reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHu r s H); reflexivity.
  - apply (function_extensionality M); intro x.
    rewrite (IHu1 r s (agree_on_left H)).
    rewrite (IHu2 _ _ (agree_on_update _ (agree_on_right H))); reflexivity.
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro j; apply IHu2; apply (agree_on_right H).
  - rewrite (IHu1 r s (agree_on_left H)), (IHu2 r s (agree_on_right H)); reflexivity.
  - apply (function_extensionality M); intro x.
    rewrite (IHu1 r s (agree_on_left H)), (IHu2 r s (agree_on_right H)); reflexivity.
  - apply (function_extensionality M); intro P.
    rewrite (IHu1 r s (agree_on_left H)), (IHu2 r s (agree_on_right H)); reflexivity.
  - unfold binder_support in H; destruct (tree_pronoun u1) as [k|] eqn:E.
    + apply tree_pronoun_exact in E; subst u1; cbn [denote].
      apply IHu2; apply agree_on_rename; exact H.
    + rewrite (IHu1 r s (agree_on_left H)); f_equal.
      apply (function_extensionality M); intro j; apply (function_extensionality M); intro x.
      apply IHu2; apply agree_on_update; apply (agree_on_right H).
  - apply (function_extensionality M); intro y.
    unfold binder_support in H; destruct (tree_pronoun u1) as [k|] eqn:E.
    + apply tree_pronoun_exact in E; subst u1; cbn [denote].
      rewrite (IHu2 _ _ (agree_on_rename H)); reflexivity.
    + rewrite (IHu1 r s (agree_on_left H)); f_equal.
      apply (function_extensionality M); intro j; apply (function_extensionality M); intro x.
      rewrite (IHu2 _ _ (agree_on_update _ (agree_on_right H))); reflexivity.
  - apply (function_extensionality M); intro y.
    unfold binder_support in H; destruct (tree_pronoun u1) as [k|] eqn:E.
    + apply tree_pronoun_exact in E; subst u1; cbn [denote].
      rewrite (IHu2 _ _ (agree_on_rename H)); reflexivity.
    + rewrite (IHu1 r s (agree_on_left H)); f_equal.
      apply (function_extensionality M); intro j; apply (function_extensionality M); intro x.
      rewrite (IHu2 _ _ (agree_on_update _ (agree_on_right H))); reflexivity.
  - f_equal; apply (function_extensionality M); intro j.
    rewrite (IHu1 r s (agree_on_left H)); f_equal.
    apply (function_extensionality M); intro l; apply IHu2; apply (agree_on_right H).
Qed.

Lemma visible_indices_erase xs : visible_indices (erase_forms xs) = visible_indices xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [erase_forms map erase_verb_form visible_indices flat_map app];
    try exact IH; f_equal; exact IH.
Qed.

Theorem amended_support_is_visible A (u : tree A) xs :
  amended_tokens u = Some xs -> incl (support u) (visible_indices xs).
Proof.
  intro E; pose proof (amendment_changes_only_verb_forms u) as H; rewrite E in H.
  destruct (realize u) as [ys|] eqn:R; [|discriminate].
  cbn [erase_result option_map] in H; injection H as H.
  apply (f_equal visible_indices) in H; rewrite !visible_indices_erase in H.
  rewrite H; apply (support_is_visible u R).
Qed.

Definition indexed_word s := orb (String.prefix "he_" s) (String.prefix "him_" s).
Definition closed_words xs := forallb (fun s => negb (indexed_word s)) xs.

Lemma prefix_empty s : String.prefix "" s = true.
Proof. destruct s; reflexivity. Qed.

Lemma closed_words_have_no_indices xs : closed_words (words xs) = true -> visible_indices xs = [].
Proof.
  induction xs as [|u xs IH]; [reflexivity|].
  unfold closed_words, words in *; cbn [flat_map]; rewrite forallb_app.
  intro H; apply andb_true_iff in H; destruct H as [T R].
  specialize (IH R); destruct u; cbn [visible_indices flat_map app]; try exact IH.
  destruct c; cbv [token_words pronoun_text indexed_word] in T; simpl in T;
    rewrite prefix_empty in T; discriminate.
Qed.

Theorem closed_surface_assignment_independence M A (u : tree A) text :
  surface u = Some text -> closed_words text = true ->
  forall r s i, denote M u r i = denote M u s i.
Proof.
  unfold surface; destruct (realize u) as [xs|] eqn:E; [|discriminate].
  cbn [option_map]; intro H; inversion H; subst text; intro C; intros r s i.
  pose proof (closed_words_have_no_indices xs C) as V.
  apply interpretation_depends_on_support; intros n N.
  pose proof (@support_is_visible A u xs E n N) as I; rewrite V in I; contradiction.
Qed.

Theorem amended_closed_assignment_independence M A (u : tree A) text :
  amended_surface u = Some text -> closed_words text = true ->
  forall r s i, denote M u r i = denote M u s i.
Proof.
  change (option_map words (amended_tokens u) = Some text -> closed_words text = true ->
    forall r s i, denote M u r i = denote M u s i).
  destruct (amended_tokens u) as [xs|] eqn:E; [|discriminate].
  cbn [option_map]; intro H; inversion H; subst text; intro C; intros r s i.
  pose proof (closed_words_have_no_indices xs C) as V.
  apply interpretation_depends_on_support; intros n N.
  pose proof (@amended_support_is_visible A u xs E n N) as I; rewrite V in I; contradiction.
Qed.

Lemma rename_without_visible_indices n k xs : visible_indices xs = [] ->
  map (rename_pronoun n k) xs = xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u; cbn; intro H;
    try discriminate; f_equal; apply IH; exact H.
Qed.

Theorem closed_bare_renaming_surface n k (u : tree ct) text :
  surface u = Some text -> closed_words text = true ->
  surface (s14 (s1_pronoun k) n u) = Some text.
Proof.
  unfold surface; destruct (realize u) as [xs|] eqn:E; [|discriminate].
  cbn [option_map]; intro H; inversion H; subst text; intro C.
  cbn [realize]; rewrite E; cbn [combine f10 bare_pronoun].
  rewrite rename_without_visible_indices by (apply closed_words_have_no_indices; exact C).
  reflexivity.
Qed.

Theorem closed_bare_renaming_semantics M n k (u : tree ct) text :
  surface u = Some text -> closed_words text = true ->
  forall r i, denote M (s14 (s1_pronoun k) n u) r i = denote M u r i.
Proof.
  intros S C r i; cbn [denote]; eapply closed_surface_assignment_independence; eassumption.
Qed.

Fixpoint repeated_bare_renaming count n k (u : tree ct) := match count with
  | 0 => u | S count => s14 (s1_pronoun k) n (repeated_bare_renaming count n k u) end.

Theorem arbitrarily_many_neutral_renamings M count n k u text :
  surface u = Some text -> closed_words text = true ->
  surface (repeated_bare_renaming count n k u) = Some text /\
  forall r i, denote M (repeated_bare_renaming count n k u) r i = denote M u r i.
Proof.
  intros S C; induction count as [|count [IH J]]; cbn [repeated_bare_renaming].
  - split; [exact S|reflexivity].
  - split; [eapply closed_bare_renaming_surface; eassumption|].
    intros r i; rewrite (@closed_bare_renaming_semantics M n k _ text IH C r i); apply J.
Qed.
