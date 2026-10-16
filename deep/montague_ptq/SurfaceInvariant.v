(* A grammar invariant for literal S4/S12: a coordinator cannot immediately
   precede a finite verb. This is about all analysis trees, not a depth limit. *)
From Coq Require Import List Bool Arith Strings.String.
From MontaguePTQ Require Import Syntax Grammar Surface Catalogue.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Definition coordinator u := match u with
  | literal s => orb (String.eqb s "and") (String.eqb s "or") | _ => false end.
Definition finite_token u := match u with
  | verb _ infinitive => false | verb _ _ => true | _ => false end.
Definition front_finite xs := match xs with [] => false | u::_ => finite_token u end.
Fixpoint scan (previous : bool) xs := match xs with
  | [] => true
  | u::rest => andb (negb (andb previous (finite_token u))) (scan (coordinator u) rest)
  end.
Fixpoint end_flag (previous : bool) xs := match xs with
  | [] => previous | u::rest => end_flag (coordinator u) rest end.
Definition sequence_ok xs := scan false xs = true /\ end_flag false xs = false /\
  front_finite xs = false /\ xs <> [].
Definition starts_verb xs := exists v rest, xs = verb v infinitive :: rest.

Lemma scan_flag xs p : scan p xs = andb (negb (andb p (front_finite xs))) (scan false xs).
Proof. destruct xs as [|u xs]; destruct p; cbn; [reflexivity|reflexivity|reflexivity|].
  destruct (finite_token u); cbn; reflexivity. Qed.
Lemma end_flag_nonempty xs p : xs <> [] -> end_flag p xs = end_flag false xs.
Proof. destruct xs; cbn; intuition. Qed.
Lemma scan_append xs ys p :
  scan p (xs ++ ys) = andb (scan p xs) (scan (end_flag p xs) ys).
Proof.
  revert p; induction xs; intro p; cbn; [reflexivity|].
  rewrite IHxs, andb_assoc; reflexivity.
Qed.
Lemma end_flag_append xs ys p : end_flag p (xs ++ ys) = end_flag (end_flag p xs) ys.
Proof. revert p; induction xs; intro p; cbn; auto. Qed.

Lemma sequence_append xs ys : sequence_ok xs -> sequence_ok ys -> sequence_ok (xs ++ ys).
Proof.
  intros [S [E [F N]]] [T [D [G K]]]; unfold sequence_ok.
  rewrite scan_append, end_flag_append, S, E, T, D; cbn; repeat split; auto.
  - destruct xs; [contradiction|exact F].
  - destruct xs; [contradiction|discriminate].
Qed.

Lemma scan_good xs p : sequence_ok xs -> scan p xs = true.
Proof. intros [S [E [F N]]]; rewrite scan_flag, F, S; destruct p; reflexivity. Qed.
Lemma end_good xs p : sequence_ok xs -> end_flag p xs = false.
Proof. intros [S [E [F N]]]; rewrite end_flag_nonempty by exact N; exact E. Qed.

Lemma map_flags f xs : (forall u, coordinator (f u) = coordinator u) ->
  (forall u, finite_token (f u) = finite_token u) ->
  (forall p, scan p (map f xs) = scan p xs /\ end_flag p (map f xs) = end_flag p xs) /\
  front_finite (map f xs) = front_finite xs.
Proof.
  intros C F; induction xs as [|u xs [IH J]]; cbn.
  - split; [intros; auto|reflexivity].
  - rewrite C, F; split; [intro p; destruct (IH (coordinator u)); rewrite H,H0; auto|reflexivity].
Qed.

Lemma replace_flags n g xs :
  (forall p, scan p (map (replace_pronoun n g) xs) = scan p xs /\
    end_flag p (map (replace_pronoun n g) xs) = end_flag p xs) /\
  front_finite (map (replace_pronoun n g) xs) = front_finite xs.
Proof.
  apply map_flags; intro u; destruct u; cbn; try reflexivity;
    destruct (Nat.eqb n n0); reflexivity.
Qed.

Lemma rename_flags n k xs :
  (forall p, scan p (map (rename_pronoun n k) xs) = scan p xs /\
    end_flag p (map (rename_pronoun n k) xs) = end_flag p xs) /\
  front_finite (map (rename_pronoun n k) xs) = front_finite xs.
Proof.
  apply map_flags; intro u; destruct u; cbn; try reflexivity;
    destruct (Nat.eqb n n0); reflexivity.
Qed.

Lemma front_append xs ys : xs <> [] -> front_finite (xs ++ ys) = front_finite xs.
Proof. destruct xs; cbn; intuition. Qed.

Lemma insert_flags n alpha g xs out : sequence_ok alpha -> insert_first n alpha g xs = Some out ->
  (forall p, scan p out = scan p xs /\ end_flag p out = end_flag p xs) /\
  front_finite out = front_finite xs /\ out <> [].
Proof.
  intros A; revert out; induction xs as [|u xs IH]; intros out H; [discriminate|].
  cbn [insert_first] in H.
  destruct (match u with indexed m _ => Nat.eqb n m | _ => false end) eqn:E.
  - inversion H; subst out; destruct u; try discriminate.
    destruct (replace_flags n g xs) as [R F].
    split.
    + intro p; rewrite scan_append, end_flag_append, scan_good by exact A.
      rewrite end_good by exact A; cbn [scan end_flag coordinator finite_token].
      destruct (R false); rewrite H0,H1; destruct p; cbn; auto.
    + rewrite front_append by exact (proj2 (proj2 (proj2 A))).
      split; [exact (proj1 (proj2 (proj2 A)))|].
      destruct alpha; [exfalso; apply (proj2 (proj2 (proj2 A))); reflexivity|discriminate].
  - destruct (insert_first n alpha g xs) as [tail|] eqn:T; [|discriminate].
    inversion H; subst out; destruct (IH tail eq_refl) as [R [F N]].
    split; [intro p; cbn; destruct (R (coordinator u)); rewrite H0,H1; auto|].
    split; [reflexivity|discriminate].
Qed.

Lemma f10_sequence n alpha xs out : sequence_ok alpha -> sequence_ok xs ->
  f10 n alpha xs = Some out -> sequence_ok out.
Proof.
  intros A X H; unfold f10 in H; destruct (bare_pronoun alpha) as [k|].
  - inversion H; subst out; destruct (rename_flags n k xs) as [R F].
    destruct X as [S [E [G N]]]; unfold sequence_ok.
    destruct (R false); rewrite H0,H1,F; repeat split; auto.
    destruct xs; [contradiction|discriminate].
  - destruct (first_gender alpha) as [g|]; [|discriminate].
    destruct (@insert_flags n alpha g xs out A H) as [R [F N]].
    destruct X as [S [E [G K]]]; unfold sequence_ok.
    destruct (R false); rewrite H0,H1,F; repeat split; auto.
Qed.

Lemma f10_starts_verb n alpha xs out : starts_verb xs -> f10 n alpha xs = Some out -> starts_verb out.
Proof.
  intros [v [rest E]] H; subst xs; unfold f10 in H; destruct (bare_pronoun alpha) as [k|].
  - inversion H; subst out; exists v, (map (rename_pronoun n k) rest); reflexivity.
  - destruct (first_gender alpha) as [g|]; [|discriminate].
    cbn [insert_first] in H; destruct (insert_first n alpha g rest) as [tail|]; [|discriminate].
    inversion H; subst out; exists v, tail; reflexivity.
Qed.

Lemma replace_sequence n g xs : sequence_ok xs -> sequence_ok (map (replace_pronoun n g) xs).
Proof.
  intros [S [E [F N]]]; destruct (replace_flags n g xs) as [R G].
  destruct (R false); unfold sequence_ok; rewrite H,H0,G; repeat split; auto.
  destruct xs; [contradiction|discriminate].
Qed.

Lemma sequence_singleton u : coordinator u = false -> finite_token u = false -> sequence_ok [u].
Proof. intros C F; unfold sequence_ok; cbn [scan end_flag front_finite]; rewrite C,F; repeat split; discriminate. Qed.
Lemma starts_verb_append xs ys : starts_verb xs -> starts_verb (xs ++ ys).
Proof. intros [v [rest E]]; subst xs; exists v, (rest ++ ys)%list; reflexivity. Qed.

Lemma sequence_join j xs ys : sequence_ok xs -> sequence_ok ys ->
  sequence_ok (xs ++ [literal (match j with conjunction => "and" | disjunction => "or" end)] ++ ys).
Proof.
  intros X Y; apply sequence_append; [exact X|].
  destruct j; unfold sequence_ok; cbn [List.app scan end_flag front_finite coordinator finite_token];
    rewrite scan_good, end_good by exact Y; repeat split; discriminate.
Qed.

Lemma object_sequence xs : sequence_ok xs -> sequence_ok (object_form xs).
Proof.
  intro X; unfold object_form; destruct xs as [|u rest]; [exact X|].
  destruct u; try exact X; destruct c; try exact X; destruct rest; try exact X;
    apply sequence_singleton; reflexivity.
Qed.

Lemma subject_sequence f alpha delta out : sequence_ok alpha -> sequence_ok delta ->
  starts_verb delta -> subject_verb f alpha delta = Some out -> sequence_ok out.
Proof.
  intros [S [E [F N]]] [T [D [G K]]] [v [rest V]] H; subst delta.
  cbn [subject_verb inflect_first] in H; inversion H; subst out.
  unfold sequence_ok; rewrite scan_append, end_flag_append, S, E.
  cbn [scan end_flag coordinator finite_token andb negb] in T,D |- *.
  rewrite T,D; cbn; repeat split; auto.
  - rewrite front_append by exact N; exact F.
  - destruct alpha; [contradiction|discriminate].
Qed.

Definition verb_category A := A = IV \/ A = TV \/ A = slash IV ct \/ A = dslash IV IV.

Lemma lexical_sequence A (w : lexeme A) : sequence_ok (lex_tokens w).
Proof.
  destruct w as [v|c|v|v|v|v|v];
    try destruct v; try destruct c; apply sequence_singleton; reflexivity.
Qed.

Lemma lexical_verb_start A (w : lexeme A) : verb_category A -> starts_verb (lex_tokens w).
Proof.
  destruct w as [v|c|v|v|v|v|v]; intro H;
    try (eexists; exists []; reflexivity).
  all: destruct H as [H|[H|[H|H]]]; discriminate.
Qed.

Lemma iv_verb_category : verb_category IV. Proof. left; reflexivity. Qed.
Lemma tv_verb_category : verb_category TV. Proof. right; left; reflexivity. Qed.
Lemma attitude_verb_category : verb_category (slash IV ct). Proof. right; right; left; reflexivity. Qed.
Lemma control_verb_category : verb_category (dslash IV IV). Proof. right; right; right; reflexivity. Qed.

Ltac extract_children H :=
  repeat match type of H with
  | context [realize ?u] =>
      let xs := fresh "part" in let E := fresh "realized" in
      destruct (realize u) as [xs|] eqn:E; cbn [combine concat_tokens join_tokens] in H; try discriminate
  end;
  repeat match goal with
  | IH : forall xs, Some ?p = Some xs -> _ |- _ =>
      let R := fresh "child" in let S := fresh "safe" in let V := fresh "head" in
      pose proof (IH p eq_refl) as R; clear IH; destruct R as [S V]
  end.
Ltac impossible_verb := intros [K|[K|[K|K]]]; discriminate.

Theorem realized_sequence_invariant A (u : tree A) : forall xs,
  realize u = Some xs -> sequence_ok xs /\ (verb_category A -> starts_verb xs).
Proof.
  induction u; intros xs H; cbn [realize] in H.
  - inversion H; subst; split; [apply lexical_sequence|apply lexical_verb_start].
  - inversion H; subst; split; [apply sequence_singleton; reflexivity|impossible_verb].
  - inversion H; subst; split; [apply sequence_singleton; reflexivity|impossible_verb].
  - inversion H; subst; split; [apply sequence_singleton; reflexivity|].
    intro K; exists vbe, []; reflexivity.
  - inversion H; subst; split; [apply sequence_singleton; reflexivity|impossible_verb].
  - extract_children H; inversion H; subst; split; [|impossible_verb].
    change (sequence_ok ([literal (match d with every => "every" | the => "the" | a_or_an => "a" end)] ++ part)).
    apply sequence_append; [destruct d; apply sequence_singleton; reflexivity|assumption].
  - extract_children H.
    destruct (first_gender part) as [g|]; [|discriminate].
    inversion H; subst; split; [|impossible_verb].
    apply sequence_append; [assumption|].
    change (sequence_ok ([literal "such"; literal "that"] ++ map (replace_pronoun n g) part0)).
    apply sequence_append.
    + change (sequence_ok ([literal "such"] ++ [literal "that"])); apply sequence_append;
        apply sequence_singleton; reflexivity.
    + apply replace_sequence; assumption.
  - extract_children H; split; [|impossible_verb].
    eauto 8 using subject_sequence, iv_verb_category.
  - extract_children H; inversion H; subst; split.
    + apply sequence_append; [assumption|apply object_sequence; assumption].
    + intro K; apply starts_verb_append; eauto using tv_verb_category.
  - extract_children H; inversion H; subst; split; [|impossible_verb].
    apply sequence_append; [assumption|apply object_sequence; assumption].
  - extract_children H; inversion H; subst; split.
    + apply sequence_append; assumption.
    + intro K; apply starts_verb_append; eauto using attitude_verb_category.
  - extract_children H; inversion H; subst; split.
    + apply sequence_append; assumption.
    + intro K; apply starts_verb_append; eauto using control_verb_category.
  - extract_children H; inversion H; subst; split; [apply sequence_append; assumption|impossible_verb].
  - extract_children H; inversion H; subst; split.
    + apply sequence_append; assumption.
    + intro K; apply starts_verb_append; eauto using iv_verb_category.
  - extract_children H; inversion H; subst; split; [apply sequence_join; assumption|impossible_verb].
  - extract_children H; inversion H; subst; split.
    + apply sequence_join; assumption.
    + intro K; apply starts_verb_append; eauto using iv_verb_category.
  - extract_children H; inversion H; subst; split; [apply (sequence_join disjunction); assumption|impossible_verb].
  - extract_children H; split; [eauto using f10_sequence|impossible_verb].
  - extract_children H; split; [eauto using f10_sequence|impossible_verb].
  - extract_children H; split; [eauto using f10_sequence|].
    intro K; eauto using f10_starts_verb, iv_verb_category.
  - extract_children H; split; [|impossible_verb].
    eauto 8 using subject_sequence, iv_verb_category.
Qed.

Definition allowed u := match u with
  | literal s => In s ["every";"the";"a";"such";"that";"necessarily";"and";"or";
      "rapidly";"slowly";"voluntarily";"allegedly";"in";"about"]
  | _ => True end.

Lemma replace_allowed n g xs : Forall allowed xs -> Forall allowed (map (replace_pronoun n g) xs).
Proof.
  rewrite Forall_map; apply Forall_impl; intros u H; destruct u; cbn; auto.
  destruct (Nat.eqb n n0); exact I.
Qed.
Lemma rename_allowed n k xs : Forall allowed xs -> Forall allowed (map (rename_pronoun n k) xs).
Proof.
  rewrite Forall_map; apply Forall_impl; intros u H; destruct u; cbn; auto.
  destruct (Nat.eqb n n0); exact I.
Qed.

Lemma insert_allowed n alpha g xs out : Forall allowed alpha -> Forall allowed xs ->
  insert_first n alpha g xs = Some out -> Forall allowed out.
Proof.
  intros A X; revert out; induction X as [|u xs U X IH]; intros out H; [discriminate|].
  cbn [insert_first] in H; destruct (match u with indexed m _ => Nat.eqb n m | _ => false end).
  - inversion H; subst out; apply Forall_app; split; [exact A|apply replace_allowed; exact X].
  - destruct (insert_first n alpha g xs) as [tail|] eqn:E; [|discriminate].
    inversion H; subst out; constructor; [exact U|apply IH; reflexivity].
Qed.

Lemma f10_allowed n alpha xs out : Forall allowed alpha -> Forall allowed xs ->
  f10 n alpha xs = Some out -> Forall allowed out.
Proof.
  intros A X H; unfold f10 in H; destruct (bare_pronoun alpha) as [k|].
  - inversion H; subst out; apply rename_allowed; exact X.
  - destruct (first_gender alpha) as [g|]; [|discriminate].
    exact (@insert_allowed n alpha g xs out A X H).
Qed.

Lemma inflect_allowed f xs out : Forall allowed xs -> inflect_first f xs = Some out -> Forall allowed out.
Proof.
  intro X; revert out; induction X as [|u xs U X IH]; intros out H; [discriminate|].
  destruct u; cbn [inflect_first] in H;
    try (destruct (inflect_first f xs) as [tail|] eqn:E; [|discriminate];
      inversion H; subst out; constructor; [exact U|apply IH; reflexivity]).
  inversion H; subst out; constructor; [exact I|exact X].
Qed.

Lemma subject_allowed f alpha delta out : Forall allowed alpha -> Forall allowed delta ->
  subject_verb f alpha delta = Some out -> Forall allowed out.
Proof.
  intros A X H; unfold subject_verb in H; destruct (inflect_first f delta) as [tail|] eqn:E; [|discriminate].
  inversion H; subst out; apply Forall_app; split; [exact A|eapply inflect_allowed; eauto].
Qed.

Lemma object_allowed xs : Forall allowed xs -> Forall allowed (object_form xs).
Proof.
  intro X; unfold object_form; destruct xs as [|u xs]; [exact X|].
  destruct u; try exact X; destruct c; try exact X; destruct xs; try exact X;
    repeat constructor.
Qed.

Lemma lex_allowed A (w : lexeme A) : Forall allowed (lex_tokens w).
Proof.
  destruct w as [v|c|v|v|v|v|v]; try destruct v; try destruct c;
    cbn [lex_tokens]; rewrite Forall_cons_iff; split; try apply Forall_nil;
    cbn [allowed In]; intuition.
Qed.

Ltac allowed_children H :=
  repeat match type of H with
  | context [realize ?u] =>
      let xs := fresh "part" in let E := fresh "realized" in
      destruct (realize u) as [xs|] eqn:E; cbn [combine concat_tokens join_tokens] in H; try discriminate
  end;
  repeat match goal with
  | IH : forall xs, Some ?p = Some xs -> _ |- _ =>
      let R := fresh "child" in pose proof (IH p eq_refl) as R; clear IH
  end.

Ltac allowed_list :=
  repeat rewrite Forall_app; repeat rewrite Forall_cons_iff;
  repeat split; try assumption; try apply Forall_nil; cbn [allowed In]; intuition.

Theorem realized_tokens_allowed A (u : tree A) : forall xs,
  realize u = Some xs -> Forall allowed xs.
Proof.
  induction u; intros xs H; cbn [realize] in H.
  - inversion H; subst; apply lex_allowed.
  - inversion H; subst; allowed_list.
  - inversion H; subst; allowed_list.
  - inversion H; subst; allowed_list.
  - inversion H; subst; allowed_list.
  - allowed_children H; inversion H; subst; destruct d; allowed_list.
  - allowed_children H; destruct (first_gender part) as [g|]; [|discriminate].
    inversion H; subst; apply Forall_app; split; [assumption|].
    repeat rewrite Forall_cons_iff; repeat split; try (cbn [allowed In]; tauto).
    apply replace_allowed; assumption.
  - allowed_children H; eauto using subject_allowed.
  - allowed_children H; inversion H; subst; apply Forall_app; split;
      [assumption|apply object_allowed; assumption].
  - allowed_children H; inversion H; subst; apply Forall_app; split;
      [assumption|apply object_allowed; assumption].
  - allowed_children H; inversion H; subst; apply Forall_app; split; assumption.
  - allowed_children H; inversion H; subst; apply Forall_app; split; assumption.
  - allowed_children H; inversion H; subst; apply Forall_app; split; assumption.
  - allowed_children H; inversion H; subst; apply Forall_app; split; assumption.
  - allowed_children H; inversion H; subst; destruct j; allowed_list.
  - allowed_children H; inversion H; subst; destruct j; allowed_list.
  - allowed_children H; inversion H; subst; allowed_list.
  - allowed_children H; eauto using f10_allowed.
  - allowed_children H; eauto using f10_allowed.
  - allowed_children H; eauto using f10_allowed.
  - allowed_children H; eauto using subject_allowed.
Qed.

Definition word_coordinator s := orb (String.eqb s "and") (String.eqb s "or").
Definition forbidden_finite s := orb (String.eqb s "tries") (String.eqb s "wishes").
Fixpoint scan_words previous xs := match xs with
  | [] => true
  | s::rest => andb (negb (andb previous (forbidden_finite s))) (scan_words (word_coordinator s) rest)
  end.
Fixpoint end_words previous xs := match xs with
  | [] => previous | s::rest => end_words (word_coordinator s) rest end.

Lemma scan_words_append xs ys p :
  scan_words p (xs ++ ys) = andb (scan_words p xs) (scan_words (end_words p xs) ys).
Proof.
  revert p; induction xs; intro p; cbn; [reflexivity|].
  rewrite IHxs, andb_assoc; reflexivity.
Qed.

Lemma allowed_fragment u : allowed u -> forall p,
  end_words p (token_words u) = coordinator u /\
  (negb (andb p (finite_token u)) = true -> scan_words p (token_words u) = true).
Proof.
  destruct u as [s|c|n|v f|n c|g c]; intro H.
  - cbn [allowed In] in H.
    repeat destruct H as [H|H]; try contradiction; subst s;
      intro p; destruct p; vm_compute; intuition discriminate.
  - destruct c; intro p; destruct p; vm_compute; intuition discriminate.
  - destruct n; intro p; destruct p; vm_compute; intuition discriminate.
  - destruct v; repeat match goal with
      | x : iv_word |- _ => destruct x
      | x : tv_word |- _ => destruct x
      | x : attitude_word |- _ => destruct x
      | x : control_word |- _ => destruct x
      end; destruct f; intro p; destruct p; vm_compute; intuition discriminate.
  - destruct c; intro p; destruct p; vm_compute; intuition discriminate.
  - destruct g, c; intro p; destruct p; vm_compute; intuition discriminate.
Qed.

Theorem rendered_scan xs : Forall allowed xs -> forall p,
  scan p xs = true -> scan_words p (words xs) = true.
Proof.
  intro X; induction X as [|u xs U X IH]; intros p H; [reflexivity|].
  cbn [scan] in H; apply andb_true_iff in H; destruct H as [G S].
  cbn [words flat_map]; rewrite scan_words_append.
  destruct (@allowed_fragment u U p) as [E V]; rewrite E, V by exact G.
  cbn; apply IH; exact S.
Qed.

Theorem every_surface_obeys_scan A (u : tree A) text :
  surface u = Some text -> scan_words false text = true.
Proof.
  unfold surface; destruct (realize u) as [xs|] eqn:E; cbn; intro H; [|discriminate].
  inversion H; subst text; apply rendered_scan.
  - eapply realized_tokens_allowed; exact E.
  - exact (proj1 (proj1 (@realized_sequence_invariant A u xs E))).
Qed.

Theorem printed_try_wish_has_no_analysis :
  forall u : tree ct, surface u <> Some printed_try_wish.
Proof.
  intros u H; pose proof (@every_surface_obeys_scan ct u printed_try_wish H) as K.
  vm_compute in K; discriminate.
Qed.

Theorem printed_wish_try_has_no_analysis :
  forall u : tree ct, surface u <> Some printed_wish_try.
Proof.
  intros u H; pose proof (@every_surface_obeys_scan ct u printed_wish_try H) as K.
  vm_compute in K; discriminate.
Qed.

Definition section4_generation_claim := forall text,
  In text (map fst catalogue ++ [printed_try_wish; printed_wish_try]) ->
  exists u : tree ct, surface u = Some text.

Theorem section4_generation_claim_refuted : ~ section4_generation_claim.
Proof.
  intro H; unfold section4_generation_claim in H.
  assert (P : In printed_try_wish (map fst catalogue ++ [printed_try_wish; printed_wish_try])).
  { apply in_or_app; right; left; reflexivity. }
  destruct (H printed_try_wish P) as [u E].
  exact (printed_try_wish_has_no_analysis u E).
Qed.
