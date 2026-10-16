(* Remove identity, unused-index and pure relabelling quantifying-in.
   Genuine merges of two visible indices are retained. The construction is
   structural and covers every successful tree, not a depth-bounded search. *)
From Coq Require Import List Bool Arith Lia.
From MontaguePTQ Require Import Syntax Models Grammar Meaning Surface SurfaceInvariant
  SurfaceAmendment SurfaceAmendmentSafety PronounSupport GrammarRenaming.
Import ListNotations.
Set Implicit Arguments.

Fixpoint tree_size {A} (u : tree A) := match u with
  | s1_word _ | s1_name _ | s1_pronoun _ | s1_be | s1_necessarily => 1
  | s2 _ c => S (tree_size c)
  | s3 p _ q | s4 p q | s5 p q | s6 p q | s7 p q | s8 p q | s9 p q
  | s10 p q | s11 _ p q | s12 _ p q | s13 p q | s14 p _ q | s15 p _ q
  | s16 p _ q | s17 _ p q => S (tree_size p + tree_size q)
  end.
Lemma rename_tree_size f A (u : tree A) : tree_size (rename_tree f u) = tree_size u.
Proof. induction u; cbn [rename_tree tree_size]; congruence. Qed.

Definition swap_index n k m :=
  if Nat.eq_dec m n then k else if Nat.eq_dec m k then n else m.
Lemma swap_index_twice n k m : swap_index n k (swap_index n k m) = m.
Proof.
  unfold swap_index; repeat destruct Nat.eq_dec; subst; congruence.
Qed.
Lemma swap_index_injective n k : injective_name_map (swap_index n k).
Proof.
  intros x y H; apply (f_equal (swap_index n k)) in H; rewrite !swap_index_twice in H; exact H.
Qed.
Definition single_rename n k m := if Nat.eqb n m then k else m.
Lemma single_rename_self n m : single_rename n n m = m.
Proof. unfold single_rename; destruct (Nat.eqb n m) eqn:H; [apply Nat.eqb_eq in H; congruence|reflexivity]. Qed.
Lemma single_rename_absent n k m : m <> n -> single_rename n k m = m.
Proof. intro H; unfold single_rename; destruct (Nat.eqb n m) eqn:E; [apply Nat.eqb_eq in E; congruence|reflexivity]. Qed.
Lemma swap_single_agree n k m : m <> k -> swap_index n k m = single_rename n k m.
Proof.
  intro H; unfold swap_index, single_rename; destruct (Nat.eq_dec m n) as [E|E].
  - subst m; rewrite Nat.eqb_refl; reflexivity.
  - destruct (Nat.eq_dec m k); [contradiction|].
    assert (K : Nat.eqb n m = false) by (apply Nat.eqb_neq; congruence).
    rewrite K; reflexivity.
Qed.
Lemma single_update M n k (r : pvalues M) m :
  r (single_rename n k m) = update r n (r k) m.
Proof. unfold single_rename, update; rewrite Nat.eqb_sym; destruct (Nat.eqb m n); reflexivity. Qed.

Lemma visible_indices_map f xs : visible_indices (rename_tokens f xs) = map f (visible_indices xs).
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [rename_tokens map rename_token visible_indices flat_map app];
    try exact IH; f_equal; exact IH.
Qed.
Lemma rename_tokens_on_visible f g xs :
  (forall n, In n (visible_indices xs) -> f n = g n) -> rename_tokens f xs = rename_tokens g xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; intro H; destruct u;
    cbn [rename_tokens map rename_token]; f_equal; try (apply IH; exact H).
  - f_equal; apply H; cbn; auto.
  - apply IH; intros n0 N; apply H; cbn; auto.
Qed.
Lemma rename_tokens_identity xs : rename_tokens (fun n => n) xs = xs.
Proof. induction xs as [|u xs IH]; [reflexivity|]; destruct u; cbn; rewrite IH; reflexivity. Qed.
Lemma single_rename_tokens n k xs : rename_tokens (single_rename n k) xs = map (rename_pronoun n k) xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [rename_tokens map rename_token rename_pronoun single_rename]; rewrite IH;
    try reflexivity; unfold single_rename; destruct (Nat.eqb n n0); reflexivity.
Qed.

Lemma all_policy_erasure policy A (u : tree A) :
  erase_result (plain_tokens (plan policy u)) = erase_result (realize u) /\
  erase_result (present_tokens (plan policy u)) = erase_result (first_present (realize u)).
Proof.
  destruct policy; [destruct (first_policy_plan_exact u) as [H K]; rewrite H, K; auto|
    apply all_tree_amendment_erasure].
Qed.
Lemma equal_erasure_indices xs ys : erase_forms xs = erase_forms ys -> visible_indices xs = visible_indices ys.
Proof. intro H; apply (f_equal visible_indices) in H; rewrite !visible_indices_erase in H; exact H. Qed.

Lemma plan_indices policy A (u : tree A) xs : realize u = Some xs ->
  (forall ys, plain_tokens (plan policy u) = Some ys -> visible_indices ys = visible_indices xs) /\
  (forall ys, present_tokens (plan policy u) = Some ys -> visible_indices ys = visible_indices xs).
Proof.
  intro E; destruct (all_policy_erasure policy u) as [P Q]; rewrite E in P, Q; split.
  - intros ys H; rewrite H in P; injection P as P; apply equal_erasure_indices; exact P.
  - intros ys H; rewrite H in Q; cbn [first_present] in Q.
    destruct (inflect_first present xs) as [zs|] eqn:F; [|discriminate].
    injection Q as Q; rewrite (@equal_erasure_indices ys zs Q); eapply visible_indices_inflect; exact F.
Qed.

Lemma rename_plan_on_visible policy A (u : tree A) xs f g :
  realize u = Some xs -> (forall n, In n (visible_indices xs) -> f n = g n) ->
  rename_plan f (plan policy u) = rename_plan g (plan policy u).
Proof.
  intros E H; destruct (@plan_indices policy A u xs E) as [P Q].
  unfold rename_plan; f_equal; unfold rename_result;
    [destruct (plain_tokens (plan policy u)) as [ys|] eqn:Y |
     destruct (present_tokens (plan policy u)) as [ys|] eqn:Y];
    cbn [option_map]; try reflexivity; f_equal; apply rename_tokens_on_visible;
    intros n N; apply H; [rewrite <- (P ys eq_refl)|rewrite <- (Q ys eq_refl)]; exact N.
Qed.
Lemma rename_plan_identity p : rename_plan (fun n => n) p = p.
Proof.
  destruct p as [p q]; unfold rename_plan, rename_result; cbn; destruct p, q;
    cbn; repeat rewrite rename_tokens_identity; reflexivity.
Qed.
Lemma rename_plan_ext f g p : (forall n, f n = g n) -> rename_plan f p = rename_plan g p.
Proof.
  intro H; destruct p as [p q]; unfold rename_plan, rename_result; cbn; f_equal;
    [destruct p|destruct q]; cbn; try reflexivity; f_equal;
    apply rename_tokens_on_visible; intros; apply H.
Qed.

Inductive binding_category := sentence_binding | noun_binding | verb_binding.
Definition binding_type b := match b with sentence_binding => ct | noun_binding => CN | verb_binding => IV end.
Definition quantify b (p : tree NP) n : tree (binding_type b) -> tree (binding_type b) :=
  match b with sentence_binding => s14 p n | noun_binding => s15 p n | verb_binding => s16 p n end.
Lemma quantify_size b p n q : tree_size (quantify b p n q) = S (tree_size p + tree_size q).
Proof. destruct b; reflexivity. Qed.
Lemma quantify_bare_meaning M b n k (q : tree (binding_type b)) r i :
  denote M (quantify b (s1_pronoun k) n q) r i = denote M q (update r n (r k)) i.
Proof. destruct b; reflexivity. Qed.
Lemma ordinary_present policy A (u : tree A) : A = ct \/ A = CN ->
  present_tokens (plan policy u) = first_present (plain_tokens (plan policy u)).
Proof. destruct u; intro H; try reflexivity; destruct H; discriminate. Qed.

Lemma quantify_bare_plan policy b n k (q : tree (binding_type b)) :
  plan policy (quantify b (s1_pronoun k) n q) = rename_plan (single_rename n k) (plan policy q).
Proof.
  assert (E : forall xs, combine (f10 n) (Some [indexed k subject_case]) xs =
    rename_result (single_rename n k) xs).
  { intros [xs|]; [|reflexivity]; cbn [combine f10 bare_pronoun rename_result option_map];
      rewrite single_rename_tokens; reflexivity. }
  destruct b; cbn [quantify plan ordinary_plan coordinated_plan plain_tokens present_tokens]; rewrite !E;
    unfold rename_plan; cbn; try rewrite rename_result_first.
  - unfold ordinary_plan; rewrite (@ordinary_present policy ct q (or_introl eq_refl)), rename_result_first; reflexivity.
  - unfold ordinary_plan; rewrite (@ordinary_present policy CN q (or_intror eq_refl)), rename_result_first; reflexivity.
  - destruct policy; try reflexivity.
    unfold coordinated_plan; f_equal.
    change (first_present (rename_result (single_rename n k) (@plain_tokens (@plan IV first_verb_only q))) =
      rename_result (single_rename n k) (@present_tokens (@plan IV first_verb_only q))).
    rewrite (proj2 (@first_policy_plan_exact IV q)), (proj1 (@first_policy_plan_exact IV q)).
    symmetry; apply rename_result_first.
Qed.

Definition tree_equivalent {A} (u v : tree A) :=
  (forall policy, plan policy u = plan policy v) /\
  (forall M r i, denote M u r i = denote M v r i).
Lemma tree_equivalent_refl A (u : tree A) : tree_equivalent u u.
Proof. split; reflexivity. Qed.
Lemma tree_equivalent_sym A (u v : tree A) : tree_equivalent u v -> tree_equivalent v u.
Proof. intros [P D]; split; intros; symmetry; auto. Qed.
Lemma tree_equivalent_trans A (u v w : tree A) :
  tree_equivalent u v -> tree_equivalent v w -> tree_equivalent u w.
Proof. intros [P D] [Q E]; split; intros; [rewrite P; apply Q|rewrite D; apply E]. Qed.
Lemma tree_equivalent_realize A (u v : tree A) : tree_equivalent u v -> realize u = realize v.
Proof.
  intros [P _]; specialize (P first_verb_only); apply (f_equal plain_tokens) in P.
  rewrite (proj1 (first_policy_plan_exact u)), (proj1 (first_policy_plan_exact v)) in P; exact P.
Qed.

Theorem identity_bare_elimination b n (q : tree (binding_type b)) :
  tree_equivalent (quantify b (s1_pronoun n) n q) q.
Proof.
  split; intros.
  - rewrite quantify_bare_plan, (rename_plan_ext _ _ _ (single_rename_self n)); apply rename_plan_identity.
  - rewrite quantify_bare_meaning; apply interpretation_depends_on_support; intros m H.
    rewrite <- single_update, single_rename_self; reflexivity.
Qed.

Theorem unused_bare_elimination b n k (q : tree (binding_type b)) xs :
  realize q = Some xs -> ~ In n (visible_indices xs) ->
  tree_equivalent (quantify b (s1_pronoun k) n q) q.
Proof.
  intros R N; split; intros.
  - rewrite quantify_bare_plan.
    rewrite (@rename_plan_on_visible policy _ q xs (single_rename n k) (fun m => m) R).
    + apply rename_plan_identity.
    + intros m I; apply single_rename_absent; intro E; subst m; contradiction.
  - rewrite quantify_bare_meaning; apply interpretation_depends_on_support; intros m I.
    rewrite <- single_update, single_rename_absent; [reflexivity|].
    intro E; subst m; apply N; eapply support_is_visible; eassumption.
Qed.

Theorem pure_bare_elimination b n k (q : tree (binding_type b)) xs :
  realize q = Some xs -> ~ In k (visible_indices xs) ->
  tree_equivalent (quantify b (s1_pronoun k) n q) (rename_tree (swap_index n k) q).
Proof.
  intros R N; split; intros.
  - rewrite quantify_bare_plan, (rename_tree_plan (swap_index_injective n k)).
    apply (@rename_plan_on_visible policy _ q xs); [exact R|].
    intros m I; symmetry; apply swap_single_agree; intro E; subst m; contradiction.
  - rewrite quantify_bare_meaning, (@rename_tree_interpretation M _ (swap_index_injective n k) _ q r i).
    apply interpretation_depends_on_support; intros m I; rewrite <- single_update.
    rewrite swap_single_agree; [reflexivity|].
    intro E; subst m; apply N; eapply support_is_visible; eassumption.
Qed.

Definition genuine_binding {A} (p : tree NP) n (q : tree A) :=
  match tree_pronoun p with
  | None => True
  | Some k => n <> k /\ exists xs, realize q = Some xs /\
      In n (visible_indices xs) /\ In k (visible_indices xs)
  end.
Fixpoint merge_normal {A} (u : tree A) : Prop := match u with
  | s1_word _ | s1_name _ | s1_pronoun _ | s1_be | s1_necessarily => True
  | s2 _ c => merge_normal c
  | s3 p _ q | s4 p q | s5 p q | s6 p q | s7 p q | s8 p q | s9 p q
  | s10 p q | s11 _ p q | s12 _ p q | s13 p q | s17 _ p q => merge_normal p /\ merge_normal q
  | s14 p n q | s15 p n q | s16 p n q =>
      merge_normal p /\ merge_normal q /\ genuine_binding p n q
  end.
Lemma merge_normal_quantify b p n q : merge_normal (quantify b p n q) <->
  merge_normal p /\ merge_normal q /\ genuine_binding p n q.
Proof. destruct b; reflexivity. Qed.
Lemma tree_pronoun_rename f A (u : tree A) :
  tree_pronoun (rename_tree f u) = option_map f (tree_pronoun u).
Proof. destruct u; reflexivity. Qed.
Lemma genuine_binding_rename f (F : injective_name_map f) A p n (q : tree A) :
  genuine_binding p n q -> genuine_binding (rename_tree f p) (f n) (rename_tree f q).
Proof.
  unfold genuine_binding; rewrite tree_pronoun_rename; destruct (tree_pronoun p) as [k|]; cbn; auto.
  intros [D [xs [R [N K]]]]; split; [intro E; apply D; apply F; exact E|].
  exists (rename_tokens f xs); split; [rewrite (rename_tree_surface F), R; reflexivity|].
  rewrite visible_indices_map; split; apply in_map; assumption.
Qed.
Theorem merge_normal_rename f (F : injective_name_map f) A (u : tree A) :
  merge_normal u -> merge_normal (rename_tree f u).
Proof.
  induction u; cbn [rename_tree merge_normal]; intuition;
    apply genuine_binding_rename; assumption.
Qed.

Definition compact_binding b (p : tree NP) n (q : tree (binding_type b)) :=
  match tree_pronoun p with
  | None => quantify b p n q
  | Some k => match realize q with
    | None => quantify b p n q
    | Some xs => if Nat.eq_dec n k then q
        else if in_dec Nat.eq_dec n (visible_indices xs)
        then if in_dec Nat.eq_dec k (visible_indices xs) then quantify b p n q
             else rename_tree (swap_index n k) q
        else q
    end
  end.
Theorem compact_binding_equivalent b p n q :
  tree_equivalent (compact_binding b p n q) (quantify b p n q).
Proof.
  unfold compact_binding; destruct (tree_pronoun p) as [k|] eqn:P; [|apply tree_equivalent_refl].
  apply tree_pronoun_exact in P; subst p; destruct (realize q) as [xs|] eqn:R; [|apply tree_equivalent_refl].
  destruct (Nat.eq_dec n k) as [E|E]; [subst k; apply tree_equivalent_sym; apply identity_bare_elimination|].
  destruct (in_dec Nat.eq_dec n (visible_indices xs)) as [N|N].
  - destruct (in_dec Nat.eq_dec k (visible_indices xs)) as [K|K]; [apply tree_equivalent_refl|].
    apply tree_equivalent_sym; eapply pure_bare_elimination; eassumption.
  - apply tree_equivalent_sym; eapply unused_bare_elimination; eassumption.
Qed.
Theorem compact_binding_size b p n q :
  tree_size (compact_binding b p n q) <= S (tree_size p + tree_size q).
Proof.
  unfold compact_binding; destruct (tree_pronoun p) as [k|]; [|rewrite quantify_size; reflexivity].
  destruct (realize q); [|rewrite quantify_size; reflexivity].
  repeat destruct Nat.eq_dec; repeat destruct in_dec;
    try rewrite quantify_size; try rewrite rename_tree_size; lia.
Qed.
Theorem compact_binding_normal b p n q xs :
  merge_normal p -> merge_normal q -> realize q = Some xs -> merge_normal (compact_binding b p n q).
Proof.
  intros P Q R; unfold compact_binding; destruct (tree_pronoun p) as [k|] eqn:E.
  - rewrite R; destruct (Nat.eq_dec n k) as [D|D]; [exact Q|].
    destruct (in_dec Nat.eq_dec n (visible_indices xs)) as [N|N]; [|exact Q].
    destruct (in_dec Nat.eq_dec k (visible_indices xs)) as [K|K].
    + apply merge_normal_quantify; repeat split; try assumption.
      unfold genuine_binding; rewrite E; split; [exact D|]; exists xs; auto.
    + apply merge_normal_rename; [apply swap_index_injective|exact Q].
  - apply merge_normal_quantify; repeat split; try assumption; unfold genuine_binding; rewrite E; exact I.
Qed.

Fixpoint normalize_renamings {A} (u : tree A) : tree A := match u with
  | s1_word w => s1_word w | s1_name n => s1_name n | s1_pronoun n => s1_pronoun n
  | s1_be => s1_be | s1_necessarily => s1_necessarily
  | s2 d c => s2 d (normalize_renamings c)
  | s3 c n p => s3 (normalize_renamings c) n (normalize_renamings p)
  | s4 p q => s4 (normalize_renamings p) (normalize_renamings q)
  | s5 p q => s5 (normalize_renamings p) (normalize_renamings q)
  | s6 p q => s6 (normalize_renamings p) (normalize_renamings q)
  | s7 p q => s7 (normalize_renamings p) (normalize_renamings q)
  | s8 p q => s8 (normalize_renamings p) (normalize_renamings q)
  | s9 p q => s9 (normalize_renamings p) (normalize_renamings q)
  | s10 p q => s10 (normalize_renamings p) (normalize_renamings q)
  | s11 j p q => s11 j (normalize_renamings p) (normalize_renamings q)
  | s12 j p q => s12 j (normalize_renamings p) (normalize_renamings q)
  | s13 p q => s13 (normalize_renamings p) (normalize_renamings q)
  | s14 p n q => compact_binding sentence_binding (normalize_renamings p) n (normalize_renamings q)
  | s15 p n q => compact_binding noun_binding (normalize_renamings p) n (normalize_renamings q)
  | s16 p n q => compact_binding verb_binding (normalize_renamings p) n (normalize_renamings q)
  | s17 k p q => s17 k (normalize_renamings p) (normalize_renamings q)
  end.

Ltac normalization_semantics M :=
  first [reflexivity |
    match goal with H : forall M r i, denote M ?u r i = denote M ?v r i |- _ =>
      progress rewrite H; normalization_semantics M end |
    lazymatch goal with |- @eq (forall _ : _, _) _ _ =>
      apply (function_extensionality M); intro; normalization_semantics M end |
    progress f_equal; normalization_semantics M].

Theorem normalize_renamings_equivalent A (u : tree A) : tree_equivalent (normalize_renamings u) u.
Proof.
  induction u; cbn [normalize_renamings].
  all: try (lazymatch goal with
    |- tree_equivalent (compact_binding ?b ?p ?n ?q) ?v =>
      eapply (@tree_equivalent_trans (binding_type b) _ (quantify b p n q) v);
      [exact (@compact_binding_equivalent b p n q)|]
    end).
  all: unfold tree_equivalent in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; split.
  all: try (intro policy; cbn [quantify plan];
    repeat match goal with H : forall policy, _ = _ |- _ => rewrite H end; reflexivity).
  all: try (intros M r i; cbn [quantify denote]; normalization_semantics M).
  - intros M r i; cbn [denote]; apply (function_extensionality M); intro x.
    rewrite H2, H0; reflexivity.
  - intros M r i; cbn [quantify denote]; apply (function_extensionality M); intro y.
    rewrite H2; f_equal; apply (function_extensionality M); intro j;
      apply (function_extensionality M); intro x; rewrite H0; reflexivity.
  - intros M r i; cbn [quantify denote]; apply (function_extensionality M); intro y.
    rewrite H2; f_equal; apply (function_extensionality M); intro j;
      apply (function_extensionality M); intro x; rewrite H0; reflexivity.
Qed.

Theorem normalize_renamings_size A (u : tree A) : tree_size (normalize_renamings u) <= tree_size u.
Proof.
  induction u; cbn [normalize_renamings tree_size]; try lia.
  all: lazymatch goal with |- tree_size (compact_binding ?b ?p ?n ?q) <= _ =>
    eapply Nat.le_trans; [exact (@compact_binding_size b p n q)|
      apply le_n_S; apply Nat.add_le_mono; assumption] end.
Qed.

Theorem normalize_renamings_normal A (u : tree A) :
  forall xs, realize u = Some xs -> merge_normal (normalize_renamings u).
Proof.
  induction u; intros xs R; cbn [realize] in R; cbn [normalize_renamings merge_normal]; try exact I.
  all: repeat match type of R with
    | context [realize ?q] =>
      let E := fresh "Realized" in destruct (realize q) as [|] eqn:E;
      cbn [combine] in R; try discriminate
    end.
  all: repeat match goal with
    | H : forall ys, Some ?ts = Some ys -> _ |- _ => specialize (H ts eq_refl)
    end.
  all: try assumption; try (split; assumption).
  all: lazymatch goal with |- merge_normal (compact_binding ?b ?p ?n ?q) =>
    eapply (@compact_binding_normal b p n q); [eassumption|eassumption|]
    end.
  all: rewrite (tree_equivalent_realize (normalize_renamings_equivalent _)); eassumption.
Qed.

Theorem every_successful_tree_has_merge_normal_form A (u : tree A) xs :
  realize u = Some xs -> exists v : tree A,
    merge_normal v /\ tree_size v <= tree_size u /\ tree_equivalent v u.
Proof.
  intro R; exists (normalize_renamings u); split; [eapply normalize_renamings_normal; exact R|].
  split; [apply normalize_renamings_size|apply normalize_renamings_equivalent].
Qed.

Lemma swap_update_fresh M n k (r : pvalues M) x m : m <> k ->
  update r k x (swap_index n k m) = update r n x m.
Proof.
  intro H; unfold swap_index; destruct (Nat.eq_dec m n) as [E|E].
  - subst m; unfold update; rewrite !Nat.eqb_refl; reflexivity.
  - destruct (Nat.eq_dec m k); [contradiction|].
    unfold update; assert (N : Nat.eqb m n = false) by (apply Nat.eqb_neq; exact E).
    assert (K : Nat.eqb m k = false) by (apply Nat.eqb_neq; exact H).
    rewrite N, K; reflexivity.
Qed.
Lemma rename_token_fresh_test n k m c : m <> k ->
  match rename_token (swap_index n k) (indexed m c) with
  | indexed j _ => Nat.eqb k j | _ => false end = Nat.eqb n m.
Proof.
  intro H; cbn [rename_token]; unfold swap_index; destruct (Nat.eq_dec m n) as [E|E].
  - subst m; cbn; rewrite !Nat.eqb_refl; reflexivity.
  - destruct (Nat.eq_dec m k); [contradiction|]; cbn.
    assert (N : Nat.eqb n m = false) by (apply Nat.eqb_neq; congruence).
    assert (K : Nat.eqb k m = false) by (apply Nat.eqb_neq; congruence).
    rewrite N, K; reflexivity.
Qed.
Lemma replace_swap_fresh n k g xs : ~ In k (visible_indices xs) ->
  map (replace_pronoun k g) (rename_tokens (swap_index n k) xs) = map (replace_pronoun n g) xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; intro H.
  assert (T : ~ In k (visible_indices xs)).
  { intro K; apply H; rewrite visible_indices_cons; apply in_or_app; auto. }
  cbn [rename_tokens map]; rewrite IH by exact T; f_equal.
  destruct u; try reflexivity; cbn [visible_indices flat_map app In] in H.
  cbn [rename_token]; unfold swap_index; destruct (Nat.eq_dec n0 n) as [E|E].
  - subst n0; cbn [replace_pronoun]; rewrite !Nat.eqb_refl; reflexivity.
  - destruct (Nat.eq_dec n0 k); [exfalso; apply H; auto|].
    cbn [replace_pronoun]; assert (N : Nat.eqb n n0 = false) by (apply Nat.eqb_neq; congruence).
    assert (K : Nat.eqb k n0 = false) by (apply Nat.eqb_neq; congruence); rewrite N, K; reflexivity.
Qed.
Lemma insert_swap_fresh n k alpha g xs : ~ In k (visible_indices xs) ->
  insert_first k alpha g (rename_tokens (swap_index n k) xs) = insert_first n alpha g xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; intro H.
  assert (T : ~ In k (visible_indices xs)).
  { intro K; apply H; rewrite visible_indices_cons; apply in_or_app; auto. }
  destruct u; cbn [rename_tokens map rename_token insert_first];
    try (rewrite IH by exact T; reflexivity).
  cbn [visible_indices flat_map app In] in H.
  assert (K : n0 <> k) by (intro E; apply H; auto).
  unfold swap_index at 1; destruct (Nat.eq_dec n0 n) as [E|E].
  - subst n0; rewrite !Nat.eqb_refl, replace_swap_fresh by exact T; reflexivity.
  - destruct (Nat.eq_dec n0 k); [contradiction|].
    assert (N : Nat.eqb n n0 = false) by (apply Nat.eqb_neq; congruence).
    assert (K0 : Nat.eqb k n0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite N, K0, IH by exact T; unfold swap_index.
    destruct (Nat.eq_dec n0 n); [contradiction|]; destruct (Nat.eq_dec n0 k); [contradiction|]; reflexivity.
Qed.
Lemma bare_swap_fresh n k j xs : ~ In k (visible_indices xs) ->
  map (rename_pronoun k j) (rename_tokens (swap_index n k) xs) = map (rename_pronoun n j) xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; intro H.
  assert (T : ~ In k (visible_indices xs)).
  { intro K; apply H; rewrite visible_indices_cons; apply in_or_app; auto. }
  cbn [rename_tokens map]; rewrite IH by exact T; f_equal.
  destruct u; try reflexivity; cbn [visible_indices flat_map app In] in H.
  cbn [rename_token]; unfold swap_index; destruct (Nat.eq_dec n0 n) as [E|E].
  - subst n0; cbn [rename_pronoun]; rewrite !Nat.eqb_refl; reflexivity.
  - destruct (Nat.eq_dec n0 k); [exfalso; apply H; auto|].
    cbn [rename_pronoun]; assert (N : Nat.eqb n n0 = false) by (apply Nat.eqb_neq; congruence).
    assert (K : Nat.eqb k n0 = false) by (apply Nat.eqb_neq; congruence); rewrite N, K; reflexivity.
Qed.
Lemma f10_swap_fresh n k alpha xs : ~ In k (visible_indices xs) ->
  f10 k alpha (rename_tokens (swap_index n k) xs) = f10 n alpha xs.
Proof.
  intro H; unfold f10; destruct (bare_pronoun alpha).
  - rewrite bare_swap_fresh by exact H; reflexivity.
  - destruct (first_gender alpha); [apply insert_swap_fresh; exact H|reflexivity].
Qed.

Lemma f10_plan_fresh policy A (q : tree A) xs n k alpha :
  realize q = Some xs -> ~ In k (visible_indices xs) ->
  (combine (f10 k) alpha (rename_result (swap_index n k) (plain_tokens (plan policy q))) =
    combine (f10 n) alpha (plain_tokens (plan policy q))) /\
  (combine (f10 k) alpha (rename_result (swap_index n k) (present_tokens (plan policy q))) =
    combine (f10 n) alpha (present_tokens (plan policy q))).
Proof.
  intros R K; destruct (@plan_indices policy A q xs R) as [P Q]; split;
    [destruct (plain_tokens (plan policy q)) as [ys|] eqn:E |
     destruct (present_tokens (plan policy q)) as [ys|] eqn:E];
    destruct alpha as [a|]; cbn [rename_result option_map combine]; try reflexivity;
    apply f10_swap_fresh; [rewrite (P ys eq_refl)|rewrite (Q ys eq_refl)]; exact K.
Qed.

Lemma freshen_body_meaning M A (q : tree A) n k xs :
  realize q = Some xs -> ~ In k (visible_indices xs) -> forall r x j,
  denote M (rename_tree (swap_index n k) q) (update r k x) j = denote M q (update r n x) j.
Proof.
  intros R K r x j; rewrite (@rename_tree_interpretation M _ (swap_index_injective n k)).
  apply interpretation_depends_on_support; intros m I; apply swap_update_fresh.
  intro E; subst m; apply K; eapply support_is_visible; eassumption.
Qed.

Theorem freshen_binding_equivalent b p n k q xs :
  realize q = Some xs -> ~ In k (visible_indices xs) ->
  tree_equivalent (quantify b p k (rename_tree (swap_index n k) q)) (quantify b p n q).
Proof.
  intros R K; split.
  - intro policy; destruct (@f10_plan_fresh policy _ q xs n k
      (plain_tokens (plan policy p)) R K) as [P Q].
    destruct b; cbn [quantify plan]; rewrite (rename_tree_plan (swap_index_injective n k));
      cbn [rename_plan plain_tokens present_tokens]; rewrite P; try rewrite Q; reflexivity.
  - intros M r i; destruct b; cbn [binding_type] in *; cbn [quantify denote];
      try (apply (function_extensionality M); intro y);
      f_equal; apply (function_extensionality M); intro j;
      apply (function_extensionality M); intro x;
      rewrite (@freshen_body_meaning M _ q n k xs R K r x j); reflexivity.
Qed.

Lemma compact_genuine b p n q : genuine_binding p n q -> compact_binding b p n q = quantify b p n q.
Proof.
  unfold compact_binding, genuine_binding; destruct (tree_pronoun p) as [k|]; [|reflexivity].
  intros [D [xs [R [N K]]]]; rewrite R; destruct (Nat.eq_dec n k); [contradiction|].
  destruct (in_dec Nat.eq_dec n (visible_indices xs)); [|contradiction].
  destruct (in_dec Nat.eq_dec k (visible_indices xs)); [reflexivity|contradiction].
Qed.
Theorem merge_normal_is_fixed A (u : tree A) : merge_normal u -> normalize_renamings u = u.
Proof.
  induction u; cbn [merge_normal]; intro H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [normalize_renamings];
    repeat match goal with
      | IH : merge_normal ?q -> normalize_renamings ?q = ?q, N : merge_normal ?q |- _ => rewrite (IH N)
      end; try reflexivity.
  all: lazymatch goal with |- compact_binding ?b ?p ?n ?q = _ =>
    exact (@compact_genuine b p n q ltac:(assumption)) end.
Qed.
Corollary normalization_idempotent A (u : tree A) xs : realize u = Some xs ->
  normalize_renamings (normalize_renamings u) = normalize_renamings u.
Proof. intro R; apply merge_normal_is_fixed; eapply normalize_renamings_normal; exact R. Qed.

Definition capture_sensitive_body := s14 (s1_name john) 1 (s11 conjunction
  (s4 (s1_pronoun 0) (s1_word (liv walk)))
  (s4 (s1_pronoun 1) (s1_word (liv talk)))).
Example normalization_avoids_internal_capture :
  normalize_renamings (s14 (s1_pronoun 1) 0 capture_sensitive_body) =
  s14 (s1_name john) 0 (s11 conjunction
    (s4 (s1_pronoun 1) (s1_word (liv walk)))
    (s4 (s1_pronoun 0) (s1_word (liv talk)))).
Proof. reflexivity. Qed.
Definition genuine_merge_example := s14 (s1_pronoun 1) 0 (s11 conjunction
  (s4 (s1_pronoun 0) (s1_word (liv walk)))
  (s4 (s1_pronoun 1) (s1_word (liv talk)))).
Example genuine_merge_is_retained : normalize_renamings genuine_merge_example = genuine_merge_example.
Proof. reflexivity. Qed.
