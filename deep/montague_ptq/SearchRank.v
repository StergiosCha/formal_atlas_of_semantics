(* The decreasing measure used by the inverse search. Theorems here concern
   local F10 steps, not completeness of the complete parser. *)
From Coq Require Import List Bool Arith Lia Sorting.Permutation
  Wellfounded.Inclusion Wellfounded.Inverse_Image Wellfounded.Lexicographic_Product
  Relations.Relation_Operators.
From MontaguePTQ Require Import Syntax Grammar Surface SurfaceInvariant PronounSupport
  RenamingNormalization SurfaceInverse.
Import ListNotations.
Set Implicit Arguments.

Definition fixed_token u := match u with indexed _ _ | plain _ _ => false | _ => true end.
Definition fixed_count xs := length (filter fixed_token xs).
Definition collisions xs := length (visible_indices xs) - length (nodup Nat.eq_dec (visible_indices xs)).
Inductive rank_before (xs ys : list token) : Prop :=
| rank_shorter : length xs < length ys -> rank_before xs ys
| rank_fewer_fixed : length xs = length ys -> fixed_count xs < fixed_count ys -> rank_before xs ys
| rank_fewer_collisions : length xs = length ys -> fixed_count xs = fixed_count ys ->
    collisions xs < collisions ys -> rank_before xs ys.

Definition token_rank xs := (length xs, (fixed_count xs, collisions xs)).
Definition triple_less := slexprod nat (nat * nat) lt (slexprod nat nat lt lt).
Theorem inverse_rank_well_founded : well_founded rank_before.
Proof.
  apply (@wf_incl _ rank_before (fun xs ys => triple_less (token_rank xs) (token_rank ys))).
  - intros xs ys H; unfold triple_less, token_rank; destruct H.
    + apply left_slex; exact H.
    + rewrite H; apply right_slex; apply left_slex; exact H0.
    + rewrite H,H0; apply right_slex; apply right_slex; exact H1.
  - apply wf_inverse_image; unfold triple_less; apply wf_slexprod;
      [apply lt_wf|apply wf_slexprod; apply lt_wf].
Qed.

Lemma fixed_count_append xs ys : fixed_count (xs ++ ys) = fixed_count xs + fixed_count ys.
Proof. unfold fixed_count; rewrite filter_app, length_app; reflexivity. Qed.
Lemma fixed_count_replace n g xs : fixed_count (map (replace_pronoun n g) xs) = fixed_count xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [map replace_pronoun fixed_count filter fixed_token]; try (cbn; f_equal; exact IH).
  all: try exact IH.
  destruct (Nat.eqb n n0); cbn [filter fixed_token]; exact IH.
Qed.
Lemma fixed_count_rename n k xs : fixed_count (map (rename_pronoun n k) xs) = fixed_count xs.
Proof.
  induction xs as [|u xs IH]; [reflexivity|]; destruct u;
    cbn [map rename_pronoun fixed_count filter fixed_token]; try (cbn; f_equal; exact IH).
  all: try exact IH.
  destruct (Nat.eqb n n0); cbn [filter fixed_token]; exact IH.
Qed.

Lemma remove_preserves_nodup n ns : NoDup ns -> NoDup (remove Nat.eq_dec n ns).
Proof.
  intro H; induction H; [constructor|].
  cbn [remove]; destruct (Nat.eq_dec n x); [exact IHNoDup|].
  constructor; [intro I; apply in_remove in I; tauto|exact IHNoDup].
Qed.
Lemma remove_one_length n ns : NoDup ns -> In n ns ->
  length ns = S (length (remove Nat.eq_dec n ns)).
Proof.
  intros H; induction H; [contradiction|]; intro I.
  cbn [remove length]; destruct (Nat.eq_dec n x) as [E|E].
  - subst x; rewrite notin_remove by exact H; reflexivity.
  - cbn [length]; cbn in I; destruct I as [I|I]; [congruence|].
    f_equal; apply IHNoDup; exact I.
Qed.
Lemma merged_distinct_indices n k ns : n <> k -> In k ns ->
  Permutation (nodup Nat.eq_dec (map (single_rename n k) ns))
    (remove Nat.eq_dec n (nodup Nat.eq_dec ns)).
Proof.
  intros N K; apply NoDup_Permutation;
    [apply NoDup_nodup|apply remove_preserves_nodup; apply NoDup_nodup|].
  intro m; rewrite nodup_In; split.
  - intro I; apply in_map_iff in I; destruct I as [x [E I]].
    unfold single_rename in E; destruct (Nat.eqb n x) eqn:X.
    + subst m; apply in_in_remove; [congruence|apply nodup_In; exact K].
    + subst m; apply in_in_remove; [apply Nat.eqb_neq in X; congruence|apply nodup_In; exact I].
  - intro I; apply in_remove in I; destruct I as [I E]; apply nodup_In in I.
    apply in_map_iff; exists m; split; [|exact I]; unfold single_rename.
    assert (X : Nat.eqb n m = false) by (apply Nat.eqb_neq; congruence); rewrite X; reflexivity.
Qed.
Lemma distinct_merge_loses_one n k ns : n <> k -> In n ns -> In k ns ->
  length (nodup Nat.eq_dec ns) = S (length (nodup Nat.eq_dec (map (single_rename n k) ns))).
Proof.
  intros N I K; pose proof (Permutation_length (@merged_distinct_indices n k ns N K)) as L.
  rewrite L; apply remove_one_length; [apply NoDup_nodup|apply nodup_In; exact I].
Qed.
Theorem genuine_merge_strictly_decreases_rank n k body :
  n <> k -> In n (visible_indices body) -> In k (visible_indices body) ->
  rank_before body (map (rename_pronoun n k) body).
Proof.
  intros N I K; apply rank_fewer_collisions.
  - rewrite length_map; reflexivity.
  - rewrite fixed_count_rename; reflexivity.
  - unfold collisions; rewrite visible_indices_rename, length_map.
    change (length (visible_indices body) - length (nodup Nat.eq_dec (visible_indices body)) <
      length (visible_indices body) - length (nodup Nat.eq_dec (map (single_rename n k) (visible_indices body)))).
    pose proof (@distinct_merge_loses_one n k (visible_indices body) N I K) as L.
    assert (B : length (nodup Nat.eq_dec (visible_indices body)) <= length (visible_indices body)).
    { apply NoDup_incl_length; [apply NoDup_nodup|intros x X; apply nodup_In in X; exact X]. }
    lia.
Qed.

Theorem nonbare_body_strictly_decreases_rank n alpha body out :
  alpha <> [] -> 0 < fixed_count alpha -> bare_pronoun alpha = None ->
  f10 n alpha body = Some out -> rank_before body out.
Proof.
  intros A C B H; unfold f10 in H; rewrite B in H.
  destruct (first_gender alpha) as [g|]; [|discriminate].
  destruct (@first_insertion_decomposition n alpha g body out H)
    as [before [after [c [E [N O]]]]]; subst body out.
  assert (L : 0 < length alpha) by (destruct alpha; [contradiction|cbn; lia]).
  destruct (Nat.eq_dec (length alpha) 1) as [K|K].
  - apply rank_fewer_fixed.
    + repeat rewrite length_app; cbn [length]; rewrite length_map; lia.
    + repeat rewrite fixed_count_append; cbn [fixed_count filter fixed_token].
      change (fixed_count before + fixed_count after <
        fixed_count before + (fixed_count alpha + fixed_count (map (replace_pronoun n g) after))).
      rewrite fixed_count_replace; lia.
  - apply rank_shorter; repeat rewrite length_app; cbn [length]; rewrite length_map; lia.
Qed.

Lemma nonbare_np_has_fixed_content A (u : tree A) : A = NP -> forall alpha,
  realize u = Some alpha -> bare_pronoun alpha = None -> 0 < fixed_count alpha.
Proof.
  destruct u; intro E; try discriminate; intros alpha H B; cbn [realize] in H.
  - destruct l; discriminate.
  - injection H as H; subst alpha; cbn; lia.
  - injection H as H; subst alpha; discriminate.
  - destruct (realize u) as [cs|]; [|discriminate]; injection H as H; subst alpha.
    destruct d; cbn; lia.
  - unfold combine in H; destruct (realize u1), (realize u2); try discriminate.
    injection H as H; subst alpha; unfold join_tokens; rewrite fixed_count_append.
    change (0 < fixed_count l + S (fixed_count l0)); lia.
Qed.
Corollary nonbare_np_body_rank (p : tree NP) n alpha body out :
  realize p = Some alpha -> bare_pronoun alpha = None ->
  f10 n alpha body = Some out -> rank_before body out.
Proof.
  intros P B H; eapply nonbare_body_strictly_decreases_rank; try eassumption.
  - pose proof (@realized_sequence_invariant NP p alpha P) as S.
    exact (proj2 (proj2 (proj2 (proj1 S)))).
  - eapply (@nonbare_np_has_fixed_content NP p eq_refl); eassumption.
Qed.

Theorem canonical_merge_inverse_rank k out body :
  In body (merge_inverses (fresh_index out) k out) -> rank_before body out.
Proof.
  intro H; destruct (@canonical_merge_inverse_sound k out body H) as [F [N K]].
  cbn [f10 bare_pronoun] in F; injection F as F.
  assert (V : In k (visible_indices out)).
  { rewrite <- F, visible_indices_rename; apply in_map_iff; exists k; split; [|exact K].
    destruct (Nat.eqb (fresh_index out) k); reflexivity. }
  assert (D : fresh_index out <> k).
  { intro E; rewrite <- E in V; exact (fresh_index_not_visible out V). }
  rewrite <- F; apply genuine_merge_strictly_decreases_rank; assumption.
Qed.
