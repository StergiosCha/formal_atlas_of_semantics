(* Named IL renaming and Thomason note 12. Bound-variable occurrences are
   renamed as well as free occurrences; freshness is checked syntactically. *)
From Coq Require Import List Bool Arith Lia.
From MontaguePTQ Require Import Syntax Models Named.
Import ListNotations.
Set Implicit Arguments.

Definition name_map := forall a : ty, nat -> nat.
Definition injective_names (f : name_map) := forall a n m, f a n = f a m -> n = m.

Fixpoint rename_named {a} (p : ntm a) (f : name_map) : ntm a := match p with
  | NV a n => NV a (f a n) | NC a n => NC a n
  | NL a n q => NL a (f a n) (rename_named q f)
  | NA q r => NA (rename_named q f) (rename_named r f)
  | NE q r => NE (rename_named q f) (rename_named r f)
  | NN q => NN (rename_named q f)
  | NCj q r => NCj (rename_named q f) (rename_named r f)
  | NDj q r => NDj (rename_named q f) (rename_named r f)
  | NI q r => NI (rename_named q f) (rename_named r f)
  | NB q r => NB (rename_named q f) (rename_named r f)
  | NAll a n q => NAll a (f a n) (rename_named q f)
  | NEx a n q => NEx a (f a n) (rename_named q f)
  | NBox q => NBox (rename_named q f)
  | NW q => NW (rename_named q f) | NH q => NH (rename_named q f)
  | NU q => NU (rename_named q f) | ND q => ND (rename_named q f)
  end.

Lemma injective_eqb f (F : injective_names f) a n m :
  Nat.eqb (f a n) (f a m) = Nat.eqb n m.
Proof.
  destruct (Nat.eqb n m) eqn:E.
  - apply Nat.eqb_eq in E; subst m; apply Nat.eqb_refl.
  - apply Nat.eqb_neq in E; apply Nat.eqb_neq; intro H; apply E; exact (F a n m H).
Qed.

Fixpoint names_at {a} (p : ntm a) b : list nat := match p with
  | NV a n => if ty_eq_dec a b then [n] else []
  | NC _ _ => []
  | NL a n q | NAll a n q | NEx a n q =>
      if ty_eq_dec a b then n :: names_at q b else names_at q b
  | NA q r | NE q r | NCj q r | NDj q r | NI q r | NB q r => names_at q b ++ names_at r b
  | NN q | NBox q | NW q | NH q | NU q | ND q => names_at q b
  end.

Definition max_name (L : list nat) := fold_right Nat.max 0 L.
Lemma max_name_bound L n : In n L -> n <= max_name L.
Proof.
  induction L; [contradiction|].
  change (a = n \/ In n L -> n <= Nat.max a (max_name L)).
  intros [E|H]; [subst; apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IHL; exact H|apply Nat.le_max_r].
Qed.

Fixpoint search_missing (L : list nat) fuel k := match fuel with
  | 0 => k
  | S fuel => if existsb (Nat.eqb (4*k)) L then search_missing L fuel (S k) else k
  end.

Lemma missing_search_correct L fuel k : max_name L < 4*(k+fuel) ->
  ~ In (4 * search_missing L fuel k) L /\
  k <= search_missing L fuel k /\
  forall j, k <= j < search_missing L fuel k -> In (4*j) L.
Proof.
  revert k; induction fuel; intros k H; cbn [search_missing].
  - split; [intro V; pose proof (@max_name_bound L (4*k) V); lia|]. split; [lia|intros; lia].
  - destruct (existsb (Nat.eqb (4*k)) L) eqn:E.
    + assert (V : In (4*k) L).
      { apply existsb_exists in E; destruct E as [v [V E]]; apply Nat.eqb_eq in E; subst v; exact V. }
      destruct (IHfuel (S k)) as [F [B K]]; [lia|].
      split; [exact F|]; split; [lia|]. intros j J.
      destruct (Nat.eq_dec k j); [subst j; exact V|apply K; lia].
    + split.
      * intro V; assert (K : existsb (Nat.eqb (4*k)) L = true).
        { apply existsb_exists; exists (4*k); split; [exact V|apply Nat.eqb_refl]. }
        congruence.
      * split; [lia|intros; lia].
Qed.

(* Source x_n abbreviates u_(2n,ic). Note 12 asks for an even index m,
   so the raw variable number is 4*k, not merely the next even raw number. *)
Definition editorial_index L := 2 * search_missing L (S (max_name L)) 0.
Theorem editorial_index_is_least_even L :
  (exists k, editorial_index L = 2*k) /\
  ~ In (2 * editorial_index L) L /\
  forall k, 2*k < editorial_index L -> In (2*(2*k)) L.
Proof.
  unfold editorial_index.
  destruct (@missing_search_correct L (S (max_name L)) 0) as [F [B K]]; [lia|].
  split; [eexists; reflexivity|]. split.
  - replace (2 * (2 * search_missing L (S (max_name L)) 0)) with
      (4 * search_missing L (S (max_name L)) 0) by lia; exact F.
  - intros k H; replace (2*(2*k)) with (4*k) by lia; apply K; lia.
Qed.

Lemma renamed_update M f (F : injective_names f) (r s : free_env M) a n x :
  (forall b m, s b (f b m) = r b m) ->
  forall b m, put s a (f a n) x b (f b m) = put r a n x b m.
Proof.
  intros H b m; unfold put; destruct (ty_eq_dec a b) as [E|N].
  - destruct E; rewrite (injective_eqb F); destruct (Nat.eqb n m); auto.
  - apply H.
Qed.

Theorem named_renaming_interpretation M a (p : ntm a) f (F : injective_names f) :
  forall r s, (forall b n, s b (f b n) = r b n) -> forall i,
  neval M (rename_named p f) s i = neval M p r i.
Proof.
  induction p; intros r s E i; cbn;
    try reflexivity; try apply E;
    try (rewrite IHp1 with (r := r), IHp2 with (r := r); auto; fail);
    try (rewrite IHp with (r := r); auto; fail).
  - apply (function_extensionality M); intro x; apply IHp; apply renamed_update; auto.
  - apply truth_congr; split; intros H x;
      [rewrite <- IHp with (s := put s a (f a n) x)
      | rewrite IHp with (r := put r a n x)]; auto using renamed_update.
  - apply truth_congr; split; intros [x H]; exists x;
      [rewrite <- IHp with (s := put s a (f a n) x)
      | rewrite IHp with (r := put r a n x)]; auto using renamed_update.
  - apply truth_congr; split; intros H j;
      [rewrite <- IHp with (s := s) | rewrite IHp with (r := r)]; auto.
  - apply truth_congr; split; intros [j [O H]]; exists j; split; auto;
      [rewrite <- IHp with (s := s) | rewrite IHp with (r := r)]; auto.
  - apply truth_congr; split; intros [j [O H]]; exists j; split; auto;
      [rewrite <- IHp with (s := s) | rewrite IHp with (r := r)]; auto.
  - apply (function_extensionality M); intro j; apply IHp; auto.
Qed.

Fixpoint free_at {a} (p : ntm a) b n : bool := match p with
  | NV a m => if ty_eq_dec a b then Nat.eqb n m else false
  | NC _ _ => false
  | NL a m q | NAll a m q | NEx a m q =>
      if ty_eq_dec a b then if Nat.eqb n m then false else free_at q b n
      else free_at q b n
  | NA q r | NE q r | NCj q r | NDj q r | NI q r | NB q r =>
      orb (free_at q b n) (free_at r b n)
  | NN q | NBox q | NW q | NH q | NU q | ND q => free_at q b n
  end.

Lemma put_other F (r : named_env F) a n x b m :
  a <> b \/ n <> m -> put r a n x b m = r b m.
Proof.
  intro H; unfold put; destruct (ty_eq_dec a b) as [E|N]; auto.
  destruct H as [H|H]; [contradiction|]. apply Nat.eqb_neq in H; rewrite H; reflexivity.
Qed.

Lemma free_updates_agree M a n x c (p : ntm c) (r s : free_env M) :
  (forall b m, free_at p b m = true -> r b m = s b m) ->
  forall b m, free_at p b m = true ->
    put r a n x b m = put s a n x b m.
Proof.
  intros H b m V; unfold put; destruct (ty_eq_dec a b) as [E|N]; auto.
  destruct (Nat.eqb n m); auto.
Qed.

Definition binds_free a n {b} (p : ntm b) c m :=
  if ty_eq_dec a c then if Nat.eqb m n then false else free_at p c m
  else free_at p c m.

Lemma binder_agreement M a n b (p : ntm b) (r s : free_env M) x :
  (forall c m, binds_free a n p c m = true -> r c m = s c m) ->
  forall c m, free_at p c m = true -> put r a n x c m = put s a n x c m.
Proof.
  intros H c m V; destruct (ty_eq_dec a c) as [E|N].
  - subst c; destruct (Nat.eq_dec n m) as [E|N].
    + subst m; rewrite !put_same; reflexivity.
    + rewrite !put_other by auto; apply H; unfold binds_free.
      destruct (ty_eq_dec a a); [|contradiction].
      assert (K : Nat.eqb m n = false) by (apply Nat.eqb_neq; auto).
      rewrite K; exact V.
  - rewrite !put_other by auto; apply H; unfold binds_free.
    destruct (ty_eq_dec a c); [contradiction|exact V].
Qed.

Theorem free_variable_agreement M a (p : ntm a) : forall (r s : free_env M),
  (forall b n, free_at p b n = true -> r b n = s b n) ->
  forall i, neval M p r i = neval M p s i.
Proof.
  induction p; intros r s E i; cbn [neval].
  - apply E; cbn [free_at]; destruct (ty_eq_dec a a); [apply Nat.eqb_refl|contradiction].
  - reflexivity.
  - apply (function_extensionality M); intro x; apply IHp; apply binder_agreement; exact E.
  - rewrite IHp1 with (s := s), IHp2 with (s := s); auto;
      intros c k H; apply E; cbn [free_at]; apply orb_true_iff; auto.
  - rewrite IHp1 with (s := s), IHp2 with (s := s); auto;
      intros c k H; apply E; cbn [free_at]; apply orb_true_iff; auto.
  - rewrite IHp with (s := s); auto.
  - rewrite IHp1 with (s := s), IHp2 with (s := s); auto;
      intros c k H; apply E; cbn [free_at]; apply orb_true_iff; auto.
  - rewrite IHp1 with (s := s), IHp2 with (s := s); auto;
      intros c k H; apply E; cbn [free_at]; apply orb_true_iff; auto.
  - rewrite IHp1 with (s := s), IHp2 with (s := s); auto;
      intros c k H; apply E; cbn [free_at]; apply orb_true_iff; auto.
  - rewrite IHp1 with (s := s), IHp2 with (s := s); auto;
      intros c k H; apply E; cbn [free_at]; apply orb_true_iff; auto.
  - apply truth_congr; split; intros H x;
      [rewrite <- IHp with (r := put r a n x)
      | rewrite IHp with (s := put s a n x)]; try apply H;
      apply binder_agreement; exact E.
  - apply truth_congr; split; intros [x H]; exists x;
      [rewrite <- IHp with (r := put r a n x)
      | rewrite IHp with (s := put s a n x)]; try exact H;
      apply binder_agreement; exact E.
  - apply truth_congr; split; intros H j;
      [rewrite <- IHp with (r := r) | rewrite IHp with (s := s)]; auto.
  - apply truth_congr; split; intros [j [O H]]; exists j; split; auto;
      [rewrite <- IHp with (r := r) | rewrite IHp with (s := s)]; auto.
  - apply truth_congr; split; intros [j [O H]]; exists j; split; auto;
      [rewrite <- IHp with (r := r) | rewrite IHp with (s := s)]; auto.
  - apply (function_extensionality M); intro j; apply IHp; exact E.
  - rewrite IHp with (s := s); auto.
Qed.

Lemma free_typed_name_occurs a (p : ntm a) wanted k :
  free_at p wanted k = true -> In k (names_at p wanted).
Proof.
  induction p; cbn [free_at names_at]; try (intros H; discriminate);
    try (intros H; apply orb_true_iff in H; apply in_or_app; destruct H; auto; fail);
    try (intro H; apply IHp; exact H; fail).
  - destruct (ty_eq_dec a wanted); try discriminate.
    intro H; apply Nat.eqb_eq in H; subst k; left; reflexivity.
  - destruct (ty_eq_dec a wanted); [destruct (Nat.eqb k n)|]; intro H; try discriminate;
      first [right; apply IHp; exact H | apply IHp; exact H].
  - destruct (ty_eq_dec a wanted); [destruct (Nat.eqb k n)|]; intro H; try discriminate;
      first [right; apply IHp; exact H | apply IHp; exact H].
  - destruct (ty_eq_dec a wanted); [destruct (Nat.eqb k n)|]; intro H; try discriminate;
      first [right; apply IHp; exact H | apply IHp; exact H].
Qed.

Definition swap_name n m k := if Nat.eqb k n then m else if Nat.eqb k m then n else k.
Lemma swap_name_involution n m k : swap_name n m (swap_name n m k) = k.
Proof.
  unfold swap_name at 2; destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; subst k; unfold swap_name.
    destruct (Nat.eqb m n) eqn:H; [apply Nat.eqb_eq in H; exact H|rewrite Nat.eqb_refl; reflexivity].
  - destruct (Nat.eqb k m) eqn:H.
    + apply Nat.eqb_eq in H; subst k; unfold swap_name; rewrite Nat.eqb_refl; reflexivity.
    + unfold swap_name; rewrite E,H; reflexivity.
Qed.
Definition swap_typed a n m : name_map := fun b k =>
  if ty_eq_dec a b then swap_name n m k else k.
Lemma swap_typed_injective a n m : injective_names (swap_typed a n m).
Proof.
  intros b k l; unfold swap_typed; destruct (ty_eq_dec a b); auto.
  intro H; apply (f_equal (swap_name n m)) in H; rewrite !swap_name_involution in H; exact H.
Qed.

Lemma fresh_assignment_irrelevant M a (p : ntm a) b n x sigma i :
  ~ In n (names_at p b) -> neval M p (put sigma b n x) i = neval M p sigma i.
Proof.
  intro F; apply free_variable_agreement; intros c k K.
  destruct (ty_eq_dec b c) as [E|N]; [subst c|apply put_other; auto].
  destruct (Nat.eq_dec n k) as [E|N]; [subst k|apply put_other; auto].
  exfalso; apply F; eapply free_typed_name_occurs; exact K.
Qed.

Theorem fresh_renaming_binds_original M a (p : ntm a) b n m x sigma i :
  ~ In m (names_at p b) ->
  neval M (rename_named p (swap_typed b n m)) (put sigma b m x) i =
  neval M p (put sigma b n x) i.
Proof.
  intro F.
  transitivity (neval M p (fun c k => put sigma b m x c (swap_typed b n m c k)) i).
  - apply named_renaming_interpretation; [apply swap_typed_injective|reflexivity].
  - apply free_variable_agreement; intros c k K; cbn beta.
    unfold swap_typed; destruct (ty_eq_dec b c) as [E|N].
    + subst c; unfold swap_name; destruct (Nat.eqb k n) eqn:E.
      * apply Nat.eqb_eq in E; subst k; rewrite !put_same; reflexivity.
      * destruct (Nat.eqb k m) eqn:H.
        -- apply Nat.eqb_eq in H; subst k; exfalso; apply F; eapply free_typed_name_occurs; exact K.
        -- apply Nat.eqb_neq in E; apply Nat.eqb_neq in H; rewrite !put_other by auto; reflexivity.
    + rewrite !put_other by auto; reflexivity.
Qed.

Definition editorial_relative (zeta : ntm ivty) n (phi : ntm t) : ntm ivty :=
  let m := 2 * editorial_index (names_at zeta ic ++ names_at phi ic) in
  NL ic m (NCj (NA zeta (NV ic m)) (rename_named phi (swap_typed ic (2*n) m))).

Theorem editorial_relative_interpretation M zeta n phi sigma i :
  neval M (editorial_relative zeta n phi) sigma i =
  (fun x => andb (neval M zeta sigma i x) (neval M phi (put sigma ic (2*n) x) i)).
Proof.
  unfold editorial_relative; set (m := 2 * editorial_index (names_at zeta ic ++ names_at phi ic)).
  assert (F : ~ In m (names_at zeta ic ++ names_at phi ic)).
  { exact (proj1 (proj2 (editorial_index_is_least_even _))). }
  assert (Fz : ~ In m (names_at zeta ic)) by (intro H; apply F; apply in_or_app; auto).
  assert (Fp : ~ In m (names_at phi ic)) by (intro H; apply F; apply in_or_app; auto).
  cbn [neval]; apply (function_extensionality M); intro x; rewrite put_same.
  rewrite fresh_assignment_irrelevant by exact Fz.
  rewrite fresh_renaming_binds_original by exact Fp; reflexivity.
Qed.

Definition intrinsic_relative (zeta : ntm ivty) n (phi : ntm t) : tm [] ivty :=
  Lam (And (App (weaken (embed_named zeta)) (Var vz))
    (nameless phi (@nbind [] ic initial_names (2*n)))).

Theorem editorial_intrinsic_relative_agree M zeta n phi sigma i :
  eval M (embed_named (editorial_relative zeta n phi)) (empty_env M) sigma i =
  eval M (intrinsic_relative zeta n phi) (empty_env M) sigma i.
Proof.
  rewrite embed_named_interpretation, editorial_relative_interpretation.
  cbn [intrinsic_relative eval]; apply (function_extensionality M); intro x.
  rewrite eval_weaken, embed_named_interpretation.
  rewrite named_interpretation with (s := put sigma ic (2*n) x); [reflexivity|].
  apply nbind_matches; intros b k j; reflexivity.
Qed.

Example least_even_is_not_least_raw_even : editorial_index [0;2] = 2.
Proof. reflexivity. Qed.
Example fresh_name_checks_bound_occurrences :
  editorial_index (names_at (NL ic 0 (NV ic 4)) ic) = 4.
Proof. reflexivity. Qed.

Lemma rename_named_supported a (p : ntm a) : forall f g,
  (forall b n, In n (names_at p b) -> f b n = g b n) ->
  rename_named p f = rename_named p g.
Proof.
  induction p; intros f g H; cbn [rename_named]; try reflexivity; f_equal;
    try (apply H; cbn [names_at]; destruct (ty_eq_dec a a); auto; fail);
    try (apply IHp; exact H; fail);
    try (apply IHp1; intros c k K; apply H; cbn [names_at]; apply in_or_app; auto; fail);
    try (apply IHp2; intros c k K; apply H; cbn [names_at]; apply in_or_app; auto; fail).
  all: try (apply H; cbn [names_at]; destruct (ty_eq_dec a a);
    [left; reflexivity|contradiction]).
  all: apply IHp; intros c k K; apply H; cbn [names_at];
    destruct (ty_eq_dec a c); [right; exact K|exact K].
Qed.

Definition replace_typed a n m : name_map := fun b k =>
  if ty_eq_dec a b then if Nat.eqb k n then m else k else k.

Lemma fresh_swap_is_literal_replacement a (p : ntm a) b n m :
  ~ In m (names_at p b) ->
  rename_named p (swap_typed b n m) = rename_named p (replace_typed b n m).
Proof.
  intro F; apply rename_named_supported; intros c k K.
  unfold swap_typed, replace_typed; destruct (ty_eq_dec b c) as [E|N]; [subst c|reflexivity].
  unfold swap_name; destruct (Nat.eqb k n); [reflexivity|].
  destruct (Nat.eqb k m) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; subst k; contradiction.
Qed.

Theorem editorial_rule_uses_literal_replacement zeta n phi :
  editorial_relative zeta n phi =
  let m := 2 * editorial_index (names_at zeta ic ++ names_at phi ic) in
  NL ic m (NCj (NA zeta (NV ic m)) (rename_named phi (replace_typed ic (2*n) m))).
Proof.
  unfold editorial_relative; rewrite fresh_swap_is_literal_replacement; [reflexivity|].
  intro H; apply (proj1 (proj2 (editorial_index_is_least_even (names_at zeta ic ++ names_at phi ic)))).
  apply in_or_app; auto.
Qed.
