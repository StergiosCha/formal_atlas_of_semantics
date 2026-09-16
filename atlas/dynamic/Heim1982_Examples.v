(* Source-bound predictions of Heim1982.v. All domains remain arbitrary in
   the general theorems; finite models at the end are separating tests only.
   Source: Heim 1982 / 2011 pp.214-218, 222-234, 236-238.
   In particular Every uses the FINAL rule with existential nuclear closure,
   not merely the preliminary rule at p.228. *)
From Coq Require Import List Arith Lia.
From dynamic Require Import Heim1982.
Import ListNotations.
Set Implicit Arguments.

Section Predictions.
Context {W D : Type}.

Lemma agree_put_fresh : forall (F : @File W D) (g : @Assignment D) i x,
  ~ dom F i -> agree (dom F) g (put g i x).
Proof.
  intros F g i x Hnew j Hj; symmetry; apply put_other.
  intro E; subst; contradiction.
Qed.

Definition donkey_restrictor (P Q : W -> D -> Prop) (R : W -> D -> D -> Prop) :=
  Seq (indefinite 0 P) (Seq (indefinite 1 Q) (binary 0 1 R)).
Definition donkey_sentence P Q R (S : W -> D -> D -> Prop) :=
  Every (donkey_restrictor P Q R) (Seq (Use 0) (Seq (Use 1) (binary 0 1 S))).

Lemma restrictor_sat : forall P Q R F w g,
  sat (update (donkey_restrictor P Q R) F) w g <->
  sat F w g /\ P w (g 0) /\ Q w (g 1) /\ R w (g 0) (g 1).
Proof. intros; unfold donkey_restrictor; simpl; tauto. Qed.
Lemma restrictor_dom : forall P Q R F i,
  dom (update (donkey_restrictor P Q R) F) i <->
  dom F i \/ i = 0 \/ i = 1.
Proof. intros; unfold donkey_restrictor; simpl; intuition congruence. Qed.
Theorem donkey_felicity : forall P Q R S F,
  licensed (donkey_sentence P Q R S) F <-> ~ dom F 0 /\ ~ dom F 1.
Proof. intros; unfold donkey_sentence, donkey_restrictor; simpl; intuition congruence. Qed.

Theorem donkey_truth_conditions : forall P Q R S F w g,
  condition_B F -> ~ dom F 0 -> ~ dom F 1 ->
  (sat (update (donkey_sentence P Q R S) F) w g <->
   sat F w g /\ forall x y, P w x -> Q w y -> R w x y -> S w x y).
Proof.
  intros P Q R S F w g HB H0 H1; split.
  - intros [HF Htest]; split; [exact HF |].
    intros x y HP HQ HR.
    set (b := put (put g 0 x) 1 y).
    assert (B0 : b 0 = x).
    { unfold b; rewrite put_other by discriminate; apply put_same. }
    assert (B1 : b 1 = y) by (unfold b; apply put_same).
    assert (Hbg : sat F w b).
    { unfold b; apply (proj2 (fresh_put F HB w (put g 0 x) 1 y H1)).
      apply (proj2 (fresh_put F HB w g 0 x H0)); exact HF. }
    assert (Hab : agree (dom F) g b).
    { unfold b; eapply agree_trans; apply agree_put_fresh; eauto. }
    assert (HbR : sat (update (donkey_restrictor P Q R) F) w b).
    { apply restrictor_sat; rewrite B0, B1; auto. }
    destruct (Htest b Hab HbR) as [c [Hbc Hc]].
    assert (HC0 : b 0 = c 0).
    { apply Hbc; apply restrictor_dom; auto. }
    assert (HC1 : b 1 = c 1).
    { apply Hbc; apply restrictor_dom; auto. }
    change (sat (update (donkey_restrictor P Q R) F) w c /\ S w (c 0) (c 1)) in Hc.
    destruct Hc as [_ HS]; rewrite <- HC0, <- HC1, B0, B1 in HS; exact HS.
  - intros [HF HS]; split; [exact HF |].
    intros b Hab Hb; exists b; split; [apply agree_refl |].
    change (sat (update (donkey_restrictor P Q R) F) w b /\ S w (b 0) (b 1)).
    split; [exact Hb |].
    apply restrictor_sat in Hb; destruct Hb as [_ [HP [HQ HR]]]; auto.
Qed.

Definition nuclear_indefinite (P Q : W -> D -> Prop) (R : W -> D -> D -> Prop) :=
  Every (indefinite 0 P) (Seq (indefinite 1 Q) (binary 0 1 R)).

Theorem nuclear_indefinite_felicity : forall P Q R F,
  licensed (nuclear_indefinite P Q R) F <-> ~ dom F 0 /\ ~ dom F 1.
Proof. intros; unfold nuclear_indefinite; simpl; intuition congruence. Qed.

Theorem nuclear_existential_truth_conditions : forall P Q R F w g,
  condition_B F -> ~ dom F 0 -> ~ dom F 1 ->
  (sat (update (nuclear_indefinite P Q R) F) w g <->
   sat F w g /\ forall x, P w x -> exists y, Q w y /\ R w x y).
Proof.
  intros P Q R F w g HB H0 H1; split.
  - intros [HF Htest]; split; [exact HF |].
    intros x HP; set (b := put g 0 x).
    assert (Hb : sat (update (indefinite 0 P) F) w b).
    { split.
      - unfold b; apply (proj2 (fresh_put F HB w g 0 x H0)); exact HF.
      - change (P w (b 0)); unfold b; rewrite put_same; exact HP. }
    assert (Hab : agree (dom F) g b) by (apply agree_put_fresh; exact H0).
    destruct (Htest b Hab Hb) as [c [Hbc Hc]].
    assert (HC0 : x = c 0).
    { rewrite <- (put_same g 0 x); apply Hbc; simpl; auto. }
    change (((sat F w c /\ P w (c 0)) /\ Q w (c 1)) /\ R w (c 0) (c 1)) in Hc.
    exists (c 1); destruct Hc as [[_ HQ] HR]; split; [exact HQ |].
    rewrite HC0; exact HR.
  - intros [HF Hrel]; split; [exact HF |].
    intros b Hab [Hb HP].
    destruct (Hrel (b 0) HP) as [y [HQ HR]].
    exists (put b 1 y); split.
    + intros i Hi; symmetry; apply put_other.
      simpl in Hi; intro E; subst; intuition discriminate.
    + change (((sat F w (put b 1 y) /\ P w (put b 1 y 0)) /\
         Q w (put b 1 y 1)) /\ R w (put b 1 y 0) (put b 1 y 1)).
      rewrite put_same, put_other by discriminate.
      repeat split; auto.
      apply (proj2 (fresh_put F HB w b 1 y H1)); exact Hb.
Qed.

Definition negative_indefinite (P Q : W -> D -> Prop) :=
  Not (Seq (indefinite 0 P) (unary 0 Q)).
Theorem negative_existential_truth_conditions : forall P Q F w g,
  condition_B F -> ~ dom F 0 ->
  (sat (update (negative_indefinite P Q) F) w g <->
   sat F w g /\ ~ exists x, P w x /\ Q w x).
Proof.
  intros P Q F w g HB H0; split.
  - intros [HF Hnot]; split; [exact HF |].
    intros [x [HP HQ]]; apply Hnot.
    exists (put g 0 x); split; [apply agree_put_fresh; exact H0 |].
    change ((sat F w (put g 0 x) /\ P w (put g 0 x 0)) /\ Q w (put g 0 x 0)).
    rewrite put_same; repeat split; auto.
    apply (proj2 (fresh_put F HB w g 0 x H0)); exact HF.
  - intros [HF Hnot]; split; [exact HF |].
    intros [b [_ [[_ HP] HQ]]]; apply Hnot; exists (b 0); auto.
Qed.

Theorem discourse_anaphora_truth : forall F i (P Q : W -> D -> Prop) w,
  condition_B F -> ~ dom F i ->
  (world_content (update (Seq (indefinite i P) (Seq (Use i) (unary i Q))) F) w <->
   world_content F w /\ exists x, P w x /\ Q w x).
Proof.
  intros F i P Q w HB Hi; split.
  - intros [g [[HF HP] HQ]]; split; [exists g; exact HF | exists (g i); auto].
  - intros [[g HF] [x [HP HQ]]]; exists (put g i x).
    change ((sat F w (put g i x) /\ P w (put g i x i)) /\ Q w (put g i x i)).
    rewrite put_same; repeat split; auto.
    apply (proj2 (fresh_put F HB w g i x Hi)); exact HF.
Qed.

(* Complex descriptive NPs are checked as wholes, as p.236 fn.19 requires. *)
Theorem complex_definite_requires_whole_content : forall (F : @File W D) i p q,
  licensed (Mark true i (Seq p q)) F ->
  forall w g, sat F w g -> sat (update q (update p F)) w g.
Proof. intros F i p q [[_ Hent] _] w g HF; apply Hent; exact HF. Qed.

End Predictions.

Module SeparatingModels.
Definition world := unit.
Definition individual := nat.
Definition F : @File world individual := empty_file.
Definition farmer (_ : world) (x : individual) := x = 0.
Definition donkey (_ : world) (x : individual) := x = 1 \/ x = 2.
Definition owns (_ : world) (x y : individual) := x = 0 /\ (y = 1 \/ y = 2).
Definition beats_one (_ : world) (x y : individual) := x = 0 /\ y = 1.

Theorem nonowners_do_not_falsify_donkey : forall w g,
  sat (update (donkey_sentence farmer donkey (fun _ _ _ => False) beats_one) F) w g.
Proof.
  intros w g; apply donkey_truth_conditions; try (apply supported_implies_B, empty_supported).
  - simpl; tauto.
  - simpl; tauto.
  - split; [exact I | intros x y HP HQ Hfalse; contradiction].
Qed.

Theorem one_beaten_donkey_is_not_enough : forall w g,
  ~ sat (update (donkey_sentence farmer donkey owns beats_one) F) w g.
Proof.
  intros w g H.
  apply donkey_truth_conditions in H; try (apply supported_implies_B, empty_supported); try (simpl; tauto).
  destruct H as [_ H]; specialize (H 0 2 eq_refl (or_intror eq_refl) (conj eq_refl (or_intror eq_refl))).
  unfold beats_one in H; lia.
Qed.

Theorem existential_nuclear_scope_allows_one_witness : forall w g,
  sat (update (nuclear_indefinite farmer donkey beats_one) F) w g.
Proof.
  intros w g; apply nuclear_existential_truth_conditions; try (apply supported_implies_B, empty_supported).
  - simpl; tauto.
  - simpl; tauto.
  - split; [exact I |].
    intros x Hx; exists 1; unfold farmer in Hx; subst; unfold donkey, beats_one; auto.
Qed.

Definition empty_domain : Domain := fun _ => False.
Definition one_card : Domain := fun i => i = 0.
Theorem false_files_still_have_distinct_domains :
  (forall w g, @sat world individual (false_file empty_domain) w g <->
               sat (false_file one_card) w g) /\
  ~ @file_equiv world individual (false_file empty_domain) (false_file one_card).
Proof.
  split; [intros; simpl; tauto |].
  intros [H _]; specialize (H 0); change (False <-> 0 = 0) in H; tauto.
Qed.

Theorem scope_blocks_later_pronoun :
  ~ licensed (Seq (Not (indefinite 0 farmer)) (Use 0)) F.
Proof. simpl; tauto. Qed.

(* A world-set alone cannot encode which individual the discourse tracks. *)
Definition tracks (x : individual) : @File world individual :=
  {| dom := one_card; sat := fun _ g => g 0 = x |}.
Theorem same_world_content_different_anaphoric_truth :
  (forall w, world_content (tracks 0) w <-> world_content (tracks 1) w) /\
  world_content (update (unary 0 farmer) (tracks 0)) tt /\
  ~ world_content (update (unary 0 farmer) (tracks 1)) tt.
Proof.
  split.
  - intro w; split; intro H; [exists (fun _ => 1) | exists (fun _ => 0)]; reflexivity.
  - split.
    + exists (fun _ => 0); split; reflexivity.
    + intros [g [H1 H0]]; change (g 0 = 0) in H0; change (g 0 = 1) in H1; congruence.
Qed.
End SeparatingModels.

Module IntensionalPresupposition.
Definition context : @File bool unit :=
  {| dom := fun i => i = 0; sat := fun _ _ => True |}.
Definition actual_only (w : bool) (_ : unit) := w = true.
Theorem actual_truth_is_not_contextual_entailment :
  (forall g, sat context true g -> actual_only true (g 0)) /\
  ~ entails context (unary 0 actual_only) /\
  ~ licensed (definite 0 actual_only) context.
Proof.
  assert (Hno : ~ entails context (unary 0 actual_only)).
  { intro H; specialize (H false (fun _ => tt) I); destruct H as [_ Hbad]; discriminate. }
  split; [intros; reflexivity | split; [exact Hno |]].
  intros [[_ HE] _]; contradiction.
Qed.
End IntensionalPresupposition.

Print Assumptions donkey_truth_conditions.
Print Assumptions nuclear_existential_truth_conditions.
Print Assumptions negative_existential_truth_conditions.
Print Assumptions discourse_anaphora_truth.
Print Assumptions SeparatingModels.one_beaten_donkey_is_not_enough.
