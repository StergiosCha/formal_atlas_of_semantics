(* Stergios Chatzikyriakidis and Giorgos Spathas, AMGL36, 24 April 2015.
   Bisyndetic Distributive Conjunction and Additive ke under a Diachronic
   Perspective, slides 6, 14 and 18-19. Source and scope: README.md.

   The slides give two lexical entries, a double additive and an atomic
   distributive reading for a pair. The Atlas supplies the world argument,
   candidate sets and observation of presupposition together with assertion.
   The final comparison uses the proposition alternatives in (5b) of
   Greek Focus Operators and Their Associates, p. 168. *)

From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

Definition image {X Y : Type} (B : X -> Y) (A : X -> Prop) : Y -> Prop :=
  fun y => exists x, A x /\ y = B x.

Section Meanings.
Variable W : Type.
Record packet := { presupposition : W -> Prop; assertion : W -> Prop }.
Definition defined_true (s : packet) w := presupposition s w /\ assertion s w.
End Meanings.

Definition DIST {D W : Type} (P : D -> W -> Prop) (atoms : list D) w :=
  forall x, In x atoms -> P x w.

Section DoubleAdditive.
Variables D W : Type.
Variable P : D -> W -> Prop.
Definition all_candidates : D -> Prop := fun _ => True.
Definition antecedent (C : D -> Prop) x w :=
  exists y, C y /\ y <> x /\ P y w.
(* Slide 6. The first version asserts P(x), the revised version also
   asserts the existential that both versions presuppose. *)
Definition original_additive C x : packet W :=
  {| presupposition := antecedent C x; assertion := P x |}.
Definition revised_additive C x : packet W :=
  {| presupposition := antecedent C x;
     assertion := fun w => P x w /\ antecedent C x w |}.
(* Slide 18, with pointwise conjunction of the two predicate meanings. *)
Definition double_additive Cx Cy x y : packet W :=
  {| presupposition := fun w => antecedent Cx x w /\ antecedent Cy y w;
     assertion := fun w =>
       (P x w /\ antecedent Cx x w) /\ (P y w /\ antecedent Cy y w) |}.

Definition original_revised_observation_statement : Prop :=
  forall C x w, defined_true (original_additive C x) w <->
                defined_true (revised_additive C x) w.
Definition double_entails_distribution_statement : Prop :=
  forall Cx Cy x y w, defined_true (double_additive Cx Cy x y) w ->
  DIST P [x; y] w.
(* Slide 19: each named associate supplies the other's existential.
   With contextual restriction, availability must also be displayed. *)
Definition mutual_antecedents_statement : Prop :=
  forall Cx Cy x y w, x <> y -> Cx y -> Cy x ->
  (DIST P [x; y] w <-> defined_true (double_additive Cx Cy x y) w).
Definition unrestricted_two_distinct_statement : Prop :=
  forall x y w, x <> y ->
  (DIST P [x; y] w <->
   defined_true (double_additive all_candidates all_candidates x y) w).
(* The talk distinguishes INDIVIDUAL alternatives, whereas CSM (5b)
   distinguishes PROPOSITION alternatives. This extra condition is local
   to the selected P and C, never a universal injectivity axiom. *)
Definition entity_proposition_bridge_statement : Prop :=
  forall C x w,
  (forall y, C y -> y <> x -> P y <> P x) ->
  (antecedent C x w <->
   exists q, image P C q /\ q <> P x /\ q w).
End DoubleAdditive.

Lemma double_additive_forward (D W : Type) (P : D -> W -> Prop) Cx Cy x y w :
  defined_true (double_additive P Cx Cy x y) w -> DIST P [x; y] w.
Proof.
  intros [_ [[Hx _] [Hy _]]] z [H | [H | []]]; subst z; assumption.
Qed.
Lemma double_additive_backward (D W : Type) (P : D -> W -> Prop) Cx Cy x y w :
  x <> y -> Cx y -> Cy x -> DIST P [x; y] w ->
  defined_true (double_additive P Cx Cy x y) w.
Proof.
  intros Hne Hcy Hcx Hd.
  assert (Hx : P x w) by (apply Hd; left; reflexivity).
  assert (Hy : P y w) by (apply Hd; right; left; reflexivity).
  assert (Ha : antecedent P Cx x w).
  { exists y. split; [exact Hcy |]. split; [congruence | exact Hy]. }
  assert (Hb : antecedent P Cy y w).
  { exists x. split; [exact Hcx |]. split; assumption. }
  repeat split; assumption.
Qed.
Section Results.
Variables D W : Type.
Variable P : D -> W -> Prop.

Theorem double_entails_distribution : double_entails_distribution_statement P.
Proof. exact (@double_additive_forward D W P). Qed.

Theorem mutual_antecedents : mutual_antecedents_statement P.
Proof.
  intros Cx Cy x y w different available_y available_x. split.
  - exact (@double_additive_backward D W P Cx Cy x y w different available_y available_x).
  - exact (@double_additive_forward D W P Cx Cy x y w).
Qed.

Theorem unrestricted_nominals : unrestricted_two_distinct_statement P.
Proof.
  intros x y w diff. split.
  - intro hd. eapply double_additive_backward; try exact diff; try exact I; exact hd.
  - apply double_additive_forward.
Qed.

Theorem original_revised_on_defined_truth : original_revised_observation_statement P.
Proof.
  intros C x w. cbn. unfold defined_true. cbn. tauto.
Qed.

Theorem individual_proposition_witness : entity_proposition_bridge_statement P.
Proof.
  intros C x w keep. split.
  - intros [y [hy [ne hold]]]. exists (P y). split.
    + exists y. split. { exact hy. } reflexivity.
    + split. { exact (keep y hy ne). } exact hold.
  - intros [q [[y [hy e]] [neq hold]]]. subst q. exists y. split. { exact hy. }
    split. { intro e. apply neq. now subst y. } exact hold.
Qed.
End Results.

Module Models.
Definition P (x : bool) (_ : unit) := x = true \/ x = false.
Example double_additive_with_mutual_witnesses :
  defined_true (double_additive P (fun _ => True) (fun _ => True) true false) tt.
Proof.
  assert (Ha : antecedent P (fun _ => True) true tt).
  { exists false. repeat split; try exact I; try discriminate. right; reflexivity. }
  assert (Hb : antecedent P (fun _ => True) false tt).
  { exists true. repeat split; try exact I; try discriminate. left; reflexivity. }
  split; [split; assumption |]. split; split; try assumption.
  - left; reflexivity.
  - right; reflexivity.
Qed.
Example restricted_context_blocks_converse :
  DIST P [true; false] tt /\
  ~ defined_true (double_additive P (fun _ => False) (fun _ => True) true false) tt.
Proof.
  split.
  - intros x _. destruct x; [left | right]; reflexivity.
  - intros [[H _] _]. destruct H as [y [H _]]. exact H.
Qed.
Example coincident_associates_do_not_supply_each_other :
  DIST (fun (_ : unit) (_ : unit) => True) [tt; tt] tt /\
  ~ defined_true (double_additive (fun (_ : unit) (_ : unit) => True)
      (fun _ => True) (fun _ => True) tt tt) tt.
Proof.
  split; [intros z Hz; exact I |]. intros [[H _] _].
  destruct H as [[] [_ [H _]]]. apply H. reflexivity.
Qed.
(* Different individuals can have identical proposition meanings.
   Then slide 6's individual condition succeeds but CSM (5b)'s
   proposition-distinctness condition fails for this generated image. *)
Example individual_distinctness_is_not_proposition_distinctness :
  antecedent (fun (_ : bool) (_ : unit) => True) (fun _ => True) true tt /\
  ~ exists q, image (fun (_ : bool) (_ : unit) => True) (fun _ => True) q /\
       q <> (fun _ : unit => True) /\ q tt.
Proof.
  split.
  - exists false. repeat split; try exact I; discriminate.
  - intros [q [[x [_ H]] [Hne _]]]. apply Hne. exact H.
Qed.
End Models.

Print Assumptions original_revised_on_defined_truth.
Print Assumptions double_entails_distribution.
Print Assumptions mutual_antecedents.
Print Assumptions unrestricted_nominals.
Print Assumptions individual_proposition_witness.
