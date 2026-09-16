(* Heim 1982 / 2011 pp.90-100,105-111,118-120. Binding infrastructure for
   the earlier indexed language. Input construal trees are already NP-prefixed
   with a selected scope reading; this is not an English/movement parser.
   No new logical axioms; all semantic-dependence results are constructive. *)
From Coq Require Import List Arith Bool Lia.
From dynamic Require Import Heim1982 Heim1982_Indexed.
Import ListNotations.
Set Implicit Arguments.

Definition without (xs bound : list nat) :=
  List.filter (fun i => if in_dec Nat.eq_dec i bound then false else true) xs.
Lemma in_without : forall i xs bound,
  In i (without xs bound) <-> In i xs /\ ~ In i bound.
Proof.
  intros; unfold without; rewrite filter_In.
  destruct (in_dec Nat.eq_dec i bound); simpl; intuition discriminate.
Qed.

Section Binding.
Context {W D : Type}.
Fixpoint free_indices (p : @Indexed W D) : list nat :=
  match p with
  | IAtom n xs _ => slots n xs
  | IAnd p q => free_indices p ++ free_indices q
  | IAll xs p q => without (free_indices p ++ free_indices q) xs
  | IEx xs p => without (free_indices p) xs
  | INeg p => free_indices p
  | IMust xs _ _ p q | IMay xs _ _ p q =>
      without (free_indices p ++ free_indices q) xs
  end.
Fixpoint occurs_free (i : nat) (p : @Indexed W D) : Prop :=
  match p with
  | IAtom n xs _ => In i (slots n xs)
  | IAnd p q => occurs_free i p \/ occurs_free i q
  | IAll xs p q | IMust xs _ _ p q | IMay xs _ _ p q =>
      (occurs_free i p \/ occurs_free i q) /\ ~ In i xs
  | IEx xs p => occurs_free i p /\ ~ In i xs
  | INeg p => occurs_free i p
  end.
Theorem free_indices_exact : forall p i,
  In i (free_indices p) <-> occurs_free i p.
Proof.
  induction p; intro i; simpl; try rewrite in_without;
    try rewrite in_app_iff; try rewrite IHp; try rewrite IHp1, IHp2; tauto.
Qed.

Definition agree_indices xs (g h : @Assignment D) := forall i, In i xs -> g i = h i.
Definition depends_on xs (P : @Assignment D -> Prop) :=
  forall g h, agree_indices xs g h -> (P g <-> P h).
Lemma agree_indices_sym : forall xs g h,
  agree_indices xs g h -> agree_indices xs h g.
Proof. intros xs g h H i Hi; symmetry; auto. Qed.
Lemma agree_indices_app : forall xs ys g h,
  agree_indices (xs ++ ys) g h <-> agree_indices xs g h /\ agree_indices ys g h.
Proof.
  intros xs ys g h; unfold agree_indices; split.
  - intro H; split; intros i Hi; apply H, in_app_iff; auto.
  - intros [Hx Hy] i Hi; apply in_app_iff in Hi; destruct Hi; auto.
Qed.

Definition splice (xs : list nat) (base witness : @Assignment D) : Assignment :=
  fun i => if in_dec Nat.eq_dec i xs then witness i else base i.
Lemma splice_outside : forall xs base witness, outside xs base (splice xs base witness).
Proof.
  intros xs base witness i Hi; unfold splice;
    destruct (in_dec Nat.eq_dec i xs); congruence.
Qed.
Lemma splice_transport : forall used xs g h a,
  agree_indices (without used xs) g h -> outside xs g a ->
  agree_indices used a (splice xs h a).
Proof.
  intros used xs g h a Hag Hoa i Hi; unfold splice.
  destruct (in_dec Nat.eq_dec i xs) as [Hin|Hout]; [reflexivity|].
  rewrite <- (Hoa i Hout); apply Hag, in_without; auto.
Qed.
Lemma selected_all_depends : forall used xs P,
  depends_on used P -> depends_on (without used xs)
    (fun g => forall a, outside xs g a -> P a).
Proof.
  intros used xs P HP g h Hag; split; intros H a Ha.
  - pose proof (@splice_transport used xs h g a (agree_indices_sym Hag) Ha) as E.
    apply (proj2 (HP a (splice xs g a) E)); apply H, splice_outside.
  - pose proof (@splice_transport used xs g h a Hag Ha) as E.
    apply (proj2 (HP a (splice xs h a) E)); apply H, splice_outside.
Qed.
Lemma selected_exists_depends : forall used xs P,
  depends_on used P -> depends_on (without used xs)
    (fun g => exists a, outside xs g a /\ P a).
Proof.
  intros used xs P HP g h Hag; split; intros [a [Ha HPa]].
  - exists (splice xs h a); split; [apply splice_outside|].
    apply (proj1 (HP a _ (@splice_transport used xs g h a Hag Ha))); exact HPa.
  - exists (splice xs g a); split; [apply splice_outside|].
    apply (proj1 (HP a _ (@splice_transport used xs h g a (agree_indices_sym Hag) Ha))); exact HPa.
Qed.
Lemma best_predicate_congr : forall access closer (R : W -> @Assignment D -> Prop) w v g h,
  (forall u, R u g <-> R u h) ->
  (best access closer R w v g <-> best access closer R w v h).
Proof. unfold best; intros; firstorder. Qed.

Theorem satisfaction_depends_only_on_free : forall p w,
  depends_on (free_indices p) (satisfies p w).
Proof.
  induction p as [n xs P|p IHp1 q IHp2|xs p IHp1 q IHp2|
    xs p IHp|p IHp|xs access closer p IHp1 q IHp2|
    xs access closer p IHp1 q IHp2]; intro w; simpl.
  - intros g h H; rewrite (values_agree n xs g h H); reflexivity.
  - intros g h H; apply agree_indices_app in H; destruct H as [Hp Hq].
    rewrite (IHp1 w g h Hp), (IHp2 w g h Hq); reflexivity.
  - apply selected_all_depends; intros g h H.
    apply agree_indices_app in H; destruct H as [Hp Hq].
    rewrite (IHp1 w g h Hp), (IHp2 w g h Hq); reflexivity.
  - apply selected_exists_depends; apply IHp.
  - intros g h H; rewrite (IHp w g h H); reflexivity.
  - change (depends_on (without (free_indices p ++ free_indices q) xs)
      (fun g => forall v h, outside xs g h ->
        best access closer (satisfies p) w v h -> satisfies q v h)).
    intros g h H; assert (E : (forall a, outside xs g a ->
        forall v, best access closer (satisfies p) w v a -> satisfies q v a) <->
      (forall a, outside xs h a ->
        forall v, best access closer (satisfies p) w v a -> satisfies q v a)).
    { apply selected_all_depends with (used := free_indices p ++ free_indices q); [|exact H].
      intros a b Hab; apply agree_indices_app in Hab; destruct Hab as [Hp Hq].
      assert (EB : forall v, best access closer (satisfies p) w v a <-> best access closer (satisfies p) w v b).
      { intro v; apply best_predicate_congr; intro u; apply IHp1; exact Hp. }
      split; intros HM v HB; [apply (proj1 (IHp2 v a b Hq))|apply (proj2 (IHp2 v a b Hq))];
        apply HM; [apply (proj2 (EB v))|apply (proj1 (EB v))]; exact HB. }
    split; intros HM v a Ha HB.
    + exact ((proj1 E (fun b Hb u Hu => HM u b Hb Hu)) a Ha v HB).
    + exact ((proj2 E (fun b Hb u Hu => HM u b Hb Hu)) a Ha v HB).
  - change (depends_on (without (free_indices p ++ free_indices q) xs)
      (fun g => exists v h, outside xs g h /\
        best access closer (satisfies p) w v h /\ satisfies q v h)).
    intros g h H; assert (E : (exists a, outside xs g a /\
        exists v, best access closer (satisfies p) w v a /\ satisfies q v a) <->
      (exists a, outside xs h a /\
        exists v, best access closer (satisfies p) w v a /\ satisfies q v a)).
    { apply selected_exists_depends with (used := free_indices p ++ free_indices q); [|exact H].
      intros a b Hab; apply agree_indices_app in Hab; destruct Hab as [Hp Hq].
      assert (EB : forall v, best access closer (satisfies p) w v a <-> best access closer (satisfies p) w v b).
      { intro v; apply best_predicate_congr; intro u; apply IHp1; exact Hp. }
      split; intros [v [HB HQ]]; exists v;
        [rewrite <- (EB v), <- (IHp2 v a b Hq)|rewrite (EB v), (IHp2 v a b Hq)]; auto. }
    split; intros [v [a [Ha [HB HQ]]]].
    + assert (EA : exists b, outside xs g b /\
          exists u, best access closer (satisfies p) w u b /\ satisfies q u b).
      { exists a; split; [exact Ha|exists v; auto]. }
      destruct (proj1 E EA) as [b [Hb [u [HU HQU]]]]; exists u, b; auto.
    + assert (EA : exists b, outside xs h b /\
          exists u, best access closer (satisfies p) w u b /\ satisfies q u b).
      { exists a; split; [exact Ha|exists v; auto]. }
      destruct (proj2 E EA) as [b [Hb [u [HU HQU]]]]; exists u, b; auto.
Qed.
Theorem changing_bound_or_absent_index_preserves_truth : forall p w g i x,
  ~ In i (free_indices p) -> (satisfies p w (put g i x) <-> satisfies p w g).
Proof.
  intros; apply satisfaction_depends_only_on_free.
  intros j Hj; apply put_other; intro E; subst; contradiction.
Qed.

Definition contextual_truth_computed p w reference :=
  contextual_truth p w (free_indices p) reference.
Theorem computed_context_uses_exact_free_indices : forall p w reference,
  contextual_truth_computed p w reference <->
  (forall i, occurs_free i p -> exists x, reference i x /\ forall y, reference i y -> y = x) /\
  exists g, satisfies p w g /\ forall i, occurs_free i p -> reference i (g i).
Proof.
  intros; unfold contextual_truth_computed, contextual_truth, context_references.
  setoid_rewrite <- free_indices_exact; reflexivity.
Qed.

(* Operator-free introductions are passed upward until the nearest operator.
   Quantifier seed indices represent indices carried along by NP extraction,
   p.96. Definite descriptions/pronouns never contribute selection indices. *)
Inductive Construal : Type :=
| CAtom : forall n, tuple nat n -> (W -> tuple D n -> Prop) -> Construal
| CAnd : Construal -> Construal -> Construal
| CNP : bool -> nat -> Construal -> Construal
| CPronoun : nat -> Construal
| CEvery : list nat -> Construal -> Construal -> Construal
| CNot : Construal -> Construal
| CMust : list nat -> (W -> W -> Prop) -> (W -> W -> Prop) -> Construal -> Construal -> Construal
| CMay : list nat -> (W -> W -> Prop) -> (W -> W -> Prop) -> Construal -> Construal -> Construal.
Fixpoint pending_indices (p : Construal) : list nat :=
  match p with
  | CAnd p q => pending_indices p ++ pending_indices q
  | CNP b i p => if b then pending_indices p else i :: pending_indices p
  | _ => []
  end.
Definition selection seed p := nodup Nat.eq_dec (seed ++ pending_indices p).
Fixpoint compile_indexed (p : Construal) : Indexed :=
  match p with
  | CAtom n xs P => IAtom n xs P
  | CAnd p q => IAnd (compile_indexed p) (compile_indexed q)
  | CNP _ i p => IAnd (iunary i (fun _ _ => True)) (compile_indexed p)
  | CPronoun i => iunary i (fun _ _ => True)
  | CEvery seed p q => IAll (selection seed p) (compile_indexed p)
      (IEx (selection [] q) (compile_indexed q))
  | CNot p => INeg (IEx (selection [] p) (compile_indexed p))
  | CMust seed access closer p q => IMust (selection seed p) access closer
      (compile_indexed p) (IEx (selection [] q) (compile_indexed q))
  | CMay seed access closer p q => IMay (selection seed p) access closer
      (compile_indexed p) (IEx (selection [] q) (compile_indexed q))
  end.
Definition compile_text p := IEx (selection [] p) (compile_indexed p).
Theorem selection_exact : forall seed p i,
  In i (selection seed p) <-> In i seed \/ In i (pending_indices p).
Proof. intros; unfold selection; rewrite nodup_In, in_app_iff; reflexivity. Qed.
Theorem pronouns_do_not_request_binding : forall i, pending_indices (CPronoun i) = [].
Proof. reflexivity. Qed.
Theorem inner_operator_shields_introductions : forall seed p q,
  pending_indices (CEvery seed p q) = [].
Proof. reflexivity. Qed.
Theorem nuclear_index_not_selected_by_outer : forall seed p q i,
  ~ In i seed -> ~ In i (pending_indices p) -> In i (pending_indices q) ->
  ~ In i (selection seed p) /\ In i (selection [] q).
Proof. intros; rewrite !selection_exact; simpl; tauto. Qed.

Definition cnoun i (P : W -> D -> Prop) := CAtom 1 (i, tt) (fun w v => P w (fst v)).
Definition crelation i j (P : W -> D -> D -> Prop) :=
  CAtom 2 (i, (j, tt)) (fun w v => P w (fst v) (fst (snd v))).
Definition indefinite_tree i P := CNP false i (cnoun i P).
Definition text_with_deictic P R :=
  CAnd (indefinite_tree 0 P) (CAnd (CPronoun 1) (crelation 1 0 R)).
Theorem text_closure_keeps_deictic_free : forall P R,
  free_indices (compile_text (text_with_deictic P R)) = [1;1].
Proof. reflexivity. Qed.
Theorem deictic_not_accidentally_bound : forall P R,
  ~ In 1 (selection [] (text_with_deictic P R)).
Proof. intros; simpl; intuition discriminate. Qed.

Definition nuclear_tree P Q R :=
  CEvery [] (indefinite_tree 0 P) (CAnd (indefinite_tree 1 Q) (crelation 0 1 R)).
Theorem compiler_nuclear_indices : forall P Q R,
  selection [] (indefinite_tree 0 P) = [0] /\
  selection [] (CAnd (indefinite_tree 1 Q) (crelation 0 1 R)) = [1] /\
  free_indices (compile_text (nuclear_tree P Q R)) = [].
Proof. intros; repeat split; reflexivity. Qed.

Theorem compiler_nuclear_truth : forall P Q R w g,
  satisfies (compile_indexed (nuclear_tree P Q R)) w g <->
  forall x, P w x -> exists y, Q w y /\ R w x y.
Proof.
  intros P Q R w g.
  change ((forall h, outside [0] g h -> True /\ P w (h 0) ->
    exists a, outside [1] h a /\ (True /\ Q w (a 1)) /\ R w (a 0) (a 1)) <->
    forall x, P w x -> exists y, Q w y /\ R w x y).
  rewrite <- (indexed_nuclear_truth P Q R w g).
  unfold indexed_nuclear; simpl; split; intros H h Ho Hp;
    specialize (H h Ho); firstorder.
Qed.
Theorem closed_indexed_formula_ignores_assignment : forall p w g h,
  free_indices p = [] -> (satisfies p w g <-> satisfies p w h).
Proof.
  intros p w g h H; apply satisfaction_depends_only_on_free.
  intros i Hi; rewrite H in Hi; contradiction.
Qed.
Theorem empty_selection_is_semantically_vacuous : forall (p : @Indexed W D) w g,
  satisfies (IEx [] p) w g <-> satisfies p w g.
Proof.
  intros; split.
  - intros [h [Ho Hp]].
    assert (E : agree_indices (free_indices p) g h) by (intros i Hi; apply Ho; simpl; tauto).
    apply (proj2 (@satisfaction_depends_only_on_free p w g h E)); exact Hp.
  - intro H; exists g; split; [intros i Hi; reflexivity|exact H].
Qed.
Theorem compiled_closed_text_truth : forall p w g,
  pending_indices p = [] ->
  (satisfies (compile_text p) w g <-> satisfies (compile_indexed p) w g).
Proof.
  intros p w g H; unfold compile_text, selection; rewrite H; simpl.
  apply empty_selection_is_semantically_vacuous.
Qed.
Theorem contextual_truth_agrees_with_resolved_assignment : forall p w reference g,
  (forall i, In i (free_indices p) -> reference i (g i)) ->
  contextual_truth_computed p w reference -> satisfies p w g.
Proof.
  intros p w reference g Hg [Hunique [h [Hp Hh]]].
  assert (E : agree_indices (free_indices p) h g).
  { intros i Hi; destruct (Hunique i Hi) as [x [_ Hx]].
    rewrite (Hx (h i) (Hh i Hi)), (Hx (g i) (Hg i Hi)); reflexivity.
  }
  apply (proj1 (@satisfaction_depends_only_on_free p w h g E)); exact Hp.
Qed.

Definition donkey_tree P Q R S :=
  CEvery [] (CAnd (indefinite_tree 0 P)
    (CAnd (indefinite_tree 1 Q) (crelation 0 1 R))) (crelation 0 1 S).
Theorem compiler_donkey_truth : forall P Q R S w g,
  satisfies (compile_indexed (donkey_tree P Q R S)) w g <->
  forall x y, P w x -> Q w y -> R w x y -> S w x y.
Proof.
  intros P Q R S w g.
  change ((forall h, outside [0;1] g h ->
    (True /\ P w (h 0)) /\ (True /\ Q w (h 1)) /\ R w (h 0) (h 1) ->
    satisfies (IEx [] (ibinary 0 1 S)) w h) <->
    forall x y, P w x -> Q w y -> R w x y -> S w x y).
  setoid_rewrite empty_selection_is_semantically_vacuous.
  rewrite <- (indexed_donkey_truth P Q R S w g).
  unfold indexed_donkey; simpl; split; intros H h Ho Hp; specialize (H h Ho); firstorder.
Qed.
End Binding.

Print Assumptions satisfaction_depends_only_on_free.
Print Assumptions computed_context_uses_exact_free_indices.
