(* Earlier indexed semantics and modality: Heim 1982 / 2011 II.2-4,
   pp.87-100, 105-111, 115-129. This is kept separate from the final FCS,
   not silently blended with it. Correspondence is proved for named examples.
   Accessibility is written access actual candidate (source: candidate RB actual).
   best uses the source's minimum/best-world simplification, NOT a limit-free
   replacement from later Kratzer. Existence of best worlds is not assumed by
   definition; the source's p.117 fn.8 assumption and its effect are tested.
   Classical is used only to establish necessity/possibility duality. *)
From Coq Require Import List Arith Lia Classical.
From dynamic Require Import Heim1982 Heim1982_Examples.
Import ListNotations.
Set Implicit Arguments.

Section IndexedSemantics.
Context {W D : Type}.
Definition outside (xs : list nat) (g h : @Assignment D) :=
  forall i, ~ In i xs -> g i = h i.
Definition best (access closer : W -> W -> Prop)
  (restrictor : W -> @Assignment D -> Prop) w v g :=
  access w v /\ restrictor v g /\
  forall u, access w u -> restrictor u g -> closer v u.

Inductive Indexed : Type :=
| IAtom : forall n, tuple nat n -> (W -> tuple D n -> Prop) -> Indexed
| IAnd : Indexed -> Indexed -> Indexed
| IAll : list nat -> Indexed -> Indexed -> Indexed
| IEx : list nat -> Indexed -> Indexed
| INeg : Indexed -> Indexed
| IMust : list nat -> (W -> W -> Prop) -> (W -> W -> Prop) -> Indexed -> Indexed -> Indexed
| IMay : list nat -> (W -> W -> Prop) -> (W -> W -> Prop) -> Indexed -> Indexed -> Indexed.

Fixpoint satisfies (p : Indexed) (w : W) (g : @Assignment D) : Prop :=
  match p with
  | IAtom n xs P => P w (values n g xs)
  | IAnd p q => satisfies p w g /\ satisfies q w g
  | IAll xs p q => forall h, outside xs g h -> satisfies p w h -> satisfies q w h
  | IEx xs p => exists h, outside xs g h /\ satisfies p w h
  | INeg p => ~ satisfies p w g
  | IMust xs access closer p q => forall v h,
      outside xs g h -> best access closer (satisfies p) w v h -> satisfies q v h
  | IMay xs access closer p q => exists v h,
      outside xs g h /\ best access closer (satisfies p) w v h /\ satisfies q v h
  end.

Definition iunary i (P : W -> D -> Prop) :=
  IAtom 1 (i, tt) (fun w v => P w (fst v)).
Definition ibinary i j (P : W -> D -> D -> Prop) :=
  IAtom 2 (i, (j, tt)) (fun w v => P w (fst v) (fst (snd v))).
Definition iconstant (P : W -> Prop) := IAtom 0 tt (fun w _ => P w).

Lemma outside_put : forall xs g i x, In i xs -> outside xs g (put g i x).
Proof.
  intros xs g i x Hin j Hj; symmetry; apply put_other.
  intro E; subst; contradiction.
Qed.
Lemma outside_put2 : forall xs g i j x y,
  In i xs -> In j xs -> outside xs g (put (put g i x) j y).
Proof.
  intros xs g i j x y Hi Hj k Hk.
  rewrite put_other, put_other; auto; intro E; subst; contradiction.
Qed.
Lemma outside_keeps : forall xs g h i,
  outside xs g h -> ~ In i xs -> g i = h i.
Proof. auto. Qed.

Definition indexed_donkey (P Q : W -> D -> Prop) (R S : W -> D -> D -> Prop) :=
  IAll [0;1] (IAnd (iunary 0 P) (IAnd (iunary 1 Q) (ibinary 0 1 R)))
    (ibinary 0 1 S).
Theorem indexed_donkey_truth : forall P Q R S w g,
  satisfies (indexed_donkey P Q R S) w g <->
  forall x y, P w x -> Q w y -> R w x y -> S w x y.
Proof.
  intros P Q R S w g; split.
  - intros H x y HP HQ HR.
    specialize (H (put (put g 0 x) 1 y)).
    assert (Ho : outside [0;1] g (put (put g 0 x) 1 y)).
    { apply outside_put2; simpl; auto. }
    specialize (H Ho); simpl in H.
    rewrite put_same, put_other, put_same in H by discriminate; auto.
  - intros H h Ho [HP [HQ HR]]; apply H; assumption.
Qed.
Theorem final_indexed_donkey_correspondence : forall P Q R S F w g,
  condition_B F -> ~ dom F 0 -> ~ dom F 1 ->
  (sat (update (donkey_sentence P Q R S) F) w g <->
   sat F w g /\ satisfies (indexed_donkey P Q R S) w g).
Proof.
  intros; rewrite donkey_truth_conditions by assumption.
  rewrite indexed_donkey_truth; reflexivity.
Qed.

Definition indexed_nuclear (P Q : W -> D -> Prop) (R : W -> D -> D -> Prop) :=
  IAll [0] (iunary 0 P) (IEx [1] (IAnd (iunary 1 Q) (ibinary 0 1 R))).
Theorem indexed_nuclear_truth : forall P Q R w g,
  satisfies (indexed_nuclear P Q R) w g <->
  forall x, P w x -> exists y, Q w y /\ R w x y.
Proof.
  intros P Q R w g; split.
  - intros H x HP.
    assert (Ho : outside [0] g (put g 0 x)) by (apply outside_put; simpl; auto).
    specialize (H (put g 0 x) Ho); simpl in H; rewrite put_same in H.
    destruct (H HP) as [h [Hh [HQ HR]]].
    assert (E : x = h 0).
    { rewrite <- (put_same g 0 x); apply Hh; simpl; intuition discriminate. }
    exists (h 1); rewrite E; auto.
  - intros H h Ho HP.
    destruct (H (h 0) HP) as [y [HQ HR]].
    exists (put h 1 y); split; [apply outside_put; simpl; auto |].
    simpl; rewrite put_same, put_other by discriminate; auto.
Qed.
Theorem final_indexed_nuclear_correspondence : forall P Q R F w g,
  condition_B F -> ~ dom F 0 -> ~ dom F 1 ->
  (sat (update (nuclear_indefinite P Q R) F) w g <->
   sat F w g /\ satisfies (indexed_nuclear P Q R) w g).
Proof.
  intros; rewrite nuclear_existential_truth_conditions by assumption.
  rewrite indexed_nuclear_truth; reflexivity.
Qed.

Theorem indexed_text_closure : forall i (P Q : W -> D -> Prop) w g,
  satisfies (IEx [i] (IAnd (iunary i P) (iunary i Q))) w g <->
  exists x, P w x /\ Q w x.
Proof.
  intros i P Q w g; split.
  - intros [h [_ [HP HQ]]]; exists (h i); auto.
  - intros [x [HP HQ]]; exists (put g i x); split.
    + apply outside_put; simpl; auto.
    + simpl; rewrite put_same; auto.
Qed.

(* Necessary deictic condition of II.3.3 p.109, not sufficient for all felicity.
   Reference provision is explicit context data, not a resolver implemented here. *)
Definition context_references (free : list nat) (reference : nat -> D -> Prop) :=
  forall i, In i free -> exists x, reference i x /\ forall y, reference i y -> y = x.
Definition contextual_truth p w free reference :=
  context_references free reference /\
  exists g, satisfies p w g /\ forall i, In i free -> reference i (g i).

Theorem may_implies_not_must_not : forall xs access closer p q w g,
  satisfies (IMay xs access closer p q) w g ->
  ~ satisfies (IMust xs access closer p (INeg q)) w g.
Proof. intros xs access closer p q w g [v [h [Ho [Hb Hq]]]] H; exact (H v h Ho Hb Hq). Qed.
Theorem modal_duality_classical : forall xs access closer p q w g,
  satisfies (IMay xs access closer p q) w g <->
  ~ satisfies (IMust xs access closer p (INeg q)) w g.
Proof.
  intros; split; [apply may_implies_not_must_not |].
  intro H; apply NNPP; intro Hnone; apply H.
  intros v h Ho Hb Hq; apply Hnone; exists v, h; auto.
Qed.
Theorem no_best_worlds_make_necessity_vacuous : forall xs access closer p q w g,
  (forall v h, outside xs g h -> ~ best access closer (satisfies p) w v h) ->
  satisfies (IMust xs access closer p q) w g /\
  ~ satisfies (IMay xs access closer p q) w g.
Proof.
  intros xs access closer p q w g H; split.
  - intros v h Ho Hb; exfalso; exact (H v h Ho Hb).
  - intros [v [h [Ho [Hb _]]]]; exact (H v h Ho Hb).
Qed.
Theorem realistic_necessity_has_actual_consequences : forall xs access closer p q w g,
  access w w -> (forall v, access w v -> closer w v) ->
  satisfies (IMust xs access closer p q) w g ->
  forall h, outside xs g h -> satisfies p w h -> satisfies q w h.
Proof.
  intros xs access closer p q w g HR HC HM h Ho Hp.
  apply (HM w h Ho); unfold best; auto.
Qed.

(* A minimal source-directed subject-NP construal, p.87. General movement
   possibilities and grammar constraints are represented separately below. *)
Inductive SubjectNP :=
| PronounNP : nat -> SubjectNP
| FullNP : bool -> nat -> @Formula W D -> SubjectNP
| EveryNP : nat -> @Formula W D -> SubjectNP.
Definition prefix_subject np (vp : nat -> @Formula W D) :=
  match np with
  | PronounNP i => Seq (Use i) (vp i)
  | FullNP definite i description => Seq (Mark definite i description) (vp i)
  | EveryNP i restriction => Every (Mark false i restriction) (vp i)
  end.
Theorem indefinite_prefix_has_no_quantifier : forall i description vp F,
  update (prefix_subject (FullNP false i description) vp) F =
  update (vp i) (update description F).
Proof. reflexivity. Qed.

(* pp.137-138 fn.27: scope invariance is conditional on the name's
   felicity, not an unconditional equivalence of the two open formulas. *)
Theorem proper_name_scope_on_felicitous_assignments : forall (named : D) p q w g,
  g 1 = named ->
  (satisfies (IAnd (iunary 1 (fun _ x => x = named)) (IAll [0] p q)) w g <->
   satisfies (IAll [0] (IAnd (iunary 1 (fun _ x => x = named)) p) q) w g).
Proof.
  intros named p q w g Hname; split.
  - intros [_ H] h Ho [_ Hp]; apply H; assumption.
  - intro H; split; [exact Hname |].
    intros h Ho Hp; apply H; [exact Ho | split; [|exact Hp]].
    change (h 1 = named); rewrite <- Hname; symmetry; apply Ho; simpl; intuition discriminate.
Qed.
End IndexedSemantics.

Module ModalModels.
Definition forever : @Indexed nat bool := iconstant (fun _ => True).
Definition never : @Indexed nat bool := iconstant (fun _ => False).
Definition unbounded_better (v u : nat) := u <= v.
Theorem limit_assumption_is_substantive : forall w g,
  satisfies (IMust [] (fun _ _ => True) unbounded_better forever never) w g /\
  ~ satisfies (IMay [] (fun _ _ => True) unbounded_better forever forever) w g.
Proof.
  intros w g; split.
  - intros v h Ho [_ [_ Hbest]].
    specialize (Hbest (S v) I I); unfold unbounded_better in Hbest; lia.
  - intros [v [h [_ [[_ [_ Hbest]] _]]]].
    specialize (Hbest (S v) I I); unfold unbounded_better in Hbest; lia.
Qed.

Definition any_world : @Indexed bool unit := iconstant (fun _ => True).
Definition ideal_property : @Indexed bool unit := iconstant (fun w => w = true).
Definition ideal_first (v u : bool) := v = true \/ u = false.
Theorem ideal_necessity_does_not_entail_actuality : forall g,
  satisfies (IMust [] (fun _ _ => True) ideal_first any_world ideal_property) false g /\
  ~ satisfies ideal_property false g.
Proof.
  intro g; split.
  - intros v h Ho [_ [_ Hb]].
    specialize (Hb true I I); unfold ideal_first in Hb; intuition discriminate.
  - simpl; discriminate.
Qed.

Definition box (access : bool -> bool -> Prop) (P : bool -> Prop) w :=
  forall v, access w v -> P v.
Theorem reflexive_access_gives_factivity : forall access P w,
  access w w -> box access P w -> P w.
Proof. auto. Qed.
Theorem nonfactive_access_does_not_give_factivity :
  box (fun _ v => v = true) (fun v => v = true) false /\ false <> true.
Proof. unfold box; split; auto; discriminate. Qed.
End ModalModels.

(* II.5.2 pp.133-140: constraints on an already analyzed source structure.
   The source imports syntactic notions from grammar; these data do not
   pretend to implement a parser or decide all movement possibilities. *)
Module ConstrualConstraints.
Record NP := {
  index : nat;
  pronoun : bool;
  reflexive_or_reciprocal : bool;
  indefinite_np : bool
}.
Definition DRR (ccommands intervenes : NP -> NP -> Prop) (x y : NP) :=
  ccommands x y -> reflexive_or_reciprocal y = false ->
  ~ intervenes x y -> index x <> index y.
Definition NCR (ccommands : NP -> NP -> Prop) (x y : NP) :=
  ccommands x y -> pronoun y = false -> index x <> index y.
Definition novelty (earlier : list NP) (x : NP) :=
  indefinite_np x = true -> forall y, In y earlier -> index x <> index y.
Theorem earlier_definite_also_blocks_indefinite_coindexing : forall earlier x y,
  novelty earlier x -> indefinite_np x = true -> In y earlier -> index x <> index y.
Proof. auto. Qed.
(* p.136: do not adjoin above the lowest source S. The source itself
   sets attitude-complement exceptions aside; no stronger claim is made. *)
Definition scope_constraint (dominates : nat -> nat -> Prop)
  (lowest_source_sentence : nat -> nat) occurrence target :=
  target = lowest_source_sentence occurrence \/
  dominates (lowest_source_sentence occurrence) target.
Definition lowest_operator (commands : nat -> nat -> Prop)
  (operator : nat -> Prop) op occurrence :=
  operator op /\ commands op occurrence /\
  ~ exists inner, operator inner /\ commands op inner /\ commands inner occurrence.
Definition operator_indexing commands operator (assigned : nat -> nat -> Prop)
  op occurrence (np : NP) :=
  indefinite_np np = true -> lowest_operator commands operator op occurrence ->
  assigned op (index np).
(* The source leaves leftness versus c-command for weak crossover open
   (p.140); neither alternative is silently selected here. *)
Definition weak_crossover (permitted : NP -> NP -> Prop) quantified x y :=
  quantified x -> index x = index y -> permitted x y.
End ConstrualConstraints.

Print Assumptions final_indexed_donkey_correspondence.
Print Assumptions final_indexed_nuclear_correspondence.
Print Assumptions modal_duality_classical.
Print Assumptions ModalModels.limit_assumption_is_substantive.
Print Assumptions ModalModels.ideal_necessity_does_not_entail_actuality.
