Require Import InqB.
From Coq Require Import List Bool Arith.
Import ListNotations.

(* ========================================================================== *)
(*  Questions_Partitions.v — questions as partitions of the set of indices     *)
(*  FORMAL-ATLAS / atlas/inquisitive                                           *)
(* ========================================================================== *)
(*
   SOURCES
     Groenendijk, J. & Stokhof, M. (1984). Studies on the Semantics of
       Questions and the Pragmatics of Answers. Dissertation, University of
       Amsterdam.  [the paper "On the semantics of questions and the
       pragmatics of answers", sections 1-3, pp. 213-224: partitions (1)
       p. 214; questions as relations between indices (2) p. 215; the
       partition I/Q (3) p. 216; intersection (5) p. 219; whether-questions
       and constituent questions pp. 214-215, 219-220; inclusion (7) and
       the facts (8)-(11) pp. 220-221; "offers an answer" (20) p. 224]
     The corpus copy is a scan with an OCR text layer; formulas were read
     from that layer and are garbled in places.  Page numbers are the
     dissertation's.
   Builds on InqB.v (states, issues as downward-closed sets of states, the
   powerset and pseudo-complement), which this file leaves unchanged.

   WHAT IS FORMALIZED
     Q1  question_is_partition    a question (2) is an equivalence, and its
                                  answers (3) form a partition (1)
     Q2  whether_bipartition      whether-p has the answers p and not-p;
                                  whether-p and whether-not-p coincide
     Q3  meet_cells               the intersection (5) of two questions is a
                                  question; its answers are intersections
     Q4  entails_iff_cells        inclusion (7), as printed with cells, is
                                  refinement of the relations
     Q5  inclusion_facts          the facts (8), (9), (10) and (11)
     Q6  who_from_whether         a constituent question is the intersection
                                  of its whether-questions (p. 220)
     Q7  offers_monotone          an information set that offers an answer
                                  (20) to Q offers one to every R that Q
                                  entails
     Q8  issue_bridge             the sets that offer an answer to Q form an
                                  inquisitive issue; inclusion becomes
                                  refinement; whether-p is the polar
                                  question ?p on inhabited states
     and a four-world model with computed cell counts and three separating
     examples.

   NOT FORMALIZED (and why)
     * The union operations (4) and (6) and the facts (12)-(13): the OCR of
       their definitions is too damaged to transcribe with confidence.
     * Relativization to information sets (16)-(18), partial answers, and
       the pragmatics of answers (sections 2 and 4 onwards).
     * The intensional type theory in which (2) is written: a question is
       given here directly by the denotation function of its expression.

   REPRESENTATION CHOICES
     A question is a relation between indices, as in (2); the partition view
     (3) is derived, not primitive.  Inclusion (7) is stated twice: as
     refinement of relations (ours) and with cells as printed; Q4 proves
     them equivalent.  For the bridge, an inquisitive state is a predicate
     on indices, as in InqB.v; the equivalence with ?p needs the state to be
     inhabited, because the empty state cannot be inspected constructively.
*)

Section Questions.
Variable W : Type.

(* (2) p. 215: the relation that holds between two indices iff the
   expression has the same denotation at both. *)
Definition question := W -> W -> Prop.
Definition of_denotation {D : Type} (a : W -> D) : question :=
  fun i j => a i = a j.

(* p. 215: "reflexive, symmetric and transitive". *)
Definition is_question (Q : question) : Prop :=
  (forall i, Q i i) /\ (forall i j, Q i j -> Q j i) /\
  (forall i j k, Q i j -> Q j k -> Q i k).

(* (3) p. 216: [i]_Q, the answer to Q at i. *)
Definition answer (Q : question) (i : W) : W -> Prop := fun j => Q i j.

(* Q1.  (2) gives an equivalence, and by (1) p. 214 the answers of an
   equivalence form a partition: every index lies in its own answer, and two
   answers that overlap are the same. *)
Theorem question_is_partition :
  (forall (D : Type) (a : W -> D), is_question (of_denotation a)) /\
  (forall Q, is_question Q ->
     (forall i, answer Q i i) /\
     (forall i j, (exists k, answer Q i k /\ answer Q j k) ->
                  forall k, answer Q i k <-> answer Q j k)).
Proof.
  split.
  - intros D a. unfold of_denotation. repeat split; intros; congruence.
  - intros Q (R & S & T). split; [exact R|].
    intros i j (k & Hi & Hj) m. unfold answer in *. split; intros H.
    + exact (T j i m (T j k i Hj (S i k Hi)) H).
    + exact (T i j m (T i k j Hi (S j k Hj)) H).
Qed.

(* pp. 214, 219: a single whether-question. *)
Definition whether (p : W -> bool) : question := of_denotation p.

(* Q2.  whether-p has two possible answers, p and not-p (p. 214), and
   whether-p and whether-not-p are the same question (p. 219). *)
Theorem whether_bipartition : forall (p : W -> bool),
  (forall i j, answer (whether p) i j <-> p j = p i) /\
  (forall i j, whether p i j <-> whether (fun w => negb (p w)) i j).
Proof.
  intros p. split; intros i j; unfold answer, whether, of_denotation.
  - split; intros H; symmetry; exact H.
  - destruct (p i), (p j); simpl; split; intros H; congruence.
Qed.

(* (5) p. 219: the intersection of two questions. *)
Definition meet (Q R : question) : question := fun i j => Q i j /\ R i j.

(* Q3.  The intersection is again a question, and its answers are the
   intersections of the answers of the two. *)
Theorem meet_cells : forall Q R, is_question Q -> is_question R ->
  is_question (meet Q R) /\
  (forall i k, answer (meet Q R) i k <-> answer Q i k /\ answer R i k).
Proof.
  intros Q R (R1 & S1 & T1) (R2 & S2 & T2). split.
  - split; [|split].
    + intros i. split; [apply R1 | apply R2].
    + intros i j [A B]. split; [apply S1; exact A | apply S2; exact B].
    + intros i j k [A B] [C D]. split; [exact (T1 i j k A C) | exact (T2 i j k B D)].
  - intros i k. unfold answer, meet. tauto.
Qed.

(* (7) p. 220, in relational form (ours): Q refines R. *)
Definition entails (Q R : question) : Prop := forall i j, Q i j -> R i j.

(* (7) as printed: every answer to Q is included in an answer to R. *)
Definition entails_cells (Q R : question) : Prop :=
  forall i, exists k, forall j, answer Q i j -> answer R k j.

(* Q4.  The two forms of (7) agree. *)
Theorem entails_iff_cells : forall Q R, is_question Q -> is_question R ->
  (entails Q R <-> entails_cells Q R).
Proof.
  intros Q R (R1 & _ & _) (_ & S2 & T2). split.
  - intros H i. exists i. intros j Hj. exact (H i j Hj).
  - intros H i j Hij. destruct (H i) as (k & Hk). unfold answer in Hk.
    exact (T2 i k j (S2 k i (Hk i (R1 i))) (Hk j Hij)).
Qed.

(* Q5.  (8): every question is included in the one-cell partition.
   (9): the partition into singletons is included in every question.
   (10): an intersection is included in its first term.
   (11): Q is included in R iff their intersection is Q. *)
Theorem inclusion_facts : forall Q R, is_question Q ->
  entails Q (fun _ _ => True) /\
  entails (fun i j => i = j) Q /\
  entails (meet Q R) Q /\
  (entails Q R <-> forall i j, meet Q R i j <-> Q i j).
Proof.
  intros Q R (R1 & _ & _). split; [|split; [|split]].
  - intros i j _. exact I.
  - intros i j ->. apply R1.
  - intros i j H. exact (proj1 H).
  - split.
    + intros Hq i j. split.
      * intros H. exact (proj1 H).
      * intros H. split; [exact H | exact (Hq i j H)].
    + intros H i j Hq. exact (proj2 (proj2 (H i j) Hq)).
Qed.

(* pp. 214-215: a constituent question "who G's": the denotation of G at an
   index, over a finite domain. *)
Definition who {E : Type} (dom : list E) (G : W -> E -> bool) : question :=
  of_denotation (fun w => map (G w) dom).

(* Q6.  p. 220: a constituent question can be constructed by intersection
   from the questions whether a G's, one for each a. *)
Theorem who_from_whether : forall (E : Type) (dom : list E) (G : W -> E -> bool) i j,
  who dom G i j <-> forall a, In a dom -> whether (fun w => G w a) i j.
Proof.
  intros E dom G i j. unfold who, whether, of_denotation. split.
  - intros H a Ha. induction dom as [|b t IH]; [destruct Ha|].
    simpl in H. injection H as Hb Ht. destruct Ha as [<-|Ha]; [exact Hb | exact (IH Ht Ha)].
  - intros H. apply map_ext_in. exact H.
Qed.

(* (20) p. 224: an information set offers an answer to Q iff it lies inside
   one cell of Q. *)
Definition offers (J : W -> Prop) (Q : question) : Prop :=
  forall i j, J i -> J j -> Q i j.

(* Q7.  If Q is included in R, an information set that offers an answer to
   Q offers an answer to R.  This is inclusion read as answerhood (p. 221:
   every answer to Q implies an answer to R). *)
Theorem offers_monotone : forall Q R J, entails Q R -> offers J Q -> offers J R.
Proof. intros Q R J H HJ i j Hi Hj. exact (H i j (HJ i j Hi Hj)). Qed.

(* The inquisitive issue of a question (ours): the states that offer an
   answer to it. *)
Definition issue (Q : question) : @iprop W := fun s => offers s Q.

(* Q8.  Bridge to InqB.v.  The issue of a question is an inquisitive
   proposition; inclusion of questions gives refinement of issues; and on an
   inhabited state, whether-p is supported exactly when the polar question
   ?p = p or not-p is (the join of the powerset of p with its
   pseudo-complement). *)
Theorem issue_bridge :
  (forall Q, @is_prop W (issue Q)) /\
  (forall Q R, entails Q R -> @ple W (issue Q) (issue R)) /\
  (forall (p : W -> bool) (s : @state W) (i0 : W), s i0 ->
     (issue (whether p) s <->
      @pjoin W (@pow W (fun w => p w = true))
               (@pstar W (@pow W (fun w => p w = true))) s)).
Proof.
  split; [|split].
  - intros Q. split.
    + exists (fun _ => False). intros i j [].
    + intros s t Hs Hsub i j Hi Hj. exact (Hs i j (Hsub i Hi) (Hsub j Hj)).
  - intros Q R H s Hs. exact (offers_monotone Q R s H Hs).
  - intros p s i0 Hi0. unfold issue, offers, whether, of_denotation.
    unfold pjoin, pstar, pimp, pbot, pow, sub, empty. split.
    + intros H. destruct (p i0) eqn:E.
      * left. intros w Hw. rewrite <- (H i0 w Hi0 Hw). exact E.
      * right. intros t Hts Htp w Hw.
        pose proof (H i0 w Hi0 (Hts w Hw)) as K. rewrite E in K.
        rewrite (Htp w Hw) in K. discriminate K.
    + intros [H | H] i j Hi Hj.
      * rewrite (H i Hi), (H j Hj). reflexivity.
      * assert (F : forall w, s w -> p w = false).
        { intros w Hw. destruct (p w) eqn:E; [|reflexivity]. exfalso.
          apply (H (fun v => v = w)) with (w := w).
          - intros v ->. exact Hw.
          - intros v ->. exact E.
          - reflexivity. }
        rewrite (F i Hi), (F j Hj). reflexivity.
Qed.

End Questions.

(* ========================================================================== *)
(*  A four-world model                                                         *)
(* ========================================================================== *)

Module FourWorlds.

(* Two atomic sentences; an index says which are true.  Two individuals a
   and b; a G's iff the first sentence holds, b G's iff the second does. *)
Definition Wd := (bool * bool)%type.
Definition ws : list Wd := [(true, true); (true, false); (false, true); (false, false)].
Definition p (w : Wd) : bool := fst w.
Definition q (w : Wd) : bool := snd w.
Definition G (w : Wd) (x : bool) : bool := if x then fst w else snd w.
Definition dom : list bool := [true; false].

(* The number of cells of the question of a denotation function is the
   number of distinct denotations (ours, for the examples). *)
Definition cells {D : Type} (dec : forall x y : D, {x = y} + {x <> y})
  (a : Wd -> D) : nat := length (nodup dec (map a ws)).

(* whether-p makes a bipartition; the constituent question a four-fold one
   (p. 215: n is the number of possible denotations of the predicate). *)
Example cell_counts :
  cells bool_dec p = 2 /\
  cells (list_eq_dec bool_dec) (fun w => map (G w) dom) = 4.
Proof. split; reflexivity. Qed.

(* The constituent question includes each of its whether-questions. *)
Example who_entails_whether :
  entails Wd (who Wd dom G) (whether Wd p) /\
  entails Wd (who Wd dom G) (whether Wd q).
Proof.
  split; intros i j H.
  - exact (proj1 (who_from_whether Wd bool dom G i j) H true (or_introl eq_refl)).
  - exact (proj1 (who_from_whether Wd bool dom G i j) H false (or_intror (or_introl eq_refl))).
Qed.

(* Separating example 1: the converse inclusion fails. *)
Example whether_does_not_entail_who : ~ entails Wd (whether Wd p) (who Wd dom G).
Proof.
  intros H. specialize (H (true, true) (true, false) eq_refl).
  unfold who, of_denotation in H. simpl in H. discriminate H.
Qed.

(* Separating example 2: two independent whether-questions; neither is
   included in the other. *)
Example independent_questions :
  ~ entails Wd (whether Wd p) (whether Wd q) /\
  ~ entails Wd (whether Wd q) (whether Wd p).
Proof.
  split; intros H.
  - specialize (H (true, true) (true, false) eq_refl). discriminate H.
  - specialize (H (true, true) (false, true) eq_refl). discriminate H.
Qed.

(* Separating example 3: the information that p offers an answer to
   whether-p and not to the constituent question. *)
Example information_and_answers :
  offers Wd (fun w => p w = true) (whether Wd p) /\
  ~ offers Wd (fun w => p w = true) (who Wd dom G).
Proof.
  split.
  - intros i j Hi Hj. unfold whether, of_denotation. rewrite Hi, Hj. reflexivity.
  - intros H. specialize (H (true, true) (true, false) eq_refl eq_refl).
    unfold who, of_denotation in H. simpl in H. discriminate H.
Qed.

End FourWorlds.

(* ========================================================================== *)
(*  Assumption audit                                                           *)
(* ========================================================================== *)
Print Assumptions question_is_partition.
Print Assumptions whether_bipartition.
Print Assumptions meet_cells.
Print Assumptions entails_iff_cells.
Print Assumptions inclusion_facts.
Print Assumptions who_from_whether.
Print Assumptions offers_monotone.
Print Assumptions issue_bridge.
Print Assumptions FourWorlds.cell_counts.
Print Assumptions FourWorlds.who_entails_whether.
Print Assumptions FourWorlds.whether_does_not_entail_who.
Print Assumptions FourWorlds.independent_questions.
Print Assumptions FourWorlds.information_and_answers.
