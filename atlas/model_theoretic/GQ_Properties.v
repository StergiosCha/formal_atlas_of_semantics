Require Import List Bool Arith Lia Permutation.
Import ListNotations.

(* ========================================================================== *)
(*  GQ_Properties.v -- properties of determiners on finite universes          *)
(*  FORMAL-ATLAS / atlas/model_theoretic (standard library only)              *)
(* ========================================================================== *)
(*
   SOURCES
     Barwise, J. & Cooper, R. (1981). Generalized quantifiers and natural
       language. Linguistics and Philosophy 4(2): 159-219.
       Read for this file: section 2.5 (S5, S6, pp. 169-170); section 4.4
       (pp. 178-179, "lives on", U3); 4.6 (p. 182, strong determiners); 4.7
       (pp. 184-186, monotone quantifiers, -Q and Q-); 4.8 (pp. 189-190,
       intersection condition); 4.9 (p. 193, persistence, U8); 4.11
       (pp. 197-199, duals); Appendix B (p. 208, SP1-SP3); Appendix C
       (pp. 209-212, C1-C10).
     Nothing else is cited.  Notions the source does not state are marked
     "ours".

   WHAT IS FORMALIZED
     Determiners as boolean relations between two subsets of a finite
     universe E (a list), and the source's properties of them.
       T1 logical_determiners_live_on   every, some, no, (at least) n,
                                        exactly n, more than half live on
                                        their first argument (p. 170)
       T2 monotonicity_profile          mon-up / mon-down and (anti-)
                                        persistence of these (pp. 185, 193)
       T3 C1_lives_on_top               C1 (p. 209)
       T4 C5_intersection_iff_symmetric C5 (pp. 210-211), via lemma C4
       T5 C6_strong_intersective_trivial  the claim proved inside C6 (p. 211)
       T6 C7_persistent_symmetric_mon_up  C7 (p. 212)
       T7 C9_negation_reverses_monotonicity  C9 (p. 212; text p. 186)
       T8 C10_mon_up_meets_dual         C10 (p. 212; text p. 199)
     Worked model: universe {0..4}, man = {0,1,2}, run = {0,1,3}.
     Separating examples: "only" does not live on its first argument (ours);
     "exactly 2" is not monotone (p. 185); "some but not all" is persistent
     but neither mon-up nor symmetric (p. 211); "every" fails the
     intersection condition (instance of C6).

   NOT FORMALIZED (and why)
     * Partial determiners (the n, both, neither: "undefined otherwise",
       p. 169-170).  All determiners here are total.  Consequence recorded
       below (no_total_proper_strong): for total determiners the hypothesis
       "proper strong" of C6 cannot be met, so T5 states the claim that the
       source's proof of C6 actually establishes.
     * most, many, few: non-logical in the source (S6, p. 170; Appendix B).
       Only "more than half" is defined here; it is not the source's "most"
       (it fails SP1 at the empty set, see mth_fails_SP1_at_empty).
     * Universals U1-U10: empirical claims about languages, not theorems.
     * C2, C3 (principal filters, definites), C8, C11-C13, witness sets,
       the logic L(GQ) and the fragment of English.
     * Infinite universes ("finitely many", "infinitely many").

   REPRESENTATION CHOICES
     * A subset of E is a function U -> bool; only its values on the members
       of E matter.  Inclusion (sub) and equality (eqset) are relative to E.
     * Because two functions can agree on E without being equal, theorems
       whose source proofs replace a set by an equal one carry the visible
       premise ExtD D (D respects equality of sets on E; ours).  In the
       source this is automatic.  All determiners defined here satisfy it.
     * Cardinality is the length of the filtered list E.  It is the number
       of members only when E is listed without repetition: this is the
       premise of card_counts_members, it holds of the model (E5_nodup), and
       repetition_inflates_counts shows what goes wrong without it.
     * "lives on" is stated as an equation of booleans, D A X = D A (X n A).
*)

Section GQ.
Context {U : Type}.

Definition eset := U -> bool.
Definition full : eset := fun _ => true.
Definition empty : eset := fun _ => false.
Definition inter (A B : eset) : eset := fun x => A x && B x.
Definition compl (A : eset) : eset := fun x => negb (A x).

(* B&C p. 209: a quantifier on M is any set of subsets of E. *)
Definition quantifier := eset -> bool.
(* A (total) determiner assigns a quantifier to each set (S5-S6, pp. 169-170). *)
Definition determiner := eset -> eset -> bool.

(* -Q and Q- (section 4.7, p. 186) and the dual (section 4.11, p. 197). *)
Definition neg (Q : quantifier) : quantifier := fun X => negb (Q X).
Definition postneg (Q : quantifier) : quantifier := fun X => Q (compl X).
Definition dual (Q : quantifier) : quantifier := fun X => negb (Q (compl X)).

(* "Q lives on A": X in Q iff (X n A) in Q (section 4.4, p. 178; p. 209). *)
Definition LivesOnQ (Q : quantifier) (A : eset) : Prop :=
  forall X, Q X = Q (inter X A).
(* The determiner requirement of S6 (p. 170) and U3 (p. 179). *)
Definition LivesOn (D : determiner) : Prop := forall A, LivesOnQ (D A) A.

(* Symmetry and the intersection condition (p. 189-190; p. 210). *)
Definition Symmetric (D : determiner) : Prop := forall A B, D A B = D B A.
Definition Intersection (D : determiner) : Prop :=
  forall A B, D A B = D (inter A B) B.

(* Positive / negative strong (section 4.6, p. 182; p. 210-211). *)
Definition PosStrong (D : determiner) : Prop := forall A, D A A = true.
Definition NegStrong (D : determiner) : Prop := forall A, D A A = false.

(* Proper quantifier or sieve (section 4.5; p. 209). *)
Definition ProperQ (Q : quantifier) : Prop :=
  (exists X, Q X = true) /\ (exists X, Q X = false).

(* ---- counting on an explicit list (ours, auxiliary) ---- *)
Definition cardl (l : list U) (A : eset) : nat := length (filter A l).

Lemma cardl_ext : forall l A B,
  (forall x, In x l -> A x = B x) -> cardl l A = cardl l B.
Proof.
  unfold cardl; induction l as [|a l IH]; intros A B H; [reflexivity|].
  assert (IH' : length (filter A l) = length (filter B l))
    by (apply IH; intros; apply H; right; assumption).
  simpl. rewrite (H a (or_introl eq_refl)).
  destruct (B a); simpl; rewrite IH'; reflexivity.
Qed.

Lemma cardl_mono : forall l A B,
  (forall x, In x l -> A x = true -> B x = true) -> cardl l A <= cardl l B.
Proof.
  unfold cardl; induction l as [|a l IH]; intros A B H; [apply le_n|].
  assert (IH' : length (filter A l) <= length (filter B l))
    by (apply IH; intros; apply H; [right|]; assumption).
  simpl. destruct (A a) eqn:Ha.
  - rewrite (H a (or_introl eq_refl) Ha). simpl. lia.
  - destruct (B a); simpl; lia.
Qed.

Section Universe.
Variable E : list U.

Definition sub (A B : eset) : Prop :=
  forall x, In x E -> A x = true -> B x = true.
Definition eqset (A B : eset) : Prop := forall x, In x E -> A x = B x.
Definition card (A : eset) : nat := cardl E A.

(* ours: D (resp. Q) depends only on the parts of its arguments inside E. *)
Definition ExtQ (Q : quantifier) : Prop :=
  forall X Y, eqset X Y -> Q X = Q Y.
Definition ExtD (D : determiner) : Prop :=
  forall A A' B B', eqset A A' -> eqset B B' -> D A B = D A' B'.

(* Monotone increasing / decreasing quantifiers (section 4.7, p. 184). *)
Definition MonUpQ (Q : quantifier) : Prop :=
  forall X Y, sub X Y -> Q X = true -> Q Y = true.
Definition MonDownQ (Q : quantifier) : Prop :=
  forall X Y, sub Y X -> Q X = true -> Q Y = true.
(* A determiner is mon-up if all its quantifiers are (p. 185; p. 211). *)
Definition MonUp (D : determiner) : Prop := forall A, MonUpQ (D A).
Definition MonDown (D : determiner) : Prop := forall A, MonDownQ (D A).

(* Persistent / anti-persistent determiners (section 4.9, p. 193). *)
Definition Persistent (D : determiner) : Prop :=
  forall A B X, sub A B -> D A X = true -> D B X = true.
Definition AntiPersistent (D : determiner) : Prop :=
  forall A B X, sub A B -> D B X = true -> D A X = true.

(* ---- the determiners ---- *)
(* S5 a-c, p. 169: some, every, no. *)
Definition every : determiner :=
  fun A X => forallb (fun x => implb (A x) (X x)) E.
Definition some : determiner :=
  fun A X => existsb (fun x => A x && X x) E.
Definition no : determiner := fun A X => negb (some A X).
(* S5 d, p. 169: the numeral n (|X n A| >= n) and "exactly n". *)
Definition at_least (n : nat) : determiner :=
  fun A X => n <=? card (inter A X).
Definition exactly (n : nat) : determiner :=
  fun A X => card (inter A X) =? n.
(* "more than half", "at least half": named as a dual pair on pp. 198-199;
   the cardinality definitions are the standard ones (ours). *)
Definition more_than_half : determiner :=
  fun A X => card A <? 2 * card (inter A X).
Definition at_least_half : determiner :=
  fun A X => card A <=? 2 * card (inter A X).
(* p. 211: "some but not all of the things in A". *)
Definition some_not_all : determiner :=
  fun A X => some A X && negb (every A X).
(* ours: "only" read as a determiner, only A X iff X is included in A.
   The source does not discuss it. *)
Definition only : determiner := fun A X => every X A.

(* ---- basic facts (ours, auxiliary) ---- *)
Lemma every_spec : forall A B, every A B = true <-> sub A B.
Proof.
  intros A B; unfold every, sub; rewrite forallb_forall; split; intros H x Hx.
  - intro HA. specialize (H x Hx). rewrite HA in H. exact H.
  - specialize (H x Hx). destruct (A x); simpl; auto.
Qed.

Lemma some_spec : forall A B,
  some A B = true <-> exists x, In x E /\ A x = true /\ B x = true.
Proof.
  intros A B; unfold some; rewrite existsb_exists; split;
    intros [x [Hx H]]; exists x; (split; [exact Hx|]).
  - apply (proj1 (andb_true_iff _ _)); exact H.
  - apply (proj2 (andb_true_iff _ _)); exact H.
Qed.

Lemma sub_refl : forall A, sub A A.
Proof. intros A x _ H; exact H. Qed.

Lemma inter_sub : forall A A' X Y,
  sub A A' -> sub X Y -> sub (inter A X) (inter A' Y).
Proof.
  intros A A' X Y HA HX x Hx H; unfold inter in *.
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff; split; [apply HA | apply HX]; assumption.
Qed.

Lemma compl_sub : forall X Y, sub X Y -> sub (compl Y) (compl X).
Proof.
  intros X Y H x Hx; unfold compl; intro HY.
  destruct (X x) eqn:e; [|reflexivity].
  rewrite (H x Hx e) in HY. simpl in HY. discriminate.
Qed.

Lemma inter_ext : forall A A' B B',
  eqset A A' -> eqset B B' -> eqset (inter A B) (inter A' B').
Proof.
  intros A A' B B' HA HB x Hx; unfold inter.
  rewrite (HA x Hx), (HB x Hx); reflexivity.
Qed.

Lemma card_ext : forall A B, eqset A B -> card A = card B.
Proof. intros A B H; apply cardl_ext; exact H. Qed.

Lemma card_mono : forall A B, sub A B -> card A <= card B.
Proof. intros A B H; apply cardl_mono; exact H. Qed.

(* The defined determiners respect equality on E (ours). *)
Lemma every_ext : ExtD every.
Proof.
  intros A A' B B' HA HB; apply eq_true_iff_eq; rewrite !every_spec.
  split; intros H x Hx Ha; pose proof (HA x Hx); pose proof (HB x Hx);
    pose proof (H x Hx); destruct (A x), (A' x), (B x), (B' x);
    auto; discriminate.
Qed.

Lemma some_ext : ExtD some.
Proof.
  intros A A' B B' HA HB; apply eq_true_iff_eq; rewrite !some_spec.
  split; intros [x [Hx [H1 H2]]]; exists x;
    pose proof (HA x Hx); pose proof (HB x Hx);
    (split; [exact Hx | split; congruence]).
Qed.

Lemma no_ext : ExtD no.
Proof.
  intros A A' B B' HA HB; unfold no.
  rewrite (some_ext A A' B B' HA HB); reflexivity.
Qed.

Lemma at_least_ext : forall n, ExtD (at_least n).
Proof.
  intros n A A' B B' HA HB; unfold at_least.
  rewrite (card_ext _ _ (inter_ext A A' B B' HA HB)); reflexivity.
Qed.

Lemma more_than_half_ext : ExtD more_than_half.
Proof.
  intros A A' B B' HA HB; unfold more_than_half.
  rewrite (card_ext _ _ (inter_ext A A' B B' HA HB)), (card_ext _ _ HA).
  reflexivity.
Qed.

(* ========================================================================== *)
(*  T1.  The logical determiners live on their first argument.                *)
(*  B&C p. 170, the note after S5: membership of X in ||D||(A) depends on    *)
(*  X n A alone.  ("more than half" added by us; it is not in S5.)            *)
(* ========================================================================== *)

Lemma inter_absorb : forall A X, eqset (inter A X) (inter A (inter X A)).
Proof.
  intros A X x _; unfold inter; destruct (A x), (X x); reflexivity.
Qed.

Lemma some_lives_on : LivesOn some.
Proof.
  intros A X; apply eq_true_iff_eq; rewrite !some_spec; unfold inter.
  split; intros [x [Hx [H1 H2]]]; exists x; (split; [exact Hx|]);
    (split; [exact H1|]).
  - rewrite H1, H2; reflexivity.
  - apply andb_true_iff in H2; destruct H2; assumption.
Qed.

Theorem logical_determiners_live_on :
  LivesOn every /\ LivesOn some /\ LivesOn no /\
  (forall n, LivesOn (at_least n)) /\ (forall n, LivesOn (exactly n)) /\
  LivesOn more_than_half.
Proof.
  repeat split.
  - intros A X; apply eq_true_iff_eq; rewrite !every_spec; unfold sub, inter.
    split; intros H x Hx HA.
    + rewrite (H x Hx HA), HA; reflexivity.
    + specialize (H x Hx HA). apply andb_true_iff in H; destruct H; assumption.
  - exact some_lives_on.
  - intros A X; unfold no; rewrite (some_lives_on A X); reflexivity.
  - intros n A X; unfold at_least.
    rewrite (card_ext _ _ (inter_absorb A X)); reflexivity.
  - intros n A X; unfold exactly.
    rewrite (card_ext _ _ (inter_absorb A X)); reflexivity.
  - intros A X; unfold more_than_half.
    rewrite (card_ext _ _ (inter_absorb A X)); reflexivity.
Qed.

(* ========================================================================== *)
(*  T2.  Monotonicity profile.                                                *)
(*  Mon-up / mon-down: lists in section 4.7, p. 185.  Persistence: section    *)
(*  4.9, p. 193 (some, at least n persistent; every, no anti-persistent).     *)
(*  "more than half" mon-up is ours (the source lists "most men" as mon-up).  *)
(* ========================================================================== *)

Lemma every_mon_up : MonUp every.
Proof.
  intros A X Y HXY H; apply every_spec in H; apply every_spec.
  intros x Hx Ha; apply HXY; [exact Hx | apply H; assumption].
Qed.

Lemma every_anti_persistent : AntiPersistent every.
Proof.
  intros A B X HAB H; apply every_spec in H; apply every_spec.
  intros x Hx Ha; apply H; [exact Hx | apply HAB; assumption].
Qed.

Lemma some_mon_up : MonUp some.
Proof.
  intros A X Y HXY H; apply some_spec in H; apply some_spec.
  destruct H as [x [Hx [H1 H2]]]; exists x; repeat split; auto.
Qed.

Lemma some_persistent : Persistent some.
Proof.
  intros A B X HAB H; apply some_spec in H; apply some_spec.
  destruct H as [x [Hx [H1 H2]]]; exists x; repeat split; auto.
Qed.

Lemma no_mon_down : MonDown no.
Proof.
  intros A X Y HYX H; unfold no in *.
  destruct (some A Y) eqn:e; [|reflexivity].
  rewrite (some_mon_up A Y X HYX e) in H. simpl in H; discriminate.
Qed.

Lemma no_anti_persistent : AntiPersistent no.
Proof.
  intros A B X HAB H; unfold no in *.
  destruct (some A X) eqn:e; [|reflexivity].
  rewrite (some_persistent A B X HAB e) in H. simpl in H; discriminate.
Qed.

Theorem monotonicity_profile :
  (MonUp every /\ AntiPersistent every) /\
  (MonUp some /\ Persistent some) /\
  (MonDown no /\ AntiPersistent no) /\
  (forall n, MonUp (at_least n) /\ Persistent (at_least n)) /\
  MonUp more_than_half.
Proof.
  split; [exact (conj every_mon_up every_anti_persistent)|].
  split; [exact (conj some_mon_up some_persistent)|].
  split; [exact (conj no_mon_down no_anti_persistent)|].
  split.
  - intro n; split.
    + intros A X Y HXY H; unfold at_least in *.
      apply Nat.leb_le in H; apply Nat.leb_le.
      pose proof (card_mono _ _ (inter_sub A A X Y (sub_refl A) HXY)); lia.
    + intros A B X HAB H; unfold at_least in *.
      apply Nat.leb_le in H; apply Nat.leb_le.
      pose proof (card_mono _ _ (inter_sub A B X X HAB (sub_refl X))); lia.
  - intros A X Y HXY H; unfold more_than_half in *.
    apply Nat.ltb_lt in H; apply Nat.ltb_lt.
    pose proof (card_mono _ _ (inter_sub A A X Y (sub_refl A) HXY)); lia.
Qed.

(* ========================================================================== *)
(*  T3.  C1 (p. 209; stated in the text on p. 182): if Q lives on A then      *)
(*  A is in Q iff E is in Q.  Here X n A with X = E computes to A.            *)
(* ========================================================================== *)
Theorem C1_lives_on_top : forall (Q : quantifier) (A : eset),
  LivesOnQ Q A -> Q A = Q full.
Proof. intros Q A H. rewrite (H full). reflexivity. Qed.

(* ========================================================================== *)
(*  C4 (p. 210), auxiliary to T4: under the intersection condition,           *)
(*  B in D(A) iff E in D(A n B).                                              *)
(* ========================================================================== *)
Lemma C4_intersection_existential : forall D : determiner,
  ExtD D -> LivesOn D -> Intersection D ->
  forall A B, D A B = D (inter A B) full.
Proof.
  intros D HE HL HI A B.
  transitivity (D (inter A B) B); [apply HI|].
  transitivity (D (inter A B) (inter B (inter A B))); [apply HL|].
  transitivity (D (inter A B) (inter full (inter A B)));
    [|symmetry; apply (HL (inter A B) full)].
  apply HE; intros x _; unfold inter, full; destruct (A x), (B x); reflexivity.
Qed.

(* ========================================================================== *)
(*  T4.  C5 (pp. 210-211): for a determiner that lives on its argument, the   *)
(*  intersection condition is equivalent to symmetry.                         *)
(* ========================================================================== *)
Theorem C5_intersection_iff_symmetric : forall D : determiner,
  ExtD D -> LivesOn D -> (Intersection D <-> Symmetric D).
Proof.
  intros D HE HL; split.
  - intros HI A B.
    rewrite (C4_intersection_existential D HE HL HI A B),
            (C4_intersection_existential D HE HL HI B A).
    apply HE; intros x _; unfold inter, full; destruct (A x), (B x); reflexivity.
  - intros HS A B.
    transitivity (D B A); [apply HS|].
    transitivity (D B (inter A B)); [apply HL|].
    apply HS.
Qed.

(* ========================================================================== *)
(*  T5.  The claim inside the proof of C6 (p. 211): a determiner that lives   *)
(*  on its argument, satisfies the intersection condition and is positive     *)
(*  strong holds of every pair of sets; if negative strong, of none.          *)
(*  Our proof goes through C4 and C1 rather than through symmetry.            *)
(* ========================================================================== *)
Theorem C6_strong_intersective_trivial : forall D : determiner,
  ExtD D -> LivesOn D -> Intersection D ->
  (PosStrong D -> forall A B, D A B = true) /\
  (NegStrong D -> forall A B, D A B = false).
Proof.
  intros D HE HL HI.
  assert (K : forall A B, D A B = D (inter A B) (inter A B)).
  { intros A B. rewrite (C4_intersection_existential D HE HL HI A B).
    symmetry. apply C1_lives_on_top. apply HL. }
  split; intros HS A B; rewrite K; apply HS.
Qed.

(* ours, a note on C6.  For a TOTAL determiner that lives on its argument,
   strength already makes D(empty set) improper, so the hypothesis "proper
   strong determiner" of C6 (proper = defined for all A with D(A) proper,
   p. 210) has no instance in this total setting. *)
Lemma no_total_proper_strong : forall D : determiner,
  ExtD D -> LivesOn D -> PosStrong D \/ NegStrong D -> ~ ProperQ (D empty).
Proof.
  intros D HE HL HS [[X HX] [Y HY]].
  assert (K : forall Z, D empty Z = D empty empty).
  { intro Z. transitivity (D empty (inter Z empty)); [apply HL|].
    apply HE; intros x _; unfold inter, empty;
      [reflexivity | destruct (Z x); reflexivity]. }
  rewrite K in HX, HY. destruct HS as [HS|HS]; rewrite (HS empty) in *;
    discriminate.
Qed.

(* ========================================================================== *)
(*  T6.  C7 (p. 212): persistent and symmetric implies mon-up.                *)
(* ========================================================================== *)
Theorem C7_persistent_symmetric_mon_up : forall D : determiner,
  Persistent D -> Symmetric D -> MonUp D.
Proof.
  intros D HP HS A X Y HXY H.
  rewrite (HS A Y). apply (HP X Y A HXY). rewrite (HS X A). exact H.
Qed.

(* ========================================================================== *)
(*  T7.  C9 (p. 212; text p. 186): negation reverses monotonicity, the dual   *)
(*  of a mon-up quantifier is mon-up, and double negation cancels.            *)
(* ========================================================================== *)
Theorem C9_negation_reverses_monotonicity : forall Q : quantifier,
  (MonUpQ Q -> MonDownQ (neg Q) /\ MonDownQ (postneg Q)) /\
  (MonDownQ Q -> MonUpQ (neg Q) /\ MonUpQ (postneg Q)) /\
  (MonUpQ Q -> MonUpQ (dual Q)) /\
  (forall X, neg (neg Q) X = Q X) /\
  (ExtQ Q -> forall X, postneg (postneg Q) X = Q X).
Proof.
  intro Q.
  split; [intro HQ; split|].
  - intros X Y HYX H; unfold neg in *.
    destruct (Q Y) eqn:e; [|reflexivity].
    rewrite (HQ Y X HYX e) in H. simpl in H; discriminate.
  - intros X Y HYX H; unfold postneg in *.
    apply (HQ (compl X) (compl Y)); [apply compl_sub; exact HYX | exact H].
  - split; [intro HQ; split|].
    + intros X Y HXY H; unfold neg in *.
      destruct (Q Y) eqn:e; [|reflexivity].
      rewrite (HQ Y X HXY e) in H. simpl in H; discriminate.
    + intros X Y HXY H; unfold postneg in *.
      apply (HQ (compl X) (compl Y)); [apply compl_sub; exact HXY | exact H].
    + split; [|split].
      * intros HQ X Y HXY H; unfold dual in *.
        destruct (Q (compl Y)) eqn:e; [|reflexivity].
        rewrite (HQ (compl Y) (compl X) (compl_sub X Y HXY) e) in H.
        simpl in H; discriminate.
      * intro X; unfold neg; apply negb_involutive.
      * intros HE X; unfold postneg; apply HE.
        intros x _; unfold compl; apply negb_involutive.
Qed.

(* ========================================================================== *)
(*  T8.  C10 (p. 212; text p. 199): if Q is mon-up, A is in Q and B is in     *)
(*  the dual of Q, then A and B meet.  On a finite universe we get the        *)
(*  common element itself, not only a non-emptiness statement.                *)
(* ========================================================================== *)
Theorem C10_mon_up_meets_dual : forall Q : quantifier,
  MonUpQ Q -> forall A B, Q A = true -> dual Q B = true ->
  exists x, In x E /\ A x = true /\ B x = true.
Proof.
  intros Q HQ A B HA HB.
  destruct (some A B) eqn:e; [apply some_spec; exact e|].
  exfalso. assert (S : sub A (compl B)).
  { intros x Hx Ha. unfold compl. destruct (B x) eqn:eb; [|reflexivity].
    assert (some A B = true) by (apply some_spec; exists x; auto).
    congruence. }
  unfold dual in HB. rewrite (HQ A (compl B) S HA) in HB.
  simpl in HB; discriminate.
Qed.

(* ---- facts used by the examples ---- *)
Lemma some_symmetric : Symmetric some.
Proof.
  intros A B; apply eq_true_iff_eq; rewrite !some_spec.
  split; intros [x [Hx [H1 H2]]]; exists x; auto.
Qed.

Lemma every_pos_strong : PosStrong every.
Proof. intro A; apply every_spec; apply sub_refl. Qed.

(* p. 211: "some but not all" is persistent. *)
Lemma some_not_all_persistent : Persistent some_not_all.
Proof.
  intros A B X HAB H; unfold some_not_all in *.
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply andb_true_iff; split; [exact (some_persistent A B X HAB H1)|].
  destruct (every B X) eqn:e; [|reflexivity].
  rewrite (every_anti_persistent A B X HAB e) in H2. simpl in H2; discriminate.
Qed.

(* ours: what the counting determiners count.  If the universe is listed
   without repetition, card A is the number of members of A: any
   repetition-free list of exactly the members of A has that length.  The
   counting determiners (at_least, exactly, more_than_half, at_least_half)
   are the intended ones only under this premise; see the example
   repetition_inflates_counts below. *)
Theorem card_counts_members : NoDup E ->
  forall (A : eset) (l : list U), NoDup l ->
    (forall x, In x l <-> In x E /\ A x = true) -> length l = card A.
Proof.
  intros Hnd A l Hl Hin. unfold card, cardl. apply Permutation_length.
  apply NoDup_Permutation; [exact Hl | apply NoDup_filter; exact Hnd |].
  intros x. rewrite filter_In. apply Hin.
Qed.

End Universe.
End GQ.

(* ========================================================================== *)
(*  WORKED MODEL (ours).  E = {0,1,2,3,4}; man = {0,1,2}; run = {0,1,3}.      *)
(* ========================================================================== *)

Definition E5 : list nat := [0;1;2;3;4].
Definition mk (l : list nat) : nat -> bool := fun x => existsb (Nat.eqb x) l.
Definition man := mk [0;1;2].
Definition run := mk [0;1;3].

(* The model's universe is listed without repetition, so card_counts_members
   applies to it. *)
Example E5_nodup : NoDup E5.
Proof. repeat constructor; simpl; intros H; repeat destruct H as [H|H]; try discriminate H; exact H. Qed.

(* Separating example (ours): on a universe that lists one individual twice,
   "at least two" things are self-identical, although there is only one. *)
Example repetition_inflates_counts :
  at_least [0; 0] 2 (fun _ => true) (fun _ => true) = true /\ ~ NoDup [0; 0].
Proof.
  split; [reflexivity|]. intros H. inversion H as [|? ? Hn _]; subst.
  apply Hn. left. reflexivity.
Qed.

Fixpoint powerset (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | a :: l => map (cons a) (powerset l) ++ powerset l
  end.
(* all 32 subsets of E5 *)
Definition subs : list (nat -> bool) := map mk (powerset E5).
Definition all2 (f : (nat -> bool) -> (nat -> bool) -> bool) : bool :=
  forallb (fun A => forallb (f A) subs) subs.

(* Computed truth values: |man| = 3, |man n run| = 2. *)
Example model_values :
  every E5 man run = false /\ some E5 man run = true /\
  no E5 man run = false /\ at_least E5 2 man run = true /\
  at_least E5 3 man run = false /\ exactly E5 2 man run = true /\
  more_than_half E5 man run = true /\ only E5 man run = false.
Proof. vm_compute. repeat split. Qed.

(* Separating example 1 (ours): "only" does not live on its first argument.
   Only men run is false (3 runs), only men are men who run is true. *)
Example only_not_conservative : ~ LivesOn (only E5).
Proof.
  intro H. specialize (H man run). vm_compute in H. discriminate.
Qed.

(* Separating example 2 (p. 185, "exactly two men" not monotone). *)
Example exactly_two_not_monotone :
  ~ MonUp E5 (exactly E5 2) /\ ~ MonDown E5 (exactly E5 2).
Proof.
  split; intro H.
  - assert (K := H man run full (fun x _ _ => eq_refl) eq_refl).
    vm_compute in K. discriminate.
  - assert (S : sub E5 empty run) by (intros x _ Hx; unfold empty in Hx; discriminate Hx).
    assert (K := H man run empty S eq_refl).
    vm_compute in K. discriminate.
Qed.

(* Separating example 3 (p. 211): "some but not all" is persistent but
   neither mon-up nor symmetric.  So C7 needs its symmetry premise. *)
Example some_not_all_separates :
  Persistent E5 (some_not_all E5) /\
  ~ MonUp E5 (some_not_all E5) /\ ~ Symmetric (some_not_all E5).
Proof.
  split; [apply some_not_all_persistent|]. split; intro H.
  - assert (K := H man run full (fun x _ _ => eq_refl) eq_refl).
    vm_compute in K. discriminate.
  - specialize (H full man). vm_compute in H. discriminate.
Qed.

(* Separating example 4 (instance of C6, p. 211): "every" is positive strong
   and fails the intersection condition, hence (C5) is not symmetric. *)
Example every_not_intersective :
  PosStrong (every E5) /\ ~ Intersection (every E5) /\ ~ Symmetric (every E5).
Proof.
  split; [apply every_pos_strong|]. split; intro H.
  - specialize (H man run). vm_compute in H. discriminate.
  - specialize (H (mk [0]) man). vm_compute in H. discriminate.
Qed.

(* Non-vacuity of T4, T6: "some" meets every premise of C5 and C7, and the
   conclusions are obtained through those theorems. *)
Example some_meets_premises :
  ExtD E5 (some E5) /\ LivesOn (some E5) /\ Symmetric (some E5) /\
  Persistent E5 (some E5) /\ Intersection (some E5) /\ MonUp E5 (some E5).
Proof.
  assert (HE := some_ext E5). assert (HL := some_lives_on E5).
  assert (HS := some_symmetric E5). assert (HP := some_persistent E5).
  repeat split; try assumption.
  - apply (proj2 (C5_intersection_iff_symmetric E5 _ HE HL) HS).
  - apply (C7_persistent_symmetric_mon_up E5 _ HP HS).
Qed.

(* Non-vacuity of T5: the premises of C6 are jointly satisfiable (by the
   trivial determiner), and by T5 only trivially. *)
Example C6_premises_satisfiable :
  let D : @determiner nat := fun _ _ => true in
  ExtD E5 D /\ LivesOn D /\ Intersection D /\ PosStrong D.
Proof. repeat split. Qed.

(* Non-vacuity of T8: Q = more than half the men; run is in Q, {0,1} is in
   the dual of Q, and C10 yields a common element. *)
Example C10_instance :
  exists x, In x E5 /\ run x = true /\ mk [0;1] x = true.
Proof.
  apply (C10_mon_up_meets_dual E5 (more_than_half E5 man)).
  - apply monotonicity_profile.
  - reflexivity.
  - reflexivity.
Qed.

(* Duals, checked on all 32 x 32 pairs of subsets of E5.
   p. 197: the dual of "some man" is "every man";
   pp. 198-199: the dual of "more than half" is "at least half". *)
Example duals_on_model :
  all2 (fun A X => eqb (dual (some E5 A) X) (every E5 A X)) = true /\
  all2 (fun A X => eqb (dual (every E5 A) X) (some E5 A X)) = true /\
  all2 (fun A X => eqb (dual (more_than_half E5 A) X) (at_least_half E5 A X))
    = true.
Proof. vm_compute. repeat split. Qed.

(* p. 197: on a set of odd cardinality "more than half" is self-dual
   (man has 3 elements); on one of even cardinality it is not (ours). *)
Example self_dual_odd :
  forallb (fun X => eqb (dual (more_than_half E5 man) X)
                        (more_than_half E5 man X)) subs = true /\
  dual (more_than_half E5 (mk [0;1])) (mk [0]) = true /\
  more_than_half E5 (mk [0;1]) (mk [0]) = false.
Proof. vm_compute. repeat split. Qed.

(* "more than half" against the postulates for "most" (Appendix B, p. 208).
   SP3 (two sets in most(A) meet) holds on the model for all A, X, Y.
   SP1 (A in most(A) for every A) fails at the empty set: ours, and the
   reason "more than half" is not offered here as the source's "most". *)
Example mth_SP3_on_model :
  forallb (fun A => all2 (fun X Y =>
    implb (more_than_half E5 A X && more_than_half E5 A Y) (some E5 X Y)))
    subs = true.
Proof. vm_compute. reflexivity. Qed.

Example mth_fails_SP1_at_empty :
  ~ PosStrong (more_than_half E5) /\
  forallb (fun A => implb (some E5 A A) (more_than_half E5 A A)) subs = true.
Proof.
  split; [|vm_compute; reflexivity].
  intro H. specialize (H empty). vm_compute in H. discriminate.
Qed.

Print Assumptions card_counts_members.
Print Assumptions E5_nodup.
Print Assumptions repetition_inflates_counts.
Print Assumptions logical_determiners_live_on.
Print Assumptions monotonicity_profile.
Print Assumptions C1_lives_on_top.
Print Assumptions C4_intersection_existential.
Print Assumptions C5_intersection_iff_symmetric.
Print Assumptions C6_strong_intersective_trivial.
Print Assumptions no_total_proper_strong.
Print Assumptions C7_persistent_symmetric_mon_up.
Print Assumptions C9_negation_reverses_monotonicity.
Print Assumptions C10_mon_up_meets_dual.
Print Assumptions model_values.
Print Assumptions only_not_conservative.
Print Assumptions exactly_two_not_monotone.
Print Assumptions some_not_all_separates.
Print Assumptions every_not_intersective.
Print Assumptions some_meets_premises.
Print Assumptions C6_premises_satisfiable.
Print Assumptions C10_instance.
Print Assumptions duals_on_model.
Print Assumptions self_dual_odd.
Print Assumptions mth_SP3_on_model.
Print Assumptions mth_fails_SP1_at_empty.
