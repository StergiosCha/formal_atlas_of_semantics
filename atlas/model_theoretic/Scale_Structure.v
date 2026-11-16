From Coq Require Import QArith Lqa Bool.
Open Scope Q_scope.

(* ========================================================================== *)
(*  Scale_Structure.v — scale structure and the standards of gradable          *)
(*  adjectives                                                                 *)
(*  FORMAL-ATLAS / atlas/model_theoretic (standard library only)              *)
(* ========================================================================== *)
(*
   SOURCE
     Kennedy, C. & McNally, L. (2005). Scale structure, degree modification,
       and the semantics of gradable predicates. Language 81(2): 345-381.
       [read: (21) p. 353 (half); (23) p. 354 (the typology of scales);
       (34) p. 358 (minimum- and maximum-standard truth conditions);
       (39)-(40) p. 359 and (41)-(44) p. 360 (the entailment tests)]
     Not read for this file: the sections on degree modifiers (very, much,
     well), on deverbal adjectives and event structure, and section 6.

   WHAT IS FORMALIZED
     K1  endpoints            a scale of (23) has a minimal (maximal) degree
                              exactly when it is lower (upper) closed
     K2  absolute_antonyms    (39): on a closed scale, with a minimum
                              standard for the positive adjective and a
                              maximum standard for its antonym, "not open"
                              is "closed" and "not closed" is "open"
     K3  half_tests           (41), (42): "half A" entails "not A" for a
                              maximum standard and "A" for a minimum one
     K4  comparative_tests    (43): "x is more A than y" entails "x is A"
                              for a minimum standard, and "y is not A" for
                              a maximum standard
     K5  half_is_midpoint     (21): the degree picked out by "half"
     and three separating examples for relative adjectives: (40) the zone
     of indifference, and (44) the comparative entails neither the positive
     nor its negation.

   NOT FORMALIZED (and why)
     * The degree morpheme pos and the standard relation (13), (35): the
       three standards are given directly, as in (34) and section 2.
     * Degree modifiers, deverbal adjectives, and the generalization of
       section 4.3 that open scales go with relative standards, which is
       an empirical claim about adjectives, not a theorem.

   REPRESENTATION CHOICES
     Degrees are rational numbers and the four scales of (23) are the four
     intervals between 0 and 1.  An adjective is its measure function.  The
     antonym of an adjective measures 1 - d: p. 359 says that a minimal
     positive degree corresponds to a maximal negative degree on the same
     scale.  "Half" is the degree equidistant from the two endpoints (21).
*)

(* (23) p. 354. *)
Inductive scale := TotallyOpen | LowerClosed | UpperClosed | TotallyClosed.

Definition in_scale (s : scale) (d : Q) : Prop :=
  match s with
  | TotallyOpen => 0 < d /\ d < 1
  | LowerClosed => 0 <= d /\ d < 1
  | UpperClosed => 0 < d /\ d <= 1
  | TotallyClosed => 0 <= d /\ d <= 1
  end.

Definition lower_closed (s : scale) : bool :=
  match s with LowerClosed | TotallyClosed => true | _ => false end.
Definition upper_closed (s : scale) : bool :=
  match s with UpperClosed | TotallyClosed => true | _ => false end.

(* K1.  (23): only the closed ends have endpoints. *)
Theorem endpoints : forall s,
  ((exists d, in_scale s d /\ forall e, in_scale s e -> d <= e) <-> lower_closed s = true) /\
  ((exists d, in_scale s d /\ forall e, in_scale s e -> e <= d) <-> upper_closed s = true).
Proof.
  intros s. split; split.
  - intros (d & Hd & Hmin). destruct s; simpl in *; try reflexivity; exfalso.
    + assert (H : d <= d * (1 # 2)) by (apply Hmin; lra). lra.
    + assert (H : d <= d * (1 # 2)) by (apply Hmin; lra). lra.
  - intros H. exists 0. destruct s; simpl in *; try discriminate H;
      (split; [lra | intros e He; lra]).
  - intros (d & Hd & Hmax). destruct s; simpl in *; try reflexivity; exfalso.
    + assert (H : (d + 1) * (1 # 2) <= d) by (apply Hmax; lra). lra.
    + assert (H : (d + 1) * (1 # 2) <= d) by (apply Hmax; lra). lra.
  - intros H. exists 1. destruct s; simpl in *; try discriminate H;
      (split; [lra | intros e He; lra]).
Qed.

Section Adjectives.
Variable X : Type.

(* (34a) p. 358: a nonminimal degree; the minimum of the scale is 0. *)
Definition AP_min (m : X -> Q) (x : X) : Prop := 0 < m x.
(* (34b) p. 358: the maximal degree; the maximum of the scale is 1. *)
Definition AP_max (m : X -> Q) (x : X) : Prop := m x == 1.
(* Section 2: a relative adjective exceeds a contextual standard. *)
Definition AP_rel (std : Q) (m : X -> Q) (x : X) : Prop := std < m x.
(* p. 360: the comparative imposes an asymmetric ordering. *)
Definition more (m : X -> Q) (x y : X) : Prop := m y < m x.
(* p. 359: the antonym on the same scale. *)
Definition antonym (m : X -> Q) : X -> Q := fun x => 1 - m x.
(* (21) p. 353: equidistant from the two endpoints. *)
Definition half (m : X -> Q) (x : X) : Prop := 1 - m x == m x - 0.

(* K2.  (39) p. 359: "The door is not open |= The door is closed", and the
   same with the adjectives exchanged. *)
Theorem absolute_antonyms : forall (m : X -> Q) (x : X),
  in_scale TotallyClosed (m x) ->
  (~ AP_min m x <-> AP_max (antonym m) x) /\
  (~ AP_max (antonym m) x <-> AP_min m x).
Proof.
  intros m x [H0 H1]. unfold AP_min, AP_max, antonym. repeat split; intros H.
  - assert (m x <= 0) by (apply Qnot_lt_le; exact H). lra.
  - intros K. lra.
  - apply Qnot_le_lt. intros K. apply H. lra.
  - intros K. lra.
Qed.

(* K3.  (41) p. 360: "half dead |= not dead"; (42): "half open |= open". *)
Theorem half_tests : forall (m : X -> Q) (x : X), half m x ->
  ~ AP_max m x /\ AP_min m x.
Proof. intros m x H. unfold half, AP_max, AP_min in *. split; [intros K|]; lra. Qed.

(* K4.  (43a) p. 360: "wetter than the countertop |= wet", for a minimum
   standard; (43b): "drier than the countertop |= the countertop is not
   dry", for a maximum standard. *)
Theorem comparative_tests : forall (m : X -> Q) (x y : X), more m x y ->
  (0 <= m y -> AP_min m x) /\ (m x <= 1 -> ~ AP_max m y).
Proof.
  intros m x y H. unfold more, AP_min, AP_max in *. split; intros K; [|intros E]; lra.
Qed.

(* K5.  (21) p. 353: the degree of "half" is the midpoint. *)
Theorem half_is_midpoint : forall (m : X -> Q) (x : X), half m x <-> m x == 1 # 2.
Proof. intros m x. unfold half. split; intros H; lra. Qed.

End Adjectives.

(* ========================================================================== *)
(*  Worked model and separating examples                                       *)
(* ========================================================================== *)

Module Doors.

(* Three doors; the measure is the degree of openness. *)
Inductive door := shut | ajar | wide.
Definition openness (d : door) : Q :=
  match d with shut => 0 | ajar => 1 # 2 | wide => 1 end.

(* "open" has a minimum standard and "closed", its antonym, a maximum one.
   The door that is half open is open and is not closed; the shut door is
   closed and is not open. *)
Example the_doors :
  half door openness ajar /\ AP_min door openness ajar /\
  ~ AP_max door (antonym door openness) ajar /\
  AP_max door (antonym door openness) shut /\ ~ AP_min door openness shut.
Proof.
  unfold half, AP_min, AP_max, antonym; simpl.
  repeat split; try (intros K); lra.
Qed.

(* Separating example 1.  (40) p. 359: "not large" does not entail "small".
   With a standard of 2/3 for "large" and 2/3 for its antonym, the door of
   size 1/2 is neither. *)
Example zone_of_indifference :
  ~ AP_rel door (2 # 3) openness ajar /\
  ~ AP_rel door (2 # 3) (antonym door openness) ajar.
Proof. unfold AP_rel, antonym; simpl. split; intros K; lra. Qed.

(* Separating examples 2 and 3.  (44) p. 360: with a relative standard, the
   comparative entails neither the positive form nor its negation. *)
Example comparative_without_positive :
  more door openness ajar shut /\ ~ AP_rel door (2 # 3) openness ajar.
Proof. unfold more, AP_rel; simpl. split; [|intros K]; lra. Qed.

Example comparative_with_positive :
  more door openness wide ajar /\ AP_rel door (1 # 3) openness ajar.
Proof. unfold more, AP_rel; simpl. split; lra. Qed.

End Doors.

Print Assumptions endpoints.
Print Assumptions absolute_antonyms.
Print Assumptions half_tests.
Print Assumptions comparative_tests.
Print Assumptions half_is_midpoint.
Print Assumptions Doors.the_doors.
Print Assumptions Doors.zone_of_indifference.
Print Assumptions Doors.comparative_without_positive.
Print Assumptions Doors.comparative_with_positive.
