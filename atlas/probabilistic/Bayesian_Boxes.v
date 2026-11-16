(* ========================================================================== *)
(*  Bayesian_Boxes.v — predicates as boxes, with exact rational bounds        *)
(*  FORMAL-ATLAS / atlas/probabilistic                                        *)
(* ========================================================================== *)
(*
   SOURCES
     [BBCLM19] Bernardy, J.-P., Blanck, R., Chatzikyriakidis, S., Lappin, S.
       & Maskharashvili, A. (2019). Predicates as Boxes in Bayesian
       Semantics for Natural Language. NoDaLiDa 2019, pp. 333-337 (ACL
       Anthology W19-6137).  [sec. 2 p. 333: a predicate is a box; sec. 2.1
       p. 334: intersection; sec. 2.2 p. 334: "every" as inclusion; sec. 2.3
       p. 334: "most" by volumes; sec. 2.4 pp. 334-335: degrees and
       comparatives; sec. 2.5 p. 335: no closure under union; sec. 3
       p. 336: inclusion is exact]
     [BIS19] The same authors (2019). Bayesian Inference Semantics: A
       Modelling System and A Test Suite. *SEM 2019, pp. 263-272
       (S19-1029).  [only the test inferences T15, T31, T76, T77]
   Builds on RSA.v and Bayesian_Semantics.v, which this file leaves unchanged.

   WHAT IS FORMALIZED
       X1  the meet of two boxes is their intersection
       X2  for a non-empty box, "every P is Q" is inclusion: the bounds of Q
           enclose those of P
       X3  "every" is transitive (test T76)
       X4  a contained predicate has no larger volume
       X5  "every" implies "most", for any threshold up to 1
       X6  membership is positive degree; the centre has degree 1 (test T15)
       X7  "taller than k" is a box
       X8  a union of two boxes that is no box
     Learning on a finite grid of candidate boxes with rational weights:
       G1  certainty under the premises     G2  a lower bound
       G3  T76 learned: after "every V is M" and "every M is R", an
           individual of V is in R with probability exactly 1
       G4  after "most P are Q" with threshold theta, an individual of P is
           in Q with probability at least theta
     and worked examples: T76, T77, T31, T15, and a grid of ten intervals.

   NOT FORMALIZED (and why)
     * The paper's priors for box bounds (uniform centres, a beta
       distribution on inverse widths) and sampling: the grid stands in for
       them, with exact weights.
     * The unit box: boxes are taken to lie inside it, where volume is
       probability.
     * Negation.

   REPRESENTATION CHOICES
     A box is a list of (lower, upper) bounds; the paper notes that this is
     interchangeable with centre and half-width.  A negative width counts as
     0, so an empty box has volume 0.
*)

From Coq Require Import List Bool QArith Qminmax Qabs Arith Lqa.
Import ListNotations.
Require Import RSA.
Import QSum.
Require Import Bayesian_Semantics.
Open Scope Q_scope.

Definition box : Type := list (Q * Q).
Definition point : Type := list Q.

(* x is in the box: strictly between the bounds in each dimension. *)
Definition inb (x : point) (P : box) : Prop :=
  Forall2 (fun xi b => fst b < xi /\ xi < snd b) x P.

Definition nonempty (P : box) : Prop := Forall (fun b => fst b < snd b) P.

(* Sec. 2.1: larger lower bound, smaller upper bound. *)
Definition meet (P Q : box) : box :=
  map (fun pq => (Qmax (fst (fst pq)) (fst (snd pq)),
                  Qmin (snd (fst pq)) (snd (snd pq)))) (combine P Q).

(* "Every P is Q": the bounds of Q enclose those of P. *)
Definition every (P Q : box) : Prop :=
  Forall2 (fun p q => fst q <= fst p /\ snd p <= snd q) P Q.

(* Volume: the product of the widths. *)
Definition vol (P : box) : Q :=
  fold_right (fun b acc => Qmax 0 (snd b - fst b) * acc) 1 P.

(* Sec. 2.3. *)
Definition most (theta : Q) (P Q : box) : Prop :=
  theta * vol P <= vol (meet P Q).

(* Sec. 2.4: 1 minus the largest scaled distance from the centre. *)
Definition deg (P : box) (x : point) : Q :=
  1 - fold_right Qmax 0
        (map (fun xb => Qabs (fst xb - (fst (snd xb) + snd (snd xb)) / 2) /
                        ((snd (snd xb) - fst (snd xb)) / 2))
             (combine x P)).

Definition centre (P : box) : point := map (fun b => (fst b + snd b) / 2) P.

(* The box with the same centre and half-widths scaled by r. *)
Definition scale (P : box) (r : Q) : box :=
  map (fun b => ((fst b + snd b) / 2 - r * ((snd b - fst b) / 2),
                 (fst b + snd b) / 2 + r * ((snd b - fst b) / 2))) P.

(* ------------------------------------------------------------------ *)
(* Statements                                                          *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Worked examples                                                     *)
(* ------------------------------------------------------------------ *)

Ltac qc := vm_compute; first [reflexivity | discriminate].
Ltac f2 := repeat (first [apply Forall2_cons | apply Forall2_nil | split]); qc.

(* Two dimensions.  The boxes lie in the unit box. *)
Definition violinist : box := [(1 # 4, 1 # 2); (1 # 4, 1 # 2)].
Definition musician  : box := [(1 # 8, 3 # 4); (1 # 8, 3 # 4)].
Definition reads     : box := [(0, 1); (0, 7 # 8)].
Definition john : point := [3 # 8; 3 # 8].

(* T76.  All violinists are musicians; all musicians read music; so all
   violinists read music. *)
Example E_T76 :
  every violinist musician /\ every musician reads /\ every violinist reads.
Proof. repeat split; f2. Qed.

(* The probabilities of the three predicates. *)
Example E_volumes :
  vol violinist == 1 # 16 /\ vol musician == 25 # 64 /\ vol reads == 7 # 8.
Proof. repeat split; qc. Qed.

(* T77.  ... so 99 percent of violinists read music. *)
Example E_T77 : most (99 # 100) violinist reads.
Proof. unfold most. qc. Qed.

(* T31, instantiation.  John is a violinist; so John is a musician. *)
Example E_T31 : inb john violinist /\ inb john musician.
Proof. split; f2. Qed.

(* T15.  One dimension.  Mary is tall; John is taller than Mary; and John
   is tall. *)
Definition tall : box := [(0, 1)].
Definition mary : point := [1 # 4].
Definition john_height : point := [1 # 2].
Example E_T15 :
  deg tall mary == 1 # 2 /\ deg tall john_height == 1 /\
  0 < deg tall mary /\ deg tall mary < deg tall john_height.
Proof. repeat split; qc. Qed.

(* ------------------------------------------------------------------ *)
(* Supporting results                                                  *)
(* ------------------------------------------------------------------ *)

Lemma meet_cons (p q : Q * Q) (P Q : box) :
  meet (p :: P) (q :: Q) =
  (Qmax (fst p) (fst q), Qmin (snd p) (snd q)) :: meet P Q.
Proof. reflexivity. Qed.

Lemma vol_cons (p : Q * Q) (P : box) :
  vol (p :: P) = Qmax 0 (snd p - fst p) * vol P.
Proof. reflexivity. Qed.

Lemma vol_nonneg (P : box) : 0 <= vol P.
Proof.
  induction P as [|p P IH]; [discriminate|].
  rewrite vol_cons. apply Qmult_le_0_compat; [apply Q.le_max_l | exact IH].
Qed.

Lemma mul_le (a b c d : Q) :
  0 <= a -> a <= b -> 0 <= c -> c <= d -> a * c <= b * d.
Proof.
  intros Ha Hab Hc Hcd. apply Qle_trans with (b * c).
  - apply Qmult_le_compat_r; assumption.
  - rewrite (Qmult_comm b c), (Qmult_comm b d).
    apply Qmult_le_compat_r; [assumption | apply Qle_trans with a; assumption].
Qed.

Lemma half_between (a b : Q) : a < b -> a < (a + b) / 2 /\ (a + b) / 2 < b.
Proof.
  intros H. split.
  - apply Qlt_shift_div_l; [lra | lra].
  - apply Qlt_shift_div_r; [lra | lra].
Qed.

Lemma centre_in (P : box) : nonempty P -> inb (centre P) P.
Proof.
  induction 1 as [|b P Hb _ IH]; [constructor|].
  constructor; [exact (half_between _ _ Hb) | exact IH].
Qed.

Lemma every_sound (P Q : box) :
  every P Q -> forall x, inb x P -> inb x Q.
Proof.
  induction 1 as [|p q P Q [A B] _ IH]; intros x Hx.
  - exact Hx.
  - inversion Hx as [|xi ? x' ? [L U] Ht]; subst.
    constructor; [split; lra | apply IH; exact Ht].
Qed.

Lemma meet_every (P Q : box) : every P Q -> vol (meet P Q) == vol P.
Proof.
  induction 1 as [|p q P Q [A B] _ IH]; [reflexivity|].
  rewrite meet_cons, !vol_cons, IH. cbn [fst snd].
  rewrite (Q.max_l _ _ A), (Q.min_l _ _ B). reflexivity.
Qed.

(* The largest scaled distance from the centre. *)
Definition Mfun (P : box) (x : point) : Q :=
  fold_right Qmax 0
    (map (fun xb => Qabs (fst xb - (fst (snd xb) + snd (snd xb)) / 2) /
                    ((snd (snd xb) - fst (snd xb)) / 2))
         (combine x P)).

Lemma deg_eq (P : box) (x : point) : deg P x = 1 - Mfun P x.
Proof. reflexivity. Qed.

Lemma Mfun_cons (b : Q * Q) (P : box) (xi : Q) (x : point) :
  Mfun (b :: P) (xi :: x) =
  Qmax (Qabs (xi - (fst b + snd b) / 2) / ((snd b - fst b) / 2)) (Mfun P x).
Proof. reflexivity. Qed.

Lemma absdiv_lt (a d r : Q) : 0 < d -> (Qabs a / d < r <-> Qabs a < r * d).
Proof.
  intros Hd. split; intros H.
  - assert (E : Qabs a == Qabs a / d * d)
      by (field; intros Z; rewrite Z in Hd; exact (Qlt_irrefl 0 Hd)).
    rewrite E. apply Qmult_lt_compat_r; assumption.
  - apply Qlt_shift_div_r; assumption.
Qed.

Lemma half_width_pos (b : Q * Q) : fst b < snd b -> 0 < (snd b - fst b) / 2.
Proof. intros H. apply Qlt_shift_div_l; [lra | lra]. Qed.

(* The key fact for degrees: the scaled distance is below r exactly inside
   the box scaled by r. *)
Lemma M_lt (r : Q) : 0 < r -> forall (P : box) (x : point),
  nonempty P -> length x = length P ->
  (Mfun P x < r <-> inb x (scale P r)).
Proof.
  intros Hr P. induction P as [|b P IH]; intros x Hne Hlen.
  - destruct x; [|discriminate Hlen]. split; [constructor | intros _; exact Hr].
  - destruct x as [|xi x]; [discriminate Hlen|].
    inversion Hne as [|? ? Hb Hne']; subst.
    injection Hlen as Hlen.
    pose proof (half_width_pos b Hb) as Hd.
    rewrite Mfun_cons, Q.max_lub_lt_iff, (absdiv_lt _ _ r Hd),
      Qabs_Qlt_condition, (IH x Hne' Hlen).
    change (scale (b :: P) r)
      with (((fst b + snd b) / 2 - r * ((snd b - fst b) / 2),
             (fst b + snd b) / 2 + r * ((snd b - fst b) / 2)) :: scale P r).
    split.
    + intros [[L U] Ht]. constructor; [cbn [fst snd]; split; lra | exact Ht].
    + intros H. inversion H as [|? ? ? ? [L U] Ht]; subst.
      cbn [fst snd] in L, U. split; [split; lra | exact Ht].
Qed.

Lemma inb_scale_one (P : box) (x : point) : inb x (scale P 1) <-> inb x P.
Proof.
  revert x. induction P as [|b P IH]; intros x; [tauto|].
  change (scale (b :: P) 1)
    with (((fst b + snd b) / 2 - 1 * ((snd b - fst b) / 2),
           (fst b + snd b) / 2 + 1 * ((snd b - fst b) / 2)) :: scale P 1).
  assert (El : (fst b + snd b) / 2 - 1 * ((snd b - fst b) / 2) == fst b)
    by field.
  assert (Eu : (fst b + snd b) / 2 + 1 * ((snd b - fst b) / 2) == snd b)
    by field.
  split; intros H; inversion H as [|xi ? x' ? [L U] Ht]; subst;
    cbn [fst snd] in L, U; constructor.
  - cbn [fst snd]. split; lra.
  - apply IH. exact Ht.
  - cbn [fst snd]. split; lra.
  - apply IH. exact Ht.
Qed.

Lemma M_centre (P : box) : Mfun P (centre P) == 0.
Proof.
  induction P as [|b P IH]; [reflexivity|].
  change (centre (b :: P)) with ((fst b + snd b) / 2 :: centre P).
  rewrite Mfun_cons, IH.
  assert (E : (fst b + snd b) / 2 - (fst b + snd b) / 2 == 0) by ring.
  rewrite E. change (Qabs 0) with 0.
  assert (Z : 0 / ((snd b - fst b) / 2) == 0)
    by (unfold Qdiv; apply Qmult_0_l).
  rewrite Z. apply Q.max_id.
Qed.

(* ------------------------------------------------------------------ *)
(* The statements                                                      *)
(* ------------------------------------------------------------------ *)

(* X1_meet_is_intersection (2.1).  The meet of two boxes is their intersection. *)
Theorem X1_meet_is_intersection :
  forall (P Q : box) (x : point), length P = length Q ->
    (inb x (meet P Q) <-> inb x P /\ inb x Q).
Proof.
  intros P. induction P as [|p P IH]; intros Q x Hlen.
  - destruct Q; [|discriminate Hlen]. simpl. tauto.
  - destruct Q as [|q Q]; [discriminate Hlen|]. injection Hlen as Hlen.
    rewrite meet_cons. split.
    + intros H. inversion H as [|xi ? x' ? [L U] Ht]; subst.
      cbn [fst snd] in L, U.
      apply Q.max_lub_lt_iff in L. apply Q.min_glb_lt_iff in U.
      apply (IH Q x' Hlen) in Ht. destruct Ht as [T1 T2].
      split; constructor; tauto.
    + intros [H1 H2].
      inversion H1 as [|xi ? x' ? [L1 U1] T1]; subst.
      inversion H2 as [|? ? ? ? [L2 U2] T2]; subst.
      constructor.
      * cbn [fst snd]. split;
          [apply Q.max_lub_lt_iff | apply Q.min_glb_lt_iff]; tauto.
      * apply (IH Q x' Hlen). tauto.
Qed.

(* X2_every_is_inclusion (2.2).  For a non-empty box, the test on bounds is inclusion. *)
Theorem X2_every_is_inclusion :
  forall P Q : box, nonempty P ->
    ((forall x, inb x P -> inb x Q) <-> every P Q).
Proof.
  intros P. induction P as [|p P IH]; intros Q Hne; split.
  - intros H. assert (E : inb [] Q) by (apply H; constructor).
    inversion E. constructor.
  - apply every_sound.
  - intros H. inversion Hne as [|? ? Hp Hne']; subst.
    pose proof (half_between _ _ Hp) as [Ml Mu].
    assert (Ec : inb (centre (p :: P)) Q)
      by (apply H; apply centre_in; exact Hne).
    change (centre (p :: P)) with ((fst p + snd p) / 2 :: centre P) in Ec.
    inversion Ec as [|? q ? Q' [Cl Cu] _]; subst.
    constructor.
    + split.
      * apply Qnot_lt_le. intros Hlt.
        assert (Hin : inb ((fst p + fst q) / 2 :: centre P) (p :: P)).
        { constructor; [|apply centre_in; exact Hne'].
          pose proof (half_between _ _ Hlt) as [A B]. split; lra. }
        apply H in Hin. inversion Hin as [|? ? ? ? [A _] _]; subst.
        pose proof (half_between _ _ Hlt) as [_ B]. lra.
      * apply Qnot_lt_le. intros Hlt.
        assert (Hin : inb ((snd q + snd p) / 2 :: centre P) (p :: P)).
        { constructor; [|apply centre_in; exact Hne'].
          pose proof (half_between _ _ Hlt) as [A B]. split; lra. }
        apply H in Hin. inversion Hin as [|? ? ? ? [_ A] _]; subst.
        pose proof (half_between _ _ Hlt) as [B _]. lra.
    + apply (IH Q' Hne'). intros x' Hx'.
      assert (Hin : inb ((fst p + snd p) / 2 :: x') (p :: P))
        by (constructor; [split; assumption | exact Hx']).
      apply H in Hin. inversion Hin; subst. assumption.
  - apply every_sound.
Qed.

(* X3_every_transitive (3).  "Every" is transitive.  Test suite T76. *)
Theorem X3_every_transitive :
  forall P Q R : box, every P Q -> every Q R -> every P R.
Proof.
  intros P Q R H. revert R.
  induction H as [|p q P Q [A B] _ IH]; intros R H2.
  - exact H2.
  - inversion H2 as [|? r ? R' [C D] H3]; subst.
    constructor; [split; lra | apply IH; exact H3].
Qed.

(* X4_inclusion_lowers_volume (3).  A contained predicate has no larger volume. *)
Theorem X4_inclusion_lowers_volume :
  forall P Q : box, every P Q -> vol P <= vol Q.
Proof.
  intros P Q H. induction H as [|p q P Q [A B] _ IH]; [apply Qle_refl|].
  rewrite !vol_cons. apply mul_le.
  - apply Q.le_max_l.
  - apply Q.max_le_compat_l. lra.
  - apply vol_nonneg.
  - exact IH.
Qed.

(* X5_every_implies_most (2.3).  "Every" implies "most", for any threshold up to 1. *)
Theorem X5_every_implies_most :
  forall (theta : Q) (P Q : box), theta <= 1 -> every P Q -> most theta P Q.
Proof.
  intros theta P Q Ht H. unfold most. rewrite (meet_every P Q H).
  setoid_replace (vol P) with (1 * vol P) at 2 by ring.
  apply Qmult_le_compat_r; [exact Ht | apply vol_nonneg].
Qed.

(* X6_degree (2.4).  Membership is positive degree, and the centre has degree 1.
   With it, test suite T15 holds in every box model: if Mary is tall and
   John is taller than Mary, then John is tall. *)
Theorem X6_degree :
  forall (P : box), nonempty P ->
    (forall x : point, length x = length P -> (inb x P <-> 0 < deg P x)) /\
    deg P (centre P) == 1.
Proof.
  intros P Hne. split.
  - intros x Hlen. rewrite deg_eq, <- (inb_scale_one P x).
    rewrite <- (M_lt 1 (eq_refl : 0 < 1) P x Hne Hlen). split; lra.
  - rewrite deg_eq, M_centre. reflexivity.
Qed.

(* X7_comparative_is_box (2.4).  "Taller than k" is a box: the same centre, with half-widths
   scaled by 1 minus the degree of k. *)
Theorem X7_comparative_is_box :
  forall (T : box) (k x : point), nonempty T -> length x = length T ->
    deg T k < 1 ->
    (deg T k < deg T x <-> inb x (scale T (1 - deg T k))).
Proof.
  intros T k x Hne Hlen Hk.
  assert (Hr : 0 < 1 - deg T k) by lra.
  rewrite <- (M_lt (1 - deg T k) Hr T x Hne Hlen), (deg_eq T x).
  split; lra.
Qed.

(* X8_union_is_not_a_box (2.5).  Separation: a union of two boxes that is no box. *)
Theorem X8_union_is_not_a_box :
  exists P Q : box,
    ~ exists B : box, forall x : point, inb x B <-> inb x P \/ inb x Q.
Proof.
  exists [(0, 1)], [(2, 3)]. intros [B HB].
  assert (H1 : inb [1 # 2] B).
  { apply HB. left. constructor; [cbn [fst snd]; split; lra | constructor]. }
  assert (H2 : inb [5 # 2] B).
  { apply HB. right. constructor; [cbn [fst snd]; split; lra | constructor]. }
  inversion H1 as [|? b ? B' [L1 U1] T1]; subst. inversion T1; subst.
  inversion H2 as [|? ? ? ? [L2 U2] _]; subst.
  assert (H3 : inb [3 # 2] [b]) by (constructor; [split; lra | constructor]).
  apply HB in H3.
  destruct H3 as [H3|H3]; inversion H3 as [|? ? ? ? [A1 A2] _]; subst;
    cbn [fst snd] in A1, A2; lra.
Qed.

(* The expected value of f among the configurations satisfying H. *)
Definition cexp {W : Type} (prior : W -> Q) (ws : list W) (f : W -> Q)
  (H : W -> bool) : Q :=
  qsum (map (fun w => if H w then prior w * f w else 0) ws) / mass prior ws H.

(* Decidable forms of "every" and "most", so that they can be observed. *)
Definition everyb (P Q : box) : bool :=
  Nat.eqb (length P) (length Q) &&
  forallb (fun pq => Qle_bool (fst (snd pq)) (fst (fst pq)) &&
                     Qle_bool (snd (fst pq)) (snd (snd pq))) (combine P Q).
Definition mostb (theta : Q) (P Q : box) : bool :=
  Qle_bool (theta * vol P) (vol (meet P Q)).

(* The probability that an individual of P is in Q. *)
Definition pr (A B : box) : Q := vol (meet A B) / vol A.

(* ------------------------------------------------------------------ *)
(* Statements                                                          *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Proofs                                                              *)
(* ------------------------------------------------------------------ *)

Lemma everyb_spec (P Q : box) : everyb P Q = true <-> every P Q.
Proof.
  revert Q. induction P as [|p P IH]; intros [|q Q].
  - split; [constructor | reflexivity].
  - split; [discriminate | intros H; inversion H].
  - split; [discriminate | intros H; inversion H].
  - specialize (IH Q). unfold everyb in IH |- *.
    cbn [length combine forallb fst snd Nat.eqb].
    rewrite andb_true_iff in IH.
    rewrite !andb_true_iff, !Qle_bool_iff. split.
    + intros (E & (A & B) & Fa).
      constructor; [split; assumption | apply IH; split; assumption].
    + intros H. inversion H as [|? ? ? ? [A B] H']; subst.
      apply IH in H'. destruct H' as [E Fa]. repeat split; assumption.
Qed.

Lemma vol_pos (P : box) : nonempty P -> 0 < vol P.
Proof.
  induction 1 as [|b P Hb _ IH]; [reflexivity|].
  rewrite vol_cons. apply Qmult_lt_0_compat; [|exact IH].
  apply Q.max_lt_iff. right. lra.
Qed.

(* G1_certain.  If the quantity is 1 wherever the premises hold, its posterior
   expectation is 1. *)
Theorem G1_certain :
  forall (W : Type) (prior : W -> Q) (ws : list W) (f : W -> Q) (H : W -> bool),
    nonneg prior ws -> 0 < mass prior ws H ->
    (forall w, In w ws -> H w = true -> f w == 1) ->
    cexp prior ws f H == 1.
Proof.
  intros W prior ws f H Hn Hpos Hf. unfold cexp.
  assert (E : qsum (map (fun w => if H w then prior w * f w else 0) ws) ==
              mass prior ws H).
  { unfold mass. apply qsum_map_ext_in. intros w Hw.
    destruct (H w) eqn:Hh; [|reflexivity]. rewrite (Hf w Hw Hh). ring. }
  rewrite E. unfold Qdiv. apply Qmult_inv_r. apply ne_of_lt. exact Hpos.
Qed.

(* G2_lower_bound.  A lower bound that holds wherever the premises hold is a lower
   bound on the posterior expectation. *)
Theorem G2_lower_bound :
  forall (W : Type) (prior : W -> Q) (ws : list W) (f : W -> Q) (H : W -> bool)
         (lo : Q),
    nonneg prior ws -> 0 < mass prior ws H ->
    (forall w, In w ws -> H w = true -> lo <= f w) ->
    lo <= cexp prior ws f H.
Proof.
  intros W prior ws f H lo Hn Hpos Hf. unfold cexp.
  apply Qle_shift_div_l; [exact Hpos|].
  unfold mass. rewrite <- qsum_scale. apply qsum_le_in. intros w Hw.
  destruct (H w) eqn:Hh.
  - rewrite (Qmult_comm (prior w) (f w)).
    apply Qmult_le_compat_r; [apply Hf; assumption | apply Hn; exact Hw].
  - assert (Z : lo * 0 == 0) by ring. rewrite Z. apply Qle_refl.
Qed.

(* G3_syllogism_learned.  Test suite T76, learned: under any prior over non-empty boxes,
   after observing "every V is M" and "every M is R", an individual of V is
   in R with probability exactly 1. *)
Theorem G3_syllogism_learned :
  forall (W : Type) (prior : W -> Q) (ws : list W) (V M R : W -> box),
    nonneg prior ws -> (forall w, In w ws -> nonempty (V w)) ->
    let H := fun w => everyb (V w) (M w) && everyb (M w) (R w) in
    0 < mass prior ws H ->
    cexp prior ws (fun w => pr (V w) (R w)) H == 1.
Proof.
  intros W prior ws V M R Hn Hne H Hpos. apply G1_certain; [exact Hn | exact Hpos|].
  intros w Hw Hh. subst H. cbv beta in Hh.
  apply andb_true_iff in Hh. destruct Hh as [E1 E2].
  apply everyb_spec in E1. apply everyb_spec in E2.
  pose proof (X3_every_transitive _ _ _ E1 E2) as E.
  unfold pr. rewrite (meet_every _ _ E). unfold Qdiv.
  apply Qmult_inv_r. apply ne_of_lt. apply vol_pos. apply Hne. exact Hw.
Qed.

(* G4_most_learned.  After observing "most P are Q" with threshold theta, an individual
   of P is in Q with probability at least theta.  The box counterpart of
   B7 in R3. *)
Theorem G4_most_learned :
  forall (theta : Q) (W : Type) (prior : W -> Q) (ws : list W)
         (P Q : W -> box),
    nonneg prior ws -> (forall w, In w ws -> nonempty (P w)) ->
    let H := fun w => mostb theta (P w) (Q w) in
    0 < mass prior ws H ->
    theta <= cexp prior ws (fun w => pr (P w) (Q w)) H.
Proof.
  intros theta W prior ws P Q Hn Hne H Hpos.
  apply G2_lower_bound; [exact Hn | exact Hpos|].
  intros w Hw Hh. subst H. cbv beta in Hh. unfold mostb in Hh.
  apply Qle_bool_iff in Hh. unfold pr.
  apply Qle_shift_div_l; [apply vol_pos; apply Hne; exact Hw | exact Hh].
Qed.

(* ------------------------------------------------------------------ *)
(* Worked grid                                                         *)
(* ------------------------------------------------------------------ *)

(* One dimension.  The candidate boxes are the ten intervals with end
   points in {0, 1/4, 1/2, 3/4, 1}.  A configuration is a pair (P, Q) of
   them; the hundred configurations have equal prior weight. *)
Definition pts : list Q := [0; 1 # 4; 1 # 2; 3 # 4; 1].
Definition ivs : list (Q * Q) :=
  filter (fun b => negb (Qle_bool (snd b) (fst b))) (list_prod pts pts).
Definition boxes1 : list box := map (fun b => [b]) ivs.
Definition cfgs : list (box * box) := list_prod boxes1 boxes1.
Definition unif (_ : box * box) : Q := 1 # 100.
Definition always (_ : box * box) : bool := true.
Definition obs_every (w : box * box) : bool := everyb (fst w) (snd w).
Definition obs_most (w : box * box) : bool := mostb (7 # 10) (fst w) (snd w).

Example E_grid_size : length boxes1 = 10%nat /\ length cfgs = 100%nat.
Proof. split; reflexivity. Qed.

(* Before any observation: an arbitrary individual satisfies an arbitrary
   predicate with probability 1/2, and a P is a Q with probability 31/60. *)
Example E_prior :
  cexp unif cfgs (fun w => vol (fst w)) always == 1 # 2 /\
  cexp unif cfgs (fun w => pr (fst w) (snd w)) always == 31 # 60.
Proof. split; vm_compute; reflexivity. Qed.

(* The premises themselves: "every P is Q" has prior probability 7/20,
   "most P are Q" (threshold 7/10) has 37/100. *)
Example E_premise_mass :
  mass unif cfgs obs_every == 7 # 20 /\ mass unif cfgs obs_most == 37 # 100.
Proof. split; vm_compute; reflexivity. Qed.

(* After observing "most P are Q": 73/74.  After "every P is Q": 1. *)
Example E_posterior :
  cexp unif cfgs (fun w => pr (fst w) (snd w)) obs_most == 73 # 74 /\
  cexp unif cfgs (fun w => pr (fst w) (snd w)) obs_every == 1.
Proof. split; vm_compute; reflexivity. Qed.

(* [BBCLM19] sec. 3: a predicate contained in another has a lower chance
   of holding of an arbitrary individual than an arbitrary predicate has.
   Here: 2/5 against the prior 1/2; the containing predicate rises to
   7/10. *)
Example E_contained_is_less_likely :
  cexp unif cfgs (fun w => vol (fst w)) obs_every == 2 # 5 /\
  cexp unif cfgs (fun w => vol (snd w)) obs_every == 7 # 10.
Proof. split; vm_compute; reflexivity. Qed.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
Print Assumptions G1_certain.
Print Assumptions G2_lower_bound.
Print Assumptions G3_syllogism_learned.
Print Assumptions G4_most_learned.
Print Assumptions X1_meet_is_intersection.
Print Assumptions X2_every_is_inclusion.
Print Assumptions X3_every_transitive.
Print Assumptions X4_inclusion_lowers_volume.
Print Assumptions X5_every_implies_most.
Print Assumptions X6_degree.
Print Assumptions X7_comparative_is_box.
Print Assumptions X8_union_is_not_a_box.
Print Assumptions E_T76.
Print Assumptions E_volumes.
Print Assumptions E_T77.
Print Assumptions E_T31.
Print Assumptions E_T15.
Print Assumptions E_grid_size.
Print Assumptions E_prior.
Print Assumptions E_premise_mass.
Print Assumptions E_posterior.
Print Assumptions E_contained_is_less_likely.
