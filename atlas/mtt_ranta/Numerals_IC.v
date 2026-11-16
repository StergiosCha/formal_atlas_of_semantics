(* ========================================================================== *)
(*  Numerals_IC.v — numerical quantifiers relative to identity criteria      *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCE
     [CL20] Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in
       Modern Type Theories. ISTE/Wiley.  [section 5.3, pp. 108-119:
       setoids (5.13); sub-setoids, Def 5.2 p. 111; Three0, Def 5.3 p. 112;
       Three, Def 5.4 p. 113; pre-setoids and the dot pre-setoid, Def 5.5
       p. 115; THREE, Def 5.6 p. 116; examples (5.26), (5.47)-(5.48),
       (5.52)-(5.55)]
     The PDF text layer prints D[B] in Def 5.3 and 5.4 with "="; the typeset
     page 112 has "<>", as Def 5.6 has with negations.

   WHAT IS FORMALIZED
     The book defines "three" relative to the identity criterion of a common
     noun.  Here the numeral is "at least n" for every n: a list of n
     objects, pairwise distinct under the criterion, all satisfying the
     predicate.
       S1   the book's three-variable numeral is the numeral at 3
       S2   counting by a supertype's criterion is counting by its restriction
       S3   (5.26) for every n: counts transfer along a sub-setoid
       S4   they do not transfer without inheritance of the criterion
       S5   n+1 entails n          S6   monotonicity
       S7   the dot relation is reflexive and symmetric
       S8   it is not transitive, so it is not an identity criterion
       S9   (5.48) for every n: double distinctness
       S10  copredication gives both separate counts
       S11  the separate counts do not give the joint count
       S12  (5.52)-(5.55) for every n: an adjective inside a Sigma-type moves
            into the predicate
       S13  reflexivity of the relation is needed
       S14  a counting form on finite listings
     and three closed models: two copies of one content (exactly two books
     physically, exactly one informationally), and five books with three
     copies and three contents but no three distinct in both.

   NOT FORMALIZED (and why)
     * How a sentence selects the criterion ((5.45): the verb decides): the
       criterion is taken as given.
     * Dot-types with their own rules (the book's App. 6): the dot-type is a
       product here, which is all that counting needs.
     * "Exactly n" appears only in the models; the book's formulas are
       existential.

   REPRESENTATION CHOICES
     Subtyping A <= B is an explicit function c : A -> B, as in MTT.v.
     Predicates are not required to respect the criterion (the book's
     footnote 7 on p. 110); no result needs it.
*)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Definitions                                                         *)
(* ------------------------------------------------------------------ *)

Definition is_pre {B : Type} (k : B -> B -> Prop) : Prop :=
  (forall x, k x x) /\ (forall x y, k x y -> k y x).

Definition is_equiv {B : Type} (k : B -> B -> Prop) : Prop :=
  is_pre k /\ (forall x y z, k x y -> k y z -> k x z).

(* The relation of B restricted to A along the coercion c. *)
Definition restrict {A B : Type} (c : A -> B) (k : B -> B -> Prop) : A -> A -> Prop :=
  fun x y => k (c x) (c y).

(* Def 5.2: (A, kA) is a sub-setoid of (B, kB) along c. *)
Definition sub_setoid {A B : Type} (c : A -> B)
  (kA : A -> A -> Prop) (kB : B -> B -> Prop) : Prop :=
  forall x y, kA x y <-> restrict c kB x y.

(* Def 5.5(2): the relation of the dot pre-setoid. *)
Definition dot_kappa {B1 B2 : Type} (k1 : B1 -> B1 -> Prop) (k2 : B2 -> B2 -> Prop)
  : B1 * B2 -> B1 * B2 -> Prop :=
  fun p q => k1 (fst p) (fst q) \/ k2 (snd p) (snd q).

(* Pairwise distinctness under k of the images of a list. *)
Definition distinct {A B : Type} (c : A -> B) (k : B -> B -> Prop) (l : list A) : Prop :=
  ForallOrdPairs (fun x y => ~ k (c x) (c y)) l.

(* The generic numeral, Def 5.6 for every n. *)
Definition at_least (n : nat) {A B : Type} (c : A -> B) (k : B -> B -> Prop)
  (P : B -> Prop) : Prop :=
  exists l : list A, length l = n /\ distinct c k l /\ Forall (fun x => P (c x)) l.

Definition exactly (n : nat) {A B : Type} (c : A -> B) (k : B -> B -> Prop)
  (P : B -> Prop) : Prop :=
  at_least n c k P /\ ~ at_least (S n) c k P.

(* Def 5.4 / 5.6 as printed, with three variables. *)
Definition three {A B : Type} (c : A -> B) (k : B -> B -> Prop) (P : B -> Prop) : Prop :=
  exists x y z : A,
    ~ k (c x) (c y) /\ ~ k (c y) (c z) /\ ~ k (c x) (c z) /\
    P (c x) /\ P (c y) /\ P (c z).

(* Def 5.3: the special case A = B. *)
Definition three0 {B : Type} (k : B -> B -> Prop) (P : B -> Prop) : Prop :=
  three (fun x : B => x) k P.

(* Class count on a finite listing, for the counting form. *)
Fixpoint dedup_by {B : Type} (kb : B -> B -> bool) (l : list B) : list B :=
  match l with
  | [] => []
  | x :: t => if existsb (kb x) t then dedup_by kb t else x :: dedup_by kb t
  end.

(* ------------------------------------------------------------------ *)
(* Statements                                                          *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Instances                                                           *)
(* ------------------------------------------------------------------ *)

(* MTT.v Part 7, generalized: two copies with one content.  Physically
   exactly two books, informationally exactly one. *)
Definition copies : Type := bool.
Definition phy_of (b : copies) : bool := b.
Definition info_of (_ : copies) : unit := tt.

(* The S11_split_does_not_join model: books as (copy, content) pairs.  Copies 1-3 of content a;
   contents b and c only on copy 1.  Three copies and three contents, but no
   three books distinct in both. *)
Definition split_books : list (nat * nat) := [(1, 0); (2, 0); (3, 0); (1, 1); (1, 2)].
Definition SB : Type := {p : nat * nat | In p split_books}.
Definition sb (s : SB) : nat * nat := proj1_sig s.

(* Supporting result: pairwise conditions transport along a map. *)
Lemma fop_map_mono {X Y : Type} (R : X -> X -> Prop) (R' : Y -> Y -> Prop) (f : X -> Y) :
  (forall x y, R x y -> R' (f x) (f y)) ->
  forall l, ForallOrdPairs R l -> ForallOrdPairs R' (map f l).
Proof.
  intros H l Hl; induction Hl as [|a t Ha Ht IH]; simpl; constructor; auto.
  apply Forall_map; eapply Forall_impl; [|exact Ha]; intros y Hy; exact (H _ _ Hy).
Qed.

Lemma fop_mono {X : Type} (R R' : X -> X -> Prop) :
  (forall x y, R x y -> R' x y) ->
  forall l, ForallOrdPairs R l -> ForallOrdPairs R' l.
Proof.
  intros H l Hl; rewrite <- (map_id l); apply (fop_map_mono R R' (fun x => x)); auto.
Qed.

(* S1_three_is_at_least_3. The book's three-variable numeral is the generic numeral at 3. *)
Theorem S1_three_is_at_least_3 :
  forall (A B : Type) (c : A -> B) (k : B -> B -> Prop) (P : B -> Prop),
    three c k P <-> at_least 3 c k P.
Proof.
  intros A B c k P; split.
  - intros (x & y & z & Hxy & Hyz & Hxz & Px & Py & Pz).
    exists [x; y; z]; repeat split; [| repeat constructor; auto].
    repeat constructor; auto.
  - intros ([|x [|y [|z [|w l]]]] & Hn & Hd & Hp); simpl in Hn; try discriminate.
    unfold distinct in Hd.
    inversion Hd as [|? ? Hx Hd1]; subst.
    inversion Hd1 as [|? ? Hy _]; subst.
    inversion Hx as [|? ? Hxy Hx2]; subst; inversion Hx2 as [|? ? Hxz _]; subst.
    inversion Hy as [|? ? Hyz _]; subst.
    inversion Hp as [|? ? Px Hp1]; subst; inversion Hp1 as [|? ? Py Hp2]; subst;
      inversion Hp2 as [|? ? Pz _]; subst.
    exists x, y, z; tauto.
Qed.

(* S2_three_is_three0_on_restriction. Def 5.4 with a setoid B restricts to Def 5.3 over the sub-setoid:
   counting A-objects by B's criterion is counting in (A, kB restricted). *)
Theorem S2_three_is_three0_on_restriction :
  forall (n : nat) (A B : Type) (c : A -> B) (k : B -> B -> Prop) (P : B -> Prop),
    at_least n c k P <-> at_least n (fun x : A => x) (restrict c k) (fun x => P (c x)).
Proof. intros n A B c k P; split; intros H; exact H. Qed.

(* S3_sub_setoid_transfer. (5.26), for every n: if (A, kA) is a sub-setoid of (B, kB), then
   n A's that P entail n B's that P. *)
Theorem S3_sub_setoid_transfer :
  forall (n : nat) (A B : Type) (c : A -> B)
         (kA : A -> A -> Prop) (kB : B -> B -> Prop) (P : B -> Prop),
    sub_setoid c kA kB ->
    at_least n (fun x : A => x) kA (fun x => P (c x)) ->
    at_least n (fun x : B => x) kB P.
Proof.
  intros n A B c kA kB P Hsub (l & Hn & Hd & Hp).
  exists (map c l); repeat split.
  - now rewrite length_map.
  - apply (fop_map_mono (fun x y => ~ kA x y) (fun x y => ~ kB x y) c); [|exact Hd].
    intros x y Hn' Hk; apply Hn'; apply Hsub; exact Hk.
  - apply Forall_map; exact Hp.
Qed.

(* S5_downward. Numerals are downward closed: n+1 entails n. *)
Theorem S5_downward :
  forall (n : nat) (A B : Type) (c : A -> B) (k : B -> B -> Prop) (P : B -> Prop),
    at_least (S n) c k P -> at_least n c k P.
Proof.
  intros n A B c k P ([|x l] & Hn & Hd & Hp); simpl in Hn; [discriminate|].
  exists l; repeat split.
  - lia.
  - inversion Hd; assumption.
  - inversion Hp; assumption.
Qed.

(* S6_monotone. Upward monotone in the predicate and along a further coercion. *)
Theorem S6_monotone :
  forall (n : nat) (A' A B : Type) (d : A' -> A) (c : A -> B)
         (k : B -> B -> Prop) (P Q : B -> Prop),
    (forall b, P b -> Q b) ->
    at_least n (fun x => c (d x)) k P -> at_least n c k Q.
Proof.
  intros n A' A B d c k P Q HPQ (l & Hn & Hd & Hp).
  exists (map d l); repeat split.
  - now rewrite length_map.
  - apply (fop_map_mono (fun x y => ~ k (c (d x)) (c (d y))) (fun x y => ~ k (c x) (c y)) d);
      [intros x y H; exact H | exact Hd].
  - apply Forall_map; eapply Forall_impl; [|exact Hp]; intros x Hx; exact (HPQ _ Hx).
Qed.

(* S7_dot_is_pre. The dot relation is a pre-setoid relation when its components are. *)
Theorem S7_dot_is_pre :
  forall (B1 B2 : Type) (k1 : B1 -> B1 -> Prop) (k2 : B2 -> B2 -> Prop),
    is_pre k1 -> is_pre k2 -> is_pre (dot_kappa k1 k2).
Proof.
  intros B1 B2 k1 k2 [r1 s1] [r2 s2]; split.
  - intros [a b]; left; apply r1.
  - intros [a b] [a' b'] [H|H]; [left; apply s1 | right; apply s2]; exact H.
Qed.

(* S8_dot_not_transitive. It is not an identity criterion: transitivity fails even when both
   components are equivalences (the book's remark after Def 5.6). *)
Theorem S8_dot_not_transitive :
  exists (B1 B2 : Type) (k1 : B1 -> B1 -> Prop) (k2 : B2 -> B2 -> Prop),
    is_equiv k1 /\ is_equiv k2 /\ ~ is_equiv (dot_kappa k1 k2).
Proof.
  exists bool, bool, (@eq bool), (@eq bool).
  assert (E : is_equiv (@eq bool)).
  { split; [split|]; [reflexivity | intros; symmetry; assumption |
                      intros; etransitivity; eassumption]. }
  split; [exact E|]; split; [exact E|].
  intros [_ T].
  destruct (T (true, true) (true, false) (false, false)) as [H|H];
    [left; reflexivity | right; reflexivity | discriminate H | discriminate H].
Qed.

(* S10_copredication_splits. Copredication entails the two separate counts. *)
Theorem S10_copredication_splits :
  forall (n : nat) (A B1 B2 : Type) (c : A -> B1 * B2)
         (k1 : B1 -> B1 -> Prop) (k2 : B2 -> B2 -> Prop)
         (P1 : B1 -> Prop) (P2 : B2 -> Prop),
    at_least n c (dot_kappa k1 k2) (fun p => P1 (fst p) /\ P2 (snd p)) ->
    at_least n (fun x => fst (c x)) k1 P1 /\ at_least n (fun x => snd (c x)) k2 P2.
Proof.
  intros n A B1 B2 c k1 k2 P1 P2 (l & Hn & Hd & Hp); split; exists l; repeat split; auto.
  - apply (fop_mono (fun x y => ~ dot_kappa k1 k2 (c x) (c y))); [|exact Hd].
    intros x y H H1; apply H; left; exact H1.
  - eapply Forall_impl; [|exact Hp]; intros x [H _]; exact H.
  - apply (fop_mono (fun x y => ~ dot_kappa k1 k2 (c x) (c y))); [|exact Hd].
    intros x y H H1; apply H; right; exact H1.
  - eapply Forall_impl; [|exact Hp]; intros x [_ H]; exact H.
Qed.

(* S13_reflexivity_needed. Why a pre-setoid relation must be reflexive: with an empty relation,
   one object counts as two. *)
Theorem S13_reflexivity_needed :
  at_least 2 (fun x : unit => x) (fun _ _ => False) (fun _ => True).
Proof.
  exists [tt; tt]; repeat split; repeat constructor; intros [].
Qed.

Lemma eq_is_equiv (X : Type) : is_equiv (@eq X).
Proof.
  split; [split|].
  - intros x; reflexivity.
  - intros x y H; symmetry; exact H.
  - intros x y z H1 H2; etransitivity; eassumption.
Qed.

(* S4_transfer_needs_inheritance. Without inheritance the transfer fails: a subtype whose criterion is
   finer than the restriction (passengers counted by trips, persons by
   persons).  There are two passengers and not two persons. *)
Theorem S4_transfer_needs_inheritance :
  exists (A B : Type) (c : A -> B) (kA : A -> A -> Prop) (kB : B -> B -> Prop)
         (P : B -> Prop),
    is_equiv kA /\ is_equiv kB /\ (forall x y, kA x y -> restrict c kB x y) /\
    at_least 2 (fun x : A => x) kA (fun x => P (c x)) /\
    ~ at_least 2 (fun x : B => x) kB P.
Proof.
  exists bool, unit, (fun _ => tt), (@eq bool), (@eq unit), (fun _ => True).
  split; [apply eq_is_equiv|].
  split; [apply eq_is_equiv|].
  split; [intros x y _; reflexivity|].
  split.
  - exists [true; false]. split; [reflexivity|]. split.
    + constructor; [|constructor; [constructor|constructor]].
      constructor; [discriminate|constructor].
    + repeat constructor.
  - intros ([|x [|y l]] & Hn & Hd & _); simpl in Hn; try discriminate.
    inversion Hd as [|? ? Hx _]; subst; inversion Hx as [|? ? H _]; subst.
    apply H; destruct x, y; reflexivity.
Qed.

Theorem I1_two_copies_phy :
  exactly 2 phy_of (@eq bool) (fun _ => True).
Proof.
  split.
  - exists [true; false]; repeat split; repeat constructor; discriminate.
  - intros ([|x [|y [|z l]]] & Hn & Hd & _); simpl in Hn; try discriminate.
    inversion Hd as [|? ? Hx Hd1]; subst; inversion Hd1 as [|? ? Hy _]; subst.
    inversion Hx as [|? ? Hxy Hx2]; subst; inversion Hx2 as [|? ? Hxz _]; subst.
    inversion Hy as [|? ? Hyz _]; subst.
    unfold phy_of in *; destruct x, y, z; tauto.
Qed.

Theorem I2_one_content_info :
  exactly 1 info_of (@eq unit) (fun _ => True).
Proof.
  split.
  - exists [true]; repeat split; repeat constructor.
  - intros ([|x [|y l]] & Hn & Hd & _); simpl in Hn; try discriminate.
    inversion Hd as [|? ? Hx _]; subst; inversion Hx as [|? ? H _]; subst.
    apply H; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Supporting results                                                  *)
(* ------------------------------------------------------------------ *)

Lemma fop_and {X : Type} (R R' : X -> X -> Prop) (l : list X) :
  ForallOrdPairs R l -> ForallOrdPairs R' l ->
  ForallOrdPairs (fun x y => R x y /\ R' x y) l.
Proof.
  intros H; induction H as [|a t Ha Ht IH]; intros H'; [constructor|].
  inversion H' as [|? ? Ha' Ht']; subst.
  constructor; [apply Forall_and; assumption | apply IH; exact Ht'].
Qed.

Lemma fop_map_inv {X Y : Type} (R' : Y -> Y -> Prop) (f : X -> Y) (l : list X) :
  ForallOrdPairs R' (map f l) -> ForallOrdPairs (fun x y => R' (f x) (f y)) l.
Proof.
  induction l as [|a t IH]; simpl; intros H; [constructor|].
  inversion H as [|? ? Ha Ht]; subst.
  constructor; [exact (proj1 (Forall_map f (R' (f a)) t) Ha) | apply IH; exact Ht].
Qed.

Lemma sig_lift {A : Type} (Q : A -> Prop) (l : list A) :
  Forall Q l -> exists l' : list {x : A | Q x}, map (@proj1_sig A Q) l' = l.
Proof.
  induction 1 as [|a t Ha Ht [l' E]].
  - exists []; reflexivity.
  - exists (exist _ a Ha :: l'); simpl; rewrite E; reflexivity.
Qed.

Lemma at_least_le (m n : nat) {A B : Type} (c : A -> B) (k : B -> B -> Prop)
  (P : B -> Prop) : m <= n -> at_least n c k P -> at_least m c k P.
Proof.
  induction 1 as [|n' Hle IH]; [auto|].
  intros H; apply IH; exact (S5_downward n' A B c k P H).
Qed.

(* Pigeonhole up to a symmetric transitive relation: pairwise unrelated
   objects, each related to a member of D, are at most as many as D. *)
Lemma pigeon {B : Type} (K : B -> B -> Prop) :
  (forall x y, K x y -> K y x) -> (forall x y z, K x y -> K y z -> K x z) ->
  forall l D : list B,
    ForallOrdPairs (fun x y => ~ K x y) l ->
    (forall x, In x l -> exists r, In r D /\ K x r) ->
    length l <= length D.
Proof.
  intros sym trans l; induction l as [|x t IH]; intros D Hd Hr; simpl; [lia|].
  inversion Hd as [|? ? Hx Ht]; subst.
  destruct (Hr x (or_introl eq_refl)) as (r & HrD & Hxr).
  destruct (in_split r D HrD) as (D1 & D2 & ->).
  assert (Hlen : length t <= length (D1 ++ D2)).
  { apply IH; [exact Ht|]. intros y Hy.
    destruct (Hr y (or_intror Hy)) as (r' & Hr' & Hyr').
    apply in_app_or in Hr'. destruct Hr' as [H|[H|H]].
    - exists r'; split; [apply in_or_app; left; exact H | exact Hyr'].
    - subst r'. exfalso. rewrite Forall_forall in Hx. apply (Hx y Hy).
      eapply trans; [exact Hxr | apply sym; exact Hyr'].
    - exists r'; split; [apply in_or_app; right; exact H | exact Hyr']. }
  rewrite length_app in *. simpl. lia.
Qed.

(* Three facts about dedup_by. *)
Lemma dedup_in {B : Type} (kb : B -> B -> bool) (l : list B) (x : B) :
  In x (dedup_by kb l) -> In x l.
Proof.
  induction l as [|a t IH]; simpl; [tauto|].
  destruct (existsb (kb a) t); simpl; intros H.
  - right; auto.
  - destruct H; [left; assumption | right; auto].
Qed.

Lemma dedup_distinct {B : Type} (kb : B -> B -> bool) (l : list B) :
  ForallOrdPairs (fun x y => kb x y <> true) (dedup_by kb l).
Proof.
  induction l as [|a t IH]; simpl; [constructor|].
  destruct (existsb (kb a) t) eqn:E; [exact IH|].
  constructor; [|exact IH].
  apply Forall_forall. intros y Hy Hk. apply dedup_in in Hy.
  assert (existsb (kb a) t = true)
    by (apply existsb_exists; exists y; split; assumption).
  congruence.
Qed.

Lemma dedup_rep {B : Type} (kb : B -> B -> bool) :
  (forall x, kb x x = true) ->
  (forall x y z, kb x y = true -> kb y z = true -> kb x z = true) ->
  forall (l : list B) (x : B),
    In x l -> exists r, In r (dedup_by kb l) /\ kb x r = true.
Proof.
  intros refl trans l; induction l as [|a t IH]; simpl; [tauto|].
  intros x [->|H].
  - destruct (existsb (kb x) t) eqn:E.
    + apply existsb_exists in E. destruct E as (y & Hy & Hxy).
      destruct (IH y Hy) as (r & Hr & Hyr).
      exists r; split; [exact Hr | eapply trans; eassumption].
    + exists x; split; [left; reflexivity | apply refl].
  - destruct (IH x H) as (r & Hr & Hxr).
    destruct (existsb (kb a) t).
    + exists r; split; assumption.
    + exists r; split; [right; exact Hr | exact Hxr].
Qed.

(* ------------------------------------------------------------------ *)
(* The statements                                                      *)
(* ------------------------------------------------------------------ *)

(* S9_dot_double_distinctness. (5.48), for every n: counting under the dot relation is counting
   objects that are distinct under both components. *)
Theorem S9_dot_double_distinctness :
  forall (n : nat) (A B1 B2 : Type) (c : A -> B1 * B2)
         (k1 : B1 -> B1 -> Prop) (k2 : B2 -> B2 -> Prop) (P : B1 * B2 -> Prop),
    at_least n c (dot_kappa k1 k2) P <->
    exists l : list A, length l = n /\
      distinct (fun x => fst (c x)) k1 l /\ distinct (fun x => snd (c x)) k2 l /\
      Forall (fun x => P (c x)) l.
Proof.
  intros n A B1 B2 c k1 k2 P; split.
  - intros (l & Hn & Hd & Hp). exists l.
    split; [exact Hn|]. split; [|split; [|exact Hp]].
    + apply (fop_mono (fun x y => ~ dot_kappa k1 k2 (c x) (c y))); [|exact Hd].
      intros x y H H1; apply H; left; exact H1.
    + apply (fop_mono (fun x y => ~ dot_kappa k1 k2 (c x) (c y))); [|exact Hd].
      intros x y H H1; apply H; right; exact H1.
  - intros (l & Hn & H1 & H2 & Hp). exists l.
    split; [exact Hn|]. split; [|exact Hp].
    apply (fop_mono (fun x y => ~ k1 (fst (c x)) (fst (c y)) /\
                                ~ k2 (snd (c x)) (snd (c y)))).
    + intros x y [Ha Hb] [H|H]; [apply Ha | apply Hb]; exact H.
    + apply fop_and; [exact H1 | exact H2].
Qed.

(* S12_sigma_absorbs_adjective. (5.52)-(5.55): the adjective inside the Sigma-type moves into the
   predicate.  "Three heavy books" counts books that are heavy; no premise on
   proofs of "heavy" is needed, because objects are compared by the
   criterion of B, not by equality in the Sigma-type. *)
Theorem S12_sigma_absorbs_adjective :
  forall (n : nat) (A B : Type) (Q : A -> Prop) (c : A -> B)
         (k : B -> B -> Prop) (P : B -> Prop),
    at_least n (fun s : {x : A | Q x} => c (proj1_sig s)) k P <->
    exists l : list A, length l = n /\ distinct c k l /\
      Forall (fun x => Q x /\ P (c x)) l.
Proof.
  intros n A B Q c k P; split.
  - intros (l & Hn & Hd & Hp). exists (map (@proj1_sig A Q) l).
    split; [rewrite length_map; exact Hn|]. split.
    + apply (fop_map_mono
               (fun s t : {x : A | Q x} => ~ k (c (proj1_sig s)) (c (proj1_sig t)))
               (fun x y => ~ k (c x) (c y)) (@proj1_sig A Q));
        [intros x y H; exact H | exact Hd].
    + apply Forall_map. apply Forall_forall. intros s Hs.
      split; [exact (proj2_sig s)|].
      rewrite Forall_forall in Hp. exact (Hp s Hs).
  - intros (l & Hn & Hd & Hp).
    assert (HQ : Forall Q l)
      by (eapply Forall_impl; [|exact Hp]; intros x [H _]; exact H).
    destruct (sig_lift Q l HQ) as [l' E]. exists l'.
    split; [rewrite <- Hn, <- E, length_map; reflexivity|]. split.
    + apply (fop_map_inv (fun x y => ~ k (c x) (c y)) (@proj1_sig A Q)).
      rewrite E. exact Hd.
    + rewrite <- E in Hp.
      pose proof (proj1 (Forall_map (@proj1_sig A Q) (fun x => Q x /\ P (c x)) l') Hp) as Hp'.
      eapply Forall_impl; [|exact Hp']. intros s [_ H]; exact H.
Qed.

(* The split model: no three of the five books are distinct both as copies
   and as contents. *)
Lemma split_no_three (p q r : nat * nat) :
  In p split_books -> In q split_books -> In r split_books ->
  ~ (fst p = fst q \/ snd p = snd q) ->
  ~ (fst q = fst r \/ snd q = snd r) ->
  ~ (fst p = fst r \/ snd p = snd r) -> False.
Proof.
  unfold split_books; simpl; intros Hp Hq Hr H1 H2 H3.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; subst; simpl in *;
    solve [apply H1; auto | apply H2; auto | apply H3; auto].
Qed.

Lemma in_sb (p : nat * nat) (H : In p split_books) : SB.
Proof. exact (exist _ p H). Defined.

Theorem I3_split_model :
  at_least 3 (fun s => fst (sb s)) (@eq nat) (fun _ => True) /\
  at_least 3 (fun s => snd (sb s)) (@eq nat) (fun _ => True) /\
  ~ at_least 3 sb (dot_kappa (@eq nat) (@eq nat)) (fun _ => True /\ True).
Proof.
  assert (h10 : In (1, 0) split_books) by (simpl; auto 10).
  assert (h20 : In (2, 0) split_books) by (simpl; auto 10).
  assert (h30 : In (3, 0) split_books) by (simpl; auto 10).
  assert (h11 : In (1, 1) split_books) by (simpl; auto 10).
  assert (h12 : In (1, 2) split_books) by (simpl; auto 10).
  split; [|split].
  - exists [in_sb _ h10; in_sb _ h20; in_sb _ h30].
    split; [reflexivity|]. split; [|repeat constructor].
    repeat constructor; simpl; discriminate.
  - exists [in_sb _ h10; in_sb _ h11; in_sb _ h12].
    split; [reflexivity|]. split; [|repeat constructor].
    repeat constructor; simpl; discriminate.
  - intros ([|x [|y [|z [|w l]]]] & Hn & Hd & _); simpl in Hn; try discriminate.
    inversion Hd as [|? ? Hx Hd1]; subst.
    inversion Hd1 as [|? ? Hy _]; subst.
    inversion Hx as [|? ? Hxy Hx2]; subst; inversion Hx2 as [|? ? Hxz _]; subst.
    inversion Hy as [|? ? Hyz _]; subst.
    exact (split_no_three (sb x) (sb y) (sb z)
             (proj2_sig x) (proj2_sig y) (proj2_sig z) Hxy Hyz Hxz).
Qed.

(* S11_split_does_not_join. The converse fails: "John picked up three books and mastered three
   books" does not entail "John picked up and mastered three books". *)
Theorem S11_split_does_not_join :
  exists (A B1 B2 : Type) (c : A -> B1 * B2)
         (k1 : B1 -> B1 -> Prop) (k2 : B2 -> B2 -> Prop)
         (P1 : B1 -> Prop) (P2 : B2 -> Prop),
    is_equiv k1 /\ is_equiv k2 /\
    at_least 3 (fun x => fst (c x)) k1 P1 /\ at_least 3 (fun x => snd (c x)) k2 P2 /\
    ~ at_least 3 c (dot_kappa k1 k2) (fun p => P1 (fst p) /\ P2 (snd p)).
Proof.
  exists SB, nat, nat, sb, (@eq nat), (@eq nat), (fun _ => True), (fun _ => True).
  destruct I3_split_model as (H1 & H2 & H3).
  split; [apply eq_is_equiv|]. split; [apply eq_is_equiv|].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* S14_counting_form. Counting form: on a finite listing, with decidable criterion and
   predicate, "at least n" holds iff the P-objects fall into at least n
   classes. *)
Theorem S14_counting_form :
  forall (n : nat) (B : Type) (all : list B) (kb : B -> B -> bool) (pb : B -> bool),
    (forall x, In x all) -> is_equiv (fun x y => kb x y = true) ->
    at_least n (fun x : B => x) (fun x y => kb x y = true) (fun x => pb x = true)
    <-> n <= length (dedup_by kb (filter pb all)).
Proof.
  intros n B all kb pb Hall [[refl sym] trans]. split.
  - intros (l & Hn & Hd & Hp). rewrite <- Hn.
    apply (pigeon (fun x y => kb x y = true) sym trans); [exact Hd|].
    intros x Hx. apply (dedup_rep kb refl trans).
    apply filter_In. split; [apply Hall|].
    rewrite Forall_forall in Hp. exact (Hp x Hx).
  - intros Hle.
    apply (at_least_le n (length (dedup_by kb (filter pb all)))); [exact Hle|].
    exists (dedup_by kb (filter pb all)). split; [reflexivity|]. split.
    + apply dedup_distinct.
    + apply Forall_forall. intros x Hx.
      apply dedup_in in Hx. apply filter_In in Hx. exact (proj2 Hx).
Qed.

(* A use of S14_counting_form: the two-copies model, decided by counting. *)
Example copies_counted_phy :
  at_least 2 (fun x : bool => x) (fun x y => Bool.eqb x y = true) (fun _ => true = true).
Proof.
  apply (proj2 (S14_counting_form 2 bool [true; false] Bool.eqb (fun _ => true)
                  (fun x => ltac:(destruct x; simpl; auto))
                  ltac:(split; [split|];
                        [intros []; reflexivity
                        |intros [] []; simpl; auto
                        |intros [] [] []; simpl; auto]))).
  simpl; lia.
Qed.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
Print Assumptions I1_two_copies_phy.
Print Assumptions I2_one_content_info.
Print Assumptions I3_split_model.
Print Assumptions S1_three_is_at_least_3.
Print Assumptions S2_three_is_three0_on_restriction.
Print Assumptions S3_sub_setoid_transfer.
Print Assumptions S4_transfer_needs_inheritance.
Print Assumptions S5_downward.
Print Assumptions S6_monotone.
Print Assumptions S7_dot_is_pre.
Print Assumptions S8_dot_not_transitive.
Print Assumptions S9_dot_double_distinctness.
Print Assumptions S10_copredication_splits.
Print Assumptions S11_split_does_not_join.
Print Assumptions S12_sigma_absorbs_adjective.
Print Assumptions S13_reflexivity_needed.
Print Assumptions S14_counting_form.
Print Assumptions copies_counted_phy.
