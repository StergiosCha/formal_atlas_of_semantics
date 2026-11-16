(* ========================================================================== *)
(*  Bayesian_Semantics.v — probability conditions on finite models           *)
(*  FORMAL-ATLAS / atlas/probabilistic                                        *)
(* ========================================================================== *)
(*
   SOURCE
     [BBCL18] Bernardy, J.-P., Blanck, R., Chatzikyriakidis, S. & Lappin, S.
       (2018). A Compositional Bayesian Semantics for Natural Language.
       Proc. First International Workshop on Language Cognition and
       Computational Models, pp. 1-10 (ACL Anthology W18-4101).
       [sec. 1 p. 1: a sentence gets a conditional probability p(A | H);
       sec. 2.1 p. 3: observe, modelSimple; sec. 2.4 p. 5: eq. (1)-(3),
       most with threshold 0.7 and many with 0.6; sec. 2.4 pp. 5-6:
       chairExample1, chairExample2, chairExample3]
   Builds on RSA.v (finite sums, the literal listener), which this file
   leaves unchanged.

   WHAT IS FORMALIZED
     A finite, exact-weight fragment.  A model is a finite list of
     configurations with rational weights, and observe is conditioning.
       B1  what the hypotheses entail has probability 1
       B2  probability is monotone along entailment
       B3  a sentence and its negation share the unit
       B4  two observations in sequence are one joint observation
       B5  the literal listener of RSA.v is conditioning on truth
       B6  with equal weights on individuals, eq. (2) is eq. (1)
       B7  "many chairs have four legs" makes it probable, above the
           quantifier's threshold, that a given chair has four legs
       B8  on a worked model, that inference is supported and not entailed,
           and the inverse inference depends on the prior
     and a worked chair model with exact values 1/2, 2/3 and 1/3.

   NOT FORMALIZED (and why)
     * Individuals as vectors and predicates as biased directions, Gaussian
       priors and MCMC: the atlas uses exact rationals; the paper's printed
       numbers are sampling estimates under those priors and are not
       reproduced.
     * Comparatives (2.2), vague predicates (2.3), learning (3).
     * "every", which the paper uses without displaying its definition.

   REPRESENTATION CHOICES
     "Likely" in B7 is read as "more probable than the threshold".  The
     expectation in eq. (2) is itself a conditional probability over a
     finite list of individuals.
*)

From Coq Require Import List Bool QArith Arith.
Import ListNotations.
Require Import RSA.
Import QSum.
Open Scope Q_scope.

(* Total weight of the configurations satisfying H. *)
Definition mass {W : Type} (prior : W -> Q) (ws : list W) (H : W -> bool) : Q :=
  qsum (map (fun w => if H w then prior w else 0) ws).

(* p(A | H): [BBCL18] sec. 1; observe H, then return A. *)
Definition prob {W : Type} (prior : W -> Q) (ws : list W) (A H : W -> bool) : Q :=
  mass prior ws (fun w => A w && H w) / mass prior ws H.

Definition nonneg {W : Type} (prior : W -> Q) (ws : list W) : Prop :=
  forall w, In w ws -> 0 <= prior w.

(* Eq. (2): the expected value of vp among the cn-individuals exceeds theta.
   The expectation is itself a conditional probability over individuals. *)
Definition gq (theta : Q) {X : Type} (iw : X -> Q) (xs : list X)
  (cn vp : X -> bool) : bool :=
  negb (Qle_bool (prob iw xs vp cn) theta).
Definition many {X : Type} := @gq (3 # 5) X.
Definition most {X : Type} := @gq (7 # 10) X.

(* A configuration together with a sampled individual. *)
Definition joint {W X : Type} (prior : W -> Q) (iw : X -> Q) (p : W * X) : Q :=
  prior (fst p) * iw (snd p).

(* ------------------------------------------------------------------ *)
(* Statements                                                          *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Worked model                                                        *)
(* ------------------------------------------------------------------ *)

(* Seven individuals 0..6 with equal weights; chairs are 0, 1, 2.
   Configuration true:  0 and 1 and 3..6 have four legs.
   Configuration false: only 0 has four legs.
   Each configuration has prior 1/2. *)
Definition xs7 : list nat := seq 0 7.
Definition cfgs : list bool := [true; false].
Definition half (_ : bool) : Q := 1 # 2.
Definition one (_ : nat) : Q := 1.
Definition chair (_ : bool) (x : nat) : bool := x <? 3.
Definition fourlegs (w : bool) (x : nat) : bool :=
  if w then (x <? 2) || (3 <=? x) else x =? 0.

Definition many_chairs (p : bool * nat) : bool :=
  many one xs7 (chair (fst p)) (fourlegs (fst p)).

(* "Many chairs have four legs" holds in one configuration of the two. *)
Example E1_many_has_mass_half :
  mass half cfgs (fun w => many one xs7 (chair w) (fourlegs w)) == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

(* Before the observation, a chair has four legs with probability 1/2. *)
Example E2_before_observing :
  prob (joint half one) (list_prod cfgs xs7)
       (fun p => fourlegs (fst p) (snd p))
       (fun p => chair (fst p) (snd p)) == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

(* chairExample1: after observing it, 2/3. *)
Example E3_chair_example_1 :
  prob (joint half one) (list_prod cfgs xs7)
       (fun p => fourlegs (fst p) (snd p))
       (fun p => many_chairs p && chair (fst p) (snd p)) == 2 # 3.
Proof. vm_compute. reflexivity. Qed.

(* chairExample2, the inverse inference: 1/3. *)
Example E4_chair_example_2 :
  prob (joint half one) (list_prod cfgs xs7)
       (fun p => chair (fst p) (snd p))
       (fun p => many_chairs p && fourlegs (fst p) (snd p)) == 1 # 3.
Proof. vm_compute. reflexivity. Qed.

(* B8.  Separation, on this model.  The supported instance is not
   entailed: its probability is below 1.  And the inverse inference is not
   supported by the semantics alone: here it is below 1/2.  [BBCL18]
   reports 0.653 for the inverse under its Gaussian priors and 0.221 after
   one more hypothesis; the value depends on the prior. *)
Example B8_supported_not_entailed_and_inverse_fails :
  prob (joint half one) (list_prod cfgs xs7)
       (fun p => fourlegs (fst p) (snd p))
       (fun p => many_chairs p && chair (fst p) (snd p)) < 1 /\
  prob (joint half one) (list_prod cfgs xs7)
       (fun p => chair (fst p) (snd p))
       (fun p => many_chairs p && fourlegs (fst p) (snd p)) < 1 # 2.
Proof. split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Supporting results                                                  *)
(* ------------------------------------------------------------------ *)

Lemma mass_ext {W : Type} (prior : W -> Q) (ws : list W) (H H' : W -> bool) :
  (forall w, In w ws -> H w = H' w) -> mass prior ws H == mass prior ws H'.
Proof.
  intros E. unfold mass. apply qsum_map_ext_in. intros w Hw.
  rewrite (E w Hw). reflexivity.
Qed.

Lemma mass_nonneg {W : Type} (prior : W -> Q) (ws : list W) (H : W -> bool) :
  nonneg prior ws -> 0 <= mass prior ws H.
Proof.
  intros Hn. unfold mass. apply qsum_nonneg. intros q Hq.
  apply in_map_iff in Hq. destruct Hq as (w & <- & Hw).
  destruct (H w); [apply Hn; exact Hw | apply Qle_refl].
Qed.

Lemma mass_le {W : Type} (prior : W -> Q) (ws : list W) (H H' : W -> bool) :
  nonneg prior ws -> (forall w, In w ws -> H w = true -> H' w = true) ->
  mass prior ws H <= mass prior ws H'.
Proof.
  intros Hn Himp. unfold mass. apply qsum_le_in. intros w Hw.
  destruct (H w) eqn:E.
  - rewrite (Himp w Hw E). apply Qle_refl.
  - destruct (H' w); [apply Hn; exact Hw | apply Qle_refl].
Qed.

Lemma mass_split {W : Type} (prior : W -> Q) (ws : list W) (A H : W -> bool) :
  mass prior ws (fun w => A w && H w) +
  mass prior ws (fun w => negb (A w) && H w) == mass prior ws H.
Proof.
  unfold mass. rewrite <- qsum_plus. apply qsum_map_ext_in. intros w _.
  destruct (A w), (H w); simpl; ring.
Qed.

Lemma add_div (a b h : Q) : ~ h == 0 -> a + b == h -> a / h + b / h == 1.
Proof.
  intros nz E.
  assert (K : a / h + b / h == (a + b) / h) by (field; exact nz).
  rewrite K, E. unfold Qdiv. apply Qmult_inv_r. exact nz.
Qed.

Lemma qsum_pos_exists (l : list Q) :
  (forall x, In x l -> 0 <= x) -> 0 < qsum l -> exists x, In x l /\ 0 < x.
Proof.
  induction l as [|a t IH]; intros Hn Hpos.
  - exfalso. exact (Qlt_irrefl 0 Hpos).
  - destruct (Qlt_le_dec 0 a) as [h|h].
    + exists a. split; [left; reflexivity | exact h].
    + assert (a0 : a == 0)
        by (apply Qle_antisym; [exact h | apply Hn; left; reflexivity]).
      destruct IH as (x & Hx & xpos).
      * intros x Hx. apply Hn. right. exact Hx.
      * change (0 < a + qsum t) in Hpos. rewrite a0 in Hpos.
        rewrite Qplus_0_l in Hpos. exact Hpos.
      * exists x. split; [right; exact Hx | exact xpos].
Qed.

(* A sum over pairs is an iterated sum. *)
Lemma qsum_list_prod {W X : Type} (F : W * X -> Q) (ws : list W) (xs : list X) :
  qsum (map F (list_prod ws xs)) ==
  qsum (map (fun w => qsum (map (fun x => F (w, x)) xs)) ws).
Proof.
  induction ws as [|a t IH].
  - reflexivity.
  - change (list_prod (a :: t) xs)
      with (map (fun y => (a, y)) xs ++ list_prod t xs).
    rewrite map_app, qsum_app, map_map, IH. reflexivity.
Qed.

Lemma mass_scale_inner {X : Type} (p : Q) (iw : X -> Q) (xs : list X)
  (b : X -> bool) :
  qsum (map (fun x => if b x then p * iw x else 0) xs) == p * mass iw xs b.
Proof.
  unfold mass. rewrite <- qsum_scale. apply qsum_map_ext_in. intros x _.
  destruct (b x); ring.
Qed.

Lemma mass_joint {W X : Type} (prior : W -> Q) (iw : X -> Q) (ws : list W)
  (xs : list X) (Hb : W * X -> bool) :
  mass (joint prior iw) (list_prod ws xs) Hb ==
  qsum (map (fun w => prior w * mass iw xs (fun x => Hb (w, x))) ws).
Proof.
  unfold mass at 1. rewrite qsum_list_prod. apply qsum_map_ext_in.
  intros w _. exact (mass_scale_inner (prior w) iw xs (fun x => Hb (w, x))).
Qed.

(* The arithmetic core of B7_quantifier_supports_instance, for one configuration. *)
Lemma num_point (theta p c n : Q) :
  0 <= p -> 0 <= n -> n <= c -> theta < n / c ->
  theta * (p * c) <= p * n /\ (0 < p * c -> theta * (p * c) < p * n).
Proof.
  intros Hp Hn Hnc Hlt.
  destruct (Qlt_le_dec 0 c) as [cpos|cle].
  - assert (T : theta * c < n).
    { assert (E : n == n / c * c) by (field; apply ne_of_lt; exact cpos).
      rewrite E. apply Qmult_lt_compat_r; assumption. }
    split.
    + setoid_replace (theta * (p * c)) with (theta * c * p) by ring.
      setoid_replace (p * n) with (n * p) by ring.
      apply Qmult_le_compat_r; [apply Qlt_le_weak; exact T | exact Hp].
    + intros Hpc.
      assert (ppos : 0 < p).
      { destruct (Qlt_le_dec 0 p) as [h|h]; [exact h|]. exfalso.
        assert (p0 : p == 0) by (apply Qle_antisym; assumption).
        rewrite p0 in Hpc. assert (Z : 0 * c == 0) by ring.
        rewrite Z in Hpc. exact (Qlt_irrefl 0 Hpc). }
      setoid_replace (theta * (p * c)) with (theta * c * p) by ring.
      setoid_replace (p * n) with (n * p) by ring.
      apply Qmult_lt_compat_r; assumption.
  - assert (c0 : c == 0)
      by (apply Qle_antisym; [exact cle | eapply Qle_trans; eassumption]).
    assert (n0 : n == 0)
      by (apply Qle_antisym; [eapply Qle_trans; eassumption | exact Hn]).
    rewrite c0, n0. assert (Z : p * 0 == 0) by ring. split.
    + rewrite Z. setoid_replace (theta * 0) with 0 by ring. apply Qle_refl.
    + intros Hpc. exfalso. rewrite Z in Hpc. exact (Qlt_irrefl 0 Hpc).
Qed.

Lemma point (theta : Q) {X : Type} (iw : X -> Q) (xs : list X)
  (cn vp : X -> bool) (p : Q) :
  nonneg iw xs -> 0 <= p ->
  theta * (p * mass iw xs (fun x => gq theta iw xs cn vp && cn x)) <=
  p * mass iw xs (fun x => vp x && (gq theta iw xs cn vp && cn x)) /\
  (0 < p * mass iw xs (fun x => gq theta iw xs cn vp && cn x) ->
   theta * (p * mass iw xs (fun x => gq theta iw xs cn vp && cn x)) <
   p * mass iw xs (fun x => vp x && (gq theta iw xs cn vp && cn x))).
Proof.
  intros Hi Hp. destruct (gq theta iw xs cn vp) eqn:G.
  - assert (E1 : mass iw xs (fun x => true && cn x) == mass iw xs cn)
      by (apply mass_ext; intros; reflexivity).
    assert (E2 : mass iw xs (fun x => vp x && (true && cn x)) ==
                 mass iw xs (fun x => vp x && cn x))
      by (apply mass_ext; intros; reflexivity).
    rewrite E1, E2. apply num_point.
    + exact Hp.
    + apply mass_nonneg. exact Hi.
    + apply mass_le; [exact Hi|]. intros x _ E.
      apply andb_true_iff in E. exact (proj2 E).
    + unfold gq in G. apply negb_true_iff in G.
      apply Qnot_le_lt. intros Hle. apply Qle_bool_iff in Hle.
      unfold prob in G. rewrite Hle in G. discriminate G.
  - assert (E1 : mass iw xs (fun x => false && cn x) == 0)
      by (unfold mass; apply qsum_zero_of; intros; reflexivity).
    assert (E2 : mass iw xs (fun x => vp x && (false && cn x)) == 0)
      by (unfold mass; apply qsum_zero_of; intros x _; destruct (vp x);
          reflexivity).
    rewrite E1, E2. assert (Z : p * 0 == 0) by ring. split.
    + rewrite Z. setoid_replace (theta * 0) with 0 by ring. apply Qle_refl.
    + intros Hpc. exfalso. rewrite Z in Hpc. exact (Qlt_irrefl 0 Hpc).
Qed.

(* ------------------------------------------------------------------ *)
(* The statements                                                      *)
(* ------------------------------------------------------------------ *)

(* B1_entailed_is_certain.  What is entailed by the hypotheses is certain.  modelSimple of
   sec. 2.1 is the case A = H. *)
Theorem B1_entailed_is_certain :
  forall (W : Type) (prior : W -> Q) (ws : list W) (A H : W -> bool),
    nonneg prior ws -> 0 < mass prior ws H ->
    (forall w, In w ws -> H w = true -> A w = true) ->
    prob prior ws A H == 1.
Proof.
  intros W prior ws A H Hn Hpos Hent. unfold prob.
  assert (E : mass prior ws (fun w => A w && H w) == mass prior ws H).
  { apply mass_ext. intros w Hw. destruct (H w) eqn:Hh.
    - rewrite (Hent w Hw Hh). reflexivity.
    - apply andb_false_r. }
  rewrite E. unfold Qdiv. apply Qmult_inv_r. apply ne_of_lt. exact Hpos.
Qed.

(* B2_monotone.  Probability is monotone along entailment. *)
Theorem B2_monotone :
  forall (W : Type) (prior : W -> Q) (ws : list W) (A B H : W -> bool),
    nonneg prior ws -> 0 < mass prior ws H ->
    (forall w, In w ws -> A w = true -> B w = true) ->
    prob prior ws A H <= prob prior ws B H.
Proof.
  intros W prior ws A B H Hn Hpos Himp. unfold prob, Qdiv.
  apply Qmult_le_compat_r.
  - apply mass_le; [exact Hn|]. intros w Hw E.
    apply andb_true_iff in E. destruct E as [Ea Eh].
    apply andb_true_iff. split; [apply Himp; assumption | exact Eh].
  - apply Qinv_le_0_compat. apply Qlt_le_weak. exact Hpos.
Qed.

(* B3_complement.  A sentence and its negation share the unit. *)
Theorem B3_complement :
  forall (W : Type) (prior : W -> Q) (ws : list W) (A H : W -> bool),
    nonneg prior ws -> 0 < mass prior ws H ->
    0 <= prob prior ws A H /\
    prob prior ws A H + prob prior ws (fun w => negb (A w)) H == 1.
Proof.
  intros W prior ws A H Hn Hpos. unfold prob. split.
  - apply Qdiv_nonneg; apply mass_nonneg; exact Hn.
  - apply add_div; [apply ne_of_lt; exact Hpos | apply mass_split].
Qed.

(* B4_chain.  Two observations in sequence are one joint observation. *)
Theorem B4_chain :
  forall (W : Type) (prior : W -> Q) (ws : list W) (A H1 H2 : W -> bool),
    nonneg prior ws -> 0 < mass prior ws (fun w => H1 w && H2 w) ->
    prob prior ws (fun w => A w && H2 w) H1 ==
    prob prior ws A (fun w => H1 w && H2 w) * prob prior ws H2 H1.
Proof.
  intros W prior ws A H1 H2 Hn Hpos.
  assert (Hpos1 : 0 < mass prior ws H1).
  { eapply Qlt_le_trans; [exact Hpos|]. apply mass_le; [exact Hn|].
    intros w _ E. apply andb_true_iff in E. exact (proj1 E). }
  assert (E1 : mass prior ws (fun w => A w && (H1 w && H2 w)) ==
               mass prior ws (fun w => A w && H2 w && H1 w)).
  { apply mass_ext. intros w _. destruct (A w), (H1 w), (H2 w); reflexivity. }
  assert (E2 : mass prior ws (fun w => H2 w && H1 w) ==
               mass prior ws (fun w => H1 w && H2 w)).
  { apply mass_ext. intros w _. apply andb_comm. }
  unfold prob. cbv beta. rewrite E1, E2.
  field. split; apply ne_of_lt; assumption.
Qed.

(* B5_literal_listener_is_conditioning.  The bridge.  The RSA literal listener, summed over a set of worlds,
   is the probability of that set given that the utterance is true. *)
Theorem B5_literal_listener_is_conditioning :
  forall (W U : Type) (ws : list W) (meaning : U -> W -> bool) (prior : W -> Q)
         (u : U) (A : W -> bool),
    mass (L0 W U ws meaning prior u) ws A == prob prior ws A (meaning u).
Proof.
  intros W U ws meaning prior u A. unfold prob.
  transitivity
    (qsum (map (fun w => (if A w && meaning u w then prior w else 0) /
                         mass prior ws (meaning u)) ws)).
  - unfold mass at 1. apply qsum_map_ext_in. intros w _.
    destruct (A w); simpl.
    + unfold L0. rewrite normalize_spec. unfold L0_raw. reflexivity.
    + unfold Qdiv. ring.
  - exact (qsum_div W (mass prior ws (meaning u))
             (fun w => if A w && meaning u w then prior w else 0) ws).
Qed.

(* B6_uniform_is_counting.  With equal weights on individuals, eq. (2) is eq. (1): a ratio of
   cardinalities. *)
Theorem B6_uniform_is_counting :
  forall (X : Type) (xs : list X) (cn vp : X -> bool),
    prob (fun _ => 1) xs vp cn ==
    inject_Z (Z.of_nat (length (filter (fun x => vp x && cn x) xs))) /
    inject_Z (Z.of_nat (length (filter cn xs))).
Proof.
  intros X xs cn vp. unfold prob, mass.
  rewrite (qsum_indicator X (fun x => vp x && cn x) 1 xs).
  rewrite (qsum_indicator X cn 1 xs).
  rewrite !Qmult_1_l. reflexivity.
Qed.

(* B7_quantifier_supports_instance.  The prediction of sec. 2.4: "if many chairs have four legs, then it
   is likely that any given chair has four legs".  Here "likely" is: more
   probable than the quantifier's threshold. *)
Theorem B7_quantifier_supports_instance :
  forall (theta : Q) (W X : Type) (ws : list W) (xs : list X)
         (prior : W -> Q) (iw : X -> Q) (cn vp : W -> X -> bool),
    nonneg prior ws -> nonneg iw xs ->
    let H := fun p : W * X =>
               gq theta iw xs (cn (fst p)) (vp (fst p)) && cn (fst p) (snd p) in
    0 < mass (joint prior iw) (list_prod ws xs) H ->
    theta < prob (joint prior iw) (list_prod ws xs)
              (fun p => vp (fst p) (snd p)) H.
Proof.
  intros theta W X ws xs prior iw cn vp Hp Hi H Hpos. unfold prob.
  apply Qlt_shift_div_l; [exact Hpos|].
  assert (ED : mass (joint prior iw) (list_prod ws xs) H ==
               qsum (map (fun w => prior w * mass iw xs
                            (fun x => gq theta iw xs (cn w) (vp w) && cn w x))
                         ws))
    by exact (mass_joint prior iw ws xs H).
  assert (EN : mass (joint prior iw) (list_prod ws xs)
                 (fun p => vp (fst p) (snd p) && H p) ==
               qsum (map (fun w => prior w * mass iw xs
                            (fun x => vp w x &&
                               (gq theta iw xs (cn w) (vp w) && cn w x)))
                         ws))
    by exact (mass_joint prior iw ws xs (fun p => vp (fst p) (snd p) && H p)).
  rewrite ED in Hpos. rewrite ED, EN. rewrite <- qsum_scale.
  destruct (qsum_pos_exists _
              (fun d Hd =>
                 match proj1 (in_map_iff _ _ _) Hd with
                 | ex_intro _ w (conj E Hw) =>
                     eq_ind _ (fun q => 0 <= q)
                       (Qmult_le_0_compat _ _ (Hp w Hw)
                          (mass_nonneg iw xs _ Hi)) _ E
                 end) Hpos) as (d & Hd & dpos).
  apply in_map_iff in Hd. destruct Hd as (w0 & <- & Hw0).
  apply (qsum_le_lt_in W _ _ ws w0).
  - intros w Hw.
    exact (proj1 (point theta iw xs (cn w) (vp w) (prior w) Hi (Hp w Hw))).
  - exact Hw0.
  - exact (proj2 (point theta iw xs (cn w0) (vp w0) (prior w0) Hi (Hp w0 Hw0))
             dpos).
Qed.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
Print Assumptions B1_entailed_is_certain.
Print Assumptions B2_monotone.
Print Assumptions B3_complement.
Print Assumptions B4_chain.
Print Assumptions B5_literal_listener_is_conditioning.
Print Assumptions B6_uniform_is_counting.
Print Assumptions B7_quantifier_supports_instance.
Print Assumptions E1_many_has_mass_half.
Print Assumptions E2_before_observing.
Print Assumptions E3_chair_example_1.
Print Assumptions E4_chair_example_2.
Print Assumptions B8_supported_not_entailed_and_inverse_fails.
