(* ========================================================================== *)
(*  Donkey_Sums.v — Donkey anaphora with strong and weak sums                 *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCES
     [L21] Luo, Z. (2021). "On Type-Theoretical Semantics of Donkey
       Anaphora".  The 14-page version on the author's page, whose file
       name indicates LACL 2021; cited by SECTION and FORMULA NUMBER.
       [section 2 (strong and weak sums; (4)-(7)); section 3.1 (the
       proof-irrelevance rule; (9), (10)); section 3.2 ((12), (13), (16),
       (18)); section 4 ((22)-(25)); Appendix B (finite types);
       Appendix D (Most)]
       A shorter version, "Donkey Anaphora: Type-Theoretic Semantics with
       Both Strong and Weak Sums", is in the proceedings of the ESSLLI
       2021 workshop CSTFRS, pp. 45-52.  It is not the text used here.
     [S89] Sundholm, G. (1989). "Constructive Generalized Quantifiers",
       Synthese 79(1): 1-12, as in Ranta_GQ.v.  Used here: injection,
       surjection, bijection and Finite, (10)-(14), p. 5; Most, (23),
       pp. 7-8; the donkey analyses (24)-(26), pp. 8-9; the two ways the
       cardinal of the Sigma type differs from that of the subset type,
       p. 9; A-injections (27) and the choice of counting pairs, p. 10.
     [R94] Ranta, A. (1994). Type-Theoretical Grammar, as in Ranta.v.

   COMPANIONS
     Ranta.v supplies donkey_ctx, he, it and donkey_sentence.  Ranta_GQ.v
     supplies most_c, most_wit and sundholm_donkey_contrast.  The header of
     Ranta_GQ.v lists the choice between counting owner-proof pairs and
     counting owners as not formalized.  This file takes it up.  Neither
     file is changed.

   WHAT IS FORMALIZED
     Part 1  Vocabulary: uniqueness of proofs, complete duplicate-free
             lists, cardinality; list lemmas, including a pigeonhole for
             relations.
     Part 2  "Most" as a proposition ([L21] Appendix D): the literal form
             with an injection from Fin(k), a list form, their agreement,
             and the relation to Sundholm's proof object and to the
             counting quantifier of Ranta_GQ.v.
     Part 3  Cardinality: [L21] (10), a subset type has no more objects
             than its base when the predicate has unique proofs; a
             Type-valued family for which the bound fails ([S89] p. 9,
             first way); fidelity to the bijection with a k-element set.
     Part 4  The donkey sentence: the Sigma type of owner-donkey-proof
             triples ([L21] (5), [S89] (24)); the collection of owners
             with a weak existential ([L21] (13)); the pair, strong and
             weak readings ([L21] (7), (12), (16)); for "every" they
             agree; the strong reading entails the weak; the collection
             counts owners.
     Part 5  Counting forms of the three readings and the proofs that the
             readings on types equal them.
     Part 6  Sundholm's own alternative ([S89] (27)): A-injections; what
             they do and do not count; the map from his pairs to Luo's
             collection; agreement of all readings when nobody owns two
             donkeys.
     Part 7  Combining the two sums ([L21] section 4): the impredicative
             existential (9), the encoding (22) and its strength, and why
             a weak sum with unique proofs has no computing projection.
     Part 8  The weak sum as a truncation ([L21] (23)-(25)), through an
             interface with an axiom-free instance.
     Part 9  A mixed reading ([L21] (17)-(18)).
     Part 10 Models: every boolean model with listed carriers has its
             three readings decided by counting; Luo's ten farmers; a
             model separating the strong from the weak reading; the model
             of Ranta_GQ.sundholm_donkey_contrast.

   NOT FORMALIZED (and why)
     * UTT and Martin-Lof type theory with h-logic as type theories.  The
       inconsistency of large Sigma-propositions and the remark that small
       ones make the existential strong ([L21] section 4) are results
       about those theories.  Part 7 has only a formal shadow of the
       second, [weak_sum_no_projection].
     * General propositional truncation.  Part 8 truncates one family of
       types, the donkeys of each farmer.
     * E-type anaphora ([L21] section 3.3) and other quantifiers such as
       "few".
     * Whether the bound of Part 3 can fail for a proposition.  It is
       proved under uniqueness of proofs and fails for Type-valued
       families; nothing here exhibits two distinct proofs of one
       proposition.
     * Sundholm's objection to his own alternative, that quantifier
       definitions would stop being uniform in their domain ([S89] p. 10).
       It is a claim about definitions across domains.  What is proved is
       that Luo's collection is counted by the one [most_p].
     * The alternative definition of Most in note 4 of [S89].

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   A finite type is given by a complete duplicate-free
                    list ([listing]), as Ranta_GQ.v gives an enumerated
                    CN by a list.  [card_iff_fin] relates this to the
                    bijection with Fin(n) of [L21] Appendix B; its half
                    from a list to functions assumes decidable equality.
     [ARTIFACT-ii]  The collection of owners is stated for any
                    proposition Q equivalent to owning a donkey
                    ([weak_owner_spec]), not only for the literal
                    existential [owner].  A complete list of
                    {x | exists y, own x y} needs the proofs of that
                    existential to be unique.  Rocq proves this when
                    ownership is functional with unique proofs
                    ([functional_owner_proofs_unique]) and leaves it open
                    when someone owns two donkeys.  A boolean owner test
                    has unique proofs outright.
     [ARTIFACT-iii] The models of Part 10 are boolean tables read as
                    propositions.  Their readings on types are decided by
                    counting ([bool_model_readings]).
     [ARTIFACT-iv]  [respects_first] and the results S2 to S4 of Part 6
                    are a reading of [S89] (27).  The paper says that
                    notions such as A-finite can then be defined and does
                    not define them.
     [ARTIFACT-v]   Zero axioms, zero global Parameters.  Every principle
                    a result depends on, such as uniqueness of proofs or
                    the truncation interface, is an explicit premise of
                    that result.  Two results are stated in Type because
                    their content is a pair of functions.
*)

Require Import List Arith Lia Bool Eqdep_dec.
Import ListNotations.
(* The standard library attaches a library warning to its finite types.
   They are used only in Parts 2 and 3, to state fidelity to Fin(n). *)
Set Warnings "-stdlib-vector".
Require Coq.Vectors.Fin.
Set Warnings "stdlib-vector".
Require mtt_ranta.Ranta mtt_ranta.Ranta_GQ.


(* ========================================================================== *)
(*  Part 1 — Vocabulary and list lemmas                                       *)
(* ========================================================================== *)

(* Uniqueness of proofs, pointwise. *)
Definition proofs_unique {A : Type} (Q : A -> Prop) : Prop :=
  forall x (p q : Q x), p = q.

(* [L21] Appendix B, as a list: every object of A occurs exactly once. *)
Definition listing {A : Type} (l : list A) : Prop :=
  NoDup l /\ forall a : A, In a l.

(* |A| = n. *)
Definition card (A : Type) (n : nat) : Prop :=
  exists l : list A, listing l /\ length l = n.

Lemma len_map : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof.
  intros A B f l; induction l as [|a l IH]; cbn;
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) (l : list A),
  (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hf H; induction H as [|a l Hnin Hnd IH]; cbn.
  - constructor.
  - constructor; [|exact IH].
    intro Hin; apply in_map_iff in Hin; destruct Hin as [b [Hb Hbl]].
    apply Hf in Hb; subst b; exact (Hnin Hbl).
Qed.

Lemma NoDup_filter_l : forall (A : Type) (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros A f l H; induction H as [|a l Hnin Hnd IH]; cbn; [constructor|].
  destruct (f a); [|exact IH].
  constructor; [|exact IH].
  intro Hin; apply Hnin; apply filter_In in Hin; exact (proj1 Hin).
Qed.

Lemma proj1_sig_inj : forall (A : Type) (Q : A -> Prop), proofs_unique Q ->
  forall a b : {x : A | Q x}, proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros A Q HQ [x p] [y q] H; cbn in H; subst y.
  rewrite (HQ x p q); reflexivity.
Qed.

Lemma bool_proofs_unique : forall (A : Type) (qb : A -> bool),
  proofs_unique (fun x => qb x = true).
Proof. intros A qb x p q; apply UIP_dec; apply bool_dec. Qed.

Lemma NoDup_list_prod :
  forall (A B : Type) (l : list A) (l' : list B),
    NoDup l -> NoDup l' -> NoDup (list_prod l l').
Proof.
  intros A B l l' Hl Hl'; induction Hl as [|a l Hnin Hnd IH]; cbn;
    [constructor|].
  apply NoDup_app.
  - apply NoDup_map_inj; [|exact Hl']. intros y y' E. injection E. auto.
  - exact IH.
  - intros [x y] Hin Hin'. apply in_map_iff in Hin.
    destruct Hin as [y0 [E _]]. injection E as E1 E2. subst.
    apply in_prod_iff in Hin'. destruct Hin' as [Hx _]. exact (Hnin Hx).
Qed.

(* Two duplicate-free lists matched by an injective map have equal length. *)
Lemma image_length :
  forall (A B : Type) (f : A -> B) (lA : list A) (lB : list B),
    (forall a a', f a = f a' -> a = a') ->
    NoDup lA -> NoDup lB ->
    (forall b, In b lB <-> exists a, In a lA /\ f a = b) ->
    length lA = length lB.
Proof.
  intros A B f lA lB Hf HA HB Him.
  assert (E : length (map f lA) = length lA) by apply len_map.
  apply Nat.le_antisymm.
  - rewrite <- E. apply NoDup_incl_length.
    + apply NoDup_map_inj; assumption.
    + intros b Hb. apply in_map_iff in Hb. destruct Hb as [a [Hab Ha]].
      apply Him. exists a. split; assumption.
  - rewrite <- E. apply NoDup_incl_length; [exact HB|].
    intros b Hb. apply Him in Hb. destruct Hb as [a [Ha Hab]].
    apply in_map_iff. exists a. split; assumption.
Qed.

Lemma preimage_list :
  forall (A B : Type) (f : A -> B) (lA : list A) (w' : list B),
    (forall b, In b w' -> exists a, In a lA /\ f a = b) ->
    exists w : list A, map f w = w' /\ incl w lA.
Proof.
  intros A B f lA w'; induction w' as [|b w' IH]; intros H.
  - exists []. split; [reflexivity | intros x []].
  - destruct (H b (or_introl eq_refl)) as [a [Ha Hab]].
    destruct (IH (fun b' Hb' => H b' (or_intror Hb'))) as [w [Hw Hincl]].
    exists (a :: w). split.
    + cbn. rewrite Hab, Hw. reflexivity.
    + intros x [Hx|Hx]; [subst x; exact Ha | apply Hincl; exact Hx].
Qed.

(* A pigeonhole for relations: no function is needed, only existence. *)
Lemma rel_inj_length :
  forall (C A : Type) (R : C -> A -> Prop) (l1 : list C) (l2 : list A),
    NoDup l1 ->
    (forall c, In c l1 -> exists a, In a l2 /\ R c a) ->
    (forall c c' a, R c a -> R c' a -> c = c') ->
    length l1 <= length l2.
Proof.
  intros C A R l1; induction l1 as [|c l1 IH]; intros l2 Hnd Htot Hinj.
  - cbn. lia.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd'].
    destruct (Htot c (or_introl eq_refl)) as [a [Ha Hca]].
    destruct (in_split a l2 Ha) as [l2a [l2b El2]]. subst l2.
    assert (IH' : length l1 <= length (l2a ++ l2b)).
    { apply IH; [exact Hnd' | | exact Hinj].
      intros c' Hc'. destruct (Htot c' (or_intror Hc')) as [a' [Ha' Hc'a']].
      exists a'. split; [|exact Hc'a'].
      apply in_app_or in Ha'. apply in_or_app.
      destruct Ha' as [Ha'|[Ha'|Ha']].
      - left; exact Ha'.
      - subst a'. exfalso. apply Hnin.
        rewrite (Hinj c c' a Hca Hc'a'). exact Hc'.
      - right; exact Ha'. }
    rewrite length_app in IH'. rewrite length_app. cbn. lia.
Qed.

Lemma rel_bij_length :
  forall (C A : Type) (R : C -> A -> Prop) (l1 : list C) (l2 : list A),
    NoDup l1 -> NoDup l2 ->
    (forall c, In c l1 -> exists a, In a l2 /\ R c a) ->
    (forall a, In a l2 -> exists c, In c l1 /\ R c a) ->
    (forall c c' a, R c a -> R c' a -> c = c') ->
    (forall c a a', R c a -> R c a' -> a = a') ->
    length l1 = length l2.
Proof.
  intros C A R l1 l2 H1 H2 Ht1 Ht2 Hi Hf. apply Nat.le_antisymm.
  - apply (rel_inj_length C A R); assumption.
  - apply (rel_inj_length A C (fun a c => R c a)); [exact H2 | exact Ht2 |].
    intros a a' c Ha Ha'. exact (Hf c a a' Ha Ha').
Qed.

(* Added here.  The elements of l that pass a boolean test, each packaged with
   its proof. *)
Fixpoint sig_filter {A : Type} (qb : A -> bool) (l : list A)
  : list {x : A | qb x = true} :=
  match l with
  | [] => []
  | a :: l' =>
      match bool_dec (qb a) true with
      | left e => exist _ a e :: sig_filter qb l'
      | right _ => sig_filter qb l'
      end
  end.

Lemma sig_filter_proj : forall (A : Type) (qb : A -> bool) (l : list A),
  map (@proj1_sig A (fun x => qb x = true)) (sig_filter qb l) = filter qb l.
Proof.
  intros A qb l; induction l as [|a l IH]; cbn; [reflexivity|].
  destruct (bool_dec (qb a) true) as [e|n]; cbn.
  - rewrite e, IH; reflexivity.
  - rewrite IH; destruct (qb a);
      [exfalso; apply n; reflexivity | reflexivity].
Qed.

(* The base list need only contain the objects that pass the test.  This is
   what lets a bounded carrier be listed from a list of numbers. *)
Theorem sig_filter_listing_gen :
  forall (A : Type) (qb : A -> bool) (lA : list A),
    NoDup lA -> (forall a, qb a = true -> In a lA) ->
    listing (sig_filter qb lA).
Proof.
  intros A qb lA Hnd Hall; split.
  - apply (NoDup_map_inv (@proj1_sig A (fun x => qb x = true))).
    rewrite sig_filter_proj; apply NoDup_filter_l; exact Hnd.
  - intros [x e].
    assert (Hin : In x (filter qb lA))
      by (apply filter_In; split; [apply Hall; exact e | exact e]).
    rewrite <- sig_filter_proj in Hin; apply in_map_iff in Hin.
    destruct Hin as [[x' e'] [Hx Hin]]; cbn in Hx; subst x'.
    rewrite (bool_proofs_unique A qb x e e'); exact Hin.
Qed.

Theorem sig_filter_listing : forall (A : Type) (qb : A -> bool) (lA : list A),
  listing lA -> listing (sig_filter qb lA).
Proof.
  intros A qb lA [Hnd Hall]; apply sig_filter_listing_gen;
    [exact Hnd | intros a _; apply Hall].
Qed.

(* The premises of [card_subset_le] and [weak_collection_counts_owners]
   hold for every boolean predicate on a listed type, and the weak
   collection then has as many objects as the filter. *)
Theorem unique_proofs_instance :
  forall (A : Type) (qb : A -> bool) (lA : list A),
    listing lA ->
    proofs_unique (fun x => qb x = true) /\
    listing (sig_filter qb lA) /\
    length (sig_filter qb lA) = length (filter qb lA).
Proof.
  intros A qb lA H; split; [apply bool_proofs_unique|].
  split; [apply sig_filter_listing; exact H|].
  rewrite <- sig_filter_proj; symmetry; apply len_map.
Qed.

(* ========================================================================== *)
(*  Part 2 — "Most" as a proposition ([L21] Appendix D; [S89] (23))           *)
(* ========================================================================== *)

(* The literal form: some k at least [n/2]+1 and an injection Fin(k) -> A
   all of whose values satisfy P.  Every quantifier is the weak one. *)
Definition most_fin (A : Type) (nA : nat) (P : A -> Prop) : Prop :=
  exists k : nat, k >= Nat.div nA 2 + 1 /\
  exists f : Fin.t k -> A,
    (forall i j : Fin.t k, f i = f j -> i = j) /\ forall i : Fin.t k, P (f i).

(* The list form used below. *)
Definition most_p {A : Type} (dom : list A) (P : A -> Prop) : Prop :=
  exists w : list A,
    NoDup w /\ incl w dom /\ 2 * length w > length dom /\
    forall x, In x w -> P x.

Lemma most_p_mono : forall (A : Type) (dom : list A) (P Q : A -> Prop),
  (forall x, P x -> Q x) -> most_p dom P -> most_p dom Q.
Proof.
  intros A dom P Q H [w [Hnd [Hincl [Hlen Hall]]]].
  exists w; split; [exact Hnd | split; [exact Hincl | split; [exact Hlen|]]].
  intros x Hx; apply H; apply Hall; exact Hx.
Qed.

(* "Most" is transported along such a matching. *)
Lemma most_p_map :
  forall (A B : Type) (f : A -> B) (lA : list A) (lB : list B)
         (P : A -> Prop) (R : B -> Prop),
    (forall a a', f a = f a' -> a = a') ->
    NoDup lA -> NoDup lB ->
    (forall b, In b lB <-> exists a, In a lA /\ f a = b) ->
    (forall a, In a lA -> (P a <-> R (f a))) ->
    (most_p lA P <-> most_p lB R).
Proof.
  intros A B f lA lB P R Hf HA HB Him HPR.
  assert (Hlen : length lA = length lB)
    by (apply (image_length A B f); assumption).
  split.
  - intros [w [Hnd [Hincl [Hsz Hall]]]].
    exists (map f w). split; [apply NoDup_map_inj; assumption|].
    split.
    + intros b Hb. apply in_map_iff in Hb. destruct Hb as [a [Hab Ha]].
      apply Him. exists a. split; [apply Hincl; exact Ha | exact Hab].
    + split.
      * rewrite (len_map A B f w). lia.
      * intros b Hb. apply in_map_iff in Hb. destruct Hb as [a [Hab Ha]].
        subst b. apply HPR; [apply Hincl; exact Ha | apply Hall; exact Ha].
  - intros [w' [Hnd [Hincl [Hsz Hall]]]].
    destruct (preimage_list A B f lA w') as [w [Hw Hwin]].
    { intros b Hb. apply Him. apply Hincl. exact Hb. }
    assert (Elen : length w = length w')
      by (rewrite <- Hw; symmetry; apply len_map).
    exists w. split.
    + apply (NoDup_map_inv f). rewrite Hw. exact Hnd.
    + split; [exact Hwin|]. split.
      * lia.
      * intros a Ha. apply HPR; [apply Hwin; exact Ha|].
        apply Hall. rewrite <- Hw. apply in_map. exact Ha.
Qed.

(* [most_p] is Sundholm's proof object with its Sigma replaced by the weak
   existential: [L21] section 3.2 describes Most this way. *)
Theorem most_p_squashes_sundholm :
  forall (A : Type) (dom : list A) (P : A -> Prop),
    most_p dom P <-> inhabited (Ranta_GQ.most_wit A dom P).
Proof.
  intros A dom P; split.
  - intros [w [Hnd [Hincl [Hlen Hall]]]]; constructor; exists w.
    split; [split; assumption | split; assumption].
  - intros [[w [[Hnd Hincl] [Hlen Hall]]]]; exists w.
    split; [exact Hnd | split; [exact Hincl | split; [exact Hlen | exact Hall]]].
Qed.

(* On a decidable predicate it is the counting quantifier of Ranta_GQ. *)
Theorem most_p_counting :
  forall (A : Type) (dom : list A) (p : A -> bool),
    NoDup dom ->
    (most_p dom (fun x => p x = true) <-> Ranta_GQ.most_c A dom p).
Proof.
  intros A dom p Hnd; split.
  - intros H; apply most_p_squashes_sundholm in H; destruct H as [W].
    exact (Ranta_GQ.most_wit_counts _ _ _ W).
  - intros H; apply most_p_squashes_sundholm; constructor.
    exact (Ranta_GQ.most_counts_wit _ _ _ Hnd H).
Qed.

Fixpoint fin_list (k : nat) : list (Fin.t k) :=
  match k with
  | 0 => []
  | S k' => Fin.F1 :: map Fin.FS (fin_list k')
  end.

Lemma fin_list_length : forall k, length (fin_list k) = k.
Proof.
  induction k as [|k IH]; cbn; [reflexivity|].
  rewrite (len_map _ _ Fin.FS (fin_list k)), IH. reflexivity.
Qed.

Lemma fin_list_complete : forall k (i : Fin.t k), In i (fin_list k).
Proof.
  intros k i; induction i as [n|n i IH]; cbn;
    [left; reflexivity | right; apply in_map; exact IH].
Qed.

Lemma fin_list_NoDup : forall k, NoDup (fin_list k).
Proof.
  induction k as [|k IH]; cbn; constructor.
  - intros H. apply in_map_iff in H. destruct H as [x [E _]]. discriminate E.
  - apply NoDup_map_inj; [|exact IH]. intros a b E. apply Fin.FS_inj. exact E.
Qed.

Lemma two_k_gt : forall n k, k >= n / 2 + 1 -> 2 * k > n.
Proof.
  intros n k H. pose proof (Nat.mul_succ_div_gt n 2 (Nat.neq_succ_0 1)) as G.
  remember (n / 2) as q eqn:Eq. clear Eq. lia.
Qed.

Lemma k_ge : forall n k, 2 * k > n -> k >= n / 2 + 1.
Proof.
  intros n k H.
  assert (G : n / 2 < k) by (apply Nat.Div0.div_lt_upper_bound; lia).
  remember (n / 2) as q eqn:Eq. clear Eq. lia.
Qed.

Theorem most_fin_iff_most_p :
  forall (A : Type) (dom : list A) (P : A -> Prop),
    listing dom -> (most_fin A (length dom) P <-> most_p dom P).
Proof.
  intros A dom P [Hnd Hall]; split.
  - intros [k [Hk [f [Hf HP]]]].
    exists (map f (fin_list k)). split.
    + apply NoDup_map_inj; [exact Hf | apply fin_list_NoDup].
    + split; [intros a _; apply Hall|]. split.
      * rewrite (len_map _ _ f (fin_list k)), fin_list_length.
        apply two_k_gt. exact Hk.
      * intros a Ha. apply in_map_iff in Ha. destruct Ha as [i [E _]].
        subst a. apply HP.
  - intros [w [Hw [Hincl [Hsz HP]]]].
    destruct w as [|a0 w'].
    + cbn in Hsz. lia.
    + remember (a0 :: w') as w eqn:Ew.
      exists (length w). split; [apply k_ge; exact Hsz|].
      exists (fun i : Fin.t (length w) => nth (proj1_sig (Fin.to_nat i)) w a0).
      split.
      * intros i j E. apply Fin.to_nat_inj.
        apply (proj1 (NoDup_nth w a0) Hw);
          [exact (proj2_sig (Fin.to_nat i)) | exact (proj2_sig (Fin.to_nat j))
          | exact E].
      * intros i. apply HP. apply nth_In. exact (proj2_sig (Fin.to_nat i)).
Qed.

(* ========================================================================== *)
(*  Part 3 — Cardinality ([L21] (10), Appendix B; [S89] p. 9)                 *)
(* ========================================================================== *)

(* [L21] (10): |Sigma x:A. Q(x)| <= |A| when Q has at most one proof. *)
Theorem card_subset_le :
  forall (A : Type) (Q : A -> Prop), proofs_unique Q ->
  forall (lA : list A) (lS : list {x : A | Q x}),
    listing lA -> listing lS -> length lS <= length lA.
Proof.
  intros A Q HQ lA lS [_ HA] [HS _].
  assert (E : length (map (@proj1_sig A Q) lS) = length lS) by apply len_map.
  rewrite <- E.
  apply NoDup_incl_length.
  - apply NoDup_map_inj; [apply proj1_sig_inj; exact HQ | exact HS].
  - intros x _; apply HA.
Qed.

(* For a TYPE-valued family the bound fails: over one object, a family
   with two objects gives a Sigma type of size two.  [S89] p. 9 names
   several proof objects as the first way the count can differ; [L21]
   section 2 as the reason |F_Sigma| >= 29 is an inequality.
   Scope: this does NOT show that the premise of [card_subset_le] is
   necessary.  Rocq does not exhibit two distinguishable proofs of a
   proposition, so whether that bound holds without its premise is left
   open here. *)
Theorem type_valued_fibres_can_increase_cardinality :
  exists (A : Type) (Q : A -> Type) (lA : list A) (lS : list {x : A & Q x}),
    listing lA /\ listing lS /\ length lS > length lA.
Proof.
  exists unit, (fun _ => bool), [tt],
    [existT (fun _ : unit => bool) tt true;
     existT (fun _ : unit => bool) tt false].
  split; [split | split; [split|]].
  - constructor; [intros [] | constructor].
  - intros []; left; reflexivity.
  - constructor.
    + intros [H|[]].
      assert (E := f_equal (fun s : {x : unit & bool} => projT2 s) H).
      cbn in E; discriminate E.
    + constructor; [intros [] | constructor].
  - intros [[] [|]]; cbn; auto.
  - cbn; lia.
Qed.

Fixpoint index_of {A : Type} (dec : forall a b : A, {a = b} + {a <> b})
  (a : A) (l : list A) : nat :=
  match l with
  | [] => 0
  | b :: l' => if dec a b then 0 else S (index_of dec a l')
  end.

Lemma index_of_lt :
  forall (A : Type) (dec : forall a b : A, {a = b} + {a <> b}) (a : A)
         (l : list A), In a l -> index_of dec a l < length l.
Proof.
  intros A dec a l; induction l as [|b l IH]; intros H; [destruct H|].
  cbn. destruct (dec a b) as [E|N]; [lia|].
  destruct H as [H|H]; [exfalso; apply N; symmetry; exact H|].
  specialize (IH H). lia.
Qed.

Lemma index_of_nth :
  forall (A : Type) (dec : forall a b : A, {a = b} + {a <> b}) (a : A)
         (l : list A) (d : A), In a l -> nth (index_of dec a l) l d = a.
Proof.
  intros A dec a l d; induction l as [|b l IH]; intros H; [destruct H|].
  cbn. destruct (dec a b) as [E|N]; [symmetry; exact E|].
  destruct H as [H|H]; [exfalso; apply N; symmetry; exact H|].
  exact (IH H).
Qed.

Lemma index_of_nth_inv :
  forall (A : Type) (dec : forall a b : A, {a = b} + {a <> b})
         (l : list A) (d : A) (i : nat),
    NoDup l -> i < length l -> index_of dec (nth i l d) l = i.
Proof.
  intros A dec l d; induction l as [|b l IH]; intros i Hnd Hi;
    [cbn in Hi; lia|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd].
  destruct i as [|i]; cbn.
  - destruct (dec b b) as [_|N]; [reflexivity | exfalso; apply N; reflexivity].
  - cbn in Hi. destruct (dec (nth i l d) b) as [E|N].
    + exfalso. apply Hnin. rewrite <- E. apply nth_In. lia.
    + rewrite (IH i Hnd); [reflexivity | lia].
Qed.

(* Fidelity of [card] to the Fin(n) bijection of Appendix B.  The second
   half takes decidable equality as a premise: computing the position of an
   object in a list needs it. *)
Theorem card_iff_fin :
  forall (A : Type) (n : nat),
    ((exists (f : Fin.t n -> A) (g : A -> Fin.t n),
        (forall i, g (f i) = i) /\ (forall a, f (g a) = a)) -> card A n) /\
    ((forall a b : A, {a = b} + {a <> b}) -> card A n ->
      exists (f : Fin.t n -> A) (g : A -> Fin.t n),
        (forall i, g (f i) = i) /\ (forall a, f (g a) = a)).
Proof.
  intros A n; split.
  - intros [f [g [Hgf Hfg]]]. exists (map f (fin_list n)). split; [split|].
    + apply NoDup_map_inj; [|apply fin_list_NoDup].
      intros i j E. rewrite <- (Hgf i), <- (Hgf j), E. reflexivity.
    + intros a. rewrite <- (Hfg a). apply in_map. apply fin_list_complete.
    + rewrite (len_map _ _ f (fin_list n)). apply fin_list_length.
  - intros Hdec [l [[Hnd Hall] Hlen]]. subst n.
    destruct l as [|a0 l'].
    + exists (fun i : Fin.t 0 => Fin.case0 (fun _ => A) i).
      exists (fun a : A => match Hall a with end).
      split; [intros i; exact (Fin.case0 _ i) | intros a; destruct (Hall a)].
    + remember (a0 :: l') as l eqn:El.
      exists (fun i : Fin.t (length l) => nth (proj1_sig (Fin.to_nat i)) l a0).
      exists (fun a : A => Fin.of_nat_lt (index_of_lt A Hdec a l (Hall a))).
      split.
      * intros i. apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat. cbn.
        apply index_of_nth_inv; [exact Hnd | exact (proj2_sig (Fin.to_nat i))].
      * intros a. rewrite Fin.to_nat_of_nat. cbn.
        apply index_of_nth. apply Hall.
Qed.

(* ========================================================================== *)
(*  Part 4 — The donkey sentence with strong and weak sums                    *)
(* ========================================================================== *)

(* [L21] (5), [S89] (24): owner-donkey-proof triples.  This is Ranta's
   context, already in the atlas. *)
Definition FSig (F D : Type) (own : F -> D -> Prop) : Type :=
  Ranta.donkey_ctx F D own.

(* [L21] (13): the weak existential. *)
Definition owner {F D : Type} (own : F -> D -> Prop) (x : F) : Prop :=
  exists y : D, own x y.

(* The weak collection over any proposition Q; see ARTIFACT-ii in the header. *)
Definition FW {F : Type} (Q : F -> Prop) : Type := {x : F | Q x}.

Definition FEx {F D : Type} (own : F -> D -> Prop) : Type := FW (owner own).

Definition weak_owner_spec {F D : Type} (own : F -> D -> Prop) (Q : F -> Prop)
  : Prop := forall x, Q x <-> owner own x.

(* The donkeys of x: the second Sigma of [L21] (12). *)
Definition owned {F D : Type} (own : F -> D -> Prop) (x : F) : Type :=
  {y : D | own x y}.

Definition pair_scope {F D : Type} (own beat : F -> D -> Prop)
  (z : FSig F D own) : Prop :=
  beat (Ranta.he F D own z) (Ranta.it F D own z).

Definition strong_scope {F D : Type} (own beat : F -> D -> Prop)
  (Q : F -> Prop) (z : FW Q) : Prop :=
  forall y' : owned own (proj1_sig z), beat (proj1_sig z) (proj1_sig y').

Definition weak_scope {F D : Type} (own beat : F -> D -> Prop)
  (Q : F -> Prop) (z : FW Q) : Prop :=
  exists y' : owned own (proj1_sig z), beat (proj1_sig z) (proj1_sig y').

(* [L21] (7) and [S89] (26): Most over the pairs. *)
Definition most_pair {F D : Type} (own beat : F -> D -> Prop)
  (lS : list (FSig F D own)) : Prop := most_p lS (pair_scope own beat).

(* [L21] (12): the strong reading. *)
Definition most_strong {F D : Type} (own beat : F -> D -> Prop)
  (Q : F -> Prop) (lW : list (FW Q)) : Prop :=
  most_p lW (strong_scope own beat Q).

(* [L21] (16): the weak reading. *)
Definition most_weak {F D : Type} (own beat : F -> D -> Prop)
  (Q : F -> Prop) (lW : list (FW Q)) : Prop :=
  most_p lW (weak_scope own beat Q).

(* Definitional check: the universal sentence over the pairs, [L21] (4),
   IS Ranta's donkey sentence. *)
Example pair_every_is_ranta :
  forall (F D : Type) (own beat : F -> D -> Prop),
    @eq Type (forall z : FSig F D own, pair_scope own beat z)
             (Ranta.donkey_sentence F D own beat).
Proof. intros; reflexivity. Qed.

Definition own_proofs_unique {F D : Type} (own : F -> D -> Prop) : Prop :=
  forall x y (p q : own x y), p = q.

Definition functional_own {F D : Type} (own : F -> D -> Prop) : Prop :=
  forall x y1 y2, own x y1 -> own x y2 -> y1 = y2.

Definition reflects {F D : Type} (R : F -> D -> Prop) (rb : F -> D -> bool)
  : Prop := forall x y, rb x y = true <-> R x y.

(* D0.  When nobody owns two donkeys and ownership has unique
   proofs, the literal existential has unique proofs too.  So the premise
   [proofs_unique Q] is an extra assumption only where the two counts can
   differ. *)
Theorem functional_owner_proofs_unique :
  forall (F D : Type) (own : F -> D -> Prop),
    functional_own own -> own_proofs_unique own ->
    proofs_unique (owner own).
Proof.
  intros F D own Hf HU x [y o] [y' o'].
  assert (E : y = y') by exact (Hf x y y' o o').
  subst y'. rewrite (HU x y o o'). reflexivity.
Qed.

(* D1.  For "every" the double role of Sigma is harmless: the pair
   reading, the strong reading and the doubly universal sentence agree.
   Compare Ranta.donkey_curry and [S89] p. 8 on (24) and (25). *)
Theorem every_readings_agree :
  forall (F D : Type) (own beat : F -> D -> Prop) (Q : F -> Prop),
    weak_owner_spec own Q ->
    ((forall z : FSig F D own, pair_scope own beat z) <->
     (forall z : FW Q, strong_scope own beat Q z)) /\
    ((forall z : FW Q, strong_scope own beat Q z) <->
     (forall x y, own x y -> beat x y)).
Proof.
  intros F D own beat Q HQ; unfold pair_scope, strong_scope; split; split.
  - intros H [x q] [y o]; cbn.
    exact (H (existT (fun x => {y : D & own x y}) x
                (existT (fun y => own x y) y o))).
  - intros H [x [y o]].
    exact (H (exist _ x (proj2 (HQ x) (ex_intro _ y o))) (exist _ y o)).
  - intros H x y o.
    exact (H (exist _ x (proj2 (HQ x) (ex_intro _ y o))) (exist _ y o)).
  - intros H [x q] [y o]; cbn. exact (H x y o).
Qed.

(* D2.  The strong reading entails the weak one. *)
Theorem strong_implies_weak :
  forall (F D : Type) (own beat : F -> D -> Prop) (Q : F -> Prop),
    weak_owner_spec own Q ->
    forall lW : list (FW Q),
      most_strong own beat Q lW -> most_weak own beat Q lW.
Proof.
  intros F D own beat Q HQ lW; unfold most_strong, most_weak.
  apply most_p_mono.
  intros [x q] Hs; unfold strong_scope, weak_scope in *; cbn in *.
  destruct (proj1 (HQ x) q) as [y o].
  exists (exist _ y o); exact (Hs (exist _ y o)).
Qed.

(* D3.  The weak collection counts owners ([L21] section 3.2). *)
Theorem weak_collection_counts_owners :
  forall (F D : Type) (own : F -> D -> Prop) (Q : F -> Prop),
    weak_owner_spec own Q -> proofs_unique Q ->
    forall (lF : list F) (lW : list (FW Q)) (ownerb : F -> bool),
      listing lF -> listing lW ->
      (forall x, ownerb x = true <-> owner own x) ->
      length lW = length (filter ownerb lF).
Proof.
  intros F D own Q HQ HU lF lW ownerb [HndF HallF] [HndW HallW] Hb.
  assert (E : length (map (@proj1_sig F Q) lW) = length lW) by apply len_map.
  apply Nat.le_antisymm.
  - rewrite <- E.
    apply NoDup_incl_length.
    + apply NoDup_map_inj; [apply proj1_sig_inj; exact HU | exact HndW].
    + intros x Hx; apply in_map_iff in Hx.
      destruct Hx as [[x' q] [Hx' _]]; cbn in Hx'; subst x'.
      apply filter_In; split; [apply HallF|].
      apply Hb; apply HQ; exact q.
  - rewrite <- E.
    apply NoDup_incl_length.
    + apply NoDup_filter_l; exact HndF.
    + intros x Hx; apply filter_In in Hx; destruct Hx as [_ Hx].
      apply Hb in Hx; apply HQ in Hx.
      apply in_map_iff; exists (exist _ x Hx); split;
        [reflexivity | apply HallW].
Qed.

(* ========================================================================== *)
(*  Part 5 — Counting forms of the readings, and the bridges                  *)
(* ========================================================================== *)

Definition ownerb_of {F D : Type} (ownb : F -> D -> bool) (dD : list D)
  (x : F) : bool := existsb (ownb x) dD.

Definition strongb_of {F D : Type} (ownb beatb : F -> D -> bool)
  (dD : list D) (x : F) : bool :=
  forallb (fun y => implb (ownb x y) (beatb x y)) dD.

Definition weakb_of {F D : Type} (ownb beatb : F -> D -> bool)
  (dD : list D) (x : F) : bool :=
  existsb (fun y => ownb x y && beatb x y) dD.

Definition pairs_of {F D : Type} (ownb : F -> D -> bool) (dF : list F)
  (dD : list D) : list (F * D) :=
  filter (fun z => ownb (fst z) (snd z)) (list_prod dF dD).

Definition owners_of {F D : Type} (ownb : F -> D -> bool) (dF : list F)
  (dD : list D) : list F := filter (ownerb_of ownb dD) dF.

Definition pair_reading_c {F D : Type} (ownb beatb : F -> D -> bool)
  (dF : list F) (dD : list D) : Prop :=
  Ranta_GQ.most_c (F * D)%type (pairs_of ownb dF dD)
    (fun z => beatb (fst z) (snd z)).

Definition strong_reading_c {F D : Type} (ownb beatb : F -> D -> bool)
  (dF : list F) (dD : list D) : Prop :=
  Ranta_GQ.most_c F (owners_of ownb dF dD) (strongb_of ownb beatb dD).

Definition weak_reading_c {F D : Type} (ownb beatb : F -> D -> bool)
  (dF : list F) (dD : list D) : Prop :=
  Ranta_GQ.most_c F (owners_of ownb dF dD) (weakb_of ownb beatb dD).

Lemma implb_true :
  forall a b : bool, implb a b = true <-> (a = true -> b = true).
Proof.
  intros a b; destruct a, b; cbn; split; intro H.
  - intros _; reflexivity.
  - reflexivity.
  - discriminate H.
  - exact (H eq_refl).
  - intro K; discriminate K.
  - reflexivity.
  - intro K; exact K.
  - reflexivity.
Qed.

Lemma ownerb_spec :
  forall (F D : Type) (own : F -> D -> Prop) (ownb : F -> D -> bool),
    reflects own ownb -> forall lD : list D, listing lD ->
    forall x, ownerb_of ownb lD x = true <-> owner own x.
Proof.
  intros F D own ownb Hown lD HlD x; unfold ownerb_of, owner; split.
  - intros H; apply existsb_exists in H; destruct H as [y [_ Hy]].
    exists y; apply Hown; exact Hy.
  - intros [y Hy]; apply existsb_exists; exists y; split;
      [apply (proj2 HlD) | apply Hown; exact Hy].
Qed.

Lemma strongb_spec :
  forall (F D : Type) (own beat : F -> D -> Prop) (ownb beatb : F -> D -> bool),
    reflects own ownb -> reflects beat beatb ->
    forall lD : list D, listing lD ->
    forall x, strongb_of ownb beatb lD x = true <->
              (forall y, own x y -> beat x y).
Proof.
  intros F D own beat ownb beatb Hown Hbeat lD HlD x; unfold strongb_of; split.
  - intros H y Ho.
    pose proof (proj1 (forallb_forall _ _) H y (proj2 HlD y)) as Hy.
    apply Hbeat. apply (proj1 (implb_true _ _) Hy). apply Hown; exact Ho.
  - intros H. apply forallb_forall. intros y _. apply implb_true.
    intros Ho. apply Hbeat. apply H. apply Hown; exact Ho.
Qed.

Lemma weakb_spec :
  forall (F D : Type) (own beat : F -> D -> Prop) (ownb beatb : F -> D -> bool),
    reflects own ownb -> reflects beat beatb ->
    forall lD : list D, listing lD ->
    forall x, weakb_of ownb beatb lD x = true <->
              (exists y, own x y /\ beat x y).
Proof.
  intros F D own beat ownb beatb Hown Hbeat lD HlD x; unfold weakb_of; split.
  - intros H. apply existsb_exists in H. destruct H as [y [_ Hy]].
    apply andb_true_iff in Hy. destruct Hy as [Ho Hb].
    exists y; split; [apply Hown; exact Ho | apply Hbeat; exact Hb].
  - intros [y [Ho Hb]]. apply existsb_exists. exists y; split;
      [apply (proj2 HlD)|].
    apply andb_true_iff; split; [apply Hown; exact Ho | apply Hbeat; exact Hb].
Qed.

Lemma owners_image :
  forall (F D : Type) (own : F -> D -> Prop) (ownb : F -> D -> bool)
         (Q : F -> Prop) (lF : list F) (lD : list D) (lW : list (FW Q)),
    reflects own ownb -> weak_owner_spec own Q ->
    listing lF -> listing lD -> listing lW ->
    forall b, In b (owners_of ownb lF lD) <->
              exists a, In a lW /\ proj1_sig a = b.
Proof.
  intros F D own ownb Q lF lD lW Hown HQ HlF HlD HlW b; unfold owners_of; split.
  - intros Hb. apply filter_In in Hb. destruct Hb as [_ Hb].
    apply (ownerb_spec F D own ownb Hown lD HlD) in Hb. apply HQ in Hb.
    exists (exist Q b Hb). split; [apply (proj2 HlW) | reflexivity].
  - intros [[x q] [_ E]]. cbn in E. subst b.
    apply filter_In. split; [apply (proj2 HlF)|].
    apply (ownerb_spec F D own ownb Hown lD HlD). apply HQ. exact q.
Qed.

Lemma FSig_key_inj :
  forall (F D : Type) (own : F -> D -> Prop), own_proofs_unique own ->
  forall z z' : FSig F D own,
    (Ranta.he F D own z, Ranta.it F D own z) =
    (Ranta.he F D own z', Ranta.it F D own z') -> z = z'.
Proof.
  intros F D own HU [x [y o]] [x' [y' o']] E.
  unfold Ranta.he, Ranta.it in E. cbn in E.
  injection E as E1 E2. subst x' y'. rewrite (HU x y o o'). reflexivity.
Qed.

Lemma pairs_image :
  forall (F D : Type) (own : F -> D -> Prop) (ownb : F -> D -> bool)
         (lF : list F) (lD : list D) (lS : list (FSig F D own)),
    reflects own ownb -> listing lF -> listing lD -> listing lS ->
    forall b, In b (pairs_of ownb lF lD) <->
              exists z, In z lS /\
                        (Ranta.he F D own z, Ranta.it F D own z) = b.
Proof.
  intros F D own ownb lF lD lS Hown HlF HlD HlS [x y]; unfold pairs_of; split.
  - intros Hb. apply filter_In in Hb. destruct Hb as [_ Hb]. cbn in Hb.
    apply Hown in Hb.
    exists (existT (fun x => {y : D & own x y}) x
              (existT (fun y => own x y) y Hb)).
    split; [apply (proj2 HlS) | reflexivity].
  - intros [[x' [y' o]] [_ E]]. unfold Ranta.he, Ranta.it in E. cbn in E.
    injection E as E1 E2. subst x' y'.
    apply filter_In. split.
    + apply in_prod_iff. split; [apply (proj2 HlF) | apply (proj2 HlD)].
    + cbn. apply Hown. exact o.
Qed.

(* D4.  The strong collection counts owner-donkey pairs ([S89] p. 9,
   second way; [L21] section 2), once proofs of ownership are unique. *)
Theorem strong_collection_counts_pairs :
  forall (F D : Type) (own : F -> D -> Prop) (ownb : F -> D -> bool),
    reflects own ownb -> own_proofs_unique own ->
    forall (lF : list F) (lD : list D) (lS : list (FSig F D own)),
      listing lF -> listing lD -> listing lS ->
      length lS =
      length (filter (fun z => ownb (fst z) (snd z)) (list_prod lF lD)).
Proof.
  intros F D own ownb Hown HU lF lD lS HlF HlD HlS.
  apply (image_length (FSig F D own) (F * D)
           (fun z => (Ranta.he F D own z, Ranta.it F D own z))).
  - apply FSig_key_inj; exact HU.
  - exact (proj1 HlS).
  - apply NoDup_filter_l.
    apply NoDup_list_prod; [exact (proj1 HlF) | exact (proj1 HlD)].
  - apply (pairs_image F D own ownb lF lD lS); assumption.
Qed.

(* D5-D7.  Each type-level reading equals its counting form.  These
   justify computing the examples of Part 10 by counting. *)
Theorem pair_counting_form :
  forall (F D : Type) (own beat : F -> D -> Prop) (ownb beatb : F -> D -> bool),
    reflects own ownb -> reflects beat beatb -> own_proofs_unique own ->
    forall (lF : list F) (lD : list D) (lS : list (FSig F D own)),
      listing lF -> listing lD -> listing lS ->
      (most_pair own beat lS <-> pair_reading_c ownb beatb lF lD).
Proof.
  intros F D own beat ownb beatb Hown Hbeat HU lF lD lS HlF HlD HlS.
  assert (HndB : NoDup (pairs_of ownb lF lD)).
  { unfold pairs_of. apply NoDup_filter_l.
    apply NoDup_list_prod; [exact (proj1 HlF) | exact (proj1 HlD)]. }
  assert (Hmap : most_p lS (pair_scope own beat) <->
                 most_p (pairs_of ownb lF lD)
                        (fun p => beatb (fst p) (snd p) = true)).
  { apply (most_p_map (FSig F D own) (F * D)
             (fun z => (Ranta.he F D own z, Ranta.it F D own z))).
    - apply FSig_key_inj. exact HU.
    - exact (proj1 HlS).
    - exact HndB.
    - apply (pairs_image F D own ownb lF lD lS); assumption.
    - intros z _. unfold pair_scope. cbn. split; intro H; apply Hbeat; exact H. }
  pose proof (most_p_counting (F * D)%type (pairs_of ownb lF lD)
                (fun p => beatb (fst p) (snd p)) HndB) as Hc.
  unfold most_pair, pair_reading_c. split; intro H.
  - apply Hc. apply Hmap. exact H.
  - apply Hmap. apply Hc. exact H.
Qed.

(* D6.  The strong reading on types equals its counting form
   ([L21] (12)). *)
Theorem strong_counting_form :
  forall (F D : Type) (own beat : F -> D -> Prop) (ownb beatb : F -> D -> bool)
         (Q : F -> Prop),
    reflects own ownb -> reflects beat beatb ->
    weak_owner_spec own Q -> proofs_unique Q ->
    forall (lF : list F) (lD : list D) (lW : list (FW Q)),
      listing lF -> listing lD -> listing lW ->
      (most_strong own beat Q lW <-> strong_reading_c ownb beatb lF lD).
Proof.
  intros F D own beat ownb beatb Q Hown Hbeat HQ HU lF lD lW HlF HlD HlW.
  assert (HndB : NoDup (owners_of ownb lF lD))
    by (unfold owners_of; apply NoDup_filter_l; exact (proj1 HlF)).
  assert (Hmap : most_p lW (strong_scope own beat Q) <->
                 most_p (owners_of ownb lF lD)
                        (fun x => strongb_of ownb beatb lD x = true)).
  { apply (most_p_map (FW Q) F (@proj1_sig F Q)).
    - apply proj1_sig_inj. exact HU.
    - exact (proj1 HlW).
    - exact HndB.
    - apply (owners_image F D own ownb Q lF lD lW); assumption.
    - intros [x q] _. unfold strong_scope. cbn. split.
      + intros H. apply (strongb_spec F D own beat ownb beatb Hown Hbeat lD HlD x).
        intros y Ho. exact (H (exist _ y Ho)).
      + intros H [y Ho]. cbn.
        exact (proj1 (strongb_spec F D own beat ownb beatb Hown Hbeat lD HlD x)
                 H y Ho). }
  pose proof (most_p_counting F (owners_of ownb lF lD)
                (strongb_of ownb beatb lD) HndB) as Hc.
  unfold most_strong, strong_reading_c. split; intro H.
  - apply Hc. apply Hmap. exact H.
  - apply Hmap. apply Hc. exact H.
Qed.

(* D7.  The weak reading on types equals its counting form
   ([L21] (16)). *)
Theorem weak_counting_form :
  forall (F D : Type) (own beat : F -> D -> Prop) (ownb beatb : F -> D -> bool)
         (Q : F -> Prop),
    reflects own ownb -> reflects beat beatb ->
    weak_owner_spec own Q -> proofs_unique Q ->
    forall (lF : list F) (lD : list D) (lW : list (FW Q)),
      listing lF -> listing lD -> listing lW ->
      (most_weak own beat Q lW <-> weak_reading_c ownb beatb lF lD).
Proof.
  intros F D own beat ownb beatb Q Hown Hbeat HQ HU lF lD lW HlF HlD HlW.
  assert (HndB : NoDup (owners_of ownb lF lD))
    by (unfold owners_of; apply NoDup_filter_l; exact (proj1 HlF)).
  assert (Hmap : most_p lW (weak_scope own beat Q) <->
                 most_p (owners_of ownb lF lD)
                        (fun x => weakb_of ownb beatb lD x = true)).
  { apply (most_p_map (FW Q) F (@proj1_sig F Q)).
    - apply proj1_sig_inj. exact HU.
    - exact (proj1 HlW).
    - exact HndB.
    - apply (owners_image F D own ownb Q lF lD lW); assumption.
    - intros [x q] _. unfold weak_scope. cbn. split.
      + intros [[y Ho] Hb]. cbn in Hb.
        apply (weakb_spec F D own beat ownb beatb Hown Hbeat lD HlD x).
        exists y. split; assumption.
      + intros H.
        apply (weakb_spec F D own beat ownb beatb Hown Hbeat lD HlD x) in H.
        destruct H as [y [Ho Hb]]. exists (exist _ y Ho). exact Hb. }
  pose proof (most_p_counting F (owners_of ownb lF lD)
                (weakb_of ownb beatb lD) HndB) as Hc.
  unfold most_weak, weak_reading_c. split; intro H.
  - apply Hc. apply Hmap. exact H.
  - apply Hmap. apply Hc. exact H.
Qed.

(* ========================================================================== *)
(*  Part 6 — Sundholm's alternative: A-injections ([S89] (27), p. 10)         *)
(* ========================================================================== *)

(* [S89] (27), as printed: a map out of the Sigma type under which equal
   values come from pairs with equal FIRST components.  The proof objects
   are forgotten.  Sundholm sketches this as a way to count owners and
   then rejects it, because the quantifier definitions would stop being
   uniform in their domain; he keeps the count of pairs (p. 10). *)
Definition A_injection {A : Type} {B : A -> Type} {C : Type}
  (f : {x : A & B x} -> C) : Prop :=
  forall z w : {x : A & B x}, f z = f w -> projT1 z = projT1 w.

(* Added here: the converse condition, which (27) does not contain. *)
Definition respects_first {A : Type} {B : A -> Type} {C : Type}
  (f : {x : A & B x} -> C) : Prop :=
  forall z w : {x : A & B x}, projT1 z = projT1 w -> f z = f w.

(* [S89] (12): surjection, here with the weak existential. *)
Definition onto {X C : Type} (f : X -> C) : Prop :=
  forall c : C, exists z : X, f z = c.

(* S1.  (27) weakens (11): every injection out of a Sigma type is an
   A-injection. *)
Theorem injection_is_A_injection :
  forall (A : Type) (B : A -> Type) (C : Type) (f : {x : A & B x} -> C),
    (forall z w, f z = f w -> z = w) -> A_injection f.
Proof. intros A B C f Hf z w H; rewrite (Hf z w H); reflexivity. Qed.

(* S2.  Added here.  An A-injection onto its target does not fix the count.  For
   one first component with two proofs there is one onto a one-object type
   and one onto a two-object type. *)
Theorem A_injection_count_not_unique :
  (exists f : {x : unit & bool} -> unit, A_injection f /\ onto f) /\
  (exists f : {x : unit & bool} -> bool, A_injection f /\ onto f).
Proof.
  split.
  - exists (fun _ => tt); split.
    + intros [[] b1] [[] b2] _; reflexivity.
    + intros []; exists (existT (fun _ : unit => bool) tt true); reflexivity.
  - exists (fun s : {x : unit & bool} => projT2 s); split.
    + intros [[] b1] [[] b2] _; reflexivity.
    + intros b; exists (existT (fun _ : unit => bool) tt b); reflexivity.
Qed.

(* S3.  Added here.  With the converse condition added, the count is the number
   of first components that have a proof: the owners. *)
Theorem owner_count_by_A_injection :
  forall (A : Type) (B : A -> Type) (C : Type) (f : {x : A & B x} -> C),
    A_injection f -> respects_first f -> onto f ->
    forall (lA : list A) (lC : list C) (inhb : A -> bool),
      listing lA -> listing lC ->
      (forall x, inhb x = true <-> inhabited (B x)) ->
      length lC = length (filter inhb lA).
Proof.
  intros A B C f Hinj Hresp Honto lA lC inhb HlA HlC Hinh.
  apply (rel_bij_length C A
           (fun c x => exists z : {x : A & B x}, f z = c /\ projT1 z = x)).
  - exact (proj1 HlC).
  - apply NoDup_filter_l. exact (proj1 HlA).
  - intros c _. destruct (Honto c) as [z Hz]. exists (projT1 z). split.
    + apply filter_In. split; [apply (proj2 HlA)|].
      apply Hinh. constructor. exact (projT2 z).
    + exists z. split; [exact Hz | reflexivity].
  - intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
    apply Hinh in Hx. destruct Hx as [b].
    exists (f (existT B x b)). split; [apply (proj2 HlC)|].
    exists (existT B x b). split; reflexivity.
  - intros c c' x [z [Hz Hx]] [z' [Hz' Hx']]. subst c c'.
    apply Hresp. rewrite Hx, Hx'. reflexivity.
  - intros c x x' [z [Hz Hx]] [z' [Hz' Hx']]. subst x x'.
    apply Hinj. rewrite Hz, Hz'. reflexivity.
Qed.

(* The map that forgets the donkey: from Sundholm's pairs to Luo's
   collection of owners. *)
Definition forward {F D : Type} (own : F -> D -> Prop) (Q : F -> Prop)
  (HQ : weak_owner_spec own Q) (z : FSig F D own) : FW Q :=
  exist Q (Ranta.he F D own z)
    (proj2 (HQ (Ranta.he F D own z))
       (ex_intro (fun y => own (Ranta.he F D own z) y)
          (Ranta.it F D own z) (projT2 (projT2 z)))).

(* S4.  Added here.  Luo's collection is a target of exactly that kind: the
   forgetful map is an A-injection, respects first components and is onto.
   So counting Luo's collection with ordinary bijections is counting
   Sundholm's pairs by first components, and the quantifier stays uniform
   in its domain. *)
Theorem forward_realizes_owner_count :
  forall (F D : Type) (own : F -> D -> Prop) (Q : F -> Prop)
         (HQ : weak_owner_spec own Q),
    proofs_unique Q ->
    @A_injection F (fun x => {y : D & own x y}) (FW Q) (forward own Q HQ) /\
    @respects_first F (fun x => {y : D & own x y}) (FW Q)
      (forward own Q HQ) /\
    onto (forward own Q HQ).
Proof.
  intros F D own Q HQ HU; split; [|split].
  - intros z w H; exact (f_equal (@proj1_sig F Q) H).
  - intros z w H; apply (proj1_sig_inj F Q HU); exact H.
  - intros [x q]; destruct (proj1 (HQ x) q) as [y o].
    exists (existT (fun x => {y : D & own x y}) x
              (existT (fun y => own x y) y o)).
    apply (proj1_sig_inj F Q HU); reflexivity.
Qed.

(* D8.  When the cardinality problem cannot arise: if nobody owns two
   donkeys, the two collections have the same size and all three readings
   agree.  This covers the model of Ranta_GQ.sundholm_donkey_contrast. *)
Theorem functional_readings_agree :
  forall (F D : Type) (own beat : F -> D -> Prop) (Q : F -> Prop),
    weak_owner_spec own Q -> proofs_unique Q ->
    own_proofs_unique own -> functional_own own ->
    forall (lS : list (FSig F D own)) (lW : list (FW Q)),
      listing lS -> listing lW ->
      length lS = length lW /\
      (most_pair own beat lS <-> most_strong own beat Q lW) /\
      (most_strong own beat Q lW <-> most_weak own beat Q lW).
Proof.
  intros F D own beat Q HQ HUQ HU Hfun lS lW HlS HlW.
  assert (Hinj : forall z z' : FSig F D own,
             forward own Q HQ z = forward own Q HQ z' -> z = z').
  { intros [x [y o]] [x' [y' o']] E.
    assert (E1 := f_equal (@proj1_sig F Q) E).
    unfold forward, Ranta.he in E1. cbn in E1. subst x'.
    assert (E2 : y = y') by exact (Hfun x y y' o o'). subst y'.
    rewrite (HU x y o o'). reflexivity. }
  assert (Him : forall b, In b lW <->
                          exists z, In z lS /\ forward own Q HQ z = b).
  { intros b; split.
    - intros _. destruct b as [x q]. destruct (proj1 (HQ x) q) as [y o].
      exists (existT (fun x => {y : D & own x y}) x
                (existT (fun y => own x y) y o)).
      split; [apply (proj2 HlS)|].
      apply (proj1_sig_inj F Q HUQ). reflexivity.
    - intros _. apply (proj2 HlW). }
  assert (Hpt : forall z, In z lS ->
             (pair_scope own beat z <->
              strong_scope own beat Q (forward own Q HQ z))).
  { intros [x [y o]] _.
    unfold pair_scope, strong_scope, forward, Ranta.he, Ranta.it. cbn. split.
    - intros H [y' o']. cbn. rewrite <- (Hfun x y y' o o'). exact H.
    - intros H. exact (H (exist _ y o)). }
  split; [|split].
  - apply (image_length (FSig F D own) (FW Q) (forward own Q HQ));
      [exact Hinj | exact (proj1 HlS) | exact (proj1 HlW) | exact Him].
  - unfold most_pair, most_strong.
    apply (most_p_map (FSig F D own) (FW Q) (forward own Q HQ));
      [exact Hinj | exact (proj1 HlS) | exact (proj1 HlW) | exact Him
      | exact Hpt].
  - split.
    + apply (strong_implies_weak F D own beat Q HQ lW).
    + unfold most_weak, most_strong. apply most_p_mono.
      intros [x q] [[y o] Hb] [y' o']. cbn in *.
      rewrite <- (Hfun x y y' o o'). exact Hb.
Qed.

(* ========================================================================== *)
(*  Part 7 — Combining the two sums ([L21] section 4)                         *)
(* ========================================================================== *)

(* [L21] (9): the impredicative existential. *)
Definition ex9 (A : Type) (P : A -> Prop) : Prop :=
  forall X : Prop, (forall x : A, P x -> X) -> X.

(* [L21] (22): the same shape over a universe of types. *)
Definition ex22 (A : Type) (B : A -> Type) : Type :=
  forall X : Type, (forall x : A, B x -> X) -> X.

(* [L21] (9) is Rocq's existential. *)
Theorem ex9_is_exists :
  forall (A : Type) (P : A -> Prop), ex9 A P <-> exists x, P x.
Proof.
  intros A P; split.
  - intros H; apply H; intros x p; exists x; exact p.
  - intros [x p] X k; exact (k x p).
Qed.

(* [L21] section 4: (22) is strong, interderivable with Sigma by functions
   of the theory.  Stated in Type because the functions are the content. *)
Theorem ex22_is_strong :
  forall (A : Type) (B : A -> Type),
    ((ex22 A B -> {x : A & B x}) * ({x : A & B x} -> ex22 A B))%type.
Proof.
  intros A B; split.
  - intros e; exact (e {x : A & B x} (fun x b => existT _ x b)).
  - intros [x b] X k; exact (k x b).
Qed.

(* Added here.  A weak sum with unique proofs has no projection that returns,
   for each introduction, the witness it was built from, unless its domain
   has at most one object.  Scope: this excludes that one
   computation law only.  A selector that picks SOME witness is not
   excluded; the boolean instance of Part 8 computes one by search. *)
Theorem weak_sum_no_projection :
  forall (D : Type),
    (forall (P : D -> Prop) (p q : exists y, P y), p = q) ->
    forall proj : (forall P : D -> Prop, (exists y, P y) -> D),
      (forall (P : D -> Prop) (y : D) (h : P y),
          proj P (ex_intro P y h) = y) ->
      forall y1 y2 : D, y1 = y2.
Proof.
  intros D PI proj Hproj y1 y2.
  rewrite <- (Hproj (fun _ => True) y1 I).
  rewrite (PI (fun _ => True) (ex_intro (fun _ : D => True) y1 I)
              (ex_intro (fun _ : D => True) y2 I)).
  apply Hproj.
Qed.

(* ========================================================================== *)
(*  Part 8 — The weak sum as a truncation ([L21] (23)-(25))                   *)
(* ========================================================================== *)

(* An interface for the truncation of each [owned own x]: a map into it,
   uniqueness of its objects, and elimination into types with at most one
   object.  All three are premises of the statements. *)
Theorem truncated_counts_owners :
  forall (F D : Type) (own : F -> D -> Prop)
         (TrO : F -> Type) (trO : forall x : F, owned own x -> TrO x),
    (forall (x : F) (u v : TrO x), u = v) ->
    (forall (x : F) (B : Type),
        (forall b1 b2 : B, b1 = b2) -> (owned own x -> B) -> TrO x -> B) ->
    forall (lF : list F) (lT : list {x : F & TrO x}) (ownerb : F -> bool),
      listing lF -> listing lT ->
      (forall x, ownerb x = true <-> owner own x) ->
      length lT = length (filter ownerb lF).
Proof.
  intros F D own TrO trO HU Hrec lF lT ownerb [HndF HallF] [HndT HallT] Hb.
  assert (E : length (map (@projT1 F TrO) lT) = length lT) by apply len_map.
  assert (Hinj : forall a b : {x : F & TrO x}, projT1 a = projT1 b -> a = b).
  { intros [x u] [y v] H; cbn in H; subst y.
    rewrite (HU x u v); reflexivity. }
  apply Nat.le_antisymm.
  - rewrite <- E; apply NoDup_incl_length.
    + apply NoDup_map_inj; [exact Hinj | exact HndT].
    + intros x Hx; apply in_map_iff in Hx.
      destruct Hx as [[x' t] [Hx' _]]; cbn in Hx'; subst x'.
      apply filter_In; split; [apply HallF|].
      apply (Hrec x (ownerb x = true)).
      * intros b1 b2; apply UIP_dec; apply bool_dec.
      * intros [y o]; apply Hb; exists y; exact o.
      * exact t.
  - rewrite <- E; apply NoDup_incl_length.
    + apply NoDup_filter_l; exact HndF.
    + intros x Hx; apply filter_In in Hx; destruct Hx as [_ Hx].
      apply Hb in Hx; destruct Hx as [y o].
      apply in_map_iff; exists (existT _ x (trO x (exist _ y o))); split;
        [reflexivity | apply HallT].
Qed.

(* [L21] (24) against its counting form. *)
Theorem truncated_strong_counting_form :
  forall (F D : Type) (own beat : F -> D -> Prop) (ownb beatb : F -> D -> bool)
         (TrO : F -> Type) (trO : forall x : F, owned own x -> TrO x),
    reflects own ownb -> reflects beat beatb ->
    (forall (x : F) (u v : TrO x), u = v) ->
    (forall (x : F) (B : Type),
        (forall b1 b2 : B, b1 = b2) -> (owned own x -> B) -> TrO x -> B) ->
    forall (lF : list F) (lD : list D) (lT : list {x : F & TrO x}),
      listing lF -> listing lD -> listing lT ->
      (most_p lT (fun z => forall y' : owned own (projT1 z),
                             beat (projT1 z) (proj1_sig y'))
       <-> strong_reading_c ownb beatb lF lD).
Proof.
  intros F D own beat ownb beatb TrO trO Hown Hbeat HU Hrec
         lF lD lT HlF HlD HlT.
  assert (HndB : NoDup (owners_of ownb lF lD))
    by (unfold owners_of; apply NoDup_filter_l; exact (proj1 HlF)).
  assert (Hinj : forall a b : {x : F & TrO x}, projT1 a = projT1 b -> a = b).
  { intros [x u] [y v] H; cbn in H; subst y.
    rewrite (HU x u v); reflexivity. }
  assert (Hmap :
    most_p lT (fun z => forall y' : owned own (projT1 z),
                           beat (projT1 z) (proj1_sig y')) <->
    most_p (owners_of ownb lF lD)
           (fun x => strongb_of ownb beatb lD x = true)).
  { apply (most_p_map {x : F & TrO x} F (@projT1 F TrO)).
    - exact Hinj.
    - exact (proj1 HlT).
    - exact HndB.
    - intros b; unfold owners_of; split.
      + intros Hb. apply filter_In in Hb. destruct Hb as [_ Hb].
        apply (ownerb_spec F D own ownb Hown lD HlD) in Hb.
        destruct Hb as [y o].
        exists (existT TrO b (trO b (exist _ y o))).
        split; [apply (proj2 HlT) | reflexivity].
      + intros [[x t] [_ E]]. cbn in E. subst b.
        apply filter_In. split; [apply (proj2 HlF)|].
        apply (Hrec x (ownerb_of ownb lD x = true)).
        * intros b1 b2. apply UIP_dec. apply bool_dec.
        * intros [y o]. apply (ownerb_spec F D own ownb Hown lD HlD).
          exists y. exact o.
        * exact t.
    - intros [x t] _. cbn. split.
      + intros H. apply (strongb_spec F D own beat ownb beatb Hown Hbeat lD HlD x).
        intros y Ho. exact (H (exist _ y Ho)).
      + intros H [y Ho]. cbn.
        exact (proj1 (strongb_spec F D own beat ownb beatb Hown Hbeat lD HlD x)
                 H y Ho). }
  pose proof (most_p_counting F (owners_of ownb lF lD)
                (strongb_of ownb beatb lD) HndB) as Hc.
  unfold strong_reading_c. split; intro H.
  - apply Hc. apply Hmap. exact H.
  - apply Hmap. apply Hc. exact H.
Qed.

(* The interface can be met with no axiom on a decidable, enumerated
   model.  Stated in Type because it supplies the three operations. *)
Theorem bool_truncation_instance :
  forall (F D : Type) (ownb : F -> D -> bool) (lD : list D),
    listing lD ->
    ((forall x : F, owned (fun a b => ownb a b = true) x ->
                    existsb (ownb x) lD = true) *
     (forall (x : F) (u v : existsb (ownb x) lD = true), u = v) *
     (forall (x : F) (B : Type),
        (owned (fun a b => ownb a b = true) x -> B) ->
        existsb (ownb x) lD = true -> B))%type.
Proof.
  intros F D ownb lD [_ HallD]; split; [split|].
  - intros x [y o]; apply existsb_exists; exists y; split;
      [apply HallD | exact o].
  - intros x u v; apply UIP_dec; apply bool_dec.
  - intros x B k H.
    destruct (find (ownb x) lD) as [y|] eqn:E.
    + exact (k (exist _ y (proj2 (find_some _ _ E)))).
    + exfalso; apply existsb_exists in H; destruct H as [y [Hy Ho]].
      rewrite (find_none _ _ E y Hy) in Ho; discriminate Ho.
Qed.

(* ========================================================================== *)
(*  Part 9 — A mixed reading ([L21] (17)-(18), after Brasoveanu)              *)
(* ========================================================================== *)

(* "Every person who buys a TV and has a credit card uses it to pay for
   it": strong for the TV, weak for the card. *)
Definition mixed_reading (P T C : Type) (buy : P -> T -> Prop)
  (have : P -> C -> Prop) (pay : P -> T -> C -> Prop) : Prop :=
  forall z : {x : P | (exists y1, buy x y1) /\ (exists y2, have x y2)},
  forall y : {y1 : T | buy (proj1_sig z) y1},
  exists y' : {y2 : C | have (proj1_sig z) y2},
    pay (proj1_sig z) (proj1_sig y) (proj1_sig y').

(* The mixed reading unfolds to the expected first-order condition. *)
Theorem mixed_reading_unfolds :
  forall (P T C : Type) (buy : P -> T -> Prop) (have : P -> C -> Prop)
         (pay : P -> T -> C -> Prop),
    mixed_reading P T C buy have pay <->
    (forall x y1, buy x y1 -> (exists y2, have x y2) ->
                  exists y2, have x y2 /\ pay x y1 y2).
Proof.
  intros P T C buy have pay; unfold mixed_reading; split.
  - intros H x y1 Hb Hh.
    destruct (H (exist _ x (conj (ex_intro _ y1 Hb) Hh)) (exist _ y1 Hb))
      as [[y2 Hy2] Hp]; cbn in *.
    exists y2; split; assumption.
  - intros H [x [Hb Hh]] [y1 Hy1]; cbn in *.
    destruct (H x y1 Hy1 Hh) as [y2 [Hy2 Hp]].
    exists (exist _ y2 Hy2); exact Hp.
Qed.

(* ========================================================================== *)
(*  Part 10 — Models                                                          *)
(* ========================================================================== *)

(* The bridges of Part 5 need COMPLETE lists of their carrier types, and a
   list of some natural numbers is not a complete list of nat.  The models
   therefore live on carriers with a complete list: bounded subtypes of the
   numbers, or the finite types of Ranta_GQ.v. *)

Definition holds {X Y : Type} (rb : X -> Y -> bool) (x : X) (y : Y) : Prop :=
  rb x y = true.

Definition ownerP {X Y : Type} (rb : X -> Y -> bool) (lY : list Y) (x : X)
  : Prop := ownerb_of rb lY x = true.

(* The triples of such a model as a list. *)
Definition to_FSig {F D : Type} (rb : F -> D -> bool)
  (z : {p : F * D | rb (fst p) (snd p) = true}) : FSig F D (holds rb) :=
  existT (fun x => {y : D & holds rb x y}) (fst (proj1_sig z))
    (existT (fun y => holds rb (fst (proj1_sig z)) y) (snd (proj1_sig z))
       (proj2_sig z)).

Definition FSig_list {F D : Type} (rb : F -> D -> bool) (lF : list F)
  (lD : list D) : list (FSig F D (holds rb)) :=
  map (to_FSig rb)
      (sig_filter (fun p => rb (fst p) (snd p)) (list_prod lF lD)).

(* I2.  That list is complete and duplicate-free, which the pair-side
   results D4 and D5 need before they apply to a model. *)
Theorem FSig_list_listing :
  forall (F D : Type) (rb : F -> D -> bool) (lF : list F) (lD : list D),
    listing lF -> listing lD -> listing (FSig_list rb lF lD).
Proof.
  intros F D rb lF lD HlF HlD. unfold FSig_list.
  assert (HL : listing (sig_filter (fun p : F * D => rb (fst p) (snd p))
                          (list_prod lF lD))).
  { apply sig_filter_listing. split.
    - apply NoDup_list_prod; [exact (proj1 HlF) | exact (proj1 HlD)].
    - intros [x y]. apply in_prod_iff.
      split; [apply (proj2 HlF) | apply (proj2 HlD)]. }
  split.
  - apply NoDup_map_inj; [|exact (proj1 HL)].
    intros z z' E.
    apply (proj1_sig_inj (F * D) (fun p => rb (fst p) (snd p) = true)).
    + apply (bool_proofs_unique (F * D) (fun p => rb (fst p) (snd p))).
    + destruct z as [[x y] e], z' as [[x' y'] e'].
      assert (E1 := f_equal (Ranta.he F D (holds rb)) E).
      assert (E2 := f_equal (Ranta.it F D (holds rb)) E).
      unfold Ranta.he, Ranta.it, to_FSig in E1, E2. cbn in E1, E2.
      cbn. rewrite E1, E2. reflexivity.
  - intros [x [y o]].
    apply in_map_iff.
    exists (exist (fun p : F * D => rb (fst p) (snd p) = true) (x, y) o).
    split; [reflexivity | apply (proj2 HL)].
Qed.

(* Every boolean model on listed carriers meets the premises of the
   bridges.  [below_model_instance] below is the case of bounded carriers. *)
Lemma bool_model_premises :
  forall (F D : Type) (ob : F -> D -> bool) (lF : list F) (lD : list D),
    listing lF -> listing lD ->
    reflects (holds ob) ob /\ own_proofs_unique (holds ob) /\
    weak_owner_spec (holds ob) (ownerP ob lD) /\
    proofs_unique (ownerP ob lD) /\
    listing (sig_filter (ownerb_of ob lD) lF).
Proof.
  intros F D ob lF lD HlF HlD.
  split; [intros x y; split; intro H; exact H|].
  split; [intros x y p q; unfold holds in *; apply UIP_dec; apply bool_dec|].
  split.
  - intros x; unfold ownerP, ownerb_of, owner, holds; split.
    + intros H; apply existsb_exists in H; destruct H as [y [_ Hy]].
      exists y; exact Hy.
    + intros [y Hy]; apply existsb_exists; exists y; split;
        [apply (proj2 HlD) | exact Hy].
  - split.
    + intros x p q; unfold ownerP in *; apply UIP_dec; apply bool_dec.
    + apply sig_filter_listing; exact HlF.
Qed.

(* Corollary.  On every boolean model with listed
   carriers, Luo's three formulas, read on types, are decided by counting. *)
Theorem bool_model_readings :
  forall (F D : Type) (ob bb : F -> D -> bool) (lF : list F) (lD : list D),
    listing lF -> listing lD ->
    (most_pair (holds ob) (holds bb) (FSig_list ob lF lD) <->
     pair_reading_c ob bb lF lD) /\
    (most_strong (holds ob) (holds bb) (ownerP ob lD)
       (sig_filter (ownerb_of ob lD) lF) <->
     strong_reading_c ob bb lF lD) /\
    (most_weak (holds ob) (holds bb) (ownerP ob lD)
       (sig_filter (ownerb_of ob lD) lF) <->
     weak_reading_c ob bb lF lD).
Proof.
  intros F D ob bb lF lD HlF HlD.
  destruct (bool_model_premises F D ob lF lD HlF HlD)
    as [Hro [HUo [HQ [HUQ HlW]]]].
  assert (Hrb : reflects (holds bb) bb)
    by (intros x y; split; intro H; exact H).
  split; [|split].
  - apply (pair_counting_form F D (holds ob) (holds bb) ob bb Hro Hrb HUo
             lF lD (FSig_list ob lF lD) HlF HlD).
    apply FSig_list_listing; assumption.
  - exact (strong_counting_form F D (holds ob) (holds bb) ob bb (ownerP ob lD)
             Hro Hrb HQ HUQ lF lD _ HlF HlD HlW).
  - exact (weak_counting_form F D (holds ob) (holds bb) ob bb (ownerP ob lD)
             Hro Hrb HQ HUQ lF lD _ HlF HlD HlW).
Qed.

(* Corollary.  On every such model the triples number as many as the
   computed pairs, and the owners' collection as many as the computed
   owners.  Stated with the list expressions that the examples of this part use,
   so that no large term has to be converted. *)
Lemma bool_model_counts :
  forall (F D : Type) (ob : F -> D -> bool) (lF : list F) (lD : list D),
    listing lF -> listing lD ->
    length (FSig_list ob lF lD) = length (pairs_of ob lF lD) /\
    length (sig_filter (ownerb_of ob lD) lF) = length (owners_of ob lF lD).
Proof.
  intros F D ob lF lD HlF HlD.
  destruct (bool_model_premises F D ob lF lD HlF HlD)
    as [Hro [HUo [HQ [HUQ HlW]]]].
  split.
  - exact (strong_collection_counts_pairs F D (holds ob) ob Hro HUo lF lD
             (FSig_list ob lF lD) HlF HlD
             (FSig_list_listing F D ob lF lD HlF HlD)).
  - exact (weak_collection_counts_owners F D (holds ob) (ownerP ob lD)
             HQ HUQ lF (sig_filter (ownerb_of ob lD) lF) (ownerb_of ob lD)
             HlF HlW HQ).
Qed.

Definition Below (k : nat) : Type := {n : nat | n <? k = true}.

Definition below_list (k : nat) : list (Below k) :=
  sig_filter (fun n => n <? k) (seq 0 k).

(* A boolean table on numbers, read on bounded carriers. *)
Definition liftB (k m : nat) (rb : nat -> nat -> bool)
  (x : Below k) (y : Below m) : bool := rb (proj1_sig x) (proj1_sig y).

Lemma below_listing : forall k : nat, listing (below_list k).
Proof.
  intro k; unfold below_list; apply sig_filter_listing_gen.
  - apply seq_NoDup.
  - intros n H; apply in_seq; apply Nat.ltb_lt in H; lia.
Qed.

(* I1.  Every boolean table on bounded carriers meets the premises of the
   owner-side bridges D3, D6 and D7, with the complete lists named here. *)
Theorem below_model_instance :
  forall (k m : nat) (ob bb : nat -> nat -> bool),
    listing (below_list k) /\ listing (below_list m) /\
    reflects (holds (liftB k m ob)) (liftB k m ob) /\
    reflects (holds (liftB k m bb)) (liftB k m bb) /\
    own_proofs_unique (holds (liftB k m ob)) /\
    weak_owner_spec (holds (liftB k m ob))
      (ownerP (liftB k m ob) (below_list m)) /\
    proofs_unique (ownerP (liftB k m ob) (below_list m)) /\
    listing (sig_filter (ownerb_of (liftB k m ob) (below_list m))
               (below_list k)).
Proof.
  intros k m ob bb.
  split; [apply below_listing|].
  split; [apply below_listing|].
  split; [intros x y; split; intro H; exact H|].
  split; [intros x y; split; intro H; exact H|].
  split; [intros x y p q; unfold holds in *; apply UIP_dec; apply bool_dec|].
  split.
  - intros x; unfold ownerP, ownerb_of, owner, holds; split.
    + intros H; apply existsb_exists in H; destruct H as [y [_ Hy]].
      exists y; exact Hy.
    + intros [y Hy]; apply existsb_exists; exists y; split;
        [apply (proj2 (below_listing m)) | exact Hy].
  - split.
    + intros x p q; unfold ownerP in *; apply UIP_dec; apply bool_dec.
    + apply sig_filter_listing; apply below_listing.
Qed.

(* ---- [L21] section 2: ten farmers.  Farmer 0 owns donkeys 0-19 and beats
   them all; farmers 1-9 own one donkey each (20-28) and do not beat it.
   The tables are on numbers; the model is their reading on the carriers
   with ten and twenty-nine objects. *)
Definition ownb10 (x y : nat) : bool :=
  if x =? 0 then y <? 20 else y =? 19 + x.

Definition beatb10 (x y : nat) : bool := (x =? 0) && (y <? 20).

Definition dF10 : list (Below 10) := below_list 10.

Definition dD29 : list (Below 29) := below_list 29.

Definition ownB10 : Below 10 -> Below 29 -> bool := liftB 10 29 ownb10.

Definition beatB10 : Below 10 -> Below 29 -> bool := liftB 10 29 beatb10.

(* 29 owner-donkey pairs: the lower bound of [L21] section 2, attained
   because boolean ownership has one proof. *)
Example luo_ten_pairs : length (pairs_of ownB10 dF10 dD29) = 29.
Proof. vm_compute; reflexivity. Qed.

Example luo_ten_owners : length (owners_of ownB10 dF10 dD29) = 10.
Proof. vm_compute; reflexivity. Qed.

(* The pair reading is true: 20 of the 29 pairs are beatings. *)
Example luo_ten_pair_reading_true : pair_reading_c ownB10 beatB10 dF10 dD29.
Proof.
  unfold pair_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

(* Nine of the ten owners beat no donkey of theirs. *)
Example luo_ten_nonbeaters :
  length (filter (fun x => negb (weakb_of ownB10 beatB10 dD29 x))
                 (owners_of ownB10 dF10 dD29)) = 9.
Proof. vm_compute; reflexivity. Qed.

(* Both of Luo's readings are false: one owner in ten. *)
Example luo_ten_strong_reading_false :
  ~ strong_reading_c ownB10 beatB10 dF10 dD29.
Proof.
  unfold strong_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

Example luo_ten_weak_reading_false :
  ~ weak_reading_c ownB10 beatB10 dF10 dD29.
Proof.
  unfold weak_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

(* Corollary.  [L21] section 2, at the level of formulas (7), (12), (16):
   on the ten-farmer model (7) holds and (12) and (16) fail; the triples
   number 29 and the owners 10. *)
Theorem luo_ten_farmers_type_level :
  most_pair (holds ownB10) (holds beatB10) (FSig_list ownB10 dF10 dD29) /\
  ~ most_strong (holds ownB10) (holds beatB10) (ownerP ownB10 dD29)
      (sig_filter (ownerb_of ownB10 dD29) dF10) /\
  ~ most_weak (holds ownB10) (holds beatB10) (ownerP ownB10 dD29)
      (sig_filter (ownerb_of ownB10 dD29) dF10) /\
  length (FSig_list ownB10 dF10 dD29) = 29 /\
  length (sig_filter (ownerb_of ownB10 dD29) dF10) = 10.
Proof.
  pose proof (below_listing 10) as HlF. pose proof (below_listing 29) as HlD.
  destruct (bool_model_readings _ _ ownB10 beatB10 dF10 dD29 HlF HlD)
    as [Hp [Hs Hw]].
  destruct (bool_model_counts _ _ ownB10 dF10 dD29 HlF HlD) as [Hc1 Hc2].
  split; [apply Hp; exact luo_ten_pair_reading_true|].
  split; [intros H; apply luo_ten_strong_reading_false; apply Hs; exact H|].
  split; [intros H; apply luo_ten_weak_reading_false; apply Hw; exact H|].
  split.
  - exact (eq_trans Hc1 luo_ten_pairs).
  - exact (eq_trans Hc2 luo_ten_owners).
Qed.

(* ---- strong against weak ([L21] (14)-(16)): three farmers, two donkeys
   each, every farmer beats exactly one of his two. *)
Definition ownb3 (x y : nat) : bool := (y =? 2 * x) || (y =? 2 * x + 1).

Definition beatb3 (x y : nat) : bool := y =? 2 * x.

Definition dF3 : list (Below 3) := below_list 3.

Definition dD6 : list (Below 6) := below_list 6.

Definition ownB3 : Below 3 -> Below 6 -> bool := liftB 3 6 ownb3.

Definition beatB3 : Below 3 -> Below 6 -> bool := liftB 3 6 beatb3.

Example sep_weak_reading_true : weak_reading_c ownB3 beatB3 dF3 dD6.
Proof.
  unfold weak_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

Example sep_strong_reading_false : ~ strong_reading_c ownB3 beatB3 dF3 dD6.
Proof.
  unfold strong_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

(* Corollary.  [L21] (14)-(16) at type level: on the three-farmer model the
   weak reading holds and the strong reading fails. *)
Theorem three_farmers_type_level :
  most_weak (holds ownB3) (holds beatB3) (ownerP ownB3 dD6)
    (sig_filter (ownerb_of ownB3 dD6) dF3) /\
  ~ most_strong (holds ownB3) (holds beatB3) (ownerP ownB3 dD6)
      (sig_filter (ownerb_of ownB3 dD6) dF3).
Proof.
  pose proof (below_listing 3) as HlF. pose proof (below_listing 6) as HlD.
  destruct (bool_model_readings _ _ ownB3 beatB3 dF3 dD6 HlF HlD)
    as [_ [Hs Hw]].
  split; [apply Hw; exact sep_weak_reading_true|].
  intros H; apply sep_strong_reading_false; apply Hs; exact H.
Qed.

(* The model of Ranta_GQ.sundholm_donkey_contrast: three men, one of them
   an owner, of one donkey, which he does not beat.  The pairs computed
   here are that file's own [dom_owners]. *)
Example sundholm_model_pairs :
  pairs_of Ranta_GQ.owns Ranta_GQ.dom_men [Ranta_GQ.d1] = Ranta_GQ.dom_owners.
Proof. vm_compute; reflexivity. Qed.

Example sundholm_model_owners :
  owners_of Ranta_GQ.owns Ranta_GQ.dom_men [Ranta_GQ.d1] = [Ranta_GQ.m1].
Proof. vm_compute; reflexivity. Qed.

(* Luo's readings give the verdict of Sundholm's pair reading there, so
   the contrast with the conditional reading is preserved. *)
Example sundholm_model_strong_false :
  ~ strong_reading_c Ranta_GQ.owns Ranta_GQ.beats Ranta_GQ.dom_men
      [Ranta_GQ.d1].
Proof.
  unfold strong_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

Example sundholm_model_weak_false :
  ~ weak_reading_c Ranta_GQ.owns Ranta_GQ.beats Ranta_GQ.dom_men
      [Ranta_GQ.d1].
Proof.
  unfold weak_reading_c, Ranta_GQ.most_c, Ranta_GQ.cnt; vm_compute; lia.
Qed.

(* The model of Ranta_GQ.sundholm_donkey_contrast has complete lists of
   its two carriers already. *)
Example sundholm_model_carriers_listed :
  listing Ranta_GQ.dom_men /\ listing [Ranta_GQ.d1].
Proof.
  split; split.
  - repeat constructor; cbn; intuition discriminate.
  - intros []; cbn; auto.
  - repeat constructor; cbn; intuition.
  - intros []; cbn; auto.
Qed.

(* Corollary.  On the model of Ranta_GQ.sundholm_donkey_contrast all three
   type-level readings fail, as Sundholm's pair reading does there. *)
Theorem sundholm_model_type_level :
  ~ most_pair (holds Ranta_GQ.owns) (holds Ranta_GQ.beats)
      (FSig_list Ranta_GQ.owns Ranta_GQ.dom_men [Ranta_GQ.d1]) /\
  ~ most_strong (holds Ranta_GQ.owns) (holds Ranta_GQ.beats)
      (ownerP Ranta_GQ.owns [Ranta_GQ.d1])
      (sig_filter (ownerb_of Ranta_GQ.owns [Ranta_GQ.d1]) Ranta_GQ.dom_men) /\
  ~ most_weak (holds Ranta_GQ.owns) (holds Ranta_GQ.beats)
      (ownerP Ranta_GQ.owns [Ranta_GQ.d1])
      (sig_filter (ownerb_of Ranta_GQ.owns [Ranta_GQ.d1]) Ranta_GQ.dom_men).
Proof.
  destruct sundholm_model_carriers_listed as [HlF HlD].
  destruct (bool_model_readings _ _ Ranta_GQ.owns Ranta_GQ.beats
              Ranta_GQ.dom_men [Ranta_GQ.d1] HlF HlD) as [Hp [Hs Hw]].
  split; [|split].
  - intros H. apply Hp in H. unfold pair_reading_c in H.
    rewrite sundholm_model_pairs in H.
    exact (proj1 (proj2 Ranta_GQ.sundholm_donkey_contrast) H).
  - intros H. apply sundholm_model_strong_false. apply Hs. exact H.
  - intros H. apply sundholm_model_weak_false. apply Hw. exact H.
Qed.

(* ========================================================================== *)
(*  Part 11 — Assumption audit                                                *)
(* ========================================================================== *)

(* Expected under Coq 8.20.1: every result below prints "Closed under the
   global context" — zero axioms, zero Parameters (ARTIFACT-v).  A premise
   of a result is part of its statement and is not listed by this audit. *)

Print Assumptions len_map.
Print Assumptions NoDup_map_inj.
Print Assumptions NoDup_filter_l.
Print Assumptions proj1_sig_inj.
Print Assumptions bool_proofs_unique.
Print Assumptions NoDup_list_prod.
Print Assumptions image_length.
Print Assumptions preimage_list.
Print Assumptions rel_inj_length.
Print Assumptions rel_bij_length.
Print Assumptions sig_filter_proj.
Print Assumptions sig_filter_listing_gen.
Print Assumptions sig_filter_listing.
Print Assumptions unique_proofs_instance.
Print Assumptions most_p_mono.
Print Assumptions most_p_map.
Print Assumptions most_p_squashes_sundholm.
Print Assumptions most_p_counting.
Print Assumptions fin_list_length.
Print Assumptions fin_list_complete.
Print Assumptions fin_list_NoDup.
Print Assumptions two_k_gt.
Print Assumptions k_ge.
Print Assumptions most_fin_iff_most_p.
Print Assumptions card_subset_le.
Print Assumptions type_valued_fibres_can_increase_cardinality.
Print Assumptions index_of_lt.
Print Assumptions index_of_nth.
Print Assumptions index_of_nth_inv.
Print Assumptions card_iff_fin.
Print Assumptions pair_every_is_ranta.
Print Assumptions functional_owner_proofs_unique.
Print Assumptions every_readings_agree.
Print Assumptions strong_implies_weak.
Print Assumptions weak_collection_counts_owners.
Print Assumptions implb_true.
Print Assumptions ownerb_spec.
Print Assumptions strongb_spec.
Print Assumptions weakb_spec.
Print Assumptions owners_image.
Print Assumptions FSig_key_inj.
Print Assumptions pairs_image.
Print Assumptions strong_collection_counts_pairs.
Print Assumptions pair_counting_form.
Print Assumptions strong_counting_form.
Print Assumptions weak_counting_form.
Print Assumptions injection_is_A_injection.
Print Assumptions A_injection_count_not_unique.
Print Assumptions owner_count_by_A_injection.
Print Assumptions forward_realizes_owner_count.
Print Assumptions functional_readings_agree.
Print Assumptions ex9_is_exists.
Print Assumptions ex22_is_strong.
Print Assumptions weak_sum_no_projection.
Print Assumptions truncated_counts_owners.
Print Assumptions truncated_strong_counting_form.
Print Assumptions bool_truncation_instance.
Print Assumptions mixed_reading_unfolds.
Print Assumptions FSig_list_listing.
Print Assumptions bool_model_premises.
Print Assumptions bool_model_readings.
Print Assumptions bool_model_counts.
Print Assumptions below_listing.
Print Assumptions below_model_instance.
Print Assumptions luo_ten_pairs.
Print Assumptions luo_ten_owners.
Print Assumptions luo_ten_pair_reading_true.
Print Assumptions luo_ten_nonbeaters.
Print Assumptions luo_ten_strong_reading_false.
Print Assumptions luo_ten_weak_reading_false.
Print Assumptions luo_ten_farmers_type_level.
Print Assumptions sep_weak_reading_true.
Print Assumptions sep_strong_reading_false.
Print Assumptions three_farmers_type_level.
Print Assumptions sundholm_model_pairs.
Print Assumptions sundholm_model_owners.
Print Assumptions sundholm_model_strong_false.
Print Assumptions sundholm_model_weak_false.
Print Assumptions sundholm_model_carriers_listed.
Print Assumptions sundholm_model_type_level.
