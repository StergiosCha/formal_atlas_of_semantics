Require Import List Arith Bool Lia.
Import ListNotations.

(* ========================================================================== *)
(*  Counterfactuals.v -- counterfactual conditionals on finite ordering models *)
(*  FORMAL-ATLAS / atlas/model_theoretic (standard library only)              *)
(* ========================================================================== *)
(*
   SOURCES (local files; page numbers are the printed ones)
     Lewis, D. (1973). Counterfactuals. Blackwell (revised printing).
       Scanned book without a text layer, read by OCR.
       [1.2 p. 10 the weapons example; 1.3 pp. 13-16 spheres and truth
        conditions; 1.4 pp. 19-21 Limit Assumption; 1.5 pp. 21-22 'might';
        1.7 pp. 26-29 true antecedents, centering and weak centering;
        1.8 pp. 31-35 the three fallacies and the valid restricted
        transitivity; 2.3 pp. 48-49 comparative similarity systems;
        3.4 pp. 78-80 Stalnaker's Assumption, Conditional Excluded Middle]
     von Fintel, K. (2001). Counterfactuals in a dynamic context.  The file
       is "Chapter 3", pp. 123-152, of a volume whose title page is not in
       the scan.  Its text layer is unreadable, so it was read by OCR; the
       symbols of (22) were checked against Gillies's Definition 3.
       [3.3 p. 130 examples (10), (11); 3.7 pp. 137-139 definitions (22),
        (23) and the null-context remark; p. 142 definition (29) and the
        discussion of (10)/(11)]
     Gillies, A. (2007). Counterfactual scorekeeping.  Manuscript dated
       July 3, 2007, marked as to appear in Linguistics & Philosophy;
       manuscript page numbers.  [section 3 pp. 5-6 a Sobel sequence and
       its reversal; section 4 p. 8 Definition 1; section 5 p. 13
       Definition 3, "von Fintel-ish strict semantics".]  Used only to
       cross-check the reading of von Fintel's (22).
   Stalnaker (1968) is NOT in the corpus and was not read.  Stalnaker's
   assumption is presented only as Lewis describes it (Lewis pp. 78-79).

   WHAT IS FORMALIZED  (a fragment: one level of counterfactual, no nesting,
   propositions as boolean predicates on a finite list of worlds)
     closest, would, might     the closest-antecedent-worlds truth conditions
                               that Lewis gives under the Limit Assumption
                               (pp. 20, 21)
     T1 would_iff_lewis        they agree with Lewis's general truth condition
                               stated with comparative similarity (p. 49)
     T2 might_dual             might = not would not (p. 21)
     T3 vacuous_truth          no antecedent-world: would true, might false
                               (pp. 16, 22)
     T4 modus_ponens           under weak centering (pp. 27, 29)
     T5 centering_and          A, C |- A []-> C under centering (p. 26)
     T6 cem_stalnaker          Conditional Excluded Middle when the ordering
                               around i has no ties (pp. 78-79)
     T6' cem_stalnaker_at       the same from Stalnaker's Assumption as Lewis
                                 states it, one antecedent at a time (p. 78);
                                 the linear form implies it
     T7 restricted_transitivity  X []-> A, (X & A) []-> C |- X []-> C (p. 35)
     T8 vf_null_context        von Fintel's dynamic strict conditional agrees
                               with 'would' in the null context (p. 139)
     Worked model (4 worlds): the Sobel sequence of von Fintel's (10);
       failures of strengthening the antecedent, transitivity, contraposition
       (Lewis pp. 31-35) and of Conditional Excluded Middle when two closest
       worlds are tied; the Sobel sequence is accepted by the dynamic account
       in one order and rejected in the reverse order (von Fintel p. 142).

   NOT FORMALIZED (and why)
     * Systems of spheres (Lewis 1.3) and the equivalence with comparative
       similarity systems (2.3): only the comparative-similarity side.
     * Infinite models, where the Limit Assumption can fail (Lewis p. 20):
       the worlds here form a finite list, so it always holds (T1).
     * Inaccessible worlds (Lewis 2.3 conditions (5), (6)): every listed
       world is accessible from every world.
     * Nested counterfactuals; an object language; Lewis's axiom systems.
     * Stalnaker's selection functions and the absurd world (p. 78).
     * von Fintel's context sets, dynamic entailment (28), Strawson
       entailment (21)/(31), and his revised clause (23) for embedded
       conditionals.  Gillies's own hyperdomain semantics (his Definition 2).

   REPRESENTATION CHOICES
     * The ordering around i is given by a rank function rank i : W -> nat;
       "j is at least as similar to i as k" is rank i j <= rank i k.  This is
       always transitive and strongly connected (Lewis's conditions (1), (2),
       p. 48).  Centering is a hypothesis of the theorems that need it, not
       part of the structure.
     * Stalnaker's Assumption is given in two forms.  [stalnaker_at] is the
       form Lewis states (p. 78), antecedent by antecedent: at most one
       closest antecedent-world.  [stalnaker] is the simpler condition he
       gives for the case where every proposition is expressible, a linear
       ordering (p. 79): rank i is injective on the listed worlds.  The
       second implies the first (stalnaker_linear_implies_at).
     * von Fintel's modal horizon f assigns a set of worlds to every world.
       Without nesting only f(i) at the evaluation world i matters, so the
       horizon here is one list of worlds.
     * Dynamic acceptability of a sequence (vf_seq) is ours: each sentence is
       true at i in the horizon it is evaluated in, and the horizon is passed
       on.  von Fintel's dynamic consistency (29) speaks of context sets.
*)

Section Ordering.
Variable W : Type.
Variable dom : list W.             (* the finitely many worlds *)
Variable rank : W -> W -> nat.     (* rank i j: how far j is from i *)

Definition prop := W -> bool.
Definition pneg (A : prop) : prop := fun w => negb (A w).
Definition pand (A B : prop) : prop := fun w => A w && B w.

(* j is at least as close to i as every A-world.  Lewis p. 48 (the relation),
   p. 20 ("than which no other antecedent world is closer"). *)
Definition at_least_as_close (i : W) (A : prop) (j : W) : bool :=
  forallb (fun k => implb (A k) (rank i j <=? rank i k)) dom.

(* The closest A-worlds to i.  Lewis p. 19. *)
Definition closest (i : W) (A : prop) : list W :=
  filter (fun j => A j && at_least_as_close i A j) dom.

(* 'would': the consequent holds at every closest antecedent-world.
   Lewis p. 20, the simplified truth condition under the Limit Assumption. *)
Definition would (i : W) (A C : prop) : bool := forallb C (closest i A).

(* 'might': the consequent holds at some closest antecedent-world.
   Lewis p. 21. *)
Definition might (i : W) (A C : prop) : bool := existsb C (closest i A).

Lemma closest_spec : forall i A j,
  In j (closest i A) <->
  In j dom /\ A j = true /\
  forall k, In k dom -> A k = true -> rank i j <= rank i k.
Proof.
  intros i A j. unfold closest, at_least_as_close.
  rewrite filter_In, andb_true_iff, forallb_forall.
  split; intros (H1 & H2 & H3); repeat split; auto.
  - intros k Hk HA. specialize (H3 k Hk). rewrite HA in H3.
    apply Nat.leb_le. exact H3.
  - intros k Hk. destruct (A k) eqn:E; simpl; auto.
    apply Nat.leb_le. auto.
Qed.

(* ours: a nonempty finite set of A-worlds has a member of least rank.  This
   is the Limit Assumption for finite models (Lewis p. 19, first paragraph
   of 1.4). *)
Lemma exists_min : forall (f : W -> nat) (A : prop) (l : list W),
  (exists k, In k l /\ A k = true) ->
  exists m, In m l /\ A m = true /\
            forall k, In k l -> A k = true -> f m <= f k.
Proof.
  intros f A l; induction l as [|a l IH].
  - intros [k [[] _]].
  - intros [k [Hk HA]]. destruct (A a) eqn:Ea.
    + destruct (existsb A l) eqn:Ex.
      * apply existsb_exists in Ex.
        destruct (IH Ex) as (m & Hm & HAm & Hmin).
        destruct (le_lt_dec (f a) (f m)).
        -- exists a. split; [left; auto|]. split; auto.
           intros k' [<-|Hk'] HA'; [lia|].
           specialize (Hmin k' Hk' HA'). lia.
        -- exists m. split; [right; auto|]. split; auto.
           intros k' [<-|Hk'] HA'; [lia|auto].
      * exists a. split; [left; auto|]. split; auto.
        intros k' [<-|Hk'] HA'; [lia|]. exfalso.
        assert (existsb A l = true) by (apply existsb_exists; eauto).
        congruence.
    + destruct Hk as [<-|Hk]; [congruence|].
      destruct (IH (ex_intro _ k (conj Hk HA))) as (m & Hm & HAm & Hmin).
      exists m. split; [right; auto|]. split; auto.
      intros k' [<-|Hk'] HA'; [congruence|auto].
Qed.

(* Lewis's truth condition for 'would' in a comparative similarity system,
   p. 49: either (1) there is no antecedent-world, or (2) some antecedent-
   world k is such that the material conditional holds at every world at
   least as close as k.  (All listed worlds are accessible here.) *)
Definition would_lewis (i : W) (A C : prop) : Prop :=
  (forall k, In k dom -> A k = false) \/
  (exists k, In k dom /\ A k = true /\
     forall j, In j dom -> rank i j <= rank i k -> A j = true -> C j = true).

(* T1.  On a finite model the closest-worlds condition and Lewis's general
   condition agree.  Lewis p. 20: under the Limit Assumption the truth
   conditions simplify in this way. *)
Theorem would_iff_lewis : forall i A C,
  would i A C = true <-> would_lewis i A C.
Proof.
  intros i A C; split.
  - unfold would; rewrite forallb_forall; intros H.
    destruct (existsb A dom) eqn:E.
    + apply existsb_exists in E.
      destruct (exists_min (rank i) A dom E) as (m & Hm & HAm & Hmin).
      right. exists m. repeat split; auto.
      intros j Hj Hle HAj. apply H. apply closest_spec. repeat split; auto.
      intros k Hk HAk. specialize (Hmin k Hk HAk). lia.
    + left. intros k Hk. destruct (A k) eqn:Ek; auto.
      assert (existsb A dom = true) by (apply existsb_exists; eauto).
      congruence.
  - intros [Hvac | (k & Hk & HAk & Hall)]; unfold would;
      apply forallb_forall; intros x Hx; apply closest_spec in Hx;
      destruct Hx as (Hx & HAx & Hmin).
    + rewrite (Hvac x Hx) in HAx; discriminate.
    + apply Hall; auto.
Qed.

Lemma existsb_negb_forallb : forall (f : W -> bool) l,
  existsb f l = negb (forallb (fun x => negb (f x)) l).
Proof.
  intros f l; induction l as [|a l IH]; simpl; auto.
  rewrite IH, negb_andb, negb_involutive. reflexivity.
Qed.

(* T2.  'might' is the dual of 'would'.  Lewis p. 21 takes this as the
   definition of 'might' and derives the closest-worlds condition; here the
   closest-worlds condition is the definition and the duality is derived. *)
Theorem might_dual : forall i A C,
  might i A C = negb (would i A (pneg C)).
Proof. intros; apply existsb_negb_forallb. Qed.

(* T3.  If there is no antecedent-world, 'would' is vacuously true and
   'might' is false.  Lewis p. 16 (the vacuous case), p. 22 (might). *)
Theorem vacuous_truth : forall i A C,
  (forall k, In k dom -> A k = false) ->
  would i A C = true /\ might i A C = false.
Proof.
  intros i A C Hvac.
  assert (E : closest i A = []).
  { destruct (closest i A) as [|x l] eqn:E; auto.
    assert (Hx : In x (closest i A)) by (rewrite E; left; auto).
    apply closest_spec in Hx. destruct Hx as (Hx & HAx & _).
    rewrite (Hvac x Hx) in HAx; discriminate. }
  unfold would, might; rewrite E; split; reflexivity.
Qed.

(* Weak centering: no world is closer to i than i itself.  Lewis p. 29,
   condition (W), in comparative terms. *)
Definition weakly_centered (i : W) : Prop :=
  In i dom /\ forall j, In j dom -> rank i i <= rank i j.

(* Centering: no other world is even as close to i as i itself.  Lewis p. 48,
   condition (4); p. 14, condition (C). *)
Definition centered (i : W) : Prop :=
  In i dom /\ forall j, In j dom -> rank i j <= rank i i -> j = i.

(* ours: centering implies weak centering. *)
Lemma centered_weakly : forall i, centered i -> weakly_centered i.
Proof.
  intros i [Hi Hc]; split; auto. intros j Hj.
  destruct (le_lt_dec (rank i i) (rank i j)); auto.
  assert (j = i) by (apply Hc; auto; lia). subst; lia.
Qed.

(* T4.  Modus ponens for 'would' under weak centering.  Lewis p. 27 states
   the pattern; p. 29 says it survives the retreat to weak centering. *)
Theorem modus_ponens : forall i A C,
  weakly_centered i -> would i A C = true -> A i = true -> C i = true.
Proof.
  intros i A C [Hi Hc]; unfold would; rewrite forallb_forall; intros H HA.
  apply H; apply closest_spec; repeat split; auto.
Qed.

(* T5.  Under centering a true antecedent and a true consequent give a true
   counterfactual.  Lewis p. 26, the second of the two inference-patterns
   at the foot of the page; p. 29 says it is lost under weak centering. *)
Theorem centering_and : forall i A C,
  centered i -> A i = true -> C i = true -> would i A C = true.
Proof.
  intros i A C [Hi Hc] HA HC; unfold would; apply forallb_forall.
  intros x Hx; apply closest_spec in Hx; destruct Hx as (Hx & HAx & Hmin).
  assert (x = i) by (apply Hc; auto). subst; auto.
Qed.

(* Stalnaker's Assumption, in the form Lewis gives on p. 79 for the case
   where every proposition is expressible: the ordering around i is linear,
   so no two listed worlds are tied.  Stalnaker 1968 itself was not read. *)
Definition stalnaker (i : W) : Prop :=
  forall j k, In j dom -> In k dom -> rank i j = rank i k -> j = k.

(* T6.  Conditional Excluded Middle under Stalnaker's Assumption.
   Lewis p. 79. *)
Theorem cem_stalnaker : forall i A C,
  stalnaker i -> would i A C = true \/ would i A (pneg C) = true.
Proof.
  intros i A C Hs. destruct (closest i A) as [|x l] eqn:E.
  - left; unfold would; rewrite E; reflexivity.
  - assert (Hall : forall y, In y (closest i A) -> y = x).
    { intros y Hy.
      assert (Hx : In x (closest i A)) by (rewrite E; left; auto).
      apply closest_spec in Hy; apply closest_spec in Hx.
      destruct Hy as (Hy & HAy & Hmy); destruct Hx as (Hx & HAx & Hmx).
      apply Hs; auto. apply Nat.le_antisymm; auto. }
    destruct (C x) eqn:Ec; [left|right]; unfold would;
      apply forallb_forall; intros y Hy; rewrite (Hall y Hy);
      unfold pneg; rewrite ?Ec; auto.
Qed.

(* Stalnaker's Assumption as Lewis states it, sec. 3.4 p. 78: for every
   antecedent that is entertainable at i there is a sphere around i that
   contains exactly one antecedent-world.  In terms of closest worlds: the
   antecedent has at most one closest world.  It has at least one whenever
   it is entertainable, by exists_min.  Added on review; the linear form
   above is the stronger condition of p. 79. *)
Definition stalnaker_at (i : W) (A : prop) : Prop :=
  forall j k, In j (closest i A) -> In k (closest i A) -> j = k.

(* T6'.  Conditional Excluded Middle for one antecedent, from Stalnaker's
   Assumption at that antecedent.  Lewis pp. 78-79. *)
Theorem cem_stalnaker_at : forall i A C,
  stalnaker_at i A -> would i A C = true \/ would i A (pneg C) = true.
Proof.
  intros i A C Hs. destruct (closest i A) as [|x l] eqn:E.
  - left; unfold would; rewrite E; reflexivity.
  - assert (Hall : forall y, In y (closest i A) -> y = x).
    { intros y Hy. apply Hs; [exact Hy | rewrite E; left; reflexivity]. }
    destruct (C x) eqn:Ec; [left|right]; unfold would;
      apply forallb_forall; intros y Hy; rewrite (Hall y Hy);
      unfold pneg; rewrite ?Ec; auto.
Qed.

(* ours: the linear form implies the assumption at every antecedent. *)
Theorem stalnaker_linear_implies_at : forall i,
  stalnaker i -> forall A, stalnaker_at i A.
Proof.
  intros i Hs A j k Hj Hk.
  apply closest_spec in Hj; apply closest_spec in Hk.
  destruct Hj as (Hj & HAj & Hmj); destruct Hk as (Hk & HAk & Hmk).
  apply Hs; auto. apply Nat.le_antisymm; auto.
Qed.

(* T7.  The valid special case of transitivity.  Lewis p. 35, the simplified
   pattern: from X []-> A and (X & A) []-> C infer X []-> C. *)
Theorem restricted_transitivity : forall i X A C,
  would i X A = true -> would i (pand X A) C = true -> would i X C = true.
Proof.
  intros i X A C; unfold would; rewrite !forallb_forall; intros H1 H2 x Hx.
  apply H2. pose proof (H1 x Hx) as HAx.
  apply closest_spec in Hx; destruct Hx as (Hd & HX & Hmin).
  apply closest_spec; repeat split; auto.
  - unfold pand; rewrite HX, HAx; auto.
  - intros k Hk Hk'. unfold pand in Hk'.
    apply andb_true_iff in Hk'; destruct Hk' as [HXk _]. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(*  The dynamic strict conditional (von Fintel 2001, definition (22))      *)
(* ---------------------------------------------------------------------- *)

(* The worlds added to the horizon by antecedent A: those at least as close
   to i as every A-world.  von Fintel (22a), p. 138; the same set appears in
   Gillies's Definition 3. *)
Definition vf_reach (i : W) (A : prop) : list W :=
  filter (at_least_as_close i A) dom.

(* Context change: the horizon h grows, it never shrinks.  (22a), p. 138;
   "one-way street", p. 139. *)
Definition vf_update (h : list W) (i : W) (A : prop) : list W :=
  h ++ vf_reach i A.

(* A strict conditional over a fixed set of worlds. *)
Definition strict (h : list W) (A C : prop) : bool :=
  forallb (fun w => implb (A w) (C w)) h.

(* Truth of a counterfactual: strict over the updated horizon.  (22b). *)
Definition vf_would (h : list W) (i : W) (A C : prop) : bool :=
  strict (vf_update h i A) A C.

(* ours: a sequence of counterfactuals is accepted from horizon h when each
   is true in the horizon it meets, the horizon being passed on. *)
Fixpoint vf_seq (h : list W) (i : W) (l : list (prop * prop)) : bool :=
  match l with
  | [] => true
  | (A, C) :: l' => vf_would h i A C && vf_seq (vf_update h i A) i l'
  end.

Lemma strict_filter : forall (A C : prop) (m : W -> bool) l,
  forallb (fun w => implb (A w) (C w)) (filter m l) =
  forallb C (filter (fun j => A j && m j) l).
Proof.
  intros A C m l; induction l as [|a l IH]; simpl; auto.
  destruct (m a) eqn:Em, (A a) eqn:Ea; simpl; rewrite ?Em, ?Ea; simpl; rewrite ?IH; auto.
Qed.

(* ours: the dynamic conditional is the Lewis conditional together with a
   strict conditional over the worlds already in the horizon. *)
Lemma vf_decompose : forall h i A C,
  vf_would h i A C = strict h A C && would i A C.
Proof.
  intros; unfold vf_would, vf_update, strict, vf_reach, would, closest.
  rewrite forallb_app, strict_filter. reflexivity.
Qed.

(* T8.  In the null context, where the horizon at i is just {i}, the dynamic
   conditional has the same truth value as 'would'.  von Fintel p. 139
   ("does not lead to a difference in the truth-conditions derived for an
   isolated counterfactual").  Weak centering is the premise we need; von
   Fintel does not state it at that point. *)
Theorem vf_null_context : forall i A C,
  weakly_centered i -> vf_would [i] i A C = would i A C.
Proof.
  intros i A C Hc; rewrite vf_decompose; unfold strict; simpl.
  rewrite andb_true_r.
  destruct (would i A C) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r. destruct (A i) eqn:EA; simpl; auto.
  apply (modus_ponens i A C); auto.
Qed.

End Ordering.

Arguments pneg {W} A w.
Arguments pand {W} A B w.

(* ========================================================================== *)
(*  Worked model                                                              *)
(* ========================================================================== *)
(* Four worlds for von Fintel's example (10), p. 130 (after Lewis p. 10):
     actual  nobody disarms; no war
     usA     only the USA disarms; war
     usB     only the USA disarms; war; and a further fact 'odd' holds
     allD    all nuclear powers disarm; no war
   Seen from actual: actual < usA = usB < allD.  The tie between usA and usB
   is what makes Conditional Excluded Middle fail.  'odd' is ours: any
   proposition that separates the two tied worlds. *)
Module Model.

Inductive world := actual | usA | usB | allD.

Definition dom : list world := [actual; usA; usB; allD].

Definition world_eqb (a b : world) : bool :=
  match a, b with
  | actual, actual | usA, usA | usB, usB | allD, allD => true
  | _, _ => false
  end.

Definition base (w : world) : nat :=
  match w with actual => 0 | usA => 1 | usB => 1 | allD => 2 end.

(* Around actual the ordering is base; around any other world, that world
   comes first and the rest are tied.  Only the ordering around actual is
   used below. *)
Definition rank (i j : world) : nat :=
  match i with
  | actual => base j
  | _ => if world_eqb i j then 0 else 1
  end.

Definition usa  : prop world := fun w => match w with actual => false | _ => true end.
Definition all  : prop world := fun w => match w with allD => true | _ => false end.
Definition war  : prop world := fun w => match w with usA | usB => true | _ => false end.
Definition odd  : prop world := fun w => match w with usB => true | _ => false end.
Definition peace : prop world := pneg war.
Definition never : prop world := fun _ => false.

Notation Would := (would world dom rank actual).
Notation Might := (might world dom rank actual).

(* Computed results. *)
Example closest_usa : closest world dom rank actual usa = [usA; usB].
Proof. reflexivity. Qed.

Example closest_all : closest world dom rank actual all = [allD].
Proof. reflexivity. Qed.

(* The Sobel sequence, von Fintel (10) p. 130; Lewis p. 10: both sentences
   are true at actual, together with the negated opposite of the second. *)
Example sobel_sequence :
  Would usa war = true /\ Would all peace = true /\ Would all war = false.
Proof. repeat split. Qed.

(* The premises of T3, T4, T5, T8 are satisfiable: the model is centered
   (hence weakly centered) on actual, and 'never' has no worlds. *)
Example model_centered : centered world dom rank actual.
Proof.
  split; [left; reflexivity|].
  intros j _; destruct j; simpl; intros H; try reflexivity; lia.
Qed.

Example vacuous_instance : Would never war = true /\ Might never war = false.
Proof. split; reflexivity. Qed.

Example might_instance :
  Might usa odd = true /\ Might usa (pneg odd) = true /\ Might usa peace = false.
Proof. repeat split. Qed.

(* T7 at work: all []-> usa and (all & usa) []-> peace, so all []-> peace. *)
Example restricted_transitivity_instance :
  Would all usa = true /\ Would (pand all usa) peace = true /\
  Would all peace = true.
Proof. repeat split. Qed.

(* Separating example 1.  Strengthening the antecedent fails (Lewis p. 31):
   usa []-> war, but not (usa & all) []-> war. *)
Theorem strengthening_fails :
  ~ (forall A B C : prop world,
       Would A C = true -> Would (pand A B) C = true).
Proof. intros H. specialize (H usa all war eq_refl). discriminate H. Qed.

(* Separating example 2.  Transitivity fails (Lewis p. 32):
   all []-> usa and usa []-> war, but not all []-> war. *)
Theorem transitivity_fails :
  ~ (forall A B C : prop world,
       Would A B = true -> Would B C = true -> Would A C = true).
Proof. intros H. specialize (H all usa war eq_refl eq_refl). discriminate H. Qed.

(* Separating example 3.  Contraposition fails (Lewis p. 35):
   usa []-> not all, but not (all []-> not usa). *)
Theorem contraposition_fails :
  ~ (forall A C : prop world,
       Would A C = true -> Would (pneg C) (pneg A) = true).
Proof. intros H. specialize (H usa (pneg all) eq_refl). discriminate H. Qed.

(* Separating example 4.  Conditional Excluded Middle fails when two closest
   antecedent-worlds are tied (Lewis p. 80: comparative similarity permits
   ties): neither usa []-> odd nor usa []-> not odd. *)
Theorem cem_fails :
  ~ (forall A C : prop world,
       Would A C = true \/ Would A (pneg C) = true).
Proof. intros H. destruct (H usa odd) as [E|E]; discriminate E. Qed.

(* Hence the model does not satisfy Stalnaker's Assumption at actual. *)
Theorem model_not_stalnaker : ~ stalnaker world dom rank actual.
Proof. intros H. exact (cem_fails (fun A C => cem_stalnaker _ _ _ actual A C H)). Qed.

(* Stalnaker's Assumption antecedent by antecedent: it fails at actual for
   'usa', which has two tied closest worlds, and holds for 'all', which has
   one.  So the assumption can hold of some antecedents of a model and not
   of others; the linear form cannot express that. *)
Example stalnaker_at_on_the_model :
  ~ stalnaker_at world dom rank actual usa /\ stalnaker_at world dom rank actual all.
Proof.
  split.
  - intros H. assert (E : usA = usB)
      by (apply H; rewrite closest_usa; simpl; auto).
    discriminate E.
  - intros j k Hj Hk. rewrite closest_all in Hj, Hk.
    destruct Hj as [<-|[]]. destruct Hk as [<-|[]]. reflexivity.
Qed.

(* The premise of T6 is satisfiable: break the tie.  Around actual:
   actual < usA < usB < allD. *)
Definition base2 (w : world) : nat :=
  match w with actual => 0 | usA => 1 | usB => 2 | allD => 3 end.
Definition rank2 (i j : world) : nat :=
  match i with
  | actual => base2 j
  | _ => if world_eqb i j then 0 else 1
  end.

Example model2_stalnaker : stalnaker world dom rank2 actual.
Proof. intros j k _ _; destruct j, k; simpl; intros H; try reflexivity; discriminate H. Qed.

Example model2_cem_instance :
  would world dom rank2 actual usa odd = false /\
  would world dom rank2 actual usa (pneg odd) = true.
Proof. split; reflexivity. Qed.

(* The dynamic account on the same model, starting from the null context
   [actual].  von Fintel p. 142: the Lewis-Sobel sequence (10) is accepted,
   the reversed sequence (11) is not, because the horizon reached by the
   first sentence of (11) already contains allD, a usa-world without war. *)
Example sobel_dynamic_ok :
  vf_seq world dom rank [actual] actual [(usa, war); (all, peace)] = true.
Proof. reflexivity. Qed.

Theorem reverse_sobel_dynamic_fails :
  vf_seq world dom rank [actual] actual [(all, peace); (usa, war)] = false.
Proof. reflexivity. Qed.

(* The horizon after the first sentence of the reversed sequence. *)
Example horizon_after_all :
  vf_update world dom rank [actual] actual all = [actual; actual; usA; usB; allD].
Proof. reflexivity. Qed.

(* By contrast the static 'would' does not see the order: both sentences are
   true at actual whichever comes first. *)
Example sobel_static_order_free :
  Would usa war && Would all peace = true /\
  Would all peace && Would usa war = true.
Proof. split; reflexivity. Qed.

End Model.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Under Coq 8.20.1 every theorem below prints "Closed under the global
   context": no axioms, no classical principles, no extensionality. *)
Print Assumptions would_iff_lewis.
Print Assumptions might_dual.
Print Assumptions vacuous_truth.
Print Assumptions modus_ponens.
Print Assumptions centering_and.
Print Assumptions cem_stalnaker.
Print Assumptions cem_stalnaker_at.
Print Assumptions stalnaker_linear_implies_at.
Print Assumptions restricted_transitivity.
Print Assumptions vf_null_context.
Print Assumptions vf_decompose.
Print Assumptions Model.sobel_sequence.
Print Assumptions Model.model_centered.
Print Assumptions Model.vacuous_instance.
Print Assumptions Model.might_instance.
Print Assumptions Model.restricted_transitivity_instance.
Print Assumptions Model.strengthening_fails.
Print Assumptions Model.transitivity_fails.
Print Assumptions Model.contraposition_fails.
Print Assumptions Model.cem_fails.
Print Assumptions Model.model_not_stalnaker.
Print Assumptions Model.stalnaker_at_on_the_model.
Print Assumptions Model.model2_stalnaker.
Print Assumptions Model.model2_cem_instance.
Print Assumptions Model.sobel_dynamic_ok.
Print Assumptions Model.reverse_sobel_dynamic_fails.
Print Assumptions Model.sobel_static_order_free.
