Require Import List Bool.
Import ListNotations.

(* ========================================================================== *)
(*  Focus_Alternatives.v — focus and alternatives as side effects             *)
(*  FORMAL-ATLAS / atlas/model_theoretic (standard library only)              *)
(* ========================================================================== *)
(*
   SOURCE (read for this file)
     [C]  Charlow, S. (2014). On the semantics of exceptional scope.
          PhD dissertation, New York University.  Read: §5.4.1-5.4.4
          (pp. 135-145) and §5.5 (pp. 147-159).
          Not read: §5.1-5.3 (sloppy readings, cross-categorial and maximal
          drefs).  Read but not formalized: §5.4.5.

   WHAT IS FORMALIZED
     Part A, focus.  The Focus monad [C Def 5.6, p. 139] pairs a value with
     a set of alternatives.  F-marking puts the alternatives in; "only" and
     "also" [C Def 5.10, p. 141] consume them.
       T1  focus_monad_laws         LeftID, RightID, Assoc for Def 5.6
       T2  focus_application        Fact 5.4, p. 139 (and focus_value, (5.30))
       T3  association_single       "only met JOHN_F", p. 141
           association_unselective  "only introduced BILL_F to SUE_F",
                                    pp. 141-142
       T4  selective_association    "also only introduced BILL_F to SUE_F",
                                    pp. 142-143; nested (5.27b) and crossed
                                    (5.28b) are both instances
       T5  focus_survives_reset     the Reset derivation, p. 144
           layered_island, selective_across_island
                                    the higher-order program, p. 144
     A model with four people separates the three readings of
     "also only introduced BILL_F to SUE_F".

     Part B, alternatives.  The Reader.Set monad [C p. 153]: a program is a
     function from a stack to a set of values.
       T6  reader_set_reset_indefinite   Fact 5.7, p. 154
           reader_set_reset_universal    Fact 5.8, p. 155
       T7  binding_simplification        Fact 5.12, p. 157
           reader_set_binding            "a linguist rubbed his head", p. 157
           binding_lost_on_evaluation    the remark on p. 158
       T8  PaperModel.abstraction_overgenerates
                                         example (5.39), pp. 150-151

   ENCODING CHOICES (ours; each departs from the printed notation)
     - Equality of Focus programs (feq) is equality of the first members
       and the same elements in the second.  Equality of Reader.Set
       programs (req) is pointwise.  No extensionality axiom is used.
     - VP meanings are properties E -> W -> Prop, with W the worlds.  Two
       properties are compared by peq (true of the same individuals at the
       same worlds).  [C] compares them by set identity.
     - "only" follows the gloss on p. 141: the regular value holds, and
       every alternative that holds is the regular value.  The printed
       equation {P | P in P1 /\ P x w} = {P0} also requires P0 to be among
       the alternatives; only_printed_form states the two agree when it is.
     - Each result that reduces a comparison of properties to a comparison
       of individuals carries a premise: distinct alternatives give
       distinct properties.  [C] makes these steps without stating it.
       The model shows the premise is satisfiable when worlds vary.
     - In T3 and T4 the alternatives range over Alt.  [C] prints
       {y | met y x w} = {j} with no restriction on y.
     - Reader.Set truth values are booleans and negation is a relation, as
       in Exceptional_Scope.v.  The pronoun returns nothing on the empty
       stack.
     - T8 takes the set {read y x | paper y} of (5.39a) as given; states
       and assignment modification (Def 5.13) are not modelled.

   NOT FORMALIZED
     Rooth's two-dimensional semantics as a separate system (Def 5.4, 5.5),
     doubly focused words (5.31)-(5.32), layering of the two monads
     (§5.4.5), disjunction (Def 5.20), the layered derivation Fact 5.9,
     Novel & Romero's repair (Def 5.14, 5.15) and the Binder Roof
     Constraint argument on p. 152.
*)

(* ========================================================================== *)
(*  Part A.  The Focus monad                                                  *)
(* ========================================================================== *)

Section Focus.

Variable E : Type.                       (* entities *)
Variable W : Type.                       (* worlds *)
Variable Alt : E -> E -> Prop.           (* Alt a x: x is an alternative to a *)

(* VP meanings; type t is the type of propositions [C p. 136]. *)
Definition Pr : Type := E -> W -> Prop.
Definition peq (P Q : Pr) : Prop := forall x w, P x w <-> Q x w.

(* [C Def 5.6, p. 139]. *)
Definition FM (A : Type) : Type := (A * (A -> Prop))%type.

Definition feta {A : Type} (a : A) : FM A := (a, fun b => b = a).

Definition fbind {A B : Type} (m : FM A) (k : A -> FM B) : FM B :=
  (fst (k (fst m)), fun b => exists a, snd m a /\ snd (k a) b).

Definition feq {A : Type} (m n : FM A) : Prop :=
  fst m = fst n /\ forall a, snd m a <-> snd n a.

(* T1 *)
Theorem focus_monad_laws :
  forall (A B C : Type) (a : A) (m : FM A) (k : A -> FM B) (h : B -> FM C),
    feq (fbind (feta a) k) (k a)
    /\ feq (fbind m feta) m
    /\ feq (fbind (fbind m k) h) (fbind m (fun x => fbind (k x) h)).
Proof.
  intros A B C a m k h. unfold feq, fbind, feta. cbn [fst snd].
  split; [| split].
  - split; [reflexivity |]. intro b. split.
    + intros (a0 & Ha & Hk). subst a0. exact Hk.
    + intro Hk. exists a. split; [reflexivity | exact Hk].
  - split; [reflexivity |]. intro b. split.
    + intros (a0 & Hm & Hb). subst b. exact Hm.
    + intro Hm. exists b. split; [exact Hm | reflexivity].
  - split; [reflexivity |]. intro c. split.
    + intros (b & (a0 & Hm & Hk) & Hh). exists a0. split; [exact Hm |].
      exists b. split; assumption.
    + intros (a0 & Hm & b & Hk & Hh). exists b.
      split; [exists a0; split; assumption | exact Hh].
Qed.

(* Monadic application. *)
Definition fapp {A B : Type} (m : FM (A -> B)) (n : FM A) : FM B :=
  fbind m (fun f => fbind n (fun x => feta (f x))).

(* T2 [C Fact 5.4, p. 139]: ordinary application on the first members,
   pointwise application on the second. *)
Theorem focus_application :
  forall (A B : Type) (m : FM (A -> B)) (n : FM A),
    fst (fapp m n) = fst m (fst n)
    /\ forall b, snd (fapp m n) b <-> exists f x, snd m f /\ snd n x /\ b = f x.
Proof.
  intros A B m n. unfold fapp, fbind, feta. cbn [fst snd].
  split; [reflexivity |]. intro b. split.
  - intros (f & Hf & x & Hx & Hb). exists f, x. auto.
  - intros (f & x & Hf & Hx & Hb). exists f. split; [exact Hf |].
    exists x. split; assumption.
Qed.

(* [C Def 5.7, p. 139]. *)
Definition Fmark (a : E) : FM E := (a, Alt a).

(* Continuations [C Def 5.8, 5.9, pp. 139-140]. *)
Definition FK (R A : Type) : Type := (A -> FM R) -> FM R.
Definition flift {R A : Type} (m : FM A) : FK R A := fun k => fbind m k.
Definition flower {A : Type} (t : FK A A) : FM A := t feta.
Definition freset {R A : Type} (t : FK A A) : FK R A := flift (flower t).

(* [C (5.30), p. 140]: "JOHN_F left". *)
Lemma focus_value :
  forall (T : Type) (left : E -> T) (j : E),
    fst (flower (fun k => fbind (Fmark j) (fun x => k (left x)))) = left j
    /\ forall p, snd (flower (fun k => fbind (Fmark j) (fun x => k (left x)))) p
                 <-> exists x, Alt j x /\ p = left x.
Proof.
  intros T left j. unfold flower, fbind, Fmark, feta. cbn [fst snd].
  split; [reflexivity |]. intro p. apply iff_refl.
Qed.

(* [C Def 5.10, p. 141]. *)
Definition only (P : FM Pr) : Pr :=
  fun x w => fst P x w /\ forall Q, snd P Q -> Q x w -> peq Q (fst P).

Definition also (P : FM Pr) : Pr :=
  fun x w => fst P x w /\ exists Q, snd P Q /\ Q x w /\ ~ peq Q (fst P).

(* The printed equation, when the regular value is among the alternatives. *)
Lemma only_printed_form :
  forall (P : FM Pr) (x : E) (w : W),
    (exists Q, snd P Q /\ peq Q (fst P)) ->
    (only P x w <-> forall Q, snd P Q -> (Q x w <-> peq Q (fst P))).
Proof.
  intros P x w (Q0 & HQ0 & Hp0). unfold only. split.
  - intros (H1 & H2) Q HQ. split.
    + intro HQx. apply H2; assumption.
    + intro Hp. apply Hp. exact H1.
  - intro H. split.
    + apply Hp0. apply (H Q0 HQ0). exact Hp0.
    + intros Q HQ HQx. apply (H Q HQ). exact HQx.
Qed.

(* T3 [C p. 141]: "only met JOHN_F" holds of x at w iff x met John and
   nobody else among the alternatives. *)
Theorem association_single :
  forall (met : E -> Pr) (j x : E) (w : W),
    (forall y, Alt j y -> peq (met y) (met j) -> y = j) ->
    (only (flower (fun k => fbind (Fmark j) (fun y => k (met y)))) x w
     <-> met j x w /\ forall y, Alt j y -> met y x w -> y = j).
Proof.
  intros met j x w Hd. unfold only, flower, fbind, Fmark, feta. cbn [fst snd].
  split.
  - intros (H1 & H2). split; [exact H1 |]. intros y Hy Hm.
    apply Hd; [exact Hy |]. apply H2; [| exact Hm].
    exists y. split; [exact Hy | reflexivity].
  - intros (H1 & H2). split; [exact H1 |].
    intros Q (y & Hy & HQ) HQx. subst Q. rewrite (H2 y Hy HQx).
    intros x' w'. apply iff_refl.
Qed.

(* T3 [C pp. 141-142]: with two foci and one "only", the association is
   with the pair. *)
Theorem association_unselective :
  forall (intro : E -> E -> Pr) (b s z : E) (w : W),
    (forall x y, Alt b x -> Alt s y ->
                 peq (intro x y) (intro b s) -> x = b /\ y = s) ->
    (only (flower (fun k => fbind (Fmark b) (fun x =>
                            fbind (Fmark s) (fun y => k (intro x y))))) z w
     <-> intro b s z w
         /\ forall x y, Alt b x -> Alt s y -> intro x y z w -> x = b /\ y = s).
Proof.
  intros intro b s z w Hd. unfold only, flower, fbind, Fmark, feta.
  cbn [fst snd]. split.
  - intros (H1 & H2). split; [exact H1 |]. intros x y Hx Hy Hm.
    apply Hd; [exact Hx | exact Hy |]. apply H2; [| exact Hm].
    exists x. split; [exact Hx |]. exists y. split; [exact Hy | reflexivity].
  - intros (H1 & H2). split; [exact H1 |].
    intros Q (x & Hx & y & Hy & HQ) HQz. subst Q.
    destruct (H2 x y Hx Hy HQz) as [Ex Ey]. subst x y.
    intros x' w'. apply iff_refl.
Qed.

(* "only" associated with the inner focus a, for a fixed value y of the
   outer focus: the bottom of the tower on p. 143. *)
Definition inner (R : E -> E -> Pr) (a y : E) : Pr :=
  only (flower (fun k => fbind (Fmark a) (fun x => k (R x y)))).

Lemma inner_spec :
  forall (R : E -> E -> Pr) (a : E),
    (forall x y, Alt a x -> peq (R x y) (R a y) -> x = a) ->
    forall (y z : E) (w : W),
      inner R a y z w
      <-> R a y z w /\ forall x, Alt a x -> R x y z w -> x = a.
Proof.
  intros R a H1 y z w. unfold inner.
  exact (association_single (fun x => R x y) a z w
           (fun x Hx Hp => H1 x y Hx Hp)).
Qed.

(* T4 [C pp. 142-143]: "also" > outer focus c > "only" > inner focus a.
   With R x y := intro x y, a := Bill, c := Sue this is (5.27b); with
   R y x := intro x y, a := Sue, c := Bill it is (5.28b). *)
Theorem selective_association :
  forall (R : E -> E -> Pr) (a c z : E) (w : W),
    (forall x y, Alt a x -> peq (R x y) (R a y) -> x = a) ->
    (forall y, Alt c y -> peq (inner R a y) (inner R a c) -> y = c) ->
    (also (flower (fun k => fbind (Fmark c) (fun y => k (inner R a y)))) z w
     <-> (R a c z w /\ forall x, Alt a x -> R x c z w -> x = a)
         /\ exists y, Alt c y /\ y <> c
                      /\ R a y z w /\ forall x, Alt a x -> R x y z w -> x = a).
Proof.
  intros R a c z w H1 H2.
  unfold also, flower, fbind, Fmark, feta. cbn [fst snd]. split.
  - intros (Hc & Q & (y & Hy & HQ) & HQz & Hne). subst Q.
    split; [apply (proj1 (inner_spec R a H1 c z w)); exact Hc |].
    exists y. split; [exact Hy |]. split.
    + intro Heq. subst y. apply Hne. intros x' w'. apply iff_refl.
    + apply (proj1 (inner_spec R a H1 y z w)). exact HQz.
  - intros (Hc & y & Hy & Hne & Hyz).
    split; [apply (proj2 (inner_spec R a H1 c z w)); exact Hc |].
    exists (inner R a y). split; [exists y; split; [exact Hy | reflexivity] |].
    split; [apply (proj2 (inner_spec R a H1 y z w)); exact Hyz |].
    intro Hp. apply Hne. apply H2; assumption.
Qed.

(* T5 [C p. 144]: Reset leaves a tower unchanged when its scopal tier is
   Focus-monadic sequencing, so focus alternatives scope out of an island. *)
Theorem focus_survives_reset :
  forall (A B R : Type) (m : FM A) (f : A -> B) (k : B -> FM R),
    feq (freset (fun c => fbind m (fun v => c (f v))) k)
        (fbind m (fun v => k (f v))).
Proof.
  intros A B R m f k. unfold feq, freset, flift, flower, fbind, feta.
  cbn [fst snd]. split; [reflexivity |]. intro r. split.
  - intros (b & (v & Hm & Hb) & Hk). subst b. exists v. split; assumption.
  - intros (v & Hm & Hk). exists (f v).
    split; [exists v; split; [exact Hm | reflexivity] | exact Hk].
Qed.

Lemma also_feq :
  forall (P P' : FM Pr) (x : E) (w : W),
    feq P P' -> (also P x w <-> also P' x w).
Proof.
  intros [p0 p1] [q0 q1] x w [H0 H1]. cbn [fst snd] in H0, H1. subst q0.
  unfold also. cbn [fst snd].
  split; intros (Ha & Q & HQ & Hx & Hn); (split; [exact Ha |]); exists Q;
    (split; [apply H1; exact HQ | split; assumption]).
Qed.

(* T5 [C p. 144]: the evaluated island is a program of programs, with the
   outer focus on the outer layer.  Feeding its inner layer to "only" gives
   the configuration of T4. *)
Theorem layered_island :
  forall (R : E -> E -> Pr) (a c : E),
    feq (fbind (flower (fun k => fbind (Fmark c) (fun y =>
                  k (flower (fun k' => fbind (Fmark a) (fun x => k' (R x y)))))))
               (fun P => feta (only P)))
        (flower (fun k => fbind (Fmark c) (fun y => k (inner R a y)))).
Proof.
  intros R a c. unfold feq, inner, flower, fbind, Fmark, feta. cbn [fst snd].
  split; [reflexivity |]. intro Q. split.
  - intros (P & (y & Hy & HP) & HQ). subst P. exists y.
    split; [exact Hy | exact HQ].
  - intros (y & Hy & HQ). eexists.
    split; [exists y; split; [exact Hy | reflexivity] | exact HQ].
Qed.

Corollary selective_across_island :
  forall (R : E -> E -> Pr) (a c z : E) (w : W),
    (forall x y, Alt a x -> peq (R x y) (R a y) -> x = a) ->
    (forall y, Alt c y -> peq (inner R a y) (inner R a c) -> y = c) ->
    (also (fbind (flower (fun k => fbind (Fmark c) (fun y =>
                    k (flower (fun k' => fbind (Fmark a) (fun x => k' (R x y)))))))
                 (fun P => feta (only P))) z w
     <-> (R a c z w /\ forall x, Alt a x -> R x c z w -> x = a)
         /\ exists y, Alt c y /\ y <> c
                      /\ R a y z w /\ forall x, Alt a x -> R x y z w -> x = a).
Proof.
  intros R a c z w H1 H2. eapply iff_trans.
  - apply also_feq. apply layered_island.
  - apply selective_association; assumption.
Qed.

End Focus.

Arguments peq {E W} P Q.
Arguments only {E W} P.
Arguments also {E W} P.
Arguments Fmark {E} Alt a.
Arguments inner {E W} Alt R a y.

(* -------------------------------------------------------------------------- *)
(*  A model for [C (5.27)-(5.28)].  John introduced Bill to Sue and Bill to   *)
(*  Mary, and nobody else to anybody.  A world says whom John introduced to   *)
(*  whom; worlds must vary for the alternatives to be distinct properties.    *)
(* -------------------------------------------------------------------------- *)

Module IntroModel.

Inductive Ent : Type := john | bill | sue | mary.
Definition Wd : Type := Ent -> Ent -> bool.
Definition Alt (a x : Ent) : Prop := True.

Definition intro (x y : Ent) : Pr Ent Wd := fun z w => z = john /\ w x y = true.

Definition w0 : Wd :=
  fun x y => match x, y with bill, sue | bill, mary => true | _, _ => false end.
Definition w1 : Wd :=
  fun x y => match x, y with bill, sue => true | _, _ => false end.

Definition eqE (u v : Ent) : bool :=
  match u, v with
  | john, john | bill, bill | sue, sue | mary, mary => true
  | _, _ => false
  end.

Lemma eqE_true : forall u v, eqE u v = true -> u = v.
Proof. intros u v H. destruct u, v; try reflexivity; discriminate H. Qed.

Lemma eqE_refl : forall u, eqE u u = true.
Proof. destruct u; reflexivity. Qed.

Lemma intro_inj :
  forall x y x' y', peq (intro x y) (intro x' y') -> x = x' /\ y = y'.
Proof.
  intros x y x' y' H.
  assert (Hq : intro x' y' john (fun u v => eqE u x' && eqE v y')).
  { unfold intro. split; [reflexivity |]. rewrite !eqE_refl. reflexivity. }
  destruct (proj2 (H john _) Hq) as [_ H3]. cbv beta in H3.
  apply andb_prop in H3. destruct H3 as [Hx Hy].
  split; apply eqE_true; assumption.
Qed.

Lemma inj_first :
  forall x y, Alt bill x -> peq (intro x y) (intro bill y) -> x = bill.
Proof. intros x y _ H. destruct (intro_inj _ _ _ _ H) as [Hx _]. exact Hx. Qed.

Lemma inj_second :
  forall y x, Alt sue y -> peq (intro x y) (intro x sue) -> y = sue.
Proof. intros y x _ H. destruct (intro_inj _ _ _ _ H) as [_ Hy]. exact Hy. Qed.

Lemma inj_pair :
  forall x y, Alt bill x -> Alt sue y ->
              peq (intro x y) (intro bill sue) -> x = bill /\ y = sue.
Proof. intros x y _ _ H. exact (intro_inj _ _ _ _ H). Qed.

Lemma inner_distinct :
  forall y, Alt sue y ->
            peq (inner Alt intro bill y) (inner Alt intro bill sue) -> y = sue.
Proof.
  intros y _ H.
  assert (Hs : inner Alt intro bill sue john w1).
  { apply (proj2 (inner_spec Ent Wd Alt intro bill inj_first sue john w1)).
    split; [split; reflexivity |]. intros x _ [_ Hx].
    destruct x; compute in Hx; try discriminate Hx; reflexivity. }
  apply (proj2 (H john w1)) in Hs.
  apply (proj1 (inner_spec Ent Wd Alt intro bill inj_first y john w1)) in Hs.
  destruct Hs as [[_ Hy] _].
  destruct y; compute in Hy; try discriminate Hy; reflexivity.
Qed.

(* Nested, (5.27b): "also" with Sue, "only" with Bill.  True: Bill is the
   only one introduced to Sue, and the same holds of Mary. *)
Example nested_true :
  also (flower (fun k => fbind (Fmark Alt sue)
                           (fun y => k (inner Alt intro bill y)))) john w0.
Proof.
  apply (proj2 (selective_association Ent Wd Alt intro bill sue john w0
                  inj_first inner_distinct)).
  split.
  - split; [split; reflexivity |]. intros x _ [_ Hx].
    destruct x; compute in Hx; try discriminate Hx; reflexivity.
  - exists mary. split; [exact I |]. split; [discriminate |].
    split; [split; reflexivity |]. intros x _ [_ Hx].
    destruct x; compute in Hx; try discriminate Hx; reflexivity.
Qed.

(* Crossed, (5.28b): "also" with Bill, "only" with Sue.  False: Bill was
   introduced to Mary as well. *)
Example crossed_false :
  ~ also (flower (fun k => fbind (Fmark Alt bill)
                    (fun x => k (inner Alt (fun y x => intro x y) sue x)))) john w0.
Proof.
  intro H. unfold also, flower, fbind, Fmark, feta in H. cbn [fst snd] in H.
  destruct H as [Hc _].
  apply (proj1 (inner_spec Ent Wd Alt (fun y x => intro x y) sue
                  inj_second bill john w0)) in Hc.
  destruct Hc as [_ Hall].
  assert (Hm : mary = sue) by (apply Hall; [exact I | split; reflexivity]).
  discriminate Hm.
Qed.

(* Unselective: one "only" for both foci.  False for the same reason. *)
Example unselective_false :
  ~ only (flower (fun k => fbind (Fmark Alt bill) (fun x =>
                           fbind (Fmark Alt sue) (fun y => k (intro x y))))) john w0.
Proof.
  intro H.
  apply (proj1 (association_unselective Ent Wd Alt intro bill sue john w0
                  inj_pair)) in H.
  destruct H as [_ H].
  assert (Hm : bill = bill /\ mary = sue)
    by (apply H; [exact I | exact I | split; reflexivity]).
  destruct Hm as [_ Hm]. discriminate Hm.
Qed.

End IntroModel.

(* ========================================================================== *)
(*  Part B.  The Reader.Set monad                                             *)
(* ========================================================================== *)

Section ReaderSet.

Variable E : Type.

Definition Stack : Type := list E.

(* [C p. 153]. *)
Definition RM (A : Type) : Type := Stack -> A -> Prop.

Definition reta {A : Type} (a : A) : RM A := fun _ b => b = a.

Definition rbind {A B : Type} (m : RM A) (k : A -> RM B) : RM B :=
  fun s b => exists a, m s a /\ k a s b.

Definition req {A : Type} (m n : RM A) : Prop := forall s a, m s a <-> n s a.

Lemma reader_set_monad_laws :
  forall (A B C : Type) (a : A) (m : RM A) (k : A -> RM B) (h : B -> RM C),
    req (rbind (reta a) k) (k a)
    /\ req (rbind m reta) m
    /\ req (rbind (rbind m k) h) (rbind m (fun x => rbind (k x) h)).
Proof.
  intros A B C a m k h. unfold req, rbind, reta.
  split; [| split]; intros s r; split.
  - intros (a0 & Ha & Hk). subst a0. exact Hk.
  - intro Hk. exists a. split; [reflexivity | exact Hk].
  - intros (a0 & Hm & Hb). subst r. exact Hm.
  - intro Hm. exists r. split; [exact Hm | reflexivity].
  - intros (b & (a0 & Hm & Hk) & Hh). exists a0. split; [exact Hm |].
    exists b. split; assumption.
  - intros (a0 & Hm & b & Hk & Hh). exists b.
    split; [exists a0; split; assumption | exact Hh].
Qed.

(* [C Def 5.16, 5.17, p. 153]. *)
Definition RK (R A : Type) : Type := (A -> RM R) -> RM R.
Definition rlift {R A : Type} (m : RM A) : RK R A := fun k => rbind m k.
Definition rlower {A : Type} (t : RK A A) : RM A := t reta.
Definition rreset {R A : Type} (t : RK A A) : RK R A := rlift (rlower t).

(* [C p. 153]. *)
Definition rindef (P : E -> Prop) : RM E := fun _ x => P x.
Definition rpro : RM E := fun s x => hd_error s = Some x.

(* [C Def 5.18, 5.19, p. 154]. *)
Definition rnot (m : RM bool) : RM bool := fun s b => b = true <-> ~ m s true.
Definition revery (P : E -> Prop) : RK bool E :=
  fun k => rnot (rbind (rindef P) (fun x => rnot (k x))).

(* T6 [C Fact 5.7, p. 154]: an indefinite's alternatives survive Reset. *)
Theorem reader_set_reset_indefinite :
  forall (A B R : Type) (m : RM A) (f : A -> B) (k : B -> RM R),
    req (rreset (fun c => rbind m (fun v => c (f v))) k)
        (rbind m (fun v => k (f v))).
Proof.
  intros A B R m f k s r. unfold rreset, rlift, rlower, rbind, reta. split.
  - intros (b & (v & Hm & Hb) & Hk). subst b. exists v. split; assumption.
  - intros (v & Hm & Hk). exists (f v).
    split; [exists v; split; [exact Hm | reflexivity] | exact Hk].
Qed.

Lemma runiv_bool :
  forall (P : E -> Prop) (f : E -> bool),
    (~ exists x, P x /\ (true = true <-> ~ true = f x))
    <-> forall x, P x -> f x = true.
Proof.
  intros P f. split.
  - intros H x Px. destruct (f x) eqn:Hf; [reflexivity |]. exfalso. apply H.
    exists x. split; [exact Px |]. rewrite Hf.
    split; [intros _ H0; discriminate H0 | intros _; reflexivity].
  - intros H (x & Px & [Hi _]). apply (Hi eq_refl). symmetry. apply H. exact Px.
Qed.

(* T6 [C Fact 5.8, p. 155]: after Reset "every P left" is one truth value
   on the bottom, with nothing on the scopal tier. *)
Theorem reader_set_reset_universal :
  forall (R : Type) (P : E -> Prop) (left : E -> bool)
         (k : bool -> RM R) (s : Stack) (r : R),
    rreset (fun c => revery P (fun x => c (left x))) k s r
    <-> exists b, (b = true <-> forall x, P x -> left x = true) /\ k b s r.
Proof.
  intros R P left k s r.
  unfold rreset, rlift, rlower, rbind, revery, rnot, rindef, reta. split.
  - intros (b & Hb & Hk). exists b. split; [| exact Hk].
    eapply iff_trans; [exact Hb | exact (runiv_bool P left)].
  - intros (b & Hb & Hk). exists b. split; [| exact Hk].
    eapply iff_trans; [exact Hb | apply iff_sym; exact (runiv_bool P left)].
Qed.

(* [C Def 5.21, p. 156]. *)
Definition bshift {R : Type} (t : RK R E) : RK R E :=
  fun k => t (fun a s => k a (a :: s)).

(* T7 [C Fact 5.12, p. 157]. *)
Lemma binding_simplification :
  forall (A : Type) (k : E -> RM A) (a : E) (s : Stack) (r : A),
    rbind rpro k (a :: s) r <-> k a (a :: s) r.
Proof.
  intros A k a s r. unfold rbind, rpro. cbn [hd_error]. split.
  - intros (y & Hy & Hk). inversion Hy; subst. exact Hk.
  - intro Hk. exists a. split; [reflexivity | exact Hk].
Qed.

(* T7 [C p. 157]: "a linguist rubbed his head".  The bind-shifted
   indefinite binds the pronoun in its scope, at any incoming stack. *)
Theorem reader_set_binding :
  forall (A : Type) (P : E -> Prop) (g : E -> E -> A),
    req (rlower (fun c => bshift (rlift (rindef P))
                            (fun x => rbind rpro (fun y => c (g y x)))))
        (rbind (rindef P) (fun x => reta (g x x))).
Proof.
  intros A P g s r. unfold rlower, bshift, rlift, rbind, rindef, rpro, reta.
  cbn [hd_error]. split.
  - intros (x & Px & y & Hy & Hr). inversion Hy; subst.
    eexists. split; [eassumption | reflexivity].
  - intros (x & Px & Hr). subst r. exists x. split; [exact Px |].
    exists x. split; reflexivity.
Qed.

(* T7 [C p. 158]: after evaluation the extended stack is gone.  A pronoun
   in the next sentence reads the incoming stack, not the indefinite. *)
Theorem binding_lost_on_evaluation :
  forall (A C : Type) (P : E -> Prop) (f : E -> A) (h : A -> E -> C)
         (s : Stack) (r : C),
    rbind (rlower (fun c => bshift (rlift (rindef P)) (fun x => c (f x))))
          (fun p => rbind rpro (fun y => reta (h p y))) s r
    <-> exists x y, P x /\ hd_error s = Some y /\ r = h (f x) y.
Proof.
  intros A C P f h s r. unfold rlower, bshift, rlift, rbind, rindef, rpro, reta.
  split.
  - intros (p & (x & Px & Hp) & y & Hy & Hr). subst p r. exists x, y. auto.
  - intros (x & y & Px & Hy & Hr). exists (f x).
    split; [exists x; split; [exact Px | reflexivity] |].
    exists y. split; assumption.
Qed.

Corollary no_binding_on_empty_stack :
  forall (A C : Type) (P : E -> Prop) (f : E -> A) (h : A -> E -> C) (r : C),
    ~ rbind (rlower (fun c => bshift (rlift (rindef P)) (fun x => c (f x))))
            (fun p => rbind rpro (fun y => reta (h p y))) [] r.
Proof.
  intros A C P f h r H. apply binding_lost_on_evaluation in H.
  destruct H as (x & y & _ & Hy & _). discriminate Hy.
Qed.

End ReaderSet.

(* -------------------------------------------------------------------------- *)
(*  T8 [C (5.39), pp. 150-151].  Three people, three papers; x did not read   *)
(*  paper x and read the other two.  Kratzer & Shimoyama's abstraction rule   *)
(*  [C Def 5.13] admits every f with f x in {read y x | paper y}.             *)
(* -------------------------------------------------------------------------- *)

Module PaperModel.

Inductive Per : Type := p1 | p2 | p3.

(* read y x: person x read paper y. *)
Definition read (y x : Per) : bool :=
  match y, x with p1, p1 | p2, p2 | p3, p3 => false | _, _ => true end.

Theorem abstraction_overgenerates :
  (* some admitted f makes "nobody read a paper" true *)
  (exists f : Per -> bool,
      (forall x, exists y, f x = read y x) /\ ~ exists x, f x = true)
  (* but no paper went unread by all *)
  /\ (~ exists y, forall x, read y x = false)
  (* and it is not the case that nobody read any paper *)
  /\ (~ forall x y, read y x = false).
Proof.
  split; [| split].
  - exists (fun x => read x x). split.
    + intro x. exists x. reflexivity.
    + intros (x & Hx). destruct x; discriminate Hx.
  - intros (y & H). destruct y.
    + discriminate (H p2).
    + discriminate (H p1).
    + discriminate (H p1).
  - intro H. discriminate (H p1 p2).
Qed.

End PaperModel.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)

Print Assumptions focus_monad_laws.
Print Assumptions focus_application.
Print Assumptions focus_value.
Print Assumptions only_printed_form.
Print Assumptions association_single.
Print Assumptions association_unselective.
Print Assumptions selective_association.
Print Assumptions focus_survives_reset.
Print Assumptions layered_island.
Print Assumptions selective_across_island.
Print Assumptions IntroModel.nested_true.
Print Assumptions IntroModel.crossed_false.
Print Assumptions IntroModel.unselective_false.
Print Assumptions reader_set_monad_laws.
Print Assumptions reader_set_reset_indefinite.
Print Assumptions reader_set_reset_universal.
Print Assumptions binding_simplification.
Print Assumptions reader_set_binding.
Print Assumptions binding_lost_on_evaluation.
Print Assumptions no_binding_on_empty_stack.
Print Assumptions PaperModel.abstraction_overgenerates.
