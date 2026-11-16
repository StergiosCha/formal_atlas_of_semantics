Require Import List Bool.
Import ListNotations.

(* ========================================================================== *)
(*  Exceptional_Scope.v — alternatives, evaluation and scope: a fragment      *)
(*  FORMAL-ATLAS / atlas/model_theoretic (standard library only)              *)
(* ========================================================================== *)
(*
   SOURCE (read for this file)
     [C]  Charlow, S. (2014). On the semantics of exceptional scope.
          PhD dissertation, New York University.  Read: §2.3.3, §2.5.2,
          §3.2.1-3.2.2, §3.3.2, §3.4-3.5.2, §3.6.1 (Fact 3.16), §4.3-4.4.2.
          Not read: Chapter 5, the appendices, §4.4.3 onwards.

   WHAT IS FORMALIZED
     The State.Set monad [C Def 2.29, p. 45]: a program returning an A is a
     function from a stack to a set of (value, stack) pairs.  The set is the
     indefinite's alternatives; the stack carries discourse referents.
     Scope-taking is added by continuations, with Lift the monad's
     sequencing and Lower its injection [C Def 3.12, 3.13, p. 68].
       T1  state_set_monad_laws   LeftID, RightID, Assoc for Def 2.29
       T2  application            Fact 2.11, p. 45
       T3  S_subsumes_A           Fact 3.14, p. 69 (and lift_eta, p. 67)
       T4  binding                Fact 2.12, p. 46, and Fact 2.13, p. 47
       T5  reset_monadic          Fact 4.1, p. 91 (Facts 4.2, 4.3 follow)
       T6  reset_universal        Fact 4.5, p. 92 (Fact 4.4 follows)
       T7  exceptional_scope_negation
                                  derivation (4.8), p. 95, with the two
                                  contrasting cases
       T8  cross_sentential_binding
                                  derivation (4.7), pp. 94-95, and the
                                  remark below it on universals
     A two-relative model separates the readings of T7.

   ENCODING CHOICES (ours; each departs from the printed notation)
     - Equality of programs is pointwise (meq): the same pairs at every
       stack.  Rocq has no function extensionality without an axiom.
     - Truth values are booleans.  [C] writes not m s as the singleton
       { <~ exists s'. <True, s'> in m s, s> }.  Here the returned boolean b
       is specified by "b = true iff ~ exists s' ...".  Without excluded
       middle this does not prove that not m s is inhabited for every m; all
       results below are stated as equivalences and do not need that.
     - The pronoun reads the top of the stack with hd_error, so it returns
       nothing on the empty stack.  [C Def 2.34] writes the top of s with no
       case for the empty stack.
     - In T7 and T8 the lexical verb meanings are arbitrary boolean
       functions; "every linguist" is every Q for an arbitrary Q.

   NOT FORMALIZED
     The tower notation as syntax, the type system and evaluated types
     (Def 4.1), internal Lift and three-level towers (§3.6.2), the Binder
     Roof Constraint (§4.4.3), plurals, disjunction, the comparison with
     choice functions, and Chapter 5.  "Scope island" appears only as the
     obligation to Reset.
*)

Section Fragment.

Variable E : Type.                       (* entities *)

(* -------------------------------------------------------------------------- *)
(*  1. The State.Set monad                                                    *)
(* -------------------------------------------------------------------------- *)

Definition Stack : Type := list E.

(* [C Def 2.29, p. 45]: M a ::= s -> (a * s) -> t *)
Definition M (A : Type) : Type := Stack -> A * Stack -> Prop.

Definition eta {A : Type} (a : A) : M A := fun s r => r = (a, s).

Definition bind {A B : Type} (m : M A) (k : A -> M B) : M B :=
  fun s r => exists a s', m s (a, s') /\ k a s' r.

(* ours: pointwise equality of programs *)
Definition meq {A : Type} (m n : M A) : Prop := forall s r, m s r <-> n s r.

(* T1.  The monad laws for Def 2.29. *)
Theorem state_set_monad_laws :
  (forall (A B : Type) (a : A) (k : A -> M B), meq (bind (eta a) k) (k a)) /\
  (forall (A : Type) (m : M A), meq (bind m eta) m) /\
  (forall (A B C : Type) (m : M A) (k : A -> M B) (h : B -> M C),
     meq (bind (bind m k) h) (bind m (fun a => bind (k a) h))).
Proof.
  unfold meq, bind, eta. split; [| split]; intros; split.
  - intros (a0 & s' & H & Hk). inversion H; subst. exact Hk.
  - intro H. eauto.
  - intros (a & s' & H & Hr). subst. exact H.
  - intro H. destruct r as [a s']. eauto.
  - intros (b & s1 & (a & s0 & Hm & Hk) & Hh). eauto 8.
  - intros (a & s0 & Hm & (b & s1 & Hk & Hh)). eauto 8.
Qed.

(* Monadic application: function first, then argument. [C §2.2.4] *)
Definition app {A B : Type} (m : M (A -> B)) (n : M A) : M B :=
  bind m (fun f => bind n (fun x => eta (f x))).

(* T2.  [C Fact 2.11, p. 45] *)
Theorem application :
  forall (A B : Type) (m : M (A -> B)) (n : M A) (s : Stack) (c : B) (s2 : Stack),
    app m n s (c, s2) <->
    exists f x s1, m s (f, s1) /\ n s1 (x, s2) /\ c = f x.
Proof.
  unfold app, bind, eta. intros; split.
  - intros (f & s1 & Hm & x & s2' & Hn & Heq). inversion Heq; subst. eauto 8.
  - intros (f & x & s1 & Hm & Hn & Hc). subst. eauto 8.
Qed.

(* -------------------------------------------------------------------------- *)
(*  2. Scope: continuations over the monad                                    *)
(* -------------------------------------------------------------------------- *)

(* A scope-taker with value type A and result type M R. [C §3.4.2] *)
Definition K (R A : Type) : Type := (A -> M R) -> M R.

(* [C Def 3.12, p. 68]: Lift is sequencing. *)
Definition lift {R A : Type} (m : M A) : K R A := fun k => bind m k.

(* [C Def 3.13, p. 68]: Lower applies the tower to eta. *)
Definition lower {A : Type} (t : K A A) : M A := t eta.

(* [C Def 3.14, p. 69]: Reset is Lower, then Lift. *)
Definition reset {R A : Type} (t : K A A) : K R A := lift (lower t).

(* Scopal application. [C Fact 3.7, p. 59] *)
Definition S_ {R A B : Type} (m : K R (A -> B)) (n : K R A) : K R B :=
  fun k => m (fun f => n (fun x => k (f x))).

(* T3.  [C Fact 3.14, p. 69]: monadic application is derivable from S,
   Lift and Lower.  It holds by unfolding. *)
Theorem S_subsumes_A :
  forall (A B : Type) (m : M (A -> B)) (n : M A),
    lower (S_ (lift m) (lift n)) = app m n.
Proof. reflexivity. Qed.

(* [C p. 67 and (3.20)]: a lifted value is its Montague lift. *)
Lemma lift_eta :
  forall (R A : Type) (a : A) (k : A -> M R), meq (lift (eta a) k) (k a).
Proof. intros. unfold lift. apply state_set_monad_laws. Qed.

(* -------------------------------------------------------------------------- *)
(*  3. Indefinites, discourse referents, pronouns                             *)
(* -------------------------------------------------------------------------- *)

(* [C Def 2.33, p. 47]: a.man = fun s => { <x, s> | man x } *)
Definition indef (P : E -> Prop) : M E := fun s r => exists x, P x /\ r = (x, s).

(* [C Def 2.31, p. 46]: dref introduction; the stack is extended by x. *)
Definition push (x : E) : M E := fun s r => r = (x, x :: s).
Definition dref (m : M E) : M E := bind m push.

(* [C Def 2.34, p. 47]: the pronoun returns the top of the stack. *)
Definition pro : M E := fun s r => exists x, hd_error s = Some x /\ r = (x, s).

(* T4.  [C Fact 2.12, p. 46] and [C Fact 2.13, p. 47]. *)
Theorem binding :
  forall (R : Type) (m : M E),
    (forall k : E -> M R,
        meq (bind (dref m) k) (bind m (fun v s => k v (v :: s)))) /\
    (forall k : E -> E -> M R,
        meq (bind (dref m) (fun v => bind pro (fun u => k v u)))
            (bind (dref m) (fun v => k v v))).
Proof.
  intros R m.
  assert (H1 : forall k : E -> M R,
             meq (bind (dref m) k) (bind m (fun v s => k v (v :: s)))).
  { intros k s r. unfold dref, bind, push. split.
    - intros (v & s1 & (a & s0 & Hm & Heq) & Hk). inversion Heq; subst. eauto.
    - intros (v & s0 & Hm & Hk). exists v, (v :: s0). eauto 8. }
  split; [exact H1 |].
  intros k s r. rewrite (H1 _ s r), (H1 _ s r). unfold bind, pro. split.
  - intros (v & s0 & Hm & u & s1 & (x & Hx & Heq) & Hk).
    simpl in Hx. inversion Hx; subst. inversion Heq; subst. eauto.
  - intros (v & s0 & Hm & Hk). exists v, s0. split; [exact Hm |].
    exists v, (v :: s0). split; [| exact Hk]. exists v. auto.
Qed.

(* -------------------------------------------------------------------------- *)
(*  4. Evaluation: what survives a Reset                                      *)
(* -------------------------------------------------------------------------- *)

(* T5.  [C Fact 4.1, p. 91]: Reset does nothing to a tower whose scopal
   tier is monadic sequencing. *)
Theorem reset_monadic :
  forall (A B R : Type) (m : M A) (f : A -> B) (k : B -> M R),
    meq (reset (fun c => bind m (fun v => c (f v))) k)
        (bind m (fun v => k (f v))).
Proof.
  intros A B R m f k s r. unfold reset, lift, lower, bind, eta. split.
  - intros (b & s1 & (v & s0 & Hm & Heq) & Hk). inversion Heq; subst. eauto.
  - intros (v & s0 & Hm & Hk). exists (f v), s0. eauto 8.
Qed.

(* [C Fact 4.2, p. 91]: "a linguist left" survives Reset. *)
Corollary reset_indefinite :
  forall (R : Type) (P : E -> Prop) (f : E -> bool) (k : bool -> M R),
    meq (reset (fun c => bind (indef P) (fun x => c (f x))) k)
        (bind (indef P) (fun x => k (f x))).
Proof. intros. apply reset_monadic. Qed.

(* [C Fact 4.3, p. 91]: "she left" survives Reset. *)
Corollary reset_pronoun :
  forall (R : Type) (f : E -> bool) (k : bool -> M R),
    meq (reset (fun c => bind pro (fun x => c (f x))) k)
        (bind pro (fun x => k (f x))).
Proof. intros. apply reset_monadic. Qed.

(* [C Def 3.2, p. 51]: negation returns one boolean and the input stack. *)
Definition not_ (m : M bool) : M bool :=
  fun s r => exists b, r = (b, s) /\ (b = true <-> ~ exists s', m s (true, s')).

(* [C Def 3.4, p. 54]: ev.ling = fun k => not (a.ling_x >>= not (k x)) *)
Definition every (P : E -> Prop) : K bool E :=
  fun k => not_ (bind (indef P) (fun x => not_ (k x))).

Lemma every_spec :
  forall (P : E -> Prop) (k : E -> M bool) (s : Stack) (b : bool) (s' : Stack),
    every P k s (b, s') <->
    s' = s /\ (b = true <-> ~ exists x, P x /\ ~ exists s1, k x s (true, s1)).
Proof.
  intros P k s b s'. unfold every, not_, bind, indef.
  assert (Hin : (exists s1 : Stack, exists (a : E) (s2 : Stack),
                    (exists x, P x /\ (a, s2) = (x, s)) /\
                    exists b1, (true, s1) = (b1, s2) /\
                               (b1 = true <-> ~ exists s3, k a s2 (true, s3)))
                <-> exists x, P x /\ ~ exists s1, k x s (true, s1)).
  { split.
    - intros (s1 & a & s2 & (x & Px & Heq) & b1 & Heq1 & Hb1).
      inversion Heq; subst. inversion Heq1; subst.
      exists x. split; [exact Px | apply Hb1; reflexivity].
    - intros (x & Px & Hn). exists s, x, s. split; [eauto |].
      exists true. split; [reflexivity |]. split; auto. }
  split.
  - intros (b0 & Heq & Hb). inversion Heq; subst. split; [reflexivity |].
    rewrite Hb, Hin. reflexivity.
  - intros (Hs & Hb). subst. exists b. split; [reflexivity |].
    rewrite Hb, Hin. reflexivity.
Qed.

(* ours: on boolean bodies the truth condition is the plain universal *)
Lemma univ_bool :
  forall (Q : E -> Prop) (f : E -> bool) (s0 : Stack),
    (~ exists y, Q y /\ ~ exists s2 : Stack, eta (f y) s0 (true, s2)) <->
    (forall y, Q y -> f y = true).
Proof.
  intros Q f s0. unfold eta. split.
  - intros Hn y Qy. destruct (f y) eqn:Hf; [reflexivity |].
    exfalso. apply Hn. exists y. split; [exact Qy |].
    intros (s2 & Heq). rewrite Hf in Heq. discriminate.
  - intros Hall (y & Qy & Hn). apply Hn. exists s0. rewrite (Hall y Qy).
    reflexivity.
Qed.

(* T6.  [C Fact 4.5, p. 92]: after Reset of "a man met every linguist" the
   indefinite and its dref stay on the scopal tier; the universal is a
   truth value on the bottom. *)
Theorem reset_universal :
  forall (R : Type) (P Q : E -> Prop) (met : E -> E -> bool)
         (k : bool -> M R) (s : Stack) (r : R * Stack),
    reset (fun c => bind (dref (indef P))
                         (fun x => every Q (fun y => c (met y x)))) k s r
    <-> exists x b, P x /\ (b = true <-> forall y, Q y -> met y x = true)
                    /\ k b (x :: s) r.
Proof.
  intros R P Q met k s r. unfold reset, lift, lower.
  unfold bind at 1. split.
  - intros (b & s1 & Hl & Hk).
    destruct Hl as (x & s0 & Hd & He).
    apply every_spec in He. destruct He as (Hs & Hb). subst s1.
    unfold dref, bind, indef, push in Hd.
    destruct Hd as (a & s2 & (x0 & Px & Heq) & Heq2).
    inversion Heq; subst. inversion Heq2; subst.
    exists x0, b. split; [exact Px |]. split; [| exact Hk].
    rewrite Hb. apply univ_bool.
  - intros (x & b & Px & Hb & Hk). exists b, (x :: s). split; [| exact Hk].
    exists x, (x :: s). split.
    + unfold dref, bind, indef, push. exists x, s. eauto.
    + apply every_spec. split; [reflexivity |]. rewrite Hb. symmetry.
      apply univ_bool.
Qed.

(* [C Fact 4.4, p. 92]: "every linguist left" lowers to one truth value and
   the input stack. *)
Lemma every_lower :
  forall (Q : E -> Prop) (f : E -> bool) (s : Stack) (b : bool) (s' : Stack),
    lower (fun c => every Q (fun y => c (f y))) s (b, s') <->
    s' = s /\ (b = true <-> forall y, Q y -> f y = true).
Proof.
  intros Q f s b s'. unfold lower. rewrite every_spec, univ_bool. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*  5. Exceptional scope over negation                                        *)
(* -------------------------------------------------------------------------- *)

Definition indef_tower (P : E -> Prop) (body : E -> bool) : K bool bool :=
  fun c => bind (indef P) (fun x => c (body x)).

Definition every_tower (P : E -> Prop) (body : E -> bool) : K bool bool :=
  fun c => every P (fun x => c (body x)).

(* Derivation (4.8) [C p. 95], for an island denoting the tower T: Reset
   the island, apply eta to its bottom, combine with lifted negation by S,
   then lift the bottom and lower. *)
Definition neg_island (T : K bool bool) : M bool :=
  S_ (lift (eta not_)) (fun c => reset T (fun p => c (eta p)))
     (fun mp => bind mp eta).

Lemma neg_island_spec :
  forall (T : K bool bool) (s : Stack) (r : bool * Stack),
    neg_island T s r <-> exists p s1, lower T s (p, s1) /\ r = (negb p, s1).
Proof.
  intros T s r. unfold neg_island, S_, reset, lift.
  unfold bind at 1. unfold eta at 1. split.
  - intros (f & s0 & Heq & Hb). inversion Heq; subst. clear Heq.
    destruct Hb as (p & s1 & Hl & b & s2 & Hn & Hr).
    unfold eta in Hr. subst r.
    destruct Hn as (b0 & Heq & Hb0). inversion Heq; subst.
    exists p, s1. split; [exact Hl |]. f_equal.
    destruct b0, p; simpl; try reflexivity.
    + exfalso. apply Hb0; [reflexivity |]. exists s1. reflexivity.
    + apply Hb0. intros (s' & Heq'). unfold eta in Heq'. discriminate.
  - intros (p & s1 & Hl & Hr). subst r. exists not_, s. split; [reflexivity |].
    exists p, s1. split; [exact Hl |]. exists (negb p), s1.
    split; [| reflexivity]. exists (negb p). split; [reflexivity |].
    unfold eta. destruct p; simpl; split.
    + discriminate.
    + intro Hn. exfalso. apply Hn. exists s1. reflexivity.
    + intros _ (s' & Heq). discriminate.
    + reflexivity.
Qed.

(* T7.  (a) [C (4.8), p. 95]: the island's alternatives scope over the
   negation: one negated truth value per witness.
   (b) [C p. 96, "will restrict the scope of a universal to its minimal
   tensed clause"]: the same derivation with a universal gives a single
   value, the negation of the universal claim.
   (c) Negation applied directly to the evaluated island: a single value,
   true iff no witness verifies the body. *)
Theorem exceptional_scope_negation :
  forall (P : E -> Prop) (body : E -> bool),
    meq (neg_island (indef_tower P body))
        (bind (indef P) (fun x => eta (negb (body x)))) /\
    (forall s b s',
        neg_island (every_tower P body) s (b, s') <->
        s' = s /\ (b = true <-> ~ forall x, P x -> body x = true)) /\
    (forall s b s',
        not_ (lower (indef_tower P body)) s (b, s') <->
        s' = s /\ (b = true <-> ~ exists x, P x /\ body x = true)).
Proof.
  intros P body. split; [| split].
  - intros s r. rewrite neg_island_spec.
    unfold lower, indef_tower, bind, indef, eta. split.
    + intros (p & s1 & (x & s0 & (x0 & Px & Heq) & Heq1) & Hr).
      inversion Heq; subst. inversion Heq1; subst. eauto 8.
    + intros (x & s0 & (x0 & Px & Heq) & Hr). inversion Heq; subst.
      exists (body x0), s. eauto 8.
  - intros s b s'. rewrite neg_island_spec. split.
    + intros (p & s1 & Hl & Heq). apply every_lower in Hl.
      destruct Hl as (Hs & Hp). inversion Heq; subst. split; [reflexivity |].
      rewrite <- Hp. destruct p; simpl; split; try discriminate; auto.
    + intros (Hs & Hb). subst s'. exists (negb b), s. split.
      * apply every_lower. split; [reflexivity |].
        destruct b; simpl; split; try discriminate.
        -- intro Hall. exfalso. destruct Hb as [Hb _]. apply Hb; auto.
        -- intros _ x Px. destruct (body x) eqn:Hbx; [reflexivity |].
           exfalso. assert (Hf : false = true); [| discriminate].
           apply Hb. intro Hall. rewrite (Hall x Px) in Hbx. discriminate.
        -- auto.
      * rewrite negb_involutive. reflexivity.
  - intros s b s'. unfold not_, lower, indef_tower, bind, indef, eta.
    assert (Hin : (exists s'0 : Stack, exists (a : E) (s'1 : Stack),
                      (exists x, P x /\ (a, s'1) = (x, s)) /\
                      (true, s'0) = (body a, s'1))
                  <-> exists x, P x /\ body x = true).
    { split.
      - intros (s0 & a & s1 & (x & Px & Heq) & Heq1).
        inversion Heq; subst. inversion Heq1. eauto.
      - intros (x & Px & Hbx). exists s, x, s. rewrite Hbx. eauto. }
    split.
    + intros (b0 & Heq & Hb). inversion Heq; subst. split; [reflexivity |].
      rewrite Hb, Hin. reflexivity.
    + intros (Hs & Hb). subst. exists b. split; [reflexivity |].
      rewrite Hb, Hin. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(*  6. Binding across sentences                                               *)
(* -------------------------------------------------------------------------- *)

(* Two sentence towers combined by lifted static conjunction, left to
   right. [C (4.7), p. 94] *)
Definition conj {R : Type} (T1 T2 : K R bool) : K R bool :=
  S_ (S_ (lift (eta andb)) T1) T2.

Lemma conj_lower :
  forall (T1 T2 : K bool bool) (s : Stack) (r : bool * Stack),
    lower (conj T1 T2) s r <->
    T1 (fun p => T2 (fun q => eta (andb p q))) s r.
Proof.
  intros T1 T2 s r. unfold lower, conj, S_, lift.
  unfold bind at 1. unfold eta at 1. split.
  - intros (h & s0 & Heq & H). inversion Heq; subst. exact H.
  - intro H. exists andb, s. split; [reflexivity | exact H].
Qed.

(* T8.  (a) [C (4.7), pp. 94-95]: "a man met every linguist, and he left".
   Both sentences are Reset; the pronoun is bound by the indefinite and the
   dref is still on the output stack.
   (b) [C p. 95]: a Bind-shifted universal [C Fact 3.16, p. 76] cannot
   bind out of its sentence: the pronoun reads the input stack and the
   output stack is the input stack. *)
Theorem cross_sentential_binding :
  forall (P Q : E -> Prop) (met : E -> E -> bool) (f g : E -> bool),
    (forall s b s',
        lower (conj (reset (fun c => bind (dref (indef P))
                                          (fun x => every Q (fun y => c (met y x)))))
                    (reset (fun c => bind pro (fun z => c (g z))))) s (b, s')
        <-> exists x u, P x /\ (u = true <-> forall y, Q y -> met y x = true)
                        /\ b = andb u (g x) /\ s' = x :: s) /\
    (forall s b s',
        lower (conj (reset (fun c => every Q (fun y => bind (dref (eta y))
                                                           (fun y' => c (f y')))))
                    (reset (fun c => bind pro (fun z => c (g z))))) s (b, s')
        <-> exists z u, hd_error s = Some z
                        /\ (u = true <-> forall y, Q y -> f y = true)
                        /\ b = andb u (g z) /\ s' = s).
Proof.
  intros P Q met f g. split; intros s b s'; rewrite conj_lower.
  - rewrite reset_universal. split.
    + intros (x & u & Px & Hu & Hk).
      apply (reset_monadic _ _ _ pro g) in Hk.
      unfold bind, pro, eta in Hk.
      destruct Hk as (z & s1 & (x0 & Hx0 & Heq) & Hr).
      simpl in Hx0. inversion Hx0; subst. inversion Heq; subst.
      inversion Hr; subst. eauto 8.
    + intros (x & u & Px & Hu & Hb & Hs). subst. exists x, u.
      split; [exact Px |]. split; [exact Hu |].
      apply (reset_monadic _ _ _ pro g). unfold bind, pro, eta.
      exists x, (x :: s). split; [| reflexivity]. exists x. auto.
  - unfold reset at 1. unfold lift. unfold bind at 1.
    assert (Hl : forall u s1,
               lower (fun c => every Q (fun y => bind (dref (eta y))
                                                      (fun y' => c (f y')))) s (u, s1)
               <-> s1 = s /\ (u = true <-> forall y, Q y -> f y = true)).
    { intros u s1. unfold lower. rewrite every_spec.
      assert (Hin : forall y, (exists s2 : Stack,
                          bind (dref (eta y)) (fun y' => eta (f y')) s (true, s2))
                              <-> f y = true).
      { intro y. unfold dref, bind, push, eta. split.
        - intros (s2 & y' & s3 & (a & s0 & Heq & Heq1) & Heq2).
          inversion Heq; subst. inversion Heq1; subst. inversion Heq2. reflexivity.
        - intro Hf. exists (y :: s), y, (y :: s). rewrite Hf. eauto 8. }
      split; intros (Hs & Hu); (split; [exact Hs |]); rewrite Hu; split.
      - intros Hn y Qy. destruct (f y) eqn:Hf; [reflexivity |]. exfalso.
        apply Hn. exists y. split; [exact Qy |]. rewrite Hin, Hf. discriminate.
      - intros Hall (y & Qy & Hn). apply Hn, Hin, Hall, Qy.
      - intros Hall (y & Qy & Hn). apply Hn, Hin, Hall, Qy.
      - intros Hn y Qy. destruct (f y) eqn:Hf; [reflexivity |]. exfalso.
        apply Hn. exists y. split; [exact Qy |]. rewrite Hin, Hf. discriminate. }
    split.
    + intros (u & s1 & Hlow & Hk). apply Hl in Hlow. destruct Hlow as (Hs & Hu).
      subst s1. apply (reset_monadic _ _ _ pro g) in Hk.
      unfold bind, pro, eta in Hk.
      destruct Hk as (z & s1 & (x0 & Hx0 & Heq) & Hr).
      inversion Heq; subst. inversion Hr; subst. eauto 8.
    + intros (z & u & Hz & Hu & Hb & Hs). subst. exists u, s.
      split; [apply Hl; auto |].
      apply (reset_monadic _ _ _ pro g). unfold bind, pro, eta.
      exists z, s. split; [| reflexivity]. exists z. auto.
Qed.

End Fragment.

Arguments eta {E A} _ _ _.
Arguments bind {E A B} _ _ _ _.
Arguments indef {E} _ _ _.
Arguments not_ {E} _ _ _.
Arguments lower {E A} _ _ _.
Arguments indef_tower {E} _ _ _.
Arguments every_tower {E} _ _ _.
Arguments neg_island {E} _ _ _.

(* -------------------------------------------------------------------------- *)
(*  7. A model separating the readings of T7                                  *)
(* -------------------------------------------------------------------------- *)

(* Two relatives.  r1 met every linguist, r2 did not.  The island is "a
   relative of mine met every linguist", embedded under negation as in
   [C (4.8)]; the body is the already-evaluated universal. *)
Module RelativeModel.

Inductive Ent : Type := r1 | r2.
Definition rel (x : Ent) : Prop := True.
Definition met_all (x : Ent) : bool := match x with r1 => true | r2 => false end.

(* Exceptional scope: True is among the returned values (witness r2). *)
Example wide_scope_true :
  forall s : list Ent, neg_island (indef_tower rel met_all) s (true, s).
Proof.
  intro s. apply exceptional_scope_negation.
  exists r2, s. split; [exists r2; split; [exact I | reflexivity] | reflexivity].
Qed.

(* It is nondeterministic: False is returned too (witness r1). *)
Example wide_scope_false_too :
  forall s : list Ent, neg_island (indef_tower rel met_all) s (false, s).
Proof.
  intro s. apply exceptional_scope_negation.
  exists r1, s. split; [exists r1; split; [exact I | reflexivity] | reflexivity].
Qed.

(* Narrow scope: negation over the evaluated island returns only False. *)
Example narrow_scope_false :
  forall (s : list Ent) b s',
    not_ (lower (indef_tower rel met_all)) s (b, s') -> b = false.
Proof.
  intros s b s' H. apply exceptional_scope_negation in H. destruct H as (_ & Hb).
  destruct b; [| reflexivity]. exfalso. apply Hb; [reflexivity |].
  exists r1. split; [exact I | reflexivity].
Qed.

(* A universal in the island cannot scope over the negation: the only
   value is True ("not every relative ..."), where the wide-scope universal
   reading ("every relative did not ...") would be False. *)
Example universal_trapped :
  forall (s : list Ent) b s',
    neg_island (every_tower rel met_all) s (b, s') -> b = true.
Proof.
  intros s b s' H. apply exceptional_scope_negation in H. destruct H as (_ & Hb).
  apply Hb. intro Hall. specialize (Hall r2 I). discriminate.
Qed.

Example universal_value :
  forall s : list Ent, neg_island (every_tower rel met_all) s (true, s).
Proof.
  intro s. apply exceptional_scope_negation. split; [reflexivity |].
  split; [| reflexivity]. intros _ Hall. specialize (Hall r2 I). discriminate.
Qed.

End RelativeModel.

(* -------------------------------------------------------------------------- *)
(*  Assumption audits                                                         *)
(* -------------------------------------------------------------------------- *)
Print Assumptions state_set_monad_laws.
Print Assumptions application.
Print Assumptions S_subsumes_A.
Print Assumptions lift_eta.
Print Assumptions binding.
Print Assumptions reset_monadic.
Print Assumptions reset_indefinite.
Print Assumptions reset_pronoun.
Print Assumptions reset_universal.
Print Assumptions every_lower.
Print Assumptions exceptional_scope_negation.
Print Assumptions cross_sentential_binding.
Print Assumptions RelativeModel.wide_scope_true.
Print Assumptions RelativeModel.wide_scope_false_too.
Print Assumptions RelativeModel.narrow_scope_false.
Print Assumptions RelativeModel.universal_trapped.
Print Assumptions RelativeModel.universal_value.
