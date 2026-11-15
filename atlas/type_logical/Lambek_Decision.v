Require Import Lambek.
Require Import List Bool Lia.
Import ListNotations.
Open Scope lambek_scope.

(* ========================================================================== *)
(*  Lambek_Decision.v — deciding derivability in the Lambek calculus L        *)
(*  FORMAL-ATLAS / atlas/type_logical                                          *)
(* ========================================================================== *)
(*
   SOURCES
     Lambek, J. (1958). The mathematics of sentence structure. American
       Mathematical Monthly 65(3): 154–170.  [§8]
     Moot, R. & Retoré, C. (2012). The Logic of Categorial Grammars. LNCS 6850,
       Springer.  [ch. 2 Prop 2.18; §2.5 p. 33; p. 45]
   Design document: atlas_data/designs/lambek.md, T13–T16.
   Builds on Lambek.v (the sequent calculus Deriv, cut elimination
   derivable_iff_cf, the connective count conn_seq, the fragment), which this
   file leaves unchanged.

   WHAT IS FORMALIZED
     Lambek's decision procedure: search for a cut-free derivation from the
     bottom up, trying the axiom, the right rule for the succedent and every
     left rule at every position and split of the antecedent.  Each step
     removes a connective, so the connective count bounds the search.
       T13 prove_sound         every sequent the search accepts is derivable
       T14 prove_complete      every cut-free derivable sequent is accepted
                               once the fuel exceeds its connective count
       T15 derivable_b_spec,   derivability (with cut) is decidable
           derivable_dec, cf_derivable_dec
       T16 computed examples on the fragment of Lambek.v, including two
           sequents the count invariant (Lambek_Count.v) cannot reject

   NOT FORMALIZED (and why)
     * The search returns a boolean, not a derivation (design T28, certified
       search): soundness gives derivability only.
     * No complexity bound: the search is exponential, as is Lambek's.
     * Product ⊗: out of scope, as in Lambek.v.

   REPRESENTATION CHOICES
     Fuel is the decreasing argument of [prove]; [derivable_b] supplies
     conn_seq + 1, which T14 shows is enough.  Atom equality is a hypothesis
     (the sources assume a finite set of primitive types).
*)

Section Decide.
Context {Atom : Type} (Atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}).
Notation formula := (formula Atom).
Notation ctx := (list formula).

Definition ctx_eq_dec : forall Γ Δ : ctx, {Γ = Δ} + {Γ <> Δ} :=
  list_eq_dec (formula_eq_dec Atom_eq_dec).

(* All ways to cut a list in two: l = l1 ++ l2. *)
Fixpoint splits {X} (l : list X) : list (list X * list X) :=
  match l with
  | [] => [([], [])]
  | x :: l => ([], x :: l) :: map (fun s => (x :: fst s, snd s)) (splits l)
  end.

Lemma splits_spec : forall X (l l1 l2 : list X), In (l1, l2) (splits l) <-> l = l1 ++ l2.
Proof.
  intros X l; induction l as [|x l IH]; intros l1 l2; cbn.
  - split; [intros [H|[]]; injection H as <- <-; reflexivity|].
    intros H; symmetry in H; apply app_eq_nil in H as [-> ->]; auto.
  - rewrite in_map_iff; split.
    + intros [H|[[m1 m2] [H Hin]]]; [injection H as <- <-; reflexivity|].
      injection H as <- <-; apply IH in Hin; cbn; congruence.
    + destruct l1 as [|y l1]; cbn; intros H; [left; congruence|].
      injection H as <- H; right; exists (l1, l2); split; [reflexivity|].
      apply IH; exact H.
Qed.

(* All ways to pick out one element: l = l1 ++ x :: l2. *)
Fixpoint holes {X} (l : list X) : list (list X * X * list X) :=
  match l with
  | [] => []
  | x :: l => ([], x, l) :: map (fun h => (x :: fst (fst h), snd (fst h), snd h)) (holes l)
  end.

Lemma holes_spec : forall X (l l1 l2 : list X) x,
  In (l1, x, l2) (holes l) <-> l = l1 ++ x :: l2.
Proof.
  intros X l; induction l as [|y l IH]; intros l1 l2 x; cbn.
  - split; [intros []|intros H; destruct l1; discriminate].
  - rewrite in_map_iff; split.
    + intros [H|[[[m1 z] m2] [H Hin]]]; [injection H as <- <- <-; reflexivity|].
      injection H as <- <- <-; apply IH in Hin; cbn; congruence.
    + destruct l1 as [|w l1]; cbn; intros H; [left; congruence|].
      injection H as <- H; right; exists (l1, x, l2); split; [reflexivity|].
      apply IH; exact H.
Qed.

(* One step of the search, given a search procedure p for the premises. *)
Definition is_axiom (Γ : ctx) (A : formula) : bool :=
  if ctx_eq_dec Γ [A] then true else false.

Definition right_rule (p : ctx -> formula -> bool) (Γ : ctx) (A : formula) : bool :=
  match Γ with
  | [] => false
  | _ => match A with
         | at_ _ => false
         | bs A B => p (A :: Γ) B
         | sl B A => p (Γ ++ [A]) B
         end
  end.

Definition left_rule (p : ctx -> formula -> bool) (C : formula)
    (h : ctx * formula * ctx) : bool :=
  let Γ1 := fst (fst h) in let Γ2 := snd h in
  match snd (fst h) with
  | at_ _ => false
  | bs A B => existsb (fun s => p (snd s) A && p (fst s ++ B :: Γ2) C) (splits Γ1)
  | sl B A => existsb (fun s => p (fst s) A && p (Γ1 ++ B :: snd s) C) (splits Γ2)
  end.

(* Lambek 1958 §8 p. 167: "working from the bottom up, using Rules (1) to
   (5), but not (6)", i.e. search for a cut-free derivation. *)
Fixpoint prove (n : nat) (Γ : ctx) (A : formula) : bool :=
  match n with
  | O => false
  | S n => is_axiom Γ A || right_rule (prove n) Γ A
           || existsb (left_rule (prove n) A) (holes Γ)
  end.

(* T13.  The search is sound: an accepted sequent has a cut-free derivation.
   Lambek 1958 §8 p. 167; M&R Prop 2.18. *)
Theorem prove_sound : forall n Γ A, prove n Γ A = true -> cf_derivable Γ A.
Proof.
  induction n as [|n IH]; intros Γ A H; [discriminate|].
  cbn [prove] in H; rewrite !orb_true_iff in H; destruct H as [[H|H]|H].
  - unfold is_axiom in H; destruct (ctx_eq_dec Γ [A]) as [->|]; [|discriminate].
    exact (inhabits (d_ax A)).
  - unfold right_rule in H; destruct Γ as [|G Γ]; [discriminate|].
    destruct A as [a|A B|B A]; [discriminate| |].
    + apply IH in H as [d]; constructor; apply (d_bsR d); discriminate.
    + apply IH in H as [d]; constructor; apply (d_slR d); discriminate.
  - apply existsb_exists in H as [[[Γ1 F] Γ2] [Hin H]].
    apply holes_spec in Hin as ->; unfold left_rule in H; cbn [fst snd] in H.
    destruct F as [a|A' B|B A']; [discriminate| |];
      apply existsb_exists in H as [[X Y] [Hs H]]; apply splits_spec in Hs as ->;
      cbn [fst snd] in H; apply andb_true_iff in H as [H1 H2];
      apply IH in H1 as [d1]; apply IH in H2 as [d2]; constructor.
    + rewrite <- app_assoc; exact (d_bsL _ _ _ d1 d2).
    + exact (d_slL _ _ _ d1 d2).
Qed.

Lemma prove_complete_gen : forall b Γ A (d : Deriv b Γ A), b = false ->
  forall n, conn_seq Γ A < n -> prove n Γ A = true.
Proof.
  intros b Γ A d; induction d; intros Hb [|m] Hn; try lia; try discriminate Hb;
    cbn [prove]; rewrite !orb_true_iff; unfold conn_seq in *.
  - left; left; unfold is_axiom; destruct (ctx_eq_dec [A] [A]); congruence.
  - left; right; destruct Γ as [|G Γ]; [contradiction|]; cbn [right_rule].
    apply IHd; [exact Hb|]; rewrite !conn_ctx_cons in *; cbn [conn] in *; lia.
  - left; right; destruct Γ as [|G Γ]; [contradiction|]; cbn [right_rule].
    apply IHd; [exact Hb|]; rewrite conn_ctx_app in *; cbn [conn conn_ctx fold_right] in *; lia.
  - right; apply existsb_exists; exists (Γ1 ++ Δ, A \ B, Γ2); split.
    + apply holes_spec; rewrite <- app_assoc; reflexivity.
    + unfold left_rule; cbn [fst snd]; apply existsb_exists; exists (Γ1, Δ); split.
      * apply splits_spec; reflexivity.
      * cbn [fst snd]; apply andb_true_iff; split; [apply IHd1|apply IHd2]; try exact Hb;
          repeat rewrite ?conn_ctx_app, ?conn_ctx_cons in *; cbn [conn] in *; lia.
  - right; apply existsb_exists; exists (Γ1, B / A, Δ ++ Γ2); split.
    + apply holes_spec; reflexivity.
    + unfold left_rule; cbn [fst snd]; apply existsb_exists; exists (Δ, Γ2); split.
      * apply splits_spec; reflexivity.
      * cbn [fst snd]; apply andb_true_iff; split; [apply IHd1|apply IHd2]; try exact Hb;
          repeat rewrite ?conn_ctx_app, ?conn_ctx_cons in *; cbn [conn] in *; lia.
Qed.

(* T14.  The search is complete: with fuel above the connective count it
   finds every cut-free derivable sequent.  Lambek 1958 §8: "every upward
   step eliminates an occurrence of one of the connectives". *)
Theorem prove_complete : forall Γ A (d : Deriv false Γ A) n,
  conn_seq Γ A < n -> prove n Γ A = true.
Proof. intros Γ A d; exact (prove_complete_gen false Γ A d eq_refl). Qed.

Definition derivable_b (Γ : ctx) (A : formula) : bool :=
  prove (S (conn_seq Γ A)) Γ A.

(* T15.  The search with bound conn_seq + 1 decides derivability with cut.
   Lambek 1958 §8 ("the decision problem ... is solved affirmatively");
   M&R Prop 2.18.  Uses cut elimination (derivable_iff_cf, Lambek.v). *)
Theorem derivable_b_spec : forall Γ A, derivable_b Γ A = true <-> derivable Γ A.
Proof.
  intros Γ A; split.
  - intros H; apply cf_derivable_derivable; exact (prove_sound _ _ _ H).
  - intros H; apply derivable_iff_cf in H as [d]; apply (prove_complete _ _ d); lia.
Qed.

Theorem derivable_dec : forall (Γ : ctx) A, {derivable Γ A} + {~ derivable Γ A}.
Proof.
  intros Γ A; destruct (derivable_b Γ A) eqn:E.
  - left; apply derivable_b_spec; exact E.
  - right; intros H; apply derivable_b_spec in H; congruence.
Qed.

Theorem cf_derivable_dec : forall (Γ : ctx) A, {cf_derivable Γ A} + {~ cf_derivable Γ A}.
Proof.
  intros Γ A; destruct (derivable_dec Γ A) as [H|H]; [left|right];
    rewrite <- derivable_iff_cf; exact H.
Qed.

End Decide.

Module DecisionExamples.
Import Fragment.

Definition prim_eq_dec : forall a b : prim, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Notation NP_ := (at_ NP). Notation N_ := (at_ N). Notation S_ := (at_ S).

(* T16.  Each example is settled by running the search (vm_compute). *)
Ltac by_search := apply (derivable_b_spec prim_eq_dec); vm_compute; reflexivity.
Ltac by_failed_search :=
  intros H; apply (derivable_b_spec prim_eq_dec) in H; vm_compute in H; discriminate.

(* np, np\s ⊢ s ("John walks").  Lambek 1958 §8; M&R Ex 2.7 p. 30. *)
Theorem john_walks : derivable [NP_; NP_ \ S_] S_.
Proof. by_search. Qed.

(* np\s, np ⊬ s ("walks John").  The calculus is sensitive to word order;
   the count invariant cannot reject this sequent.  Design T16. *)
Theorem walks_john_rejected : ~ derivable [NP_ \ S_; NP_] S_.
Proof. by_failed_search. Qed.

(* (s/(np\s))/n, n, np\s ⊢ s ("every man walks").  M&R Ex 3.5 p. 81. *)
Theorem every_man_walks : derivable [(S_ / (NP_ \ S_)) / N_; N_; NP_ \ S_] S_.
Proof. by_search. Qed.

(* np ⊢ s/(np\s): type raising.  M&R p. 30; Lambek 1958 §7. *)
Theorem type_raising : derivable [NP_] (S_ / (NP_ \ S_)).
Proof. by_search. Qed.

(* s/(n\s) ⊬ n.  Balanced, so the count invariant cannot reject it
   (M&R p. 45); the search can.  Design T16. *)
Theorem raised_not_lowered : ~ derivable [S_ / (N_ \ S_)] N_.
Proof. by_failed_search. Qed.

(* np/n, (n/n)/(n/n), n ⊬ np ("a very book").  Deriving it would need the
   empty antecedent ⊢ n/n, which L excludes (M&R §2.5 p. 33).  Balanced, so
   again beyond the count invariant. *)
Theorem a_very_book_rejected : ~ derivable [NP_ / N_; (N_ / N_) / (N_ / N_); N_] NP_.
Proof. by_failed_search. Qed.

End DecisionExamples.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Under Coq 8.20.1 (2026-11-15) every theorem below prints "Closed under the
   global context": no axioms, no classical principles, no extensionality. *)
Print Assumptions prove_sound.
Print Assumptions prove_complete.
Print Assumptions derivable_b_spec.
Print Assumptions derivable_dec.
Print Assumptions cf_derivable_dec.
Print Assumptions DecisionExamples.john_walks.
Print Assumptions DecisionExamples.walks_john_rejected.
Print Assumptions DecisionExamples.every_man_walks.
Print Assumptions DecisionExamples.type_raising.
Print Assumptions DecisionExamples.raised_not_lowered.
Print Assumptions DecisionExamples.a_very_book_rejected.
