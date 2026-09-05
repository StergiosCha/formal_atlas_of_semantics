(* ========================================================================== *)
(*  Lambek.v — the associative, product-free Lambek calculus L                *)
(*  FORMAL-ATLAS / atlas/type_logical                                          *)
(* ========================================================================== *)
(* HEADER PLACEHOLDER — replaced at the end *)

Require Import List Arith Lia Bool ZArith.
Import ListNotations.

(* ========================================================================== *)
(*  Part 1 — Syntax                                                           *)
(* ========================================================================== *)

(* Def. 2 (design).  Formulas ("types") over a set of primitive types.
   M&R 2012 §2.1 p. 24: "the set of types is the smallest set containing
   the primitive types P and closed under \ and /" (product omitted, see
   header); Lambek 1958 §2 p. 155.  [bs A B] is A \ B, [sl B A] is B / A. *)
Inductive formula (Atom : Type) : Type :=
| at_ : Atom -> formula Atom
| bs  : formula Atom -> formula Atom -> formula Atom   (* A \ B *)
| sl  : formula Atom -> formula Atom -> formula Atom.  (* B / A *)

Arguments at_ {Atom} _.
Arguments bs  {Atom} _ _.
Arguments sl  {Atom} _ _.

Declare Scope lambek_scope.
Delimit Scope lambek_scope with L.
Infix "\" := bs (at level 40, left associativity) : lambek_scope.
Infix "/" := sl (at level 40, left associativity) : lambek_scope.
Open Scope lambek_scope.

Section Calculus.
Context {Atom : Type}.

Notation formula := (formula Atom).

(* Def. 2: decidable equality of formulas, given decidable equality of atoms.
   Transparent so that proof search ([prove]) computes under [vm_compute]. *)
Definition formula_eq_dec (Atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}) :
  forall A B : formula, {A = B} + {A <> B}.
Proof. decide equality. Defined.

(* Def. 3.  Contexts (antecedents) are lists of formulas; the number of
   connective occurrences is Lambek's degree d(x), Lambek 1958 §9 p. 167,
   also Moortgat 1997 p. 12 ("complexity"). *)
Definition ctx := list formula.

Fixpoint conn (A : formula) : nat :=
  match A with
  | at_ _ => 0
  | bs A B => S (conn A + conn B)
  | sl B A => S (conn B + conn A)
  end.

Definition conn_ctx (Γ : ctx) : nat := fold_right (fun A n => conn A + n) 0 Γ.

Lemma conn_ctx_app : forall Γ Δ, conn_ctx (Γ ++ Δ) = conn_ctx Γ + conn_ctx Δ.
Proof. induction Γ; simpl; intros; [reflexivity | rewrite IHΓ; lia]. Qed.

Lemma conn_ctx_cons : forall A Γ, conn_ctx (A :: Γ) = conn A + conn_ctx Γ.
Proof. reflexivity. Qed.

Definition conn_seq (Γ : ctx) (A : formula) : nat := conn_ctx Γ + conn A.

(* Def. 4.  Subformula relation: reflexive-transitive closure of "direct
   subformula" (M&R §2.3 p. 29: "its direct subformulae, that is the
   formulae A and B"; Prop 2.14 p. 40). *)
Inductive subformula : formula -> formula -> Prop :=
| sub_refl : forall A, subformula A A
| sub_bs_l : forall F A B, subformula F A -> subformula F (bs A B)
| sub_bs_r : forall F A B, subformula F B -> subformula F (bs A B)
| sub_sl_l : forall F A B, subformula F B -> subformula F (sl B A)
| sub_sl_r : forall F A B, subformula F A -> subformula F (sl B A).

Lemma subformula_trans : forall F G H,
  subformula F G -> subformula G H -> subformula F H.
Proof.
  intros F G H HFG HGH; induction HGH; auto.
  - apply sub_bs_l; auto.
  - apply sub_bs_r; auto.
  - apply sub_sl_l; auto.
  - apply sub_sl_r; auto.
Qed.

(* ========================================================================== *)
(*  Part 2 — The sequent calculus                                             *)
(* ========================================================================== *)

(* Def. 5.  Derivations of Γ ⊢ A as proof objects in Type.  The boolean flag
   says whether the cut rule is allowed (true) or not (false); all other
   constructors are polymorphic in the flag.
   Rules: M&R 2012 Fig. 2.2 p. 29 (axiom, \h, /h, \i, /i, cut; the product
   rules •h/•i are omitted); Lambek 1958 §8 p. 165 rules (1) axiom,
   (2) x,T → y ⇒ T → x\y, (2') T,y → x ⇒ T → x/y, (3),(3') the left
   rules, (6) cut p. 166; Moortgat 1997 Def. 2.13 p. 12.
   Non-emptiness: the side condition Γ ≠ ε of M&R Fig. 2.2 on \i and /i
   ("provided T is not empty", Lambek §8) is a Prop hypothesis of the
   two right rules.  A hole Γ, A, Γ' is Γ1 ++ A :: Γ2.
   [ARTIFACT-iv] holes are list concatenations; [ARTIFACT-ii] derivations
   live in Type (the sources have a relation Γ ⊢ A, recovered by
   [derivable] below). *)
Inductive Deriv : bool -> ctx -> formula -> Type :=
| d_ax  : forall {b} (A : formula), Deriv b [A] A
| d_bsR : forall {b} {Γ : ctx} {A B : formula},
    Deriv b (A :: Γ) B -> Γ <> [] -> Deriv b Γ (bs A B)
| d_slR : forall {b} {Γ : ctx} {A B : formula},
    Deriv b (Γ ++ [A]) B -> Γ <> [] -> Deriv b Γ (sl B A)
| d_bsL : forall {b} (Γ1 Γ2 : ctx) {Δ : ctx} {A} (B : formula) {C : formula},
    Deriv b Δ A -> Deriv b (Γ1 ++ B :: Γ2) C -> Deriv b (Γ1 ++ Δ ++ bs A B :: Γ2) C
| d_slL : forall {b} (Γ1 Γ2 : ctx) {Δ : ctx} {A} (B : formula) {C : formula},
    Deriv b Δ A -> Deriv b (Γ1 ++ B :: Γ2) C -> Deriv b (Γ1 ++ sl B A :: Δ ++ Γ2) C
| d_cut : forall {Γ : ctx} (Δ1 Δ2 : ctx) {A C : formula},
    Deriv true Γ A -> Deriv true (Δ1 ++ A :: Δ2) C -> Deriv true (Δ1 ++ Γ ++ Δ2) C.

(* Def. 6.  The relations Γ ⊢ A (with cut) and cut-free Γ ⊢ A of M&R §2.3. *)
Definition derivable (Γ : ctx) (A : formula) : Prop := inhabited (Deriv true Γ A).
Definition cf_derivable (Γ : ctx) (A : formula) : Prop := inhabited (Deriv false Γ A).

(* T3.  A cut-free derivation is a derivation. *)
Fixpoint weaken_flag_gen {b0 b Γ A} (d : Deriv b0 Γ A) : b0 = false -> Deriv b Γ A :=
  match d in Deriv b0 Γ A return b0 = false -> Deriv b Γ A with
  | d_ax A => fun _ => d_ax A
  | d_bsR d H => fun e => d_bsR (weaken_flag_gen d e) H
  | d_slR d H => fun e => d_slR (weaken_flag_gen d e) H
  | d_bsL Γ1 Γ2 B d1 d2 => fun e => d_bsL Γ1 Γ2 B (weaken_flag_gen d1 e) (weaken_flag_gen d2 e)
  | d_slL Γ1 Γ2 B d1 d2 => fun e => d_slL Γ1 Γ2 B (weaken_flag_gen d1 e) (weaken_flag_gen d2 e)
  | d_cut _ _ _ _ => fun e => False_rect _ (diff_true_false e)
  end.

Definition weaken_flag {b Γ A} (d : Deriv false Γ A) : Deriv b Γ A :=
  weaken_flag_gen d eq_refl.

Lemma cf_derivable_derivable : forall Γ A, cf_derivable Γ A -> derivable Γ A.
Proof. intros Γ A [d]; constructor; exact (weaken_flag d). Qed.

(* Small list toolkit (Def. 9, non-emptiness part). *)
Lemma app_not_nil_l : forall (l m : ctx), l <> [] -> l ++ m <> [].
Proof. intros [|x l] m H; [contradiction | discriminate]. Qed.

Lemma app_not_nil_r : forall (l m : ctx), m <> [] -> l ++ m <> [].
Proof. intros [|x l] m H; [exact H | discriminate]. Qed.

Lemma cons_not_nil : forall (x : formula) l, x :: l <> [].
Proof. discriminate. Qed.

(* T1.  The antecedent of a derivable sequent is never empty.
   M&R 2012 §2.5 p. 33: "the antecedent of a sequent ... never is empty in a
   proof"; Lambek 1958 §8 p. 165 ("provided T is not empty"). *)
Theorem deriv_nonempty : forall b Γ A (d : Deriv b Γ A), Γ <> [].
Proof.
  intros b Γ A d; induction d.
  - discriminate.
  - assumption.
  - assumption.
  - apply app_not_nil_r, app_not_nil_r; discriminate.
  - apply app_not_nil_r; discriminate.
  - apply app_not_nil_r, app_not_nil_l; assumption.
Qed.

(* Def. 7.  All sequents occurring in a derivation (end-sequent included);
   used for the subformula property (M&R Prop 2.14). *)
Fixpoint sequents {b Γ A} (d : Deriv b Γ A) : list (ctx * formula) :=
  (Γ, A) ::
  match d with
  | d_ax _ => []
  | d_bsR d _ => sequents d
  | d_slR d _ => sequents d
  | d_bsL _ _ _ d1 d2 => sequents d1 ++ sequents d2
  | d_slL _ _ _ d1 d2 => sequents d1 ++ sequents d2
  | d_cut _ _ d1 d2 => sequents d1 ++ sequents d2
  end.

(* T3.  The end-sequent belongs to [sequents]. *)
Lemma sequents_end : forall b Γ A (d : Deriv b Γ A), In (Γ, A) (sequents d).
Proof. intros; destruct d; simpl; left; reflexivity. Qed.

(* T3.  The sequents of a premise are sequents of the conclusion. *)
Lemma sequents_bsR : forall b Γ A B (d : Deriv b (A :: Γ) B) H s,
  In s (sequents d) -> In s (sequents (@d_bsR b Γ A B d H)).
Proof. intros; simpl; auto. Qed.
Lemma sequents_slR : forall b Γ A B (d : Deriv b (Γ ++ [A]) B) H s,
  In s (sequents d) -> In s (sequents (@d_slR b Γ A B d H)).
Proof. intros; simpl; auto. Qed.
Lemma sequents_bsL : forall b Γ1 Γ2 Δ A B C (d1 : Deriv b Δ A) (d2 : Deriv b (Γ1 ++ B :: Γ2) C) s,
  In s (sequents d1) \/ In s (sequents d2) -> In s (sequents (d_bsL Γ1 Γ2 B d1 d2)).
Proof. intros; simpl; right; apply in_or_app; assumption. Qed.
Lemma sequents_slL : forall b Γ1 Γ2 Δ A B C (d1 : Deriv b Δ A) (d2 : Deriv b (Γ1 ++ B :: Γ2) C) s,
  In s (sequents d1) \/ In s (sequents d2) -> In s (sequents (d_slL Γ1 Γ2 B d1 d2)).
Proof. intros; simpl; right; apply in_or_app; assumption. Qed.
Lemma sequents_cut : forall Γ Δ1 Δ2 A C (d1 : Deriv true Γ A) (d2 : Deriv true (Δ1 ++ A :: Δ2) C) s,
  In s (sequents d1) \/ In s (sequents d2) -> In s (sequents (d_cut Δ1 Δ2 d1 d2)).
Proof. intros; simpl; right; apply in_or_app; assumption. Qed.

(* T2.  Atomic-axiom expansion.  M&R 2012 Prop 2.3 p. 29 (Exercise 2.3):
   "Every axiom A ⊢ A can be derived from axioms p ⊢ p, with p a primitive
   type (and the proof does not use the cut rule)"; Moortgat 1997 Ex. 3.7
   (η-expansion).  [atomic_axioms d] says every axiom instance in d is on
   an atom. *)
Fixpoint atomic_axioms {b Γ A} (d : Deriv b Γ A) : Prop :=
  match d with
  | d_ax A => match A with at_ _ => True | _ => False end
  | d_bsR d _ => atomic_axioms d
  | d_slR d _ => atomic_axioms d
  | d_bsL _ _ _ d1 d2 => atomic_axioms d1 /\ atomic_axioms d2
  | d_slL _ _ _ d1 d2 => atomic_axioms d1 /\ atomic_axioms d2
  | d_cut _ _ d1 d2 => atomic_axioms d1 /\ atomic_axioms d2
  end.

Fixpoint ax_expand (A : formula) : Deriv false [A] A :=
  match A with
  | at_ a => d_ax (at_ a)
  | bs A B => d_bsR (d_bsL [] [] B (ax_expand A) (ax_expand B)) (cons_not_nil _ _)
  | sl B A => @d_slR false [sl B A] A B (d_slL [] [] B (ax_expand A) (ax_expand B)) (cons_not_nil _ _)
  end.

Theorem ax_expand_atomic : forall A, atomic_axioms (ax_expand A).
Proof. induction A; simpl; auto. Qed.

(* Def. 9.  Type-valued list surgery ("by inspection of the position of the
   cut formula": Lambek 1958 §9 p. 168 "seven cases"; M&R pp. 41-42).
   These are Type-valued because they must build derivations
   ([ARTIFACT-v]: [List.app_eq_app] is Prop). *)
Lemma split_app_cons_T : forall (l1 l2 m1 m2 : ctx) (x y : formula),
  l1 ++ x :: l2 = m1 ++ y :: m2 ->
    { k : ctx & m1 = l1 ++ x :: k /\ l2 = k ++ y :: m2 }
  + { x = y /\ l1 = m1 /\ l2 = m2 }
  + { k : ctx & l1 = m1 ++ y :: k /\ m2 = k ++ x :: l2 }.
Proof.
  induction l1 as [|a l1 IH]; intros l2 m1 m2 x y E.
  - destruct m1 as [|c m1]; simpl in E; injection E; intros; subst.
    + left; right; auto.
    + left; left; exists m1; auto.
  - destruct m1 as [|c m1]; simpl in E; injection E; intros E1 E2; subst.
    + right; exists l1; auto.
    + destruct (IH _ _ _ _ _ E1) as [[[k [H1 H2]] | [H1 [H2 H3]]] | [k [H1 H2]]]; subst.
      * left; left; exists k; auto.
      * left; right; auto.
      * right; exists k; auto.
Qed.

Lemma split_app_app_T : forall (l1 l2 m1 m2 : ctx),
  l1 ++ l2 = m1 ++ m2 ->
    { k : ctx & m1 = l1 ++ k /\ l2 = k ++ m2 }
  + { k : ctx & l1 = m1 ++ k /\ m2 = k ++ l2 }.
Proof.
  induction l1 as [|a l1 IH]; intros l2 m1 m2 E.
  - left; exists m1; auto.
  - destruct m1 as [|c m1]; simpl in E.
    + right; exists (a :: l1); subst; auto.
    + injection E; intros E1 E2; subst.
      destruct (IH _ _ _ E1) as [[k [H1 H2]] | [k [H1 H2]]]; subst.
      * left; exists k; auto.
      * right; exists k; auto.
Qed.

(* Position of a hole Δ1, X, Δ2 relative to the principal hole of a \L rule:
   Γ1, Δ, Y, Γ2 (Y = A \ B).  Four cases: X in Γ1, X in Δ, X = Y, X in Γ2. *)
Lemma split_hole_bs_T : forall (Δ1 Δ2 Γ1 Δ Γ2 : ctx) (X Y : formula),
  Δ1 ++ X :: Δ2 = Γ1 ++ Δ ++ Y :: Γ2 ->
    { k : ctx & Γ1 = Δ1 ++ X :: k /\ Δ2 = k ++ Δ ++ Y :: Γ2 }
  + { k1 : ctx & { k2 : ctx & Δ = k1 ++ X :: k2 /\ Δ1 = Γ1 ++ k1 /\ Δ2 = k2 ++ Y :: Γ2 } }
  + { X = Y /\ Δ1 = Γ1 ++ Δ /\ Δ2 = Γ2 }
  + { k : ctx & Γ2 = k ++ X :: Δ2 /\ Δ1 = Γ1 ++ Δ ++ Y :: k }.
Proof.
  intros Δ1 Δ2 Γ1 Δ Γ2 X Y E.
  rewrite app_assoc in E.
  destruct (split_app_cons_T _ _ _ _ _ _ E) as [[[k [H1 H2]] | [H1 [H2 H3]]] | [k [H1 H2]]].
  - (* X strictly before Y: in Γ1 or in Δ *)
    destruct (split_app_app_T _ _ _ _ H1) as [[k' [H3 H4]] | [k' [H3 H4]]]; subst.
    + left; left; right; exists k', k; auto.
    + destruct k' as [|c k'].
      * simpl in H4; subst; left; left; right; exists [], k; repeat split; rewrite ?app_nil_r; reflexivity.
      * injection H4; intros; subst.
        left; left; left; exists k'; split; [reflexivity | rewrite app_assoc; reflexivity].
  - subst; left; right; auto.
  - subst; right; exists k; split; [reflexivity | rewrite app_assoc; reflexivity].
Qed.

(* Same for a /L rule: Γ1, Y, Δ, Γ2 (Y = B / A). *)
Lemma split_hole_sl_T : forall (Δ1 Δ2 Γ1 Δ Γ2 : ctx) (X Y : formula),
  Δ1 ++ X :: Δ2 = Γ1 ++ Y :: Δ ++ Γ2 ->
    { k : ctx & Γ1 = Δ1 ++ X :: k /\ Δ2 = k ++ Y :: Δ ++ Γ2 }
  + { X = Y /\ Δ1 = Γ1 /\ Δ2 = Δ ++ Γ2 }
  + { k1 : ctx & { k2 : ctx & Δ = k1 ++ X :: k2 /\ Δ1 = Γ1 ++ Y :: k1 /\ Δ2 = k2 ++ Γ2 } }
  + { k : ctx & Γ2 = k ++ X :: Δ2 /\ Δ1 = Γ1 ++ Y :: Δ ++ k }.
Proof.
  intros Δ1 Δ2 Γ1 Δ Γ2 X Y E.
  destruct (split_app_cons_T _ _ _ _ _ _ E) as [[[k [H1 H2]] | [H1 [H2 H3]]] | [k [H1 H2]]].
  - left; left; left; exists k; auto.
  - subst; left; left; right; auto.
  - (* X strictly after Y: inside Δ or inside Γ2 *)
    destruct (split_app_app_T _ _ _ _ (eq_sym H2)) as [[k' [H3 H4]] | [k' [H3 H4]]]; subst.
    + destruct k' as [|c k'].
      * simpl in H4; subst; right; exists []; repeat split; rewrite ?app_nil_r; reflexivity.
      * injection H4; intros; subst.
        left; right; exists k, k'; auto.
    + right; exists k'; auto.
Qed.

End Calculus.
