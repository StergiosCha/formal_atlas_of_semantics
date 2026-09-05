(* ========================================================================== *)
(*  Lambek.v — the associative, product-free Lambek calculus L                *)
(*  FORMAL-ATLAS / atlas/type_logical                                          *)
(* ========================================================================== *)
(*
   SOURCES
     Lambek, J. (1958). The mathematics of sentence structure. American
       Mathematical Monthly 65(3): 154–170.  [§§2, 7, 8, 9]
     Moot, R. & Retoré, C. (2012). The Logic of Categorial Grammars. LNCS 6850,
       Springer.  [ch. 2 §§2.1, 2.3, 2.5, 2.7 (Fig. 2.2, Props 2.3, 2.14,
       Thm 2.17); ch. 3 §3.3 and Exs 3.2, 3.5]
     Retoré, C. (2005). The logic of categorial grammars: lecture notes.
       INRIA RR-5703.  [same material, used for text search]
     Moortgat, M. (1997). Categorial type logics. Handbook of Logic and
       Language, ch. 2.  [Def. 2.13, Prop 2.14, Def. 3.2]
   Design document: formalizing_formal_semantics/atlas/designs/lambek.md.

   WHAT IS FORMALIZED
     Part 1  Syntax: formulas over an arbitrary set of primitive types with
             \ and /, contexts as lists, connective count (Lambek's degree),
             the subformula relation.
     Part 2  The sequent calculus of Lambek 1958 §8 / M&R Fig. 2.2 with the
             non-empty-antecedent side condition on the right rules, as an
             inductive family [Deriv b Γ A] in Type; b = true admits cut,
             b = false is the cut-free calculus.
               T1  deriv_nonempty      antecedents are never empty
               T2  ax_expand           axioms reduce to atomic axioms (Prop 2.3)
               T3  weaken_flag, sequents
     Part 3  Cut elimination.
               T4  cut_adm    cut is admissible in the cut-free calculus
                              (Lambek §9, cases 1–4, 6, 7; M&R Thm 2.17)
               T5  cut_elim   every derivation has a cut-free counterpart;
                   derivable_iff_cf
     Part 4  The subformula property of cut-free derivations (M&R Prop 2.14):
               T6  subformula_property, subformula_property_derivable
     Part 5  Curry–Howard.  The type homomorphism (A\B)* = (B/A)* = A* → B*
             (M&R §3.3 step 1) is [sem]; the λ-term of a derivation is read
             directly as a Coq function [denote] (steps 2–3): axiom ↦ variable,
             right rules ↦ abstraction, left rules ↦ application substituted for
             the hypothesis, cut ↦ substitution (T18 denote_cut).
     Part 6  A Montague fragment (np, n, s; John, every, some, man, walks):
               T17 john_walks_sem, every_man_walks_sem, some_man_walks_sem —
                   the derivations compute the Montague meanings
                   (∀x. man x → walks x; ∃x. man x ∧ walks x) by conversion;
               T20 type_raise_sem (λP. P john), compose_sem (λc. f (g c));
               john_walks_cut_sem: a derivation with a cut on the raised
                   subject denotes the same proposition.

   NOT FORMALIZED (and why)
     * Product ⊗ and Lambek's arrow axiomatics: out of scope (product-free L).
     * Syntactic λ-terms with de Bruijn indices and the theorem that cut
       elimination preserves the term up to β (design T7–T11): the semantics
       here is shallow, so β is definitional and the theorem is not statable;
       dropped for budget after the design's own fallback clause.
     * Semantic invariance of cut elimination, denote (cut_elim d) = denote d
       (design STRETCH 5): would require [cut_adm] to be transparent and the
       transports along context equalities to compute; [cut_adm] is opaque
       (Qed) and uses the opaque stdlib lemma app_assoc.  Not attempted.
     * Decidability of derivability by fuel-bounded proof search (design
       T13–T15) and the vm_compute non-derivability examples (T16): not
       attempted for budget.  The subformula property proved here is the
       basis of Lambek's decision procedure.
     * Linearity/normality of terms, models, interpolation, Pentus: out of scope.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-ii]  Derivations live in Type (the sources have a relation
                    Γ ⊢ A); the relations [derivable]/[cf_derivable] are
                    recovered with [inhabited].  Needed because cut elimination
                    and [denote] compute on derivations.
     [ARTIFACT-iv]  Holes "Γ, A, Γ'" are list concatenations Γ1 ++ A :: Γ2;
                    the position analysis of the cut formula relative to the
                    principal formula (Lambek's "seven cases") is done by
                    Type-valued splitting lemmas (Def. 9) and transports
                    [deriv_cast] along context equalities.
     [ARTIFACT-v]   The stdlib's Prop-valued list lemmas (app_eq_app) cannot
                    build derivations; Type-valued twins were written.
     [ARTIFACT-iii] Because the λ-terms are Coq functions, β-conversion is
                    invisible: the semantic clause of the Curry–Howard result
                    (cut = substitution) holds by definition rather than as a
                    theorem about a term calculus.
     The non-emptiness side condition is a Prop hypothesis of the right rules
     (M&R Fig. 2.2 "Γ ≠ ε"); [deriv_nonempty] shows it propagates.
     Classical logic and extensionality are not used anywhere (see the
     Print Assumptions block at the end of the file).
*)

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

(* ========================================================================== *)
(*  Part 3 — Cut elimination                                                  *)
(* ========================================================================== *)

Section CutElimination.
Context {Atom : Type}.
Notation formula := (formula Atom).
Notation ctx := (list formula).

(* Def. 8.  Height of a derivation: Lambek's induction is on the degree of the
   cut formula and the lengths of the two premise proofs (Lambek 1958 §9
   p. 167: "by induction on the degree ... and the length"); M&R Thm 2.17. *)
Fixpoint height {b} {Γ : ctx} {A : formula} (d : Deriv b Γ A) : nat :=
  match d with
  | d_ax _ => 0
  | d_bsR d _ => S (height d)
  | d_slR d _ => S (height d)
  | d_bsL _ _ _ d1 d2 => S (height d1 + height d2)
  | d_slL _ _ _ d1 d2 => S (height d1 + height d2)
  | d_cut _ _ d1 d2 => S (height d1 + height d2)
  end.

(* Transport of a derivation along an equation between antecedents
   (design pitfall 7). *)
Definition deriv_cast {b} {Γ Γ' : ctx} {A} (e : Γ = Γ') (d : Deriv b Γ A) : Deriv b Γ' A :=
  match e in _ = Γ' return Deriv b Γ' A with eq_refl => d end.

Lemma height_cast : forall b (Γ Γ' : ctx) A (e : Γ = Γ') (d : Deriv b Γ A),
  height (deriv_cast e d) = height d.
Proof. intros; destruct e; reflexivity. Qed.

Ltac ctx_eq := simpl; repeat (rewrite <- app_assoc || rewrite app_nil_r || rewrite <- app_comm_cons); simpl; reflexivity.

(* The induction hypothesis packaged as a type (outer: degree of the cut
   formula; inner: sum of heights). *)
Definition CutIH (n m : nat) : Type :=
  forall (Γ : ctx) (A : formula) (Δ1 Δ2 : ctx) (C : formula) b1 (d1 : Deriv b1 Γ A),
    b1 = false ->
    forall Θ, Θ = Δ1 ++ A :: Δ2 ->
    forall b2 (d2 : Deriv b2 Θ C), b2 = false ->
    conn A < n -> height d1 + height d2 < m ->
    Deriv false (Δ1 ++ Γ ++ Δ2) C.

(* T4.  Cut admissibility for the cut-free calculus, Lambek 1958 §9
   ("seven cases"; case 5 is the product and does not arise here), M&R §2.7
   pp. 40–43, Moortgat 1997 Prop 2.14.  Case table (Coq branch ↔ source):
     d2 axiom                      — Lambek case 1
     d2 ends in \i or /i           — cut permutes upward through the right rule
     A non-principal in a \h or /h — cases 2–4 (cut permutes into the premise
                                     containing A: left context, minor premise,
                                     right context)
     A principal, d1 axiom         — case 1 (mirror)
     A principal, d1 ends in a left rule — cut permutes into d1's major premise
     A principal, d1 ends in \i (resp. /i), d2 in \h (resp. /h) — case 6/7:
       the cut is replaced by two cuts on the immediate subformulae. *)
Lemma cut_adm_aux : forall n m, CutIH n m.
Proof.
  unfold CutIH.
  induction n as [|n IHn]; [intros; lia|].
  induction m as [|m IHm]; [intros; lia|].
  intros Γ A Δ1 Δ2 C b1 d1 Hb1 Θ E b2 d2 Hb2 Hc Hh.
  revert Hh E.
  destruct d2 as [b A1 | b Θ A1 B1 d2 H | b Θ A1 B1 d2 H
                 | b Γ1 Γ2 Δ A1 B1 C d21 d22 | b Γ1 Γ2 Δ A1 B1 C d21 d22 | ];
    intros Hh E; try discriminate Hb2; subst b; simpl in Hh.
  - (* d2 axiom *)
    destruct Δ1 as [|x Δ1]; simpl in E; injection E as E1 E2.
    + subst. rewrite app_nil_r. exact d1.
    + destruct (app_cons_not_nil _ _ _ E2).
  - (* d2 ends in \R *)
    subst Θ. assert (Hh' : height d1 + height d2 < m) by lia.
    apply d_bsR.
    + exact (IHm Γ A (A1 :: Δ1) Δ2 B1 b1 d1 Hb1 _ eq_refl _ d2 eq_refl Hc Hh').
    + apply app_not_nil_r, app_not_nil_l. exact (deriv_nonempty _ _ _ d1).
  - (* d2 ends in /R *)
    subst Θ. assert (Hh' : height d1 + height d2 < m) by lia.
    apply d_slR.
    + refine (deriv_cast _ (IHm Γ A Δ1 (Δ2 ++ [A1]) B1 b1 d1 Hb1 _ _ _ d2 eq_refl Hc Hh')).
      * ctx_eq.
      * ctx_eq.
    + apply app_not_nil_r, app_not_nil_l. exact (deriv_nonempty _ _ _ d1).
  - (* d2 ends in \L *)
    destruct (split_hole_bs_T _ _ _ _ _ _ _ (eq_sym E))
      as [[[[k [H1 H2]] | [k1 [k2 [H1 [H2 H3]]]]] | [H1 [H2 H3]]] | [k [H1 H2]]].
    + (* A in the left context Γ1 *) subst.
      assert (Hh' : height d1 + height d22 < m) by lia.
      refine (deriv_cast _ (d_bsL (Δ1 ++ Γ ++ k) Γ2 B1 d21
        (deriv_cast _ (IHm Γ A Δ1 (k ++ B1 :: Γ2) _ false d1 eq_refl _ _ _ d22 eq_refl Hc Hh')))).
      * ctx_eq.
      * ctx_eq.
      * ctx_eq.
    + (* A in the minor premise Δ *) subst.
      assert (Hh' : height d1 + height d21 < m) by lia.
      refine (deriv_cast _ (d_bsL Γ1 Γ2 B1
        (IHm Γ A k1 k2 _ false d1 eq_refl _ eq_refl _ d21 eq_refl Hc Hh') d22)).
      ctx_eq.
    + (* A principal *)
      subst Δ1 Δ2.
      destruct d1 as [bb A' | bb G A' B' d1' H' | bb G A' B' d1' H'
                     | bb G1 G2 D A' B' C' d11 d12 | bb G1 G2 D A' B' C' d11 d12 | ];
        try discriminate Hb1; subst; simpl in Hh.
      * (* d1 axiom *)
        refine (deriv_cast _ (d_bsL Γ1 Γ2 B1 d21 d22)). ctx_eq.
      * (* d1 ends in \R: principal reduction, Lambek case 6 *)
        injection H1 as -> ->. simpl in Hc.
        assert (Hc1 : conn A1 < n) by lia. assert (Hc2 : conn B1 < n) by lia.
        refine (deriv_cast _ (IHn _ ([] ++ Δ ++ G) B1 Γ1 Γ2 C false
                  (IHn _ Δ A1 [] G B1 false d21 eq_refl _ eq_refl _ d1' eq_refl Hc1 (le_n _))
                  eq_refl _ eq_refl _ d22 eq_refl Hc2 (le_n _))).
        ctx_eq.
      * discriminate H1.
      * (* d1 ends in \L: push the cut into its major premise *)
        assert (Hh' : height d12 + height (d_bsL Γ1 Γ2 B1 d21 d22) < m) by (simpl; lia).
        refine (deriv_cast _ (d_bsL ((Γ1 ++ Δ) ++ G1) (G2 ++ Γ2) B' d11
          (deriv_cast _ (IHm _ _ (Γ1 ++ Δ) Γ2 _ false d12 eq_refl _ E _
                            (d_bsL Γ1 Γ2 B1 d21 d22) eq_refl Hc Hh')))).
        -- ctx_eq.
        -- ctx_eq.
      * (* d1 ends in /L *)
        assert (Hh' : height d12 + height (d_bsL Γ1 Γ2 B1 d21 d22) < m) by (simpl; lia).
        refine (deriv_cast _ (d_slL ((Γ1 ++ Δ) ++ G1) (G2 ++ Γ2) B' d11
          (deriv_cast _ (IHm _ _ (Γ1 ++ Δ) Γ2 _ false d12 eq_refl _ E _
                            (d_bsL Γ1 Γ2 B1 d21 d22) eq_refl Hc Hh')))).
        -- ctx_eq.
        -- ctx_eq.
    + (* A in the right context Γ2 *) subst.
      assert (Hh' : height d1 + height d22 < m) by lia.
      refine (deriv_cast _ (d_bsL Γ1 (k ++ Γ ++ Δ2) B1 d21
        (deriv_cast _ (IHm Γ A (Γ1 ++ B1 :: k) Δ2 _ false d1 eq_refl _ _ _ d22 eq_refl Hc Hh')))).
      * ctx_eq.
      * ctx_eq.
      * ctx_eq.
  - (* d2 ends in /L *)
    destruct (split_hole_sl_T _ _ _ _ _ _ _ (eq_sym E))
      as [[[[k [H1 H2]] | [H1 [H2 H3]]] | [k1 [k2 [H1 [H2 H3]]]]] | [k [H1 H2]]].
    + (* A in Γ1 *) subst.
      assert (Hh' : height d1 + height d22 < m) by lia.
      refine (deriv_cast _ (d_slL (Δ1 ++ Γ ++ k) Γ2 B1 d21
        (deriv_cast _ (IHm Γ A Δ1 (k ++ B1 :: Γ2) _ false d1 eq_refl _ _ _ d22 eq_refl Hc Hh')))).
      * ctx_eq.
      * ctx_eq.
      * ctx_eq.
    + (* A principal *)
      subst Δ1 Δ2.
      destruct d1 as [bb A' | bb G A' B' d1' H' | bb G A' B' d1' H'
                     | bb G1 G2 D A' B' C' d11 d12 | bb G1 G2 D A' B' C' d11 d12 | ];
        try discriminate Hb1; subst; simpl in Hh.
      * refine (deriv_cast _ (d_slL Γ1 Γ2 B1 d21 d22)). ctx_eq.
      * discriminate H1.
      * (* d1 ends in /R: principal reduction, Lambek case 7 *)
        injection H1 as -> ->. simpl in Hc.
        assert (Hc1 : conn A1 < n) by lia. assert (Hc2 : conn B1 < n) by lia.
        refine (deriv_cast _ (IHn _ (G ++ Δ ++ []) B1 Γ1 Γ2 C false
                  (IHn _ Δ A1 G [] B1 false d21 eq_refl _ eq_refl _ d1' eq_refl Hc1 (le_n _))
                  eq_refl _ eq_refl _ d22 eq_refl Hc2 (le_n _))).
        ctx_eq.
      * assert (Hh' : height d12 + height (d_slL Γ1 Γ2 B1 d21 d22) < m) by (simpl; lia).
        refine (deriv_cast _ (d_bsL (Γ1 ++ G1) (G2 ++ Δ ++ Γ2) B' d11
          (deriv_cast _ (IHm _ _ Γ1 (Δ ++ Γ2) _ false d12 eq_refl _ E _
                            (d_slL Γ1 Γ2 B1 d21 d22) eq_refl Hc Hh')))).
        -- ctx_eq.
        -- ctx_eq.
      * assert (Hh' : height d12 + height (d_slL Γ1 Γ2 B1 d21 d22) < m) by (simpl; lia).
        refine (deriv_cast _ (d_slL (Γ1 ++ G1) (G2 ++ Δ ++ Γ2) B' d11
          (deriv_cast _ (IHm _ _ Γ1 (Δ ++ Γ2) _ false d12 eq_refl _ E _
                            (d_slL Γ1 Γ2 B1 d21 d22) eq_refl Hc Hh')))).
        -- ctx_eq.
        -- ctx_eq.
    + (* A in Δ *) subst.
      assert (Hh' : height d1 + height d21 < m) by lia.
      refine (deriv_cast _ (d_slL Γ1 Γ2 B1
        (IHm Γ A k1 k2 _ false d1 eq_refl _ eq_refl _ d21 eq_refl Hc Hh') d22)).
      ctx_eq.
    + (* A in Γ2 *) subst.
      assert (Hh' : height d1 + height d22 < m) by lia.
      refine (deriv_cast _ (d_slL Γ1 (k ++ Γ ++ Δ2) B1 d21
        (deriv_cast _ (IHm Γ A (Γ1 ++ B1 :: k) Δ2 _ false d1 eq_refl _ _ _ d22 eq_refl Hc Hh')))).
      * ctx_eq.
      * ctx_eq.
      * ctx_eq.
Qed.

(* T4 (statement of record). *)
Theorem cut_adm : forall (Γ : ctx) A Δ1 Δ2 C,
  Deriv false Γ A -> Deriv false (Δ1 ++ A :: Δ2) C -> Deriv false (Δ1 ++ Γ ++ Δ2) C.
Proof.
  intros Γ A Δ1 Δ2 C d1 d2.
  exact (cut_adm_aux (S (conn A)) (S (height d1 + height d2)) Γ A Δ1 Δ2 C false d1 eq_refl _ eq_refl false d2 eq_refl (le_n _) (le_n _)).
Qed.

(* T5.  Cut elimination (Gentzen's Hauptsatz for L): every derivation has a
   cut-free counterpart.  Lambek 1958 §9 ("this will establish Gentzen's
   theorem"); M&R Thm 2.17 p. 43. *)
Fixpoint cut_elim {b} {Γ : ctx} {A} (d : Deriv b Γ A) : Deriv false Γ A :=
  match d with
  | d_ax A => d_ax A
  | d_bsR d H => d_bsR (cut_elim d) H
  | d_slR d H => d_slR (cut_elim d) H
  | d_bsL Γ1 Γ2 B d1 d2 => d_bsL Γ1 Γ2 B (cut_elim d1) (cut_elim d2)
  | d_slL Γ1 Γ2 B d1 d2 => d_slL Γ1 Γ2 B (cut_elim d1) (cut_elim d2)
  | d_cut Δ1 Δ2 d1 d2 => cut_adm _ _ Δ1 Δ2 _ (cut_elim d1) (cut_elim d2)
  end.

Corollary derivable_iff_cf : forall (Γ : ctx) A, derivable Γ A <-> cf_derivable Γ A.
Proof.
  split.
  - intros [d]; constructor; exact (cut_elim d).
  - apply cf_derivable_derivable.
Qed.

End CutElimination.

(* ========================================================================== *)
(*  Part 4 — The subformula property                                          *)
(* ========================================================================== *)

Section Subformula.
Context {Atom : Type}.
Notation formula := (formula Atom).
Notation ctx := (list formula).

(* "Every formula of a premise is a subformula of some formula of the
   conclusion" — the rule-local statement of M&R Prop 2.14 p. 40 and
   Moortgat 1997 p. 13. *)
Definition sub_closed (Γ : ctx) (C : formula) (Γ' : ctx) (C' : formula) : Prop :=
  forall F, In F (C' :: Γ') -> exists G, In G (C :: Γ) /\ subformula F G.

Lemma sub_closed_refl : forall Γ C, sub_closed Γ C Γ C.
Proof. intros Γ C F H; exists F; split; [assumption | constructor]. Qed.

Lemma sub_closed_trans : forall Γ C Γ' C' Γ'' C'',
  sub_closed Γ C Γ' C' -> sub_closed Γ' C' Γ'' C'' -> sub_closed Γ C Γ'' C''.
Proof.
  intros Γ C Γ' C' Γ'' C'' H1 H2 F HF.
  destruct (H2 F HF) as [G [HG1 HG2]].
  destruct (H1 G HG1) as [G' [HG'1 HG'2]].
  exists G'; split; [assumption | eapply subformula_trans; eauto].
Qed.

Lemma sub_bsR : forall Γ A B, sub_closed Γ (bs A B) (A :: Γ) B.
Proof.
  intros Γ A B F [<- | [<- | H]].
  - exists (bs A B); split; [left; reflexivity | apply sub_bs_r; constructor].
  - exists (bs A B); split; [left; reflexivity | apply sub_bs_l; constructor].
  - exists F; split; [right; assumption | constructor].
Qed.

Lemma sub_slR : forall Γ A B, sub_closed Γ (sl B A) (Γ ++ [A]) B.
Proof.
  intros Γ A B F [<- | H].
  - exists (sl B A); split; [left; reflexivity | apply sub_sl_l; constructor].
  - apply in_app_or in H; destruct H as [H | [<- | []]].
    + exists F; split; [right; assumption | constructor].
    + exists (sl B A); split; [left; reflexivity | apply sub_sl_r; constructor].
Qed.

Lemma sub_bsL_minor : forall Γ1 Γ2 Δ A B C,
  sub_closed (Γ1 ++ Δ ++ bs A B :: Γ2) C Δ A.
Proof.
  intros Γ1 Γ2 Δ A B C F [<- | H].
  - exists (bs A B); split; [| apply sub_bs_l; constructor].
    right; apply in_or_app; right; apply in_or_app; right; left; reflexivity.
  - exists F; split; [| constructor].
    right; apply in_or_app; right; apply in_or_app; left; assumption.
Qed.

Lemma sub_bsL_major : forall Γ1 Γ2 Δ A B C,
  sub_closed (Γ1 ++ Δ ++ bs A B :: Γ2) C (Γ1 ++ B :: Γ2) C.
Proof.
  intros Γ1 Γ2 Δ A B C F [<- | H].
  - exists C; split; [left; reflexivity | constructor].
  - apply in_app_or in H; destruct H as [H | [<- | H]].
    + exists F; split; [right; apply in_or_app; left; assumption | constructor].
    + exists (bs A B); split; [| apply sub_bs_r; constructor].
      right; apply in_or_app; right; apply in_or_app; right; left; reflexivity.
    + exists F; split; [| constructor].
      right; apply in_or_app; right; apply in_or_app; right; right; assumption.
Qed.

Lemma sub_slL_minor : forall Γ1 Γ2 Δ A B C,
  sub_closed (Γ1 ++ sl B A :: Δ ++ Γ2) C Δ A.
Proof.
  intros Γ1 Γ2 Δ A B C F [<- | H].
  - exists (sl B A); split; [| apply sub_sl_r; constructor].
    right; apply in_or_app; right; left; reflexivity.
  - exists F; split; [| constructor].
    right; apply in_or_app; right; right; apply in_or_app; left; assumption.
Qed.

Lemma sub_slL_major : forall Γ1 Γ2 Δ A B C,
  sub_closed (Γ1 ++ sl B A :: Δ ++ Γ2) C (Γ1 ++ B :: Γ2) C.
Proof.
  intros Γ1 Γ2 Δ A B C F [<- | H].
  - exists C; split; [left; reflexivity | constructor].
  - apply in_app_or in H; destruct H as [H | [<- | H]].
    + exists F; split; [right; apply in_or_app; left; assumption | constructor].
    + exists (sl B A); split; [| apply sub_sl_l; constructor].
      right; apply in_or_app; right; left; reflexivity.
    + exists F; split; [| constructor].
      right; apply in_or_app; right; right; apply in_or_app; right; assumption.
Qed.

(* T6.  Subformula property of cut-free derivations: every formula in every
   sequent of a cut-free derivation of Γ ⊢ C is a subformula of a formula in
   C :: Γ.  M&R Prop 2.14 p. 40 and Thm 2.17; Lambek 1958 §8 (the basis of
   his decision procedure); Moortgat 1997 p. 13. *)
Theorem subformula_property : forall b (Γ : ctx) C (d : Deriv b Γ C),
  b = false ->
  forall Γ' C', In (Γ', C') (sequents d) -> sub_closed Γ C Γ' C'.
Proof.
  intros b Γ C d; induction d; intros Hb Γ' C' Hin; simpl in Hin.
  - destruct Hin as [E | []]; injection E as -> ->; apply sub_closed_refl.
  - destruct Hin as [E | Hin]; [injection E as -> ->; apply sub_closed_refl |].
    eapply sub_closed_trans; [apply sub_bsR | apply IHd; auto].
  - destruct Hin as [E | Hin]; [injection E as -> ->; apply sub_closed_refl |].
    eapply sub_closed_trans; [apply sub_slR | apply IHd; auto].
  - destruct Hin as [E | Hin]; [injection E as -> ->; apply sub_closed_refl |].
    apply in_app_or in Hin; destruct Hin as [Hin | Hin].
    + eapply sub_closed_trans; [apply sub_bsL_minor | apply IHd1; auto].
    + eapply sub_closed_trans; [apply sub_bsL_major | apply IHd2; auto].
  - destruct Hin as [E | Hin]; [injection E as -> ->; apply sub_closed_refl |].
    apply in_app_or in Hin; destruct Hin as [Hin | Hin].
    + eapply sub_closed_trans; [apply sub_slL_minor | apply IHd1; auto].
    + eapply sub_closed_trans; [apply sub_slL_major | apply IHd2; auto].
  - discriminate.
Qed.

(* Corollary: through cut elimination, every derivable sequent has a
   derivation using only subformulas of its end-sequent. *)
Corollary subformula_property_derivable : forall (Γ : ctx) C,
  derivable Γ C ->
  exists d : Deriv false Γ C, forall Γ' C', In (Γ', C') (sequents d) -> sub_closed Γ C Γ' C'.
Proof.
  intros Γ C [d]; exists (cut_elim d); intros; eapply subformula_property; eauto.
Qed.

End Subformula.

(* ========================================================================== *)
(*  Part 5 — Curry–Howard: derivations as (linear) λ-terms, read directly    *)
(*  as Coq functions (M&R §3.3 pp. 74–75; Lambek 1958 §7 p. 159)              *)
(* ========================================================================== *)

Section Semantics.
Context {Atom : Type} (interp : Atom -> Type).
Notation formula := (formula Atom).
Notation ctx := (list formula).

(* Def. 19.  The type homomorphism of M&R §3.3 step 1 (p. 75): (A\B)* = (B/A)*
   = A* → B*.  Shallow: syntactic types are mapped to Coq types, so a
   derivation's λ-term is a Coq function and β-conversion is definitional
   ([ARTIFACT-iii] the syntactic β-reduction of cut elimination is therefore
   not a separate theorem here; see header). *)
Fixpoint sem (A : formula) : Type :=
  match A with
  | at_ a => interp a
  | bs A B => sem A -> sem B
  | sl B A => sem A -> sem B
  end.

(* Environments: one semantic value per antecedent formula. *)
Fixpoint env (Γ : ctx) : Type :=
  match Γ with
  | [] => unit
  | A :: Γ => (sem A * env Γ)%type
  end.

Fixpoint env_app {Γ1 Γ2 : ctx} : env Γ1 -> env Γ2 -> env (Γ1 ++ Γ2) :=
  match Γ1 with
  | [] => fun _ ρ2 => ρ2
  | A :: Γ1 => fun ρ1 ρ2 => (fst ρ1, env_app (snd ρ1) ρ2)
  end.

Fixpoint env_split (Γ1 : ctx) {Γ2 : ctx} : env (Γ1 ++ Γ2) -> env Γ1 * env Γ2 :=
  match Γ1 with
  | [] => fun ρ => (tt, ρ)
  | A :: Γ1 => fun ρ => let (ρ1, ρ2) := env_split Γ1 (snd ρ) in ((fst ρ, ρ1), ρ2)
  end.

(* Def. 20.  The term assigned to a derivation, M&R §3.3 steps 2–3 p. 75;
   Moortgat 1997 Def. 3.2 p. 19: axiom ↦ variable, \i and /i ↦ abstraction,
   \h and /h ↦ application substituted for the hypothesis (a "compiled cut"),
   cut ↦ substitution. *)
Fixpoint denote {b} {Γ : ctx} {A : formula} (d : Deriv b Γ A) : env Γ -> sem A :=
  match d in Deriv _ Γ A return env Γ -> sem A with
  | d_ax A => fun ρ => fst ρ
  | d_bsR d _ => fun ρ a => denote d (a, ρ)
  | @d_slR _ _ _ A' _ d _ => fun ρ a => denote d (env_app ρ ((a, tt) : env [A']))
  | d_bsL Γ1 Γ2 B d1 d2 => fun ρ =>
      let (ρ1, ρ') := env_split Γ1 ρ in
      let (ρΔ, ρ'') := env_split _ ρ' in
      denote d2 (env_app ρ1 ((fst ρ'' (denote d1 ρΔ), snd ρ'') : env (B :: Γ2)))
  | d_slL Γ1 Γ2 B d1 d2 => fun ρ =>
      let (ρ1, ρ') := env_split Γ1 ρ in
      let (ρΔ, ρ2) := env_split _ (snd ρ') in
      denote d2 (env_app ρ1 ((fst ρ' (denote d1 ρΔ), ρ2) : env (B :: Γ2)))
  | @d_cut _ _ Δ1 Δ2 A' _ d1 d2 => fun ρ =>
      let (ρ1, ρ') := env_split Δ1 ρ in
      let (ρΓ, ρ2) := env_split _ ρ' in
      denote d2 (env_app ρ1 ((denote d1 ρΓ, ρ2) : env (A' :: Δ2)))
  end.

(* T18.  Cut is substitution (Moortgat Def. 3.2 "u[t/x]"; M&R p. 75 step 3):
   the meaning of a cut is the meaning of the right premise with the meaning
   of the left premise substituted for the cut formula.  Holds by definition
   of [denote], and is stated because it is the semantic content of the cut
   rule. *)
Lemma denote_cut : forall (Γ Δ1 Δ2 : ctx) A C (d1 : Deriv true Γ A) (d2 : Deriv true (Δ1 ++ A :: Δ2) C) ρ,
  denote (d_cut Δ1 Δ2 d1 d2) ρ =
  (let (ρ1, ρ') := env_split Δ1 ρ in
   let (ρΓ, ρ2) := env_split Γ ρ' in
   denote d2 (env_app ρ1 ((denote d1 ρΓ, ρ2) : env (A :: Δ2)))).
Proof. reflexivity. Qed.

End Semantics.

(* ========================================================================== *)
(*  Part 6 — A Montague fragment (M&R §3.3, Ex. 3.2, Ex. 3.5; Lambek 1958 §7) *)
(* ========================================================================== *)

Module Fragment.

Inductive prim : Type := NP | N | S.

Section Fragment.
Context (Entity : Type).

Definition interp (p : prim) : Type :=
  match p with NP => Entity | N => Entity -> Prop | S => Prop end.

Notation formula := (formula prim).
Notation NP_ := (at_ NP). Notation N_ := (at_ N). Notation S_ := (at_ S).
Notation sem := (sem interp).
Notation denote := (denote interp).

(* Lexical meanings (M&R Ex 3.5 p. 81: every ↦ λPλQ ∀x (P x ⇒ Q x); Ex 3.2
   p. 76: some ↦ λPλQ ∃x (P x ∧ Q x); Lambek Table I p. 157: works : n\s). *)
Definition every_sem : sem ((S_ / (NP_ \ S_)) / N_) :=
  fun (P : Entity -> Prop) (Q : Entity -> Prop) => forall x, P x -> Q x.
Definition some_sem : sem ((S_ / (NP_ \ S_)) / N_) :=
  fun (P : Entity -> Prop) (Q : Entity -> Prop) => exists x, P x /\ Q x.

(* Def. 22.  Derivations.  "John walks": np, np\s ⊢ s by \h with the axiom
   np ⊢ np as minor premise (M&R Ex 2.7 p. 30). *)
Definition d_john_walks : Deriv false [NP_; NP_ \ S_] S_ :=
  d_bsL [] [] S_ (d_ax NP_) (d_ax S_).

(* "every man walks": (s/(np\s))/n, n, np\s ⊢ s: /h on the determiner with
   minor premise n ⊢ n, then /h on s/(np\s) with minor premise np\s ⊢ np\s
   (M&R Ex 3.5 pp. 81–84, with the derivation of "some student ate a pizza"
   read for the subject determiner only). *)
Definition d_every_man_walks : Deriv false [(S_ / (NP_ \ S_)) / N_; N_; NP_ \ S_] S_ :=
  d_slL [] [NP_ \ S_] (S_ / (NP_ \ S_)) (d_ax N_)
    (d_slL [] [] S_ (d_ax (NP_ \ S_)) (d_ax S_)).

Definition d_some_man_walks := d_every_man_walks.

(* Lambek 1958 §7 (h) p. 163 / M&R p. 30: type raising x ⊢ z/(x\z). *)
Definition d_type_raise : Deriv false [NP_] (S_ / (NP_ \ S_)) :=
  d_slR (d_bsL [] [] S_ (d_ax NP_) (d_ax S_)) (cons_not_nil _ _).

(* Lambek 1958 §7 (g) p. 163: composition x/y, y/z ⊢ x/z (for any types). *)
Definition d_compose (A B C : formula) : Deriv false [A / B; B / C] (A / C) :=
  @d_slR _ false [A / B; B / C] C A
    (d_slL [] [] A (d_slL [] [] B (d_ax C) (d_ax B)) (d_ax A)) (cons_not_nil _ _).

(* T17.  The derivations compute the Montague meanings (M&R Ex 3.5 p. 84:
   "∀u child(u) ⇒ …"; Ex 3.2 pp. 76–77; Lambek p. 159).  By conversion. *)
Theorem john_walks_sem : forall (john : Entity) (walks : Entity -> Prop),
  denote d_john_walks (john, (walks, tt)) = walks john.
Proof. reflexivity. Qed.

Theorem every_man_walks_sem : forall (man walks : Entity -> Prop),
  denote d_every_man_walks (every_sem, (man, (walks, tt))) = (forall x, man x -> walks x).
Proof. reflexivity. Qed.

Theorem some_man_walks_sem : forall (man walks : Entity -> Prop),
  denote d_some_man_walks (some_sem, (man, (walks, tt))) = (exists x, man x /\ walks x).
Proof. reflexivity. Qed.

(* T20.  Type raising denotes λP. P john (M&R p. 75 "Pierre ↦ λP (P Pierre)"),
   composition denotes function composition (Lambek §7 (g)). *)
Theorem type_raise_sem : forall (john : Entity),
  denote d_type_raise (john, tt) = fun P : Entity -> Prop => P john.
Proof. reflexivity. Qed.

Theorem compose_sem : forall A B C (f : sem (A / B)) (g : sem (B / C)),
  denote (d_compose A B C) (f, (g, tt)) = fun c => f (g c).
Proof. reflexivity. Qed.

(* A derivation of "John walks" that goes through a cut on the raised
   subject (np ⊢ s/(np\s), then s/(np\s), np\s ⊢ s) denotes the same
   proposition as the cut-free one — cut is substitution (T18).  Semantic
   invariance of [cut_elim] in general is NOT proved here (see header:
   [cut_adm] is opaque). *)
Definition d_john_walks_cut : Deriv true [NP_; NP_ \ S_] S_ :=
  d_cut [] [NP_ \ S_] (weaken_flag d_type_raise)
    (weaken_flag (d_slL [] [] S_ (d_ax (NP_ \ S_)) (d_ax S_))).

Theorem john_walks_cut_sem : forall (john : Entity) (walks : Entity -> Prop),
  denote d_john_walks_cut (john, (walks, tt)) = walks john.
Proof. reflexivity. Qed.

End Fragment.
End Fragment.

(* ========================================================================== *)
(*  Part 7 — Assumption audit                                                 *)
(* ========================================================================== *)
(* Output of the commands below under Coq 8.20.1 (2026-09-05): every one of
   the ten theorems prints "Closed under the global context" — the file uses
   no axioms, no classical principles and no extensionality. *)
Print Assumptions cut_adm.
Print Assumptions cut_elim.
Print Assumptions derivable_iff_cf.
Print Assumptions subformula_property.
Print Assumptions deriv_nonempty.
Print Assumptions ax_expand_atomic.
Print Assumptions Fragment.every_man_walks_sem.
Print Assumptions Fragment.some_man_walks_sem.
Print Assumptions Fragment.type_raise_sem.
Print Assumptions Fragment.compose_sem.
