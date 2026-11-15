Require Import Lambek.
Require Import List ZArith Lia.
Import ListNotations.
Open Scope lambek_scope.

(* ========================================================================== *)
(*  Lambek_Count.v — the count invariant for the Lambek calculus L            *)
(*  FORMAL-ATLAS / atlas/type_logical                                          *)
(* ========================================================================== *)
(*
   SOURCES
     Lambek, J. (1958). The mathematics of sentence structure. American
       Mathematical Monthly 65(3): 154–170.  [§10]
     Moot, R. & Retoré, C. (2012). The Logic of Categorial Grammars. LNCS 6850,
       Springer.  [ch. 2 §2.5, Prop 2.6 p. 30; p. 45]
   Design document: atlas_data/designs/lambek.md, T24.
   Builds on Lambek.v (formulas, the sequent calculus Deriv, the fragment),
   which this file leaves unchanged.

   WHAT IS FORMALIZED
     count p A counts the occurrences of the primitive type p in A, with a
     minus sign for occurrences in argument position.
       T24 count_invariant           every derivation, with or without cut,
                                     preserves the count of every p
           unbalanced_not_derivable  an unbalanced sequent is not derivable
           np_not_s, s_not_np,       non-derivability results for the
           extra_argument_rejected   fragment of Lambek.v

   NOT FORMALIZED (and why)
     * The invariant is a necessary condition only.  It ignores word order,
       so it does not rule out np\s, np ⊢ s ("walks John"), nor
       s/(n\s) ⊢ n (M&R p. 45).  Those need the decision procedure
       (design T13–T16), which is not formalized here.
     * The general interpretation in pre-ordered groups of which the count is
       an instance (design T23): only the Z-count instance is proved.
*)

Section Count.
Context {Atom : Type} (Atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}).
Notation formula := (formula Atom).
Notation ctx := (list formula).

(* Polarity-weighted count: count (A\B) = count (B/A) = count B - count A. *)
Fixpoint count (p : Atom) (A : formula) : Z :=
  match A with
  | at_ q => if Atom_eq_dec p q then 1 else 0
  | bs A B => count p B - count p A
  | sl B A => count p B - count p A
  end%Z.

(* The count of a context is the sum of the counts of its formulas. *)
Definition count_ctx (p : Atom) (Γ : ctx) : Z :=
  fold_right (fun A n => count p A + n)%Z 0%Z Γ.

Lemma count_ctx_nil : forall p, count_ctx p [] = 0%Z.
Proof. reflexivity. Qed.

Lemma count_ctx_cons : forall p A Γ,
  count_ctx p (A :: Γ) = (count p A + count_ctx p Γ)%Z.
Proof. reflexivity. Qed.

Lemma count_ctx_app : forall p Γ Δ,
  count_ctx p (Γ ++ Δ) = (count_ctx p Γ + count_ctx p Δ)%Z.
Proof.
  intros p Γ Δ; induction Γ as [|A Γ IH]; [reflexivity|].
  cbn [app]; rewrite !count_ctx_cons, IH; lia.
Qed.

(* T24.  In every derivation of Γ ⊢ A, with or without cut, each primitive
   type has the same count in Γ as in A.  Lambek 1958 §10; M&R Prop 2.6
   p. 30.  Each rule preserves the difference between the two sides. *)
Theorem count_invariant : forall b (Γ : ctx) A (d : Deriv b Γ A) p,
  count_ctx p Γ = count p A.
Proof.
  intros b Γ A d p; induction d;
    repeat first [ rewrite count_ctx_app in * | rewrite count_ctx_cons in *
                 | rewrite count_ctx_nil in * ];
    cbn [count] in *; lia.
Qed.

End Count.

Module CountExamples.
Import Fragment.

Definition prim_eq_dec : forall a b : prim, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Notation NP_ := (at_ NP). Notation S_ := (at_ S).

(* If some primitive type has different counts on the two sides, the sequent
   is not derivable.  Contrapositive of T24 (M&R p. 30). *)
Lemma unbalanced_not_derivable : forall (Γ : list (formula prim)) A p,
  count_ctx prim_eq_dec p Γ <> count prim_eq_dec p A -> ~ derivable Γ A.
Proof. intros Γ A p H [d]; exact (H (count_invariant prim_eq_dec _ _ _ d p)). Qed.

(* np ⊬ s: a noun phrase is not a sentence.  Design T24 corollary. *)
Theorem np_not_s : ~ derivable [NP_] S_.
Proof. apply (unbalanced_not_derivable _ _ S); discriminate. Qed.

(* s ⊬ np: a sentence is not a noun phrase.  Design T24 corollary. *)
Theorem s_not_np : ~ derivable [S_] NP_.
Proof. apply (unbalanced_not_derivable _ _ NP); discriminate. Qed.

(* np, np, np\s ⊬ s ("John Mary walks"): an intransitive verb cannot take a
   second subject; np occurs once too often on the left.  Illustrates
   M&R Prop 2.6 on the fragment of Lambek.v. *)
Theorem extra_argument_rejected : ~ derivable [NP_; NP_; NP_ \ S_] S_.
Proof. apply (unbalanced_not_derivable _ _ NP); discriminate. Qed.

End CountExamples.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Under Coq 8.20.1 (2026-11-15) every theorem below prints "Closed under the
   global context": no axioms, no classical principles, no extensionality. *)
Print Assumptions count_invariant.
Print Assumptions CountExamples.unbalanced_not_derivable.
Print Assumptions CountExamples.np_not_s.
Print Assumptions CountExamples.s_not_np.
Print Assumptions CountExamples.extra_argument_rejected.
