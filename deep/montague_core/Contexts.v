(* Independently presented interleaved contexts and rules for the selected C
   fragment. This bridge concerns these intrinsic/de Bruijn representations,
   not a completed adequacy proof for the source's named typing judgments. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax Calculus.
Import ListNotations.
Set Implicit Arguments.

Section Interleaved.
Variable symbol : ty -> Type.

Inductive mixed : list ty -> Type :=
| context_empty : mixed []
| context_var : forall G a, mixed G -> mixed (a :: G)
| context_true : forall G, mixed G -> tm symbol G truth -> mixed G.

Arguments context_var {G} a _.
Arguments context_true {G} _ _.

Fixpoint hypotheses {G} (C : mixed G) : list (tm symbol G truth) :=
  match C with
  | context_empty => []
  | context_var a C => map (@weaken symbol _ a truth) (hypotheses C)
  | context_true C p => p :: hypotheses C
  end.

(* A formula can mention only variables already declared when it is added.
   Crossing a later variable declaration shifts all of its free variables. *)
Inductive lookup : forall G, mixed G -> tm symbol G truth -> Prop :=
| lookup_here : forall G (C : mixed G) p, lookup (context_true C p) p
| lookup_true : forall G (C : mixed G) p q,
    lookup C p -> lookup (context_true C q) p
| lookup_var : forall G a (C : mixed G) p,
    lookup C p -> lookup (context_var a C) (weaken p).

Lemma lookup_in : forall G (C : mixed G) p,
  lookup C p -> In p (hypotheses C).
Proof.
  intros G C p K; induction K; cbn.
  - left; reflexivity.
  - right; assumption.
  - apply in_map_iff; exists p; split; [reflexivity | assumption].
Qed.

Lemma in_lookup : forall G (C : mixed G) p,
  In p (hypotheses C) -> lookup C p.
Proof.
  intros G C; induction C; intros p Hin; cbn in Hin.
  - contradiction.
  - apply in_map_iff in Hin; destruct Hin as [q [E Hin]]; subst p.
    apply lookup_var; apply IHC; exact Hin.
  - destruct Hin as [E | Hin].
    + subst p; apply lookup_here.
    + apply lookup_true; apply IHC; exact Hin.
Qed.

Theorem lookup_flatten : forall G (C : mixed G) p,
  lookup C p <-> In p (hypotheses C).
Proof. split; [apply lookup_in | apply in_lookup]. Qed.

Variable L : logic.

(* Not defined as a wrapper around derives: these are independent rules. *)
Inductive mixed_derives : forall G, mixed G -> tm symbol G truth -> Prop :=
| m_assume : forall G (C : mixed G) p, lookup C p -> mixed_derives C p
| m_imp_intro : forall G (C : mixed G) p q,
    mixed_derives (context_true C p) q -> mixed_derives C (Imp p q)
| m_imp_elim : forall G (C : mixed G) p q,
    mixed_derives C (Imp p q) -> mixed_derives C p -> mixed_derives C q
| m_all_intro : forall G a (C : mixed G) (p : tm symbol (a :: G) truth),
    mixed_derives (context_var a C) p -> mixed_derives C (All p)
| m_all_elim : forall G a (C : mixed G) (p : tm symbol (a :: G) truth) u,
    mixed_derives C (All p) -> mixed_derives C (instantiate u p)
| m_conversion : forall G (C : mixed G) p q,
    mixed_derives C p -> beta p q -> mixed_derives C q
| m_double_negation : forall G (C : mixed G) p,
    L = classical -> mixed_derives C (neg (neg p)) -> mixed_derives C p.

Theorem mixed_to_split : forall G (C : mixed G) p,
  mixed_derives C p -> derives L (hypotheses C) p.
Proof.
  intros G C p D; induction D.
  - apply d_assume; apply lookup_in; assumption.
  - apply d_imp_intro; exact IHD.
  - eapply d_imp_elim; eassumption.
  - apply d_all_intro; exact IHD.
  - apply d_all_elim; assumption.
  - eapply d_conversion; eassumption.
  - apply d_double_negation; assumption.
Qed.

Theorem split_to_mixed : forall G H (p : tm symbol G truth),
  derives L H p -> forall C : mixed G,
  hypotheses C = H -> mixed_derives C p.
Proof.
  intros G H p D; induction D; intros C E.
  - apply m_assume; apply in_lookup; rewrite E; assumption.
  - apply m_imp_intro; apply IHD; cbn; rewrite E; reflexivity.
  - eapply m_imp_elim; [apply IHD1 | apply IHD2]; exact E.
  - apply m_all_intro; apply IHD; cbn; rewrite E; reflexivity.
  - apply m_all_elim; apply IHD; exact E.
  - eapply m_conversion; [apply IHD; exact E | eassumption].
  - apply m_double_negation; [assumption | apply IHD; exact E].
Qed.

Theorem mixed_split_equivalence : forall G (C : mixed G) p,
  mixed_derives C p <-> derives L (hypotheses C) p.
Proof.
  split; [apply mixed_to_split | intro D; eapply split_to_mixed; eauto].
Qed.

Fixpoint variables_only (G : list ty) : mixed G :=
  match G with
  | [] => context_empty
  | a :: rest => context_var a (variables_only rest)
  end.

Fixpoint add_hypotheses {G} (C : mixed G) (H : list (tm symbol G truth)) : mixed G :=
  match H with
  | [] => C
  | p :: rest => context_true (add_hypotheses C rest) p
  end.

Definition pack {G} (H : list (tm symbol G truth)) :=
  add_hypotheses (variables_only G) H.

Lemma variables_only_empty : forall G, hypotheses (variables_only G) = [].
Proof. induction G; cbn; [reflexivity | rewrite IHG; reflexivity]. Qed.

Lemma add_hypotheses_flatten : forall G (C : mixed G) H,
  hypotheses (add_hypotheses C H) = H ++ hypotheses C.
Proof.
  intros G C H; induction H as [| p rest IH]; cbn;
    [reflexivity | rewrite IH; reflexivity].
Qed.

Theorem pack_flatten : forall G (H : list (tm symbol G truth)),
  hypotheses (pack H) = H.
Proof.
  intros; unfold pack; rewrite add_hypotheses_flatten, variables_only_empty, app_nil_r.
  reflexivity.
Qed.

Theorem packed_derivation : forall G H (p : tm symbol G truth),
  mixed_derives (pack H) p <-> derives L H p.
Proof. intros; rewrite mixed_split_equivalence, pack_flatten; reflexivity. Qed.

(* Flattening forgets declaration placement, so the round trip preserves
   derivability, not literal equality of the original contexts. *)
Theorem context_round_trip : forall G (C : mixed G) p,
  mixed_derives (pack (hypotheses C)) p <-> mixed_derives C p.
Proof. intros; rewrite packed_derivation, mixed_split_equivalence; reflexivity. Qed.

End Interleaved.

Arguments context_empty {symbol}.
Arguments context_var {symbol G} a _.
Arguments context_true {symbol G} _ _.
Arguments mixed_derives {symbol} L {G} _ _.
