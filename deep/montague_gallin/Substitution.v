(* Typed capture-avoiding substitution for Gallin's AS4, p. 60.
   Locally indexed binders implement the source's free-for condition.
   Signature parameters (CFree) are not substituted by this operation. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Models.
From MontagueGallin Require Import Types Target Minimal.
Import ListNotations.
Set Implicit Arguments.

Definition csub S P G D := forall a, gvar G a -> ctm S P D a.
Definition csub_lift {S P G D a} (s : csub S P G D) : csub S P (a :: G) (a :: D) :=
  fun b v => match v in gvar G' b' return
    match G' with [] => unit
    | c :: G0 => csub S P G0 D -> ctm S P (c :: D) b' end with
  | @gz _ _ => fun _ => CVar gz
  | @gvs _ _ _ w => fun s0 => cweaken (s0 _ w)
  end s.
Fixpoint csubst {S P G a} (p : ctm S P G a) : forall D, csub S P G D -> ctm S P D a :=
  match p in ctm _ _ G' a' return forall D, csub S P G' D -> ctm S P D a' with
  | CVar v => fun D s => s _ v
  | CFree n => fun D _ => CFree n
  | CCon n => fun D _ => CCon n
  | CLam p => fun D s => CLam (csubst p (csub_lift s))
  | CApp p q => fun D s => CApp (csubst p s) (csubst q s)
  | CEq p q => fun D s => CEq (csubst p s) (csubst q s)
  end.
Definition csub_head {S P G a} (q : ctm S P G a) : csub S P (a :: G) G :=
  fun b v => match v in gvar G' b' return
    match G' with [] => unit
    | c :: G0 => ctm S P G0 c -> ctm S P G0 b' end with
  | @gz _ _ => fun q0 => q0
  | @gvs _ _ _ w => fun _ => CVar w
  end q.
Definition subst0 {S P G a b} (p : ctm S P (a :: G) b) (q : ctm S P G a) :=
  csubst p (csub_head q).

Section Semantics.
Context {S P : gty -> Type} {E I : Type}.
Variable B : BooleanTruth.
Variable FE : FunExt.
Variable lex : forall a, S a -> value_domain E I a.
Variable theta : forall a, P a -> value_domain E I a.
Local Notation V := (ceval B lex theta).

Theorem substitution_preserves_interpretation G a (p : ctm S P G a) :
  forall D (s : csub S P G D) rho tau,
  (forall b v, V (s b v) tau = rho b v) ->
  V (csubst p s) tau = V p rho.
Proof.
  induction p; intros D sub rho tau H; cbn; try reflexivity; try apply H;
    try (rewrite IHp1 with (rho := rho), IHp2 with (rho := rho); auto; fail).
  apply FE; intro x; apply IHp; apply gvar_cases; cbn; [reflexivity |].
  intros tyv v; rewrite ceval_weaken by exact FE; apply H.
Qed.
Corollary single_substitution_interpretation G a b (p : ctm S P (a :: G) b)
  (q : ctm S P G a) rho :
  V (subst0 p q) rho = V p (value_extend rho (V q rho)).
Proof. apply substitution_preserves_interpretation; apply gvar_cases; cbn; reflexivity. Qed.
Theorem beta_interpretation G a b (p : ctm S P (a :: G) b) (q : ctm S P G a) rho :
  V (CApp (CLam p) q) rho = V (subst0 p q) rho.
Proof. symmetry; apply single_substitution_interpretation. Qed.
End Semantics.

(* One-hole contexts describe one occurrence, including occurrences under
   lambdas. Binder names are not term positions, so the occurrence forbidden
   by Gallin's "immediately preceded by lambda" condition is unavailable. *)
Section Contexts.
Context (S P : gty -> Type).
Inductive ccontext : list gty -> gty -> list gty -> gty -> Type :=
| Hole : forall G a, ccontext G a G a
| AppFunction : forall D a G b c, ccontext D a G (garr b c) -> ctm S P G b -> ccontext D a G c
| AppArgument : forall D a G b c, ctm S P G (garr b c) -> ccontext D a G b -> ccontext D a G c
| EqLeft : forall D a G b, ccontext D a G b -> ctm S P G b -> ccontext D a G gt
| EqRight : forall D a G b, ctm S P G b -> ccontext D a G b -> ccontext D a G gt
| LambdaBody : forall D a G b c, ccontext D a (b :: G) c -> ccontext D a G (garr b c).
End Contexts.
Arguments Hole {S P G a}.
Arguments AppFunction {S P D a G b c} _ _.
Arguments AppArgument {S P D a G b c} _ _.
Arguments EqLeft {S P D a G b} _ _.
Arguments EqRight {S P D a G b} _ _.
Arguments LambdaBody {S P D a G b c} _.
Fixpoint plug {S P D a G b} (C : ccontext S P D a G b) (p : ctm S P D a) : ctm S P G b :=
  match C in ccontext _ _ D' a' G' b' return ctm S P D' a' -> ctm S P G' b' with
  | Hole => fun p => p
  | AppFunction C q => fun p => CApp (plug C p) q
  | AppArgument q C => fun p => CApp q (plug C p)
  | EqLeft C q => fun p => CEq (plug C p) q
  | EqRight q C => fun p => CEq q (plug C p)
  | LambdaBody C => fun p => CLam (plug C p)
  end p.

Theorem replacement_preserves_global_equality {S P E I} (B : BooleanTruth) (FE : FunExt)
  (lex : forall a, S a -> value_domain E I a) (theta : forall a, P a -> value_domain E I a)
  D a G b (C : ccontext S P D a G b) (p q : ctm S P D a) :
  (forall rho, ceval B lex theta p rho = ceval B lex theta q rho) ->
  forall tau, ceval B lex theta (plug C p) tau = ceval B lex theta (plug C q) tau.
Proof.
  intro H; induction C; intro tau; cbn; try apply H;
    try (rewrite (IHC p q H tau); reflexivity).
  apply FE; intro x; apply IHC; exact H.
Qed.

Example beta_substitution_keeps_outer_variable S P :
  subst0 (@CLam S P [gt; gt] gt gt (CVar (gvs gz))) (CVar gz) =
  @CLam S P [gt] gt gt (CVar (gvs gz)).
Proof. reflexivity. Qed.
