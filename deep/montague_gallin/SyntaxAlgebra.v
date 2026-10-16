(* Syntactic substitution laws. These equalities use no semantic model,
   extensionality axiom, or rule that turns validity into derivability. *)
From Coq Require Import List.
From MontagueGallin Require Import Types Target Minimal Substitution.
Import ListNotations.
Set Implicit Arguments.

Section Algebra.
Context {S P : gty -> Type}.
Lemma crename_ext G a (p : ctm S P G a) : forall D (r s : gren G D),
  (forall b v, r b v = s b v) -> crename p r = crename p s.
Proof.
  induction p; intros D r rr H; cbn; try reflexivity; try (rewrite H; reflexivity);
    try (rewrite (IHp1 D r rr H), (IHp2 D r rr H); reflexivity).
  f_equal; apply IHp; apply gvar_cases; cbn; [reflexivity | intros; f_equal; apply H].
Qed.
Lemma crename_identity G a (p : ctm S P G a) : forall r : gren G G,
  (forall b v, r b v = v) -> crename p r = p.
Proof.
  induction p; intros r H; cbn; try reflexivity; try (rewrite H; reflexivity);
    try (rewrite (IHp1 r H), (IHp2 r H); reflexivity).
  f_equal; apply IHp; apply gvar_cases; cbn; [reflexivity | intros; f_equal; apply H].
Qed.
Lemma crename_compose G a (p : ctm S P G a) : forall D E (r : gren G D) (s : gren D E),
  crename (crename p r) s = crename p (fun b v => s b (r b v)).
Proof.
  induction p; intros D E r rr; cbn; try reflexivity; try (rewrite IHp1, IHp2; reflexivity).
  f_equal; rewrite IHp; apply crename_ext; apply gvar_cases; cbn; reflexivity.
Qed.
Lemma crename_weaken G D a b (p : ctm S P G b) (r : gren G D) :
  crename (@cweaken S P G a b p) (glift r) = cweaken (crename p r).
Proof. unfold cweaken; rewrite !crename_compose; apply crename_ext; intros; reflexivity. Qed.
Lemma csubst_ext G a (p : ctm S P G a) : forall D (s r : csub S P G D),
  (forall b v, s b v = r b v) -> csubst p s = csubst p r.
Proof.
  induction p; intros D sub r H; cbn; try reflexivity; try apply H;
    try (rewrite (IHp1 D sub r H), (IHp2 D sub r H); reflexivity).
  f_equal; apply IHp; apply gvar_cases; cbn; auto; intros; rewrite H; reflexivity.
Qed.
Lemma csubst_identity G a (p : ctm S P G a) : forall s : csub S P G G,
  (forall b v, s b v = CVar v) -> csubst p s = p.
Proof.
  induction p; intros sub H; cbn; try reflexivity; try apply H;
    try (rewrite (IHp1 sub H), (IHp2 sub H); reflexivity).
  f_equal; apply IHp; apply gvar_cases; cbn; auto; intros; rewrite H; reflexivity.
Qed.
Lemma csubst_renaming G a (p : ctm S P G a) : forall D (r : gren G D),
  csubst p (fun b v => CVar (r b v)) = crename p r.
Proof.
  induction p; intros D r; cbn; try reflexivity; try (rewrite IHp1, IHp2; reflexivity).
  f_equal; rewrite <- IHp; apply csubst_ext; apply gvar_cases; cbn; reflexivity.
Qed.
Lemma csubst_after_rename G a (p : ctm S P G a) : forall D E (r : gren G D) (s : csub S P D E),
  csubst (crename p r) s = csubst p (fun b v => s b (r b v)).
Proof.
  induction p; intros D E r sub; cbn; try reflexivity; try (rewrite IHp1, IHp2; reflexivity).
  f_equal; rewrite IHp; apply csubst_ext; apply gvar_cases; cbn; reflexivity.
Qed.
Lemma crename_after_subst G a (p : ctm S P G a) : forall D E (s : csub S P G D) (r : gren D E),
  crename (csubst p s) r = csubst p (fun b v => crename (s b v) r).
Proof.
  induction p; intros D E sub r; cbn; try reflexivity; try (rewrite IHp1, IHp2; reflexivity).
  f_equal; rewrite IHp; apply csubst_ext; apply gvar_cases; cbn; [reflexivity |].
  intros; apply crename_weaken.
Qed.
Lemma csubst_lift_weaken G D a b (p : ctm S P G b) (s : csub S P G D) :
  csubst (@cweaken S P G a b p) (csub_lift s) = cweaken (csubst p s).
Proof.
  unfold cweaken at 1 2; rewrite csubst_after_rename, crename_after_subst.
  apply csubst_ext; intros; reflexivity.
Qed.
Lemma subst0_weaken G a b (p : ctm S P G b) (q : ctm S P G a) :
  subst0 (cweaken p) q = p.
Proof. unfold subst0, cweaken; rewrite csubst_after_rename; apply csubst_identity; intros; reflexivity. Qed.
End Algebra.
