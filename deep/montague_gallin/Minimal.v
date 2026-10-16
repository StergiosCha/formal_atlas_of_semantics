(* Gallin (1975), pp. 15-16 and 59-60: only variables, constants,
   application, abstraction and equality are primitive. Bound and free
   variables are separate constructors for the locally indexed encoding.
   Logical abbreviations below are beta-reduced applications of his operators.
   No primitive truth constant or quantifier is added to the signature. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Models.
From MontagueGallin Require Import Types Target.
Import ListNotations.
Set Implicit Arguments.

Section Syntax.
Context (symbol parameter : gty -> Type).
Inductive ctm : list gty -> gty -> Type :=
| CVar : forall G a, gvar G a -> ctm G a
| CFree : forall G a, parameter a -> ctm G a
| CCon : forall G a, symbol a -> ctm G a
| CLam : forall G a b, ctm (a :: G) b -> ctm G (garr a b)
| CApp : forall G a b, ctm G (garr a b) -> ctm G a -> ctm G b
| CEq : forall G a, ctm G a -> ctm G a -> ctm G gt.
End Syntax.
Arguments CVar {symbol parameter G a} _.
Arguments CFree {symbol parameter G a} _.
Arguments CCon {symbol parameter G a} _.
Arguments CLam {symbol parameter G a b} _.
Arguments CApp {symbol parameter G a b} _ _.
Arguments CEq {symbol parameter G a} _ _.

Fixpoint crename {S P G a} (u : ctm S P G a) : forall D, gren G D -> ctm S P D a :=
  match u in ctm _ _ G' a' return forall D, gren G' D -> ctm S P D a' with
  | CVar v => fun D r => CVar (r _ v)
  | CFree n => fun D _ => CFree n
  | CCon n => fun D _ => CCon n
  | CLam p => fun D r => CLam (crename p (glift r))
  | CApp p q => fun D r => CApp (crename p r) (crename q r)
  | CEq p q => fun D r => CEq (crename p r) (crename q r)
  end.
Definition cweaken {S P G a b} (u : ctm S P G b) : ctm S P (a :: G) b :=
  crename u (fun _ v => gvs v).

Definition ctrue {S P G} : ctm S P G gt :=
  CEq (@CLam S P G gt gt (CVar gz)) (CLam (CVar gz)).
Definition cfalse {S P G} : ctm S P G gt :=
  CEq (@CLam S P G gt gt (CVar gz)) (CLam ctrue).
Definition cneg {S P G} (p : ctm S P G gt) := CEq cfalse p.
Definition cand {S P G} (p q : ctm S P G gt) : ctm S P G gt :=
  CEq (@CLam S P G (garr gt gt) gt
          (CEq (CApp (CVar gz) (cweaken p)) (cweaken q)))
      (CLam (CApp (CVar gz) ctrue)).
Definition cimp {S P G} (p q : ctm S P G gt) := CEq (cand p q) p.
Definition cor {S P G} (p q : ctm S P G gt) := cimp (cneg p) q.
(* Boolean biconditional uses the already primitive equality at type t. *)
Definition ciff {S P G} (p q : ctm S P G gt) := CEq p q.
Definition call {S P G a} (p : ctm S P (a :: G) gt) : ctm S P G gt :=
  CEq (CLam p) (CLam ctrue).
Definition cex {S P G a} (p : ctm S P (a :: G) gt) := cneg (call (cneg p)).

Fixpoint eliminate {S P G a} (p : gtm S P G a) : ctm S P G a :=
  match p with
  | GVar v => CVar v | GFree n => CFree n | GCon n => CCon n
  | GLam p => CLam (eliminate p)
  | GApp p q => CApp (eliminate p) (eliminate q)
  | GEq p q => CEq (eliminate p) (eliminate q)
  | GNeg p => cneg (eliminate p)
  | GAnd p q => cand (eliminate p) (eliminate q)
  | GOr p q => cor (eliminate p) (eliminate q)
  | GImp p q => cimp (eliminate p) (eliminate q)
  | GIff p q => ciff (eliminate p) (eliminate q)
  | GAll p => call (eliminate p)
  | GEx p => cex (eliminate p)
  end.
Fixpoint include_core {S P G a} (p : ctm S P G a) : gtm S P G a :=
  match p with
  | CVar v => GVar v | CFree n => GFree n | CCon n => GCon n
  | CLam p => GLam (include_core p)
  | CApp p q => GApp (include_core p) (include_core q)
  | CEq p q => GEq (include_core p) (include_core q)
  end.
Theorem eliminate_core_identity S P G a (p : ctm S P G a) :
  eliminate (include_core p) = p.
Proof. induction p; cbn; congruence. Qed.

Section Evaluation.
Context {S P : gty -> Type} {E I : Type}.
Variable B : BooleanTruth.
Variable lex : forall a, S a -> value_domain E I a.
Variable free : forall a, P a -> value_domain E I a.
(* Independent evaluation of the six constructors, not via include_core. *)
Fixpoint ceval {G a} (p : ctm S P G a) (rho : value_env E I G) : value_domain E I a :=
  match p in ctm _ _ G' a' return value_env E I G' -> value_domain E I a' with
  | CVar v => fun r => r _ v
  | CFree n => fun _ => @free _ n
  | CCon n => fun _ => @lex _ n
  | CLam p => fun r x => ceval p (value_extend r x)
  | CApp p q => fun r => ceval p r (ceval q r)
  | CEq p q => fun r => truth B (ceval p r = ceval q r)
  end rho.

Theorem ceval_rename (FE : FunExt) G a (p : ctm S P G a) :
  forall D (r : gren G D) rho tau,
  (forall b v, tau _ (r b v) = rho b v) ->
  ceval (crename p r) tau = ceval p rho.
Proof.
  induction p; intros D r rho tau H; cbn; try reflexivity; try apply H;
    try (rewrite IHp1 with (rho := rho), IHp2 with (rho := rho); auto; fail).
  apply FE; intro x; apply IHp; apply gvar_cases; cbn; auto.
Qed.
Corollary ceval_weaken (FE : FunExt) G a b (p : ctm S P G b) rho x :
  ceval (@cweaken S P G a b p) (value_extend rho x) = ceval p rho.
Proof. apply ceval_rename; [exact FE | intros; reflexivity]. Qed.

Lemma ceval_true G (rho : value_env E I G) : ceval ctrue rho = true.
Proof. apply (proj2 (truth_spec B _)); reflexivity. Qed.
Lemma ceval_false G (rho : value_env E I G) : ceval cfalse rho = false.
Proof.
  change (truth B ((fun x : bool => x) = (fun _ : bool => ceval ctrue rho)) = false).
  rewrite ceval_true.
  destruct (truth B ((fun x : bool => x) = (fun _ : bool => true))) eqn:H; auto.
  apply (proj1 (truth_spec B _)) in H.
  apply (f_equal (fun f => f false)) in H; discriminate.
Qed.

Lemma boolean_equality x y : truth B (x = y) = Bool.eqb x y.
Proof.
  destruct x, y; cbn; try (apply (proj2 (truth_spec B _)); reflexivity).
  all: destruct (truth B _) eqn:H; auto;
    apply (proj1 (truth_spec B _)) in H; discriminate.
Qed.
Lemma ceval_neg G (p : ctm S P G gt) rho : ceval (cneg p) rho = negb (ceval p rho).
Proof. change (truth B (ceval cfalse rho = ceval p rho) = negb (ceval p rho)).
  rewrite ceval_false, boolean_equality; destruct (ceval p rho); reflexivity. Qed.

(* The conjunction on Gallin p. 15 quantifies over Boolean functions by
   equality of functions. Its four cases exercise both Boolean reflection
   and function extensionality; no primitive conjunction is used in ctm. *)
Lemma gallin_conjunction (FE : FunExt) (x y : bool) :
  truth B ((fun f : bool -> bool => truth B (f x = y)) = (fun f => f true)) = andb x y.
Proof.
  destruct x, y; cbn.
  - apply (proj2 (truth_spec B _)); apply FE; intro f.
    rewrite boolean_equality; destruct (f true); reflexivity.
  - destruct (truth B _) eqn:H; auto.
    apply (proj1 (truth_spec B _)) in H.
    apply (f_equal (fun h => h (fun z : bool => z))) in H.
    rewrite boolean_equality in H; discriminate.
  - destruct (truth B _) eqn:H; auto.
    apply (proj1 (truth_spec B _)) in H.
    apply (f_equal (fun h => h (fun z : bool => z))) in H.
    rewrite boolean_equality in H; discriminate.
  - destruct (truth B _) eqn:H; auto.
    apply (proj1 (truth_spec B _)) in H.
    apply (f_equal (fun h => h (fun _ : bool => false))) in H.
    rewrite boolean_equality in H; discriminate.
Qed.
Lemma ceval_and (FE : FunExt) G (p q : ctm S P G gt) rho :
  ceval (cand p q) rho = andb (ceval p rho) (ceval q rho).
Proof.
  change (truth B ((fun f : bool -> bool =>
    truth B (f (ceval (cweaken p) (@value_extend E I G (garr gt gt) rho f)) =
                 ceval (cweaken q) (@value_extend E I G (garr gt gt) rho f))) =
    (fun f : bool -> bool => f (ceval ctrue (@value_extend E I G (garr gt gt) rho f)))) =
    andb (ceval p rho) (ceval q rho)).
  assert (L : (fun f : bool -> bool =>
    truth B (f (ceval (cweaken p) (@value_extend E I G (garr gt gt) rho f)) =
                 ceval (cweaken q) (@value_extend E I G (garr gt gt) rho f))) =
    (fun f => truth B (f (ceval p rho) = ceval q rho))).
  { apply FE; intro f; rewrite !ceval_weaken by exact FE; reflexivity. }
  assert (R : (fun f : bool -> bool => f (ceval ctrue (@value_extend E I G (garr gt gt) rho f))) =
    (fun f => f true)).
  { apply FE; intro f; rewrite ceval_true; reflexivity. }
  rewrite L, R; apply gallin_conjunction; exact FE.
Qed.
Lemma ceval_imp (FE : FunExt) G (p q : ctm S P G gt) rho :
  ceval (cimp p q) rho = orb (negb (ceval p rho)) (ceval q rho).
Proof. change (truth B (ceval (cand p q) rho = ceval p rho) =
    orb (negb (ceval p rho)) (ceval q rho)).
  rewrite ceval_and by exact FE; rewrite boolean_equality.
  destruct (ceval p rho), (ceval q rho); reflexivity. Qed.
Lemma ceval_or (FE : FunExt) G (p q : ctm S P G gt) rho :
  ceval (cor p q) rho = orb (ceval p rho) (ceval q rho).
Proof. unfold cor; rewrite ceval_imp by exact FE; rewrite ceval_neg.
  destruct (ceval p rho); reflexivity. Qed.
Lemma ceval_iff G (p q : ctm S P G gt) rho :
  ceval (ciff p q) rho = Bool.eqb (ceval p rho) (ceval q rho).
Proof. apply boolean_equality. Qed.
Lemma ceval_all (FE : FunExt) G a (p : ctm S P (a :: G) gt) rho :
  ceval (call p) rho = truth B (forall x, ceval p (value_extend rho x) = true).
Proof.
  change (truth B ((fun x => ceval p (value_extend rho x)) =
    (fun x => ceval ctrue (value_extend rho x))) =
    truth B (forall x, ceval p (value_extend rho x) = true)).
  apply truth_congr; split.
  - intros H x; apply (f_equal (fun f => f x)) in H; rewrite ceval_true in H; exact H.
  - intro H; apply FE; intro x; rewrite ceval_true; apply H.
Qed.
Lemma ceval_ex (FE : FunExt) G a (p : ctm S P (a :: G) gt) rho :
  ceval (cex p) rho = truth B (exists x, ceval p (value_extend rho x) = true).
Proof.
  unfold cex; rewrite ceval_neg, ceval_all by exact FE.
  assert (H : (forall x, ceval (cneg p) (value_extend rho x) = true) <->
    ~ (exists x, ceval p (value_extend rho x) = true)).
  { split.
    - intros H [x K]; specialize (H x); rewrite ceval_neg, K in H; discriminate.
    - intros H x; rewrite ceval_neg.
      destruct (ceval p (value_extend rho x)) eqn:K; auto.
      exfalso; apply H; exists x; exact K. }
  rewrite (truth_congr B H).
  destruct (truth B (exists x, ceval p (value_extend rho x) = true)) eqn:K.
  - apply (proj1 (truth_spec B _)) in K.
    destruct (truth B (~ (exists x, ceval p (value_extend rho x) = true))) eqn:L; auto.
    apply (proj1 (truth_spec B _)) in L; contradiction.
  - assert (N : ~ (exists x, ceval p (value_extend rho x) = true)).
    { intro N; apply (proj2 (truth_spec B _)) in N; congruence. }
    apply (proj2 (truth_spec B _)) in N; rewrite N; reflexivity.
Qed.

Theorem elimination_preserves_interpretation (FE : FunExt) G a (p : gtm S P G a) :
  forall rho, ceval (eliminate p) rho = geval B lex free p rho.
Proof.
  induction p; intro rho; cbn [eliminate]; try reflexivity.
  - change ((fun x => ceval (eliminate p) (value_extend rho x)) =
      (fun x => geval B lex free p (value_extend rho x))).
    apply FE; intro x; apply IHp.
  - cbn; rewrite IHp1, IHp2; reflexivity.
  - cbn; rewrite IHp1, IHp2; reflexivity.
  - rewrite ceval_neg, IHp; reflexivity.
  - rewrite ceval_and by exact FE; rewrite IHp1, IHp2; reflexivity.
  - rewrite ceval_or by exact FE; rewrite IHp1, IHp2; reflexivity.
  - rewrite ceval_imp by exact FE; rewrite IHp1, IHp2; reflexivity.
  - rewrite ceval_iff, IHp1, IHp2; reflexivity.
  - rewrite ceval_all by exact FE; apply truth_congr;
      split; intros H x; [rewrite <- IHp | rewrite IHp]; apply H.
  - rewrite ceval_ex by exact FE; apply truth_congr;
      split; intros [x H]; exists x; [rewrite <- IHp | rewrite IHp]; exact H.
Qed.
Theorem inclusion_preserves_interpretation (FE : FunExt) G a (p : ctm S P G a) rho :
  ceval p rho = geval B lex free (include_core p) rho.
Proof. rewrite <- (eliminate_core_identity p) at 1.
  apply elimination_preserves_interpretation; exact FE. Qed.
End Evaluation.
