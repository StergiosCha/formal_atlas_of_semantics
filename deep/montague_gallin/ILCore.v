(* Gallin (1975), pp. 11-16: primitive IL syntax and modally closed terms.
   The evaluator is the already checked untensed interpretation, via an
   explicit inclusion. Logical notation below expands into primitive terms. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Minimal Untensed.
Import ListNotations.
Set Implicit Arguments.

Inductive ltm : list ty -> ty -> Type :=
| LVar : forall G a, var G a -> ltm G a
| LFree : forall G a, nat -> ltm G a
| LCon : forall G a, nat -> ltm G a
| LLam : forall G a b, ltm (a :: G) b -> ltm G (arr a b)
| LApp : forall G a b, ltm G (arr a b) -> ltm G a -> ltm G b
| LEq : forall G a, ltm G a -> ltm G a -> ltm G t
| LUp : forall G a, ltm G a -> ltm G (intens a)
| LDown : forall G a, ltm G (intens a) -> ltm G a.
Arguments LVar {G a} _.
Arguments LFree {G a} _.
Arguments LCon {G a} _.
Arguments LLam {G a b} _.
Arguments LApp {G a b} _ _.
Arguments LEq {G a} _ _.
Arguments LUp {G a} _.
Arguments LDown {G a} _.

Fixpoint include_il {G a} (p : ltm G a) : itm G a :=
  match p with
  | LVar v => IVar v | LFree n => IFree n | LCon n => ICon n
  | LLam p => ILam (include_il p) | LApp p q => IApp (include_il p) (include_il q)
  | LEq p q => IEq (include_il p) (include_il q)
  | LUp p => IUp (include_il p) | LDown p => IDown (include_il p)
  end.
Definition lval M G a (p : ltm G a) rho sigma i := ieval M (include_il p) rho sigma i.
Arguments lval M {G a} p rho sigma i.

Definition lren G D := forall a, var G a -> var D a.
Definition lren_lift {G D a} (r : lren G D) : lren (a :: G) (a :: D) :=
  fun b v => match v in var G' b' return
    match G' with [] => unit | c :: G0 => lren G0 D -> var (c :: D) b' end with
  | @vz _ _ => fun _ => vz | @vs _ _ _ w => fun r0 => vs (r0 _ w)
  end r.
Fixpoint lrename {G a} (p : ltm G a) : forall D, lren G D -> ltm D a :=
  match p in ltm G' a' return forall D, lren G' D -> ltm D a' with
  | LVar v => fun D r => LVar (r _ v)
  | LFree n => fun D _ => LFree n | LCon n => fun D _ => LCon n
  | LLam p => fun D r => LLam (lrename p (lren_lift r))
  | LApp p q => fun D r => LApp (lrename p r) (lrename q r)
  | LEq p q => fun D r => LEq (lrename p r) (lrename q r)
  | LUp p => fun D r => LUp (lrename p r)
  | LDown p => fun D r => LDown (lrename p r)
  end.
Definition lweaken {G a b} (p : ltm G b) : ltm (a :: G) b :=
  lrename p (fun _ v => vs v).
(* The exchange in AS4.5: y,x,G becomes x,y,G, with no capture. *)
Definition lswap {G a b} : lren (b :: a :: G) (a :: b :: G) :=
  fun c v => match v in var G' c' return
    match G' with [] => unit | d :: D =>
      lren D (a :: b :: G) -> var (a :: b :: G) d -> var (a :: b :: G) c' end with
  | @vz _ _ => fun _ z => z
  | @vs _ _ _ w => fun r _ => r _ w
  end (lren_lift (fun _ v => vs v)) (vs vz).

Definition ltrue {G} : ltm G t := LEq (@LLam G t t (LVar vz)) (LLam (LVar vz)).
Definition lfalse {G} : ltm G t := LEq (@LLam G t t (LVar vz)) (LLam ltrue).
Definition lneg {G} (p : ltm G t) := LEq lfalse p.
Definition land {G} (p q : ltm G t) : ltm G t :=
  LEq (@LLam G (arr t t) t (LEq (LApp (LVar vz) (lweaken p)) (lweaken q)))
    (LLam (LApp (LVar vz) ltrue)).
Definition limp {G} (p q : ltm G t) := LEq (land p q) p.
Definition lall {G a} (p : ltm (a :: G) t) : ltm G t := LEq (LLam p) (LLam ltrue).
Definition lbox {G} (p : ltm G t) := LEq (LUp p) (LUp ltrue).

(* Exactly the generating clauses of MC on p. 14. In particular, neither
   an arbitrary constant nor Down of a modally closed term is admitted. *)
Inductive ModallyClosed : forall G a, ltm G a -> Prop :=
| MCVar : forall G a (v : var G a), ModallyClosed (LVar v)
| MCFree : forall G a n, ModallyClosed (@LFree G a n)
| MCUp : forall G a (p : ltm G a), ModallyClosed (LUp p)
| MCApp : forall G a b (p : ltm G (arr a b)) q,
    ModallyClosed p -> ModallyClosed q -> ModallyClosed (LApp p q)
| MCEq : forall G a (p q : ltm G a),
    ModallyClosed p -> ModallyClosed q -> ModallyClosed (LEq p q)
| MCLam : forall G a b (p : ltm (a :: G) b), ModallyClosed p -> ModallyClosed (LLam p).

Section Semantics.
Variable M : il_model.
Variable sigma : il_free_env M.
Local Notation B := (il_truth M).
Local Notation FE := (il_extensionality M).
Local Notation V := (fun G a (p : ltm G a) rho i => lval M p rho sigma i).

Theorem lval_rename G a (p : ltm G a) : forall D (r : lren G D) rho tau i,
  (forall b v, tau _ (r b v) = rho b v) ->
  lval M (lrename p r) tau sigma i = lval M p rho sigma i.
Proof.
  unfold lval; induction p; intros D r rho tau i H; cbn [include_il lrename ieval];
    try reflexivity; try apply H;
    try (rewrite IHp1 with (rho := rho), IHp2 with (rho := rho); auto; fail).
  - apply FE; intro x; apply IHp; apply var_cases; cbn; auto.
  - apply FE; intro j; apply IHp; exact H.
  - rewrite IHp with (rho := rho); auto.
Qed.
Corollary lval_weaken G a b (p : ltm G b) rho x i :
  lval M (@lweaken G a b p) (il_extend rho x) sigma i = lval M p rho sigma i.
Proof. apply lval_rename; intros; reflexivity. Qed.
Lemma lval_swap G a b c (p : ltm (b :: a :: G) c) rho x y i :
  lval M (lrename p lswap) (il_extend (il_extend rho y) x) sigma i =
  lval M p (il_extend (il_extend rho x) y) sigma i.
Proof. apply lval_rename; apply var_cases; cbn; [reflexivity |].
  intros d v; revert d v; apply var_cases; cbn; reflexivity. Qed.

Theorem modally_closed_is_index_independent G a (p : ltm G a) (H : ModallyClosed p) :
  forall rho i j, lval M p rho sigma i = lval M p rho sigma j.
Proof.
  unfold lval; induction H; intros rho i j; cbn [include_il ieval]; try reflexivity;
    try (rewrite IHModallyClosed1 with (j := j), IHModallyClosed2 with (j := j); reflexivity).
  apply FE; intro x; apply IHModallyClosed.
Qed.
Lemma lval_true G (rho : il_env M G) i : lval M ltrue rho sigma i = true.
Proof. apply (proj2 (truth_spec B _)); reflexivity. Qed.
Lemma lval_false G (rho : il_env M G) i : lval M lfalse rho sigma i = false.
Proof.
  change (truth B ((fun x : bool => x) = (fun _ : bool => lval M ltrue rho sigma i)) = false).
  rewrite lval_true; destruct (truth B _) eqn:H; auto.
  apply (proj1 (truth_spec B _)) in H; apply (f_equal (fun f => f false)) in H; discriminate.
Qed.
Lemma lval_and G (p q : ltm G t) rho i :
  lval M (land p q) rho sigma i = andb (lval M p rho sigma i) (lval M q rho sigma i).
Proof.
  change (truth B ((fun f : bool -> bool =>
    truth B (f (lval M (lweaken p) (@il_extend M G (arr t t) rho f) sigma i) =
      lval M (lweaken q) (@il_extend M G (arr t t) rho f) sigma i)) =
    (fun f : bool -> bool => f (lval M ltrue (@il_extend M G (arr t t) rho f) sigma i))) =
    andb (lval M p rho sigma i) (lval M q rho sigma i)).
  assert (L : (fun f : bool -> bool =>
    truth B (f (lval M (lweaken p) (@il_extend M G (arr t t) rho f) sigma i) =
      lval M (lweaken q) (@il_extend M G (arr t t) rho f) sigma i)) =
    (fun f => truth B (f (lval M p rho sigma i) = lval M q rho sigma i))).
  { apply FE; intro f; rewrite !lval_weaken; reflexivity. }
  assert (R : (fun f : bool -> bool => f (lval M ltrue (@il_extend M G (arr t t) rho f) sigma i)) =
    (fun f => f true)).
  { apply FE; intro f; rewrite lval_true; reflexivity. }
  rewrite L, R; apply gallin_conjunction; exact FE.
Qed.
Lemma lval_imp G (p q : ltm G t) rho i :
  lval M (limp p q) rho sigma i = orb (negb (lval M p rho sigma i)) (lval M q rho sigma i).
Proof.
  change (truth B (lval M (land p q) rho sigma i = lval M p rho sigma i) =
    orb (negb (lval M p rho sigma i)) (lval M q rho sigma i)).
  rewrite lval_and, boolean_equality; destruct (lval M p rho sigma i), (lval M q rho sigma i); reflexivity.
Qed.
Lemma lval_all G a (p : ltm (a :: G) t) rho i :
  lval M (lall p) rho sigma i = truth B (forall x, lval M p (il_extend rho x) sigma i = true).
Proof.
  change (truth B ((fun x => lval M p (il_extend rho x) sigma i) =
    (fun x => lval M ltrue (il_extend rho x) sigma i)) =
    truth B (forall x, lval M p (il_extend rho x) sigma i = true)).
  apply truth_congr; split.
  - intros H x; apply (f_equal (fun f => f x)) in H; rewrite lval_true in H; exact H.
  - intro H; apply FE; intro x; rewrite lval_true; apply H.
Qed.
Lemma lval_box G (p : ltm G t) rho i :
  lval M (lbox p) rho sigma i = truth B (forall j, lval M p rho sigma j = true).
Proof.
  change (truth B ((fun j => lval M p rho sigma j) = (fun j => lval M ltrue rho sigma j)) =
    truth B (forall j, lval M p rho sigma j = true)).
  apply truth_congr; split.
  - intros H j; apply (f_equal (fun f => f j)) in H; rewrite lval_true in H; exact H.
  - intro H; apply FE; intro j; rewrite lval_true; apply H.
Qed.
End Semantics.
