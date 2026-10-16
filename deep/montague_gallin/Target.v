(* Explicit-index Ty2 presentation. Gallin pp. 58-60 gives lambda,
   application and equality as primitives; Boolean connectives and
   quantifiers are retained as additional constructors with their standard
   semantics. Elimination into Gallin's minimal syntax is not proved here.
   No modal or tense constructor occurs in this target language. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Models.
From MontagueGallin Require Import Types.
Import ListNotations.
Set Implicit Arguments.

Inductive gvar : list gty -> gty -> Type :=
| gz : forall G a, gvar (a :: G) a
| gvs : forall G a b, gvar G a -> gvar (b :: G) a.
Arguments gz {G a}.
Arguments gvs {G a b} _.
Lemma gvar_cases G a (P : forall b, gvar (a :: G) b -> Prop) :
  P a gz -> (forall b v, P b (gvs v)) -> forall b v, P b v.
Proof.
  intros Hz Hs b v; revert P Hz Hs.
  exact (match v as w in gvar D c return
    match D as D0 return gvar D0 c -> Prop with
    | [] => fun _ => True
    | d :: D0 => fun w0 => forall P : forall b, gvar (d :: D0) b -> Prop,
        P d gz -> (forall b v, P b (gvs v)) -> P c w0
    end w with
  | @gz _ _ => fun P Hz _ => Hz
  | @gvs _ _ _ w0 => fun P _ Hs => Hs _ w0
  end).
Qed.

Section Syntax.
Context (symbol parameter : gty -> Type).
Inductive gtm : list gty -> gty -> Type :=
| GVar : forall G a, gvar G a -> gtm G a
| GFree : forall G a, parameter a -> gtm G a
| GCon : forall G a, symbol a -> gtm G a
| GLam : forall G a b, gtm (a :: G) b -> gtm G (garr a b)
| GApp : forall G a b, gtm G (garr a b) -> gtm G a -> gtm G b
| GEq : forall G a, gtm G a -> gtm G a -> gtm G gt
| GNeg : forall G, gtm G gt -> gtm G gt
| GAnd : forall G, gtm G gt -> gtm G gt -> gtm G gt
| GOr : forall G, gtm G gt -> gtm G gt -> gtm G gt
| GImp : forall G, gtm G gt -> gtm G gt -> gtm G gt
| GIff : forall G, gtm G gt -> gtm G gt -> gtm G gt
| GAll : forall G a, gtm (a :: G) gt -> gtm G gt
| GEx : forall G a, gtm (a :: G) gt -> gtm G gt.
End Syntax.
Arguments GVar {symbol parameter G a} _.
Arguments GFree {symbol parameter G a} _.
Arguments GCon {symbol parameter G a} _.
Arguments GLam {symbol parameter G a b} _.
Arguments GApp {symbol parameter G a b} _ _.
Arguments GEq {symbol parameter G a} _ _.
Arguments GNeg {symbol parameter G} _.
Arguments GAnd {symbol parameter G} _ _.
Arguments GOr {symbol parameter G} _ _.
Arguments GImp {symbol parameter G} _ _.
Arguments GIff {symbol parameter G} _ _.
Arguments GAll {symbol parameter G a} _.
Arguments GEx {symbol parameter G a} _.

Definition gren G D := forall a, gvar G a -> gvar D a.
Definition glift {G D a} (r : gren G D) : gren (a :: G) (a :: D) :=
  fun b v => match v in gvar G' b' return
    match G' with [] => unit | c :: G0 => gren G0 D -> gvar (c :: D) b' end with
  | @gz _ _ => fun _ => gz
  | @gvs _ _ _ w => fun r0 => gvs (r0 _ w)
  end r.
Fixpoint grename {S P G a} (u : gtm S P G a) : forall D, gren G D -> gtm S P D a :=
  match u in gtm _ _ G' a' return forall D, gren G' D -> gtm S P D a' with
  | GVar v => fun D r => GVar (r _ v)
  | GFree n => fun D _ => GFree n | GCon n => fun D _ => GCon n
  | GLam p => fun D r => GLam (grename p (glift r))
  | GApp p q => fun D r => GApp (grename p r) (grename q r)
  | GEq p q => fun D r => GEq (grename p r) (grename q r)
  | GNeg p => fun D r => GNeg (grename p r)
  | GAnd p q => fun D r => GAnd (grename p r) (grename q r)
  | GOr p q => fun D r => GOr (grename p r) (grename q r)
  | GImp p q => fun D r => GImp (grename p r) (grename q r)
  | GIff p q => fun D r => GIff (grename p r) (grename q r)
  | GAll p => fun D r => GAll (grename p (glift r))
  | GEx p => fun D r => GEx (grename p (glift r))
  end.
Definition gweaken {S P G a b} (u : gtm S P G b) : gtm S P (a :: G) b :=
  grename u (fun _ v => gvs v).

Definition value_env E I G := forall a, gvar G a -> value_domain E I a.
Definition value_extend {E I G a} (rho : value_env E I G) (x : value_domain E I a)
  : value_env E I (a :: G) :=
  fun b v => match v in gvar G' b' return
    match G' with [] => unit
    | c :: G0 => value_env E I G0 -> value_domain E I c -> value_domain E I b' end with
  | @gz _ _ => fun _ x0 => x0
  | @gvs _ _ _ w => fun r _ => r _ w
  end rho x.
Definition value_empty E I : value_env E I [] := fun a v =>
  match v in gvar G b return match G with [] => value_domain E I b | _ => unit end with
  | gz => tt | gvs _ => tt end.
(* Compatibility names for checkpoint 1. *)
Definition genv F := value_env (entity F) (index F).
Definition gextend {F G a} := @value_extend (entity F) (index F) G a.
Definition gempty F := value_empty (entity F) (index F).

Section Evaluation.
Context {S P : gty -> Type} {E I : Type}.
Variable B : BooleanTruth.
Variable lex : forall a, S a -> value_domain E I a.
Variable free : forall a, P a -> value_domain E I a.
Fixpoint geval {G a} (u : gtm S P G a) (rho : value_env E I G) : value_domain E I a :=
  match u in gtm _ _ G' a' return value_env E I G' -> value_domain E I a' with
  | GVar v => fun r => r _ v
  | GFree n => fun _ => @free _ n | GCon n => fun _ => @lex _ n
  | GLam p => fun r x => geval p (value_extend r x)
  | GApp p q => fun r => geval p r (geval q r)
  | GEq p q => fun r => truth B (geval p r = geval q r)
  | GNeg p => fun r => negb (geval p r)
  | GAnd p q => fun r => andb (geval p r) (geval q r)
  | GOr p q => fun r => orb (geval p r) (geval q r)
  | GImp p q => fun r => orb (negb (geval p r)) (geval q r)
  | GIff p q => fun r => Bool.eqb (geval p r) (geval q r)
  | GAll p => fun r => truth B (forall x, geval p (value_extend r x) = true)
  | GEx p => fun r => truth B (exists x, geval p (value_extend r x) = true)
  end rho.

Theorem geval_rename (FE : FunExt) G a (p : gtm S P G a) :
  forall D (r : gren G D) rho tau,
  (forall b v, tau _ (r b v) = rho b v) ->
  geval (grename p r) tau = geval p rho.
Proof.
  induction p; intros D r rho tau H; cbn; try reflexivity; try apply H;
    try (rewrite IHp1 with (rho := rho), IHp2 with (rho := rho); auto; fail);
    try (rewrite IHp with (rho := rho); auto; fail).
  - apply FE; intro x; apply IHp; apply gvar_cases; cbn; auto.
  - apply truth_congr.
    assert (K : forall x, geval (grename p (glift r)) (value_extend tau x) =
      geval p (value_extend rho x)).
    { intro x; apply IHp; apply gvar_cases; cbn; auto. }
    split; intros Q x; [rewrite <- K | rewrite K]; apply Q.
  - apply truth_congr.
    assert (K : forall x, geval (grename p (glift r)) (value_extend tau x) =
      geval p (value_extend rho x)).
    { intro x; apply IHp; apply gvar_cases; cbn; auto. }
    split; intros [x Q]; exists x; [rewrite <- K | rewrite K]; exact Q.
Qed.
Corollary geval_weaken (FE : FunExt) G a b (p : gtm S P G b) rho x :
  geval (@gweaken S P G a b p) (value_extend rho x) = geval p rho.
Proof. apply geval_rename; [exact FE | intros; reflexivity]. Qed.
End Evaluation.

(* Interpretation is insensitive to pointwise-equal symbol assignments.
   This applies to every target term, not only translated source terms. *)
Theorem geval_extensional {S P E I} (B : BooleanTruth) (FE : FunExt)
  (lex1 lex2 : forall a, S a -> value_domain E I a)
  (free1 free2 : forall a, P a -> value_domain E I a)
  (HL : forall a c, lex1 a c = lex2 a c)
  (HF : forall a v, free1 a v = free2 a v) G a (p : gtm S P G a) :
  forall rho, geval B lex1 free1 p rho = geval B lex2 free2 p rho.
Proof.
  induction p; intro rho; cbn; try reflexivity; try apply HL; try apply HF;
    try (rewrite IHp1, IHp2; reflexivity); try (rewrite IHp; reflexivity).
  - apply FE; intro x; apply IHp.
  - apply truth_congr; split; intros H x;
      [rewrite <- IHp | rewrite IHp]; apply H.
  - apply truth_congr; split; intros [x H]; exists x;
      [rewrite <- IHp | rewrite IHp]; exact H.
Qed.
