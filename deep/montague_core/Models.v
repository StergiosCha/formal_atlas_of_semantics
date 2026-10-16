(* A declared Prop-valued interpretation of C. This is not yet an adequacy
   theorem for two-valued set-theoretic or Henkin models of Montague/Ty2.
   Function extensionality is an explicit theorem premise, never imported. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax.
Import ListNotations.
Set Implicit Arguments.

Fixpoint domain (E : Type) (a : ty) : Type :=
  match a with
  | entity => E
  | truth => Prop
  | arrow a b => domain E a -> domain E b
  end.

Definition FunExt : Prop := forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Definition ClassicalTruth : Prop := forall P : Prop, P \/ ~ P.

Section Interpretation.
Variable symbol : ty -> Type.

Record model : Type := {
  individuals : Type;
  individuals_nonempty : inhabited individuals;
  lexical : forall a, symbol a -> domain individuals a
}.

Variable M : model.
Definition env G := forall a, var G a -> domain (individuals M) a.

Definition extend {G a} (rho : env G) (x : domain (individuals M) a) : env (a :: G) :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => env G0 -> domain (individuals M) c -> domain (individuals M) b'
    end with
  | @vz _ _ => fun _ x0 => x0
  | @vs _ _ _ w => fun rho0 _ => rho0 _ w
  end rho x.

Fixpoint eval {G a} (t : tm symbol G a) : env G -> domain (individuals M) a :=
  match t in tm _ G' a' return env G' -> domain (individuals M) a' with
  | Var v => fun rho => rho _ v
  | Const c => fun _ => lexical M c
  | Lam u => fun rho x => eval u (extend rho x)
  | App f x => fun rho => eval f rho (eval x rho)
  | Imp p q => fun rho => eval p rho -> eval q rho
  | All p => fun rho => forall x, eval p (extend rho x)
  end.

Lemma eval_rename (FE : FunExt) : forall G a (t : tm symbol G a)
  D (r : ren G D) (rho : env D) (sigma : env G),
  (forall b v, sigma b v = rho b (r b v)) ->
  eval (rename t r) rho = eval t sigma.
Proof.
  intros G a t; induction t; intros D r rho sigma H; cbn.
  - symmetry; apply H.
  - reflexivity.
  - apply FE; intro x. apply IHt. apply var_cons_cases;
      cbn; [reflexivity | intros; apply H].
  - rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H). reflexivity.
  - rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H). reflexivity.
  - assert (E : (fun x => eval (rename t (lift_ren r)) (extend rho x)) =
                (fun x => eval t (extend sigma x))).
    { apply FE; intro x. apply IHt. apply var_cons_cases;
        cbn; [reflexivity | intros; apply H]. }
    change ((forall x, (fun x => eval (rename t (lift_ren r)) (extend rho x)) x) =
            (forall x, (fun x => eval t (extend sigma x)) x)).
    rewrite E; reflexivity.
Qed.

Lemma eval_weaken (FE : FunExt) : forall G a b (t : tm symbol G b)
  (rho : env G) (x : domain (individuals M) a),
  eval (weaken t) (extend rho x) = eval t rho.
Proof. intros; apply eval_rename; [exact FE | intros; reflexivity]. Qed.

Lemma eval_substitution (FE : FunExt) : forall G a (t : tm symbol G a)
  D (s : sub symbol G D) (rho : env D) (sigma : env G),
  (forall b v, eval (s b v) rho = sigma b v) ->
  eval (subst t s) rho = eval t sigma.
Proof.
  intros G a t; induction t; intros D theta rho sigma H; cbn.
  - apply H.
  - reflexivity.
  - apply FE; intro x. apply IHt. apply var_cons_cases; cbn; [reflexivity |].
    intros; rewrite (eval_weaken FE); apply H.
  - rewrite (IHt1 _ theta rho sigma H), (IHt2 _ theta rho sigma H). reflexivity.
  - rewrite (IHt1 _ theta rho sigma H), (IHt2 _ theta rho sigma H). reflexivity.
  - assert (E : (fun x => eval (subst t (lift_sub theta)) (extend rho x)) =
                (fun x => eval t (extend sigma x))).
    { apply FE; intro x. apply IHt. apply var_cons_cases; cbn; [reflexivity |].
      intros; rewrite (eval_weaken FE); apply H. }
    change ((forall x, (fun x => eval (subst t (lift_sub theta)) (extend rho x)) x) =
            (forall x, (fun x => eval t (extend sigma x)) x)).
    rewrite E; reflexivity.
Qed.

Lemma eval_instantiate (FE : FunExt) : forall G a b (u : tm symbol G a)
  (t : tm symbol (a :: G) b) rho,
  eval (instantiate u t) rho = eval t (extend rho (eval u rho)).
Proof.
  intros. apply eval_substitution; [exact FE |].
  apply var_cons_cases; intros; reflexivity.
Qed.

Theorem beta_sound (FE : FunExt) : forall G a (t u : tm symbol G a),
  beta t u -> forall rho, eval t rho = eval u rho.
Proof.
  intros G a t u H; induction H; intro rho; cbn.
  - reflexivity.
  - symmetry; apply IHbeta.
  - transitivity (eval u rho); [apply IHbeta1 | apply IHbeta2].
  - symmetry; apply eval_instantiate; exact FE.
  - apply FE; intro x; apply IHbeta.
  - rewrite IHbeta1, IHbeta2; reflexivity.
  - rewrite IHbeta1, IHbeta2; reflexivity.
  - assert (E : (fun x => eval p (extend rho x)) =
                (fun x => eval q (extend rho x))).
    { apply FE; intro x; apply IHbeta. }
    change ((forall x, (fun x => eval p (extend rho x)) x) =
            (forall x, (fun x => eval q (extend rho x)) x)).
    rewrite E; reflexivity.
Qed.

Lemma falsity_meaning : forall G (rho : env G), eval falsity rho <-> False.
Proof. intros; cbn; split; [intro H; exact (H False) | contradiction]. Qed.

Lemma neg_meaning : forall G (p : tm symbol G truth) rho,
  eval (neg p) rho <-> ~ eval p rho.
Proof.
  intros; unfold neg; cbn; split.
  - intros H Hp; exact (H Hp False).
  - intros H Hp; exfalso; exact (H Hp).
Qed.

Lemma conj_meaning (FE : FunExt) : forall G (p q : tm symbol G truth) rho,
  eval (conj p q) rho <-> eval p rho /\ eval q rho.
Proof.
  intros; unfold conj; cbn -[weaken].
  split.
  - intro H; specialize (H (eval p rho /\ eval q rho)).
    rewrite (eval_weaken FE), (eval_weaken FE) in H. apply H; auto.
  - intros [Hp Hq] X H. apply H; rewrite (eval_weaken FE); assumption.
Qed.

Lemma disj_meaning (FE : FunExt) : forall G (p q : tm symbol G truth) rho,
  eval (disj p q) rho <-> eval p rho \/ eval q rho.
Proof.
  intros; unfold disj; cbn -[weaken].
  split.
  - intro H; specialize (H (eval p rho \/ eval q rho)).
    rewrite (eval_weaken FE), (eval_weaken FE) in H. apply H; auto.
  - intros [Hp | Hq] X H1 H2.
    + apply H1; rewrite (eval_weaken FE); exact Hp.
    + apply H2; rewrite (eval_weaken FE); exact Hq.
Qed.

Lemma exists_meaning (FE : FunExt) : forall G a (p : tm symbol (a :: G) truth) rho,
  eval (exists_ p) rho <-> exists x, eval p (extend rho x).
Proof.
  intros G a p rho.
  assert (E : forall (X : Prop) (x : domain (individuals M) a),
    eval (rename p (lift_ren (fun _ v => vs v))) (extend (@extend G truth rho X) x) =
    eval p (extend rho x)).
  { intros; apply eval_rename; [exact FE |].
    apply var_cons_cases; intros; reflexivity. }
  unfold exists_; cbn -[rename lift_ren]. split.
  - intro H; specialize (H (exists x, eval p (extend rho x))).
    apply H; intros x Hx; exists x.
    rewrite <- (E (exists x, eval p (extend rho x)) x); exact Hx.
  - intros [x Hx] X H; apply (H x); rewrite (E X x); exact Hx.
Qed.

Definition satisfies {G} (rho : env G) (H : list (tm symbol G truth)) :=
  forall p, In p H -> eval p rho.

End Interpretation.

Arguments eval {symbol} M {G a} _ _.
Arguments satisfies {symbol} M {G} _ _.

(* Unlike the old fixed-interpretation logically_true, consequence explicitly
   ranges over every model and assignment of this DECLARED interpretation. *)
Definition consequence {symbol G} (H : list (tm symbol G truth)) (p : tm symbol G truth) :=
  forall (M : model symbol) (rho : env M G), satisfies M rho H -> eval M p rho.
