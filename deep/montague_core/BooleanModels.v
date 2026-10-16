(* Two-valued, full internal function-space interpretation of extensional C.
   Source contract: MODEL_SPEC.md. No claim of external set-model adequacy,
   Henkin completeness, intensionality, or equivalence to the Prop model.
   A total Boolean quantifier must carry its reflection proof. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Syntax Models Calculus.
Import ListNotations.
Set Implicit Arguments.

Fixpoint bdomain (E : Type) (a : ty) : Type :=
  match a with
  | entity => E
  | truth => bool
  | arrow a b => bdomain E a -> bdomain E b
  end.

Record BooleanQuantifiers (E : Type) : Type := {
  bforall : forall a, (bdomain E a -> bool) -> bool;
  bforall_spec : forall a p, bforall a p = true <-> forall x, p x = true
}.
Arguments bforall {E} _ a _.

(* Stronger in formulation than Prop-valued excluded middle: decisions are
   data in Set. This is an optional explicit construction premise, not an
   imported axiom and not a requirement of the finite implementation. *)
Definition ClassicalDecision := forall P : Prop, {P} + {~ P}.

Definition decision_quantifiers (CD : ClassicalDecision) (E : Type) : BooleanQuantifiers E.
Proof.
  refine {| bforall := fun a p => if CD (forall x : bdomain E a, p x = true)
                                then true else false |}.
  intros a p; destruct (CD (forall x : bdomain E a, p x = true));
    intuition discriminate.
Defined.

Lemma classical_decision_implies_excluded_middle : ClassicalDecision -> ClassicalTruth.
Proof. intros CD P; destruct (CD P); [left | right]; assumption. Qed.

Section BooleanInterpretation.
Variable symbol : ty -> Type.

Record bmodel : Type := {
  bindividuals : Type;
  bindividuals_nonempty : inhabited bindividuals;
  blexical : forall a, symbol a -> bdomain bindividuals a;
  bquantifiers : BooleanQuantifiers bindividuals
}.

Variable M : bmodel.
Definition benv G := forall a, var G a -> bdomain (bindividuals M) a.

Definition bextend {G a} (rho : benv G) (x : bdomain (bindividuals M) a) : benv (a :: G) :=
  fun b v => match v in var G' b' return
    match G' with
    | nil => unit
    | c :: G0 => benv G0 -> bdomain (bindividuals M) c -> bdomain (bindividuals M) b'
    end with
  | @vz _ _ => fun _ x0 => x0
  | @vs _ _ _ w => fun rho0 _ => rho0 _ w
  end rho x.

Definition bimp (p q : bool) := orb (negb p) q.

Lemma bimp_spec : forall p q, bimp p q = true <-> (p = true -> q = true).
Proof. destruct p, q; cbn; intuition discriminate. Qed.

Fixpoint beval {G a} (t : tm symbol G a) : benv G -> bdomain (bindividuals M) a :=
  match t in tm _ G' a' return benv G' -> bdomain (bindividuals M) a' with
  | Var v => fun rho => rho _ v
  | Const c => fun _ => blexical M c
  | Lam u => fun rho x => beval u (bextend rho x)
  | App f x => fun rho => beval f rho (beval x rho)
  | Imp p q => fun rho => bimp (beval p rho) (beval q rho)
  | All p => fun rho => bforall (bquantifiers M) _ (fun x => beval p (bextend rho x))
  end.

Lemma beval_rename (FE : FunExt) : forall G a (t : tm symbol G a)
  D (r : ren G D) (rho : benv D) (sigma : benv G),
  (forall b v, sigma b v = rho b (r b v)) ->
  beval (rename t r) rho = beval t sigma.
Proof.
  intros G a t; induction t; intros D r rho sigma H; cbn.
  - symmetry; apply H.
  - reflexivity.
  - apply FE; intro x; apply IHt; apply var_cons_cases;
      cbn; [reflexivity | intros; apply H].
  - rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H); reflexivity.
  - rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H); reflexivity.
  - f_equal; apply FE; intro x; apply IHt; apply var_cons_cases;
      cbn; [reflexivity | intros; apply H].
Qed.

Lemma beval_weaken (FE : FunExt) : forall G a b (t : tm symbol G b)
  (rho : benv G) (x : bdomain (bindividuals M) a),
  beval (weaken t) (bextend rho x) = beval t rho.
Proof. intros; apply beval_rename; [exact FE | intros; reflexivity]. Qed.

Lemma beval_substitution (FE : FunExt) : forall G a (t : tm symbol G a)
  D (s : sub symbol G D) (rho : benv D) (sigma : benv G),
  (forall b v, beval (s b v) rho = sigma b v) ->
  beval (subst t s) rho = beval t sigma.
Proof.
  intros G a t; induction t; intros D theta rho sigma H; cbn.
  - apply H.
  - reflexivity.
  - apply FE; intro x; apply IHt; apply var_cons_cases; cbn; [reflexivity |].
    intros; rewrite (beval_weaken FE); apply H.
  - rewrite (IHt1 _ theta rho sigma H), (IHt2 _ theta rho sigma H); reflexivity.
  - rewrite (IHt1 _ theta rho sigma H), (IHt2 _ theta rho sigma H); reflexivity.
  - f_equal; apply FE; intro x; apply IHt; apply var_cons_cases; cbn; [reflexivity |].
    intros; rewrite (beval_weaken FE); apply H.
Qed.

Lemma beval_instantiate (FE : FunExt) : forall G a b (u : tm symbol G a)
  (t : tm symbol (a :: G) b) rho,
  beval (instantiate u t) rho = beval t (bextend rho (beval u rho)).
Proof.
  intros; apply beval_substitution; [exact FE |].
  apply var_cons_cases; intros; reflexivity.
Qed.

Theorem beta_boolean_sound (FE : FunExt) : forall G a (t u : tm symbol G a),
  beta t u -> forall rho, beval t rho = beval u rho.
Proof.
  intros G a t u B; induction B; intro rho; cbn.
  - reflexivity.
  - symmetry; apply IHB.
  - transitivity (beval u rho); [apply IHB1 | apply IHB2].
  - symmetry; apply beval_instantiate; exact FE.
  - apply FE; intro x; apply IHB.
  - rewrite IHB1, IHB2; reflexivity.
  - rewrite IHB1, IHB2; reflexivity.
  - f_equal; apply FE; intro x; apply IHB.
Qed.

Lemma bfalsity_value : forall G (rho : benv G), beval falsity rho = false.
Proof.
  intros; change (bforall (bquantifiers M) truth (fun x => x) = false).
  pose proof (bforall_spec (bquantifiers M) truth (fun x => x)) as H.
  destruct (bforall (bquantifiers M) truth (fun x => x)) eqn:E; [| reflexivity].
  specialize (proj1 H eq_refl false); discriminate.
Qed.

Lemma bneg_value : forall G (p : tm symbol G truth) rho,
  beval (neg p) rho = negb (beval p rho).
Proof.
  intros; change (bimp (beval p rho) (beval falsity rho) = negb (beval p rho)).
  rewrite bfalsity_value; unfold bimp; apply orb_false_r.
Qed.

Lemma bdouble_negation_value : forall G (p : tm symbol G truth) rho,
  beval (neg (neg p)) rho = beval p rho.
Proof. intros; rewrite !bneg_value; apply negb_involutive. Qed.

Definition bsatisfies {G} (rho : benv G) (H : list (tm symbol G truth)) :=
  forall p, In p H -> beval p rho = true.

(* Both modes are sound in this class. The classical rule is validated by
   finite Boolean case analysis, not an additional Prop-valued LEM premise.
   Quantifier totality/reflection is visible in the supplied model record. *)
Theorem derivation_boolean_sound (FE : FunExt) : forall L G H (p : tm symbol G truth),
  derives L H p -> forall rho, bsatisfies rho H -> beval p rho = true.
Proof.
  intros L G H p D; induction D; intros rho Sat.
  - apply Sat; assumption.
  - cbn; apply bimp_spec; intro Hp; apply IHD.
    intros r [E | Hin]; [subst; exact Hp | apply Sat; exact Hin].
  - pose proof (IHD1 rho Sat) as HI; cbn in HI.
    apply (proj1 (bimp_spec _ _) HI); apply IHD2; exact Sat.
  - cbn; apply bforall_spec; intro x; apply IHD.
    intros r Hin; apply in_map_iff in Hin; destruct Hin as [q [E Hin]]; subst r.
    rewrite (beval_weaken FE); apply Sat; exact Hin.
  - rewrite (beval_instantiate FE).
    pose proof (IHD rho Sat) as HA.
    exact (proj1 (bforall_spec (bquantifiers M) _ _) HA (beval u rho)).
  - rewrite <- (beta_boolean_sound FE H0 rho); apply IHD; exact Sat.
  - rewrite <- bdouble_negation_value; apply IHD; exact Sat.
Qed.

End BooleanInterpretation.

Arguments beval {symbol} M {G a} _ _.
Arguments bsatisfies {symbol} M {G} _ _.

Definition decision_model {symbol E} (CD : ClassicalDecision) (nonempty : inhabited E)
  (lex : forall a, symbol a -> bdomain E a) : bmodel symbol :=
  {| bindividuals := E;
     bindividuals_nonempty := nonempty;
     blexical := lex;
     bquantifiers := decision_quantifiers CD E |}.

Definition bconsequence {symbol G} (H : list (tm symbol G truth)) (p : tm symbol G truth) :=
  forall (M : bmodel symbol) (rho : benv M G), bsatisfies M rho H -> beval M p rho = true.

Theorem classical_boolean_sound (FE : FunExt) : forall symbol G H (p : tm symbol G truth),
  derives classical H p -> bconsequence H p.
Proof. intros symbol G H p D M rho Sat; eapply derivation_boolean_sound; eassumption. Qed.

Theorem constructive_boolean_sound (FE : FunExt) : forall symbol G H (p : tm symbol G truth),
  derives constructive H p -> bconsequence H p.
Proof. intros symbol G H p D M rho Sat; eapply derivation_boolean_sound; eassumption. Qed.

Theorem boolean_countermodel_blocks_derivation (FE : FunExt) :
  forall symbol L G H (p : tm symbol G truth) (M : bmodel symbol) (rho : benv M G),
  bsatisfies M rho H -> beval M p rho = false -> ~ derives L H p.
Proof.
  intros symbol L G H p M rho Sat FalseValue D.
  pose proof (derivation_boolean_sound (M:=M) FE D (rho:=rho) Sat) as TrueValue.
  rewrite FalseValue in TrueValue; discriminate.
Qed.
