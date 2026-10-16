(* Interpretation-preserving embedding of the already checked extensional
   Boolean core. This is not an IL translation or a conservativity theorem. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax Models Calculus BooleanModels
  Ty2Syntax Ty2Models Ty2Calculus.
Import ListNotations.
Set Implicit Arguments.

Fixpoint embed_type (a : ty) : wty :=
  match a with entity => we | truth => wt | arrow a b => warr (embed_type a) (embed_type b) end.
Fixpoint embed_var {G a} (v : var G a) : wvar (map embed_type G) (embed_type a) :=
  match v in var G' a' return wvar (map embed_type G') (embed_type a') with
  | vz => wz | vs v => wvs (embed_var v)
  end.

Section SyntaxEmbedding.
Context {symbol : ty -> Type} {target : wty -> Type}.
Variable constants : forall a, symbol a -> target (embed_type a).
Fixpoint embed_term {G a} (t : tm symbol G a) : wtm target (map embed_type G) (embed_type a) :=
  match t in tm _ G' a' return wtm target (map embed_type G') (embed_type a') with
  | Var v => WVar (embed_var v)
  | Const c => WConst (@constants _ c)
  | Lam t => WLam (embed_term t)
  | App f x => WApp (embed_term f) (embed_term x)
  | Imp p q => WImp (embed_term p) (embed_term q)
  | All p => WAll (embed_term p)
  end.
End SyntaxEmbedding.

(* Explicit isomorphisms avoid identifying recursive type interpreters by
   unproved casts or equality-proof irrelevance. *)
Fixpoint value_maps (E W : Type) (a : ty) :
  ((bdomain E a -> wdomain E W (embed_type a)) *
   (wdomain E W (embed_type a) -> bdomain E a))%type :=
  match a with
  | entity => (fun x => x, fun x => x)
  | truth => (fun x => x, fun x => x)
  | arrow a b =>
      let A := value_maps E W a in let B := value_maps E W b in
      (fun f x => fst B (f (snd A x)), fun g x => snd B (g (fst A x)))
  end.
Definition lift_value {E W} a := fst (value_maps E W a).
Definition lower_value {E W} a := snd (value_maps E W a).

Lemma value_round_trips (FE : FunExt) : forall E W a,
  (forall x : bdomain E a, lower_value a (lift_value (W:=W) a x) = x) /\
  (forall y : wdomain E W (embed_type a), lift_value a (lower_value a y) = y).
Proof.
  intros E W a; induction a; cbn; split; intro f; try reflexivity.
  - apply FE; intro x; cbn.
    unfold lower_value, lift_value in IHa1, IHa2.
    rewrite (proj1 IHa1 x), (proj1 IHa2); reflexivity.
  - apply FE; intro x; cbn.
    unfold lower_value, lift_value in IHa1, IHa2.
    rewrite (proj2 IHa1 x), (proj2 IHa2); reflexivity.
Qed.

Lemma lower_lift (FE : FunExt) : forall E W a (x : bdomain E a),
  lower_value a (lift_value (W:=W) a x) = x.
Proof. intros; apply (proj1 (value_round_trips FE E W a)). Qed.
Lemma lift_lower (FE : FunExt) : forall E W a (x : wdomain E W (embed_type a)),
  lift_value a (lower_value a x) = x.
Proof. intros; apply (proj2 (value_round_trips FE E W a)). Qed.

Section ModelEmbedding.
Context {symbol : ty -> Type} {target : wty -> Type}.
Variable constants : forall a, symbol a -> target (embed_type a).
Variable FE : FunExt.
Variable M : wmodel target.

Definition reduct_quantifiers : BooleanQuantifiers (windividuals M).
Proof.
  refine {| bforall := fun a p => wforall (wquantifiers M) (embed_type a)
              (fun x => p (lower_value a x)) |}.
  intros a p; rewrite wforall_spec; split.
  - intros H x; specialize (H (lift_value a x)); rewrite (lower_lift FE) in H; exact H.
  - intros H x; apply H.
Defined.

Definition core_reduct : bmodel symbol :=
  {| bindividuals := windividuals M;
     bindividuals_nonempty := @windividuals_nonempty target M;
     blexical := fun a c => lower_value a (wlexical M _ (@constants a c));
     bquantifiers := reduct_quantifiers |}.

Theorem embedding_interpretation : forall G a (t : tm symbol G a)
  (rho : wenv M (map embed_type G)) (sigma : benv core_reduct G),
  (forall b v, rho _ (embed_var v) = lift_value b (sigma b v)) ->
  weval M (embed_term constants t) rho = lift_value a (beval core_reduct t sigma).
Proof.
  intros G a t; induction t; intros rho sigma H; cbn.
  - apply H.
  - symmetry; apply lift_lower; exact FE.
  - apply FE; intro x; apply IHt; apply var_cons_cases; cbn.
    + symmetry; apply lift_lower; exact FE.
    + intros; apply H.
  - etransitivity.
    + exact (f_equal2 (fun f x => f x) (IHt1 rho sigma H) (IHt2 rho sigma H)).
    + change (lift_value (W:=worlds M) b (beval core_reduct t1 sigma
        (lower_value a (lift_value (W:=worlds M) a (beval core_reduct t2 sigma)))) =
        lift_value (W:=worlds M) b (beval core_reduct t1 sigma (beval core_reduct t2 sigma))).
      rewrite (lower_lift FE); reflexivity.
  - exact (f_equal2 bimp (IHt1 rho sigma H) (IHt2 rho sigma H)).
  - f_equal; apply FE; intro x; apply IHt; apply var_cons_cases; cbn.
    + symmetry; apply lift_lower; exact FE.
    + intros; apply H.
Qed.

Definition project_env {G} (rho : wenv M (map embed_type G)) : benv core_reduct G :=
  fun a v => lower_value a (rho _ (embed_var v)).

Theorem embedded_formula_interpretation : forall G (p : tm symbol G truth)
  (rho : wenv M (map embed_type G)),
  weval M (embed_term constants p) rho = beval core_reduct p (project_env rho).
Proof.
  intros G p rho.
  refine (@embedding_interpretation G truth p rho (project_env rho) _).
  intros; symmetry; apply lift_lower; exact FE.
Qed.

End ModelEmbedding.

(* This transports semantic consequences of existing derivations. It does
   not claim a syntactic derivation translation or the reverse direction. *)
Theorem core_derivation_world_sound (FE : FunExt) : forall symbol target
  (constants : forall a, symbol a -> target (embed_type a)) L G H (p : tm symbol G truth),
  derives L H p ->
  wconsequence (map (embed_term constants) H) (embed_term constants p).
Proof.
  intros symbol target constants L G H p D M rho Sat.
  rewrite (embedded_formula_interpretation constants FE (M:=M) p).
  apply (derivation_boolean_sound FE D).
  intros q Hin; rewrite <- (embedded_formula_interpretation constants FE (M:=M) q).
  apply Sat; apply in_map_iff; exists q; split; [reflexivity | exact Hin].
Qed.
