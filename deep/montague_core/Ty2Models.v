(* Constant-domain, two-valued full INTERNAL models of the selected Ty2
   fragment. World dependence is explicit in terms/types, not an extra
   evaluation parameter. All assumptions remain arguments or record fields. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Models BooleanModels BooleanFinite Ty2Syntax.
Import ListNotations.
Set Implicit Arguments.

Fixpoint wdomain (E W : Type) (a : wty) : Type :=
  match a with
  | we => E | wt => bool | ws => W
  | warr a b => wdomain E W a -> wdomain E W b
  end.
Record WorldQuantifiers (E W : Type) : Type := {
  wforall : forall a, (wdomain E W a -> bool) -> bool;
  wforall_spec : forall a p, wforall a p = true <-> forall x, p x = true
}.
Arguments wforall {E W} _ a _.

Record wmodel (symbol : wty -> Type) : Type := {
  windividuals : Type;
  worlds : Type;
  windividuals_nonempty : inhabited windividuals;
  worlds_nonempty : inhabited worlds;
  wlexical : forall a, symbol a -> wdomain windividuals worlds a;
  wquantifiers : WorldQuantifiers windividuals worlds
}.
Arguments windividuals {symbol} _.
Arguments worlds {symbol} _.
Arguments wlexical {symbol} _ a _.
Arguments wquantifiers {symbol} _.

Section Interpretation.
Context {symbol} (M : wmodel symbol).
Definition wenv G := forall a, wvar G a -> wdomain (windividuals M) (worlds M) a.
Definition wextend {G a} (rho : wenv G)
  (x : wdomain (windividuals M) (worlds M) a) : wenv (a :: G) :=
  fun b v => match v in wvar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => wenv G0 -> wdomain (windividuals M) (worlds M) c ->
                wdomain (windividuals M) (worlds M) b'
    end with
  | @wz _ _ => fun _ x0 => x0
  | @wvs _ _ _ w => fun rho0 _ => rho0 _ w
  end rho x.

Fixpoint weval {G a} (t : wtm symbol G a) : wenv G -> wdomain (windividuals M) (worlds M) a :=
  match t in wtm _ G' a' return wenv G' -> wdomain (windividuals M) (worlds M) a' with
  | WVar v => fun rho => rho _ v
  | WConst c => fun _ => wlexical M _ c
  | WLam t => fun rho x => weval t (wextend rho x)
  | WApp f x => fun rho => weval f rho (weval x rho)
  | WImp p q => fun rho => bimp (weval p rho) (weval q rho)
  | WAll p => fun rho => wforall (wquantifiers M) _ (fun x => weval p (wextend rho x))
  end.

Lemma weval_rename (FE : FunExt) : forall G a (t : wtm symbol G a)
  D (r : wren G D) (rho : wenv D) (sigma : wenv G),
  (forall b v, sigma b v = rho b (r b v)) ->
  weval (wrename t r) rho = weval t sigma.
Proof.
  intros G a t; induction t; intros D r rho sigma H; cbn.
  - symmetry; apply H.
  - reflexivity.
  - apply FE; intro x; apply IHt; apply wvar_cons_cases;
      cbn; [reflexivity | intros; apply H].
  - rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H); reflexivity.
  - rewrite (IHt1 _ r rho sigma H), (IHt2 _ r rho sigma H); reflexivity.
  - f_equal; apply FE; intro x; apply IHt; apply wvar_cons_cases;
      cbn; [reflexivity | intros; apply H].
Qed.

Lemma weval_weaken (FE : FunExt) : forall G a b (t : wtm symbol G b)
  (rho : wenv G) (x : wdomain (windividuals M) (worlds M) a),
  weval (wweaken t) (wextend rho x) = weval t rho.
Proof. intros; apply weval_rename; [exact FE | intros; reflexivity]. Qed.

Lemma weval_substitution (FE : FunExt) : forall G a (t : wtm symbol G a)
  D (s : wsub symbol G D) (rho : wenv D) (sigma : wenv G),
  (forall b v, weval (s b v) rho = sigma b v) ->
  weval (wsubst t s) rho = weval t sigma.
Proof.
  intros G a t; induction t; intros D theta rho sigma H; cbn.
  - apply H.
  - reflexivity.
  - apply FE; intro x; apply IHt; apply wvar_cons_cases; cbn; [reflexivity |].
    intros; rewrite (weval_weaken FE); apply H.
  - rewrite (IHt1 _ theta rho sigma H), (IHt2 _ theta rho sigma H); reflexivity.
  - rewrite (IHt1 _ theta rho sigma H), (IHt2 _ theta rho sigma H); reflexivity.
  - f_equal; apply FE; intro x; apply IHt; apply wvar_cons_cases; cbn; [reflexivity |].
    intros; rewrite (weval_weaken FE); apply H.
Qed.

Lemma weval_instantiate (FE : FunExt) : forall G a b (u : wtm symbol G a)
  (t : wtm symbol (a :: G) b) rho,
  weval (winstantiate u t) rho = weval t (wextend rho (weval u rho)).
Proof.
  intros; apply weval_substitution; [exact FE |].
  apply wvar_cons_cases; intros; reflexivity.
Qed.

Theorem wbeta_sound (FE : FunExt) : forall G a (t u : wtm symbol G a),
  wbeta t u -> forall rho, weval t rho = weval u rho.
Proof.
  intros G a t u B; induction B; intro rho; cbn.
  - reflexivity.
  - symmetry; apply IHB.
  - transitivity (weval u rho); [apply IHB1 | apply IHB2].
  - symmetry; apply weval_instantiate; exact FE.
  - apply FE; intro x; apply IHB.
  - rewrite IHB1, IHB2; reflexivity.
  - rewrite IHB1, IHB2; reflexivity.
  - f_equal; apply FE; intro x; apply IHB.
Qed.

Lemma wfalsity_value : forall G (rho : wenv G), weval wfalsity rho = false.
Proof.
  intros; change (wforall (wquantifiers M) wt (fun x => x) = false).
  pose proof (wforall_spec (wquantifiers M) wt (fun x => x)) as H.
  destruct (wforall (wquantifiers M) wt (fun x => x)); [| reflexivity].
  specialize (proj1 H eq_refl false); discriminate.
Qed.
Lemma wneg_value : forall G (p : wtm symbol G wt) rho,
  weval (wneg p) rho = negb (weval p rho).
Proof.
  intros; change (bimp (weval p rho) (weval wfalsity rho) = negb (weval p rho)).
  rewrite wfalsity_value; unfold bimp; apply orb_false_r.
Qed.

Theorem necessity_meaning (FE : FunExt) : forall G (p : wtm symbol G (warr ws wt)) rho,
  weval (necessarily p) rho = true <-> forall w, weval p rho w = true.
Proof.
  intros; unfold necessarily; cbn -[wweaken wforall].
  rewrite wforall_spec; split; intros H w.
  - specialize (H w); rewrite (weval_weaken FE) in H; exact H.
  - rewrite (weval_weaken FE); apply H.
Qed.

Theorem intension_application_beta (FE : FunExt) : forall G a
  (t : wtm symbol (ws :: G) a) (w : wtm symbol G ws) rho,
  weval (at_world (WLam t) w) rho = weval (winstantiate w t) rho.
Proof. intros; cbn -[winstantiate]; symmetry; apply weval_instantiate; exact FE. Qed.

End Interpretation.
Arguments weval {symbol} M {G a} _ _.

Fixpoint world_finite_domain {E W} (FE : FunExt) (F : finite E) (V : finite W)
  (a : wty) : finite (wdomain E W a) :=
  match a with
  | we => F | wt => finite_bool | ws => V
  | warr a b => finite_arrow (world_finite_domain FE F V a)
                              (world_finite_domain FE F V b) FE
  end.
Definition world_finite_quantifiers {E W} (FE : FunExt) (F : finite E) (V : finite W)
  : WorldQuantifiers E W :=
  {| wforall := fun a p => forallb p (values (world_finite_domain FE F V a));
     wforall_spec := fun a p => finite_forall_spec (world_finite_domain FE F V a) p |}.
Definition world_finite_model {symbol E W} (FE : FunExt) (F : finite E) (V : finite W)
  (lex : forall a, symbol a -> wdomain E W a) : wmodel symbol :=
  {| windividuals := E; worlds := W;
     windividuals_nonempty := inhabits (default_value F);
     worlds_nonempty := inhabits (default_value V);
     wlexical := lex; wquantifiers := world_finite_quantifiers FE F V |}.

Definition world_decision_quantifiers (CD : ClassicalDecision) (E W : Type)
  : WorldQuantifiers E W.
Proof.
  refine {| wforall := fun a p => if CD (forall x : wdomain E W a, p x = true)
                                then true else false |}.
  intros a p; destruct (CD (forall x : wdomain E W a, p x = true));
    intuition discriminate.
Defined.

Definition world_decision_model {symbol E W} (CD : ClassicalDecision)
  (NE : inhabited E) (NW : inhabited W)
  (lex : forall a, symbol a -> wdomain E W a) : wmodel symbol :=
  {| windividuals := E; worlds := W;
     windividuals_nonempty := NE; worlds_nonempty := NW;
     wlexical := lex; wquantifiers := world_decision_quantifiers CD E W |}.
