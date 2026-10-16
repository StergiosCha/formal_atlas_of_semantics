(* Independent implicit-index evaluation and its preservation in Ty2.
   Source and target share full internal value domains and quantifiers;
   the source evaluator is NOT defined by applying the translation. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Models BooleanModels Ty2Syntax Ty2Models ILSyntax.
Import ListNotations.
Set Implicit Arguments.

Section Interpretation.
Context {symbol : ity -> Type} {target : wty -> Type}.
Variable constants : forall a, symbol a -> target (world_type a).
Variable M : wmodel target.

Definition idomain a := wdomain (windividuals M) (worlds M) (world_type a).
Definition ienv G := forall a, ivar G a -> idomain a.
Definition iextend {G a} (rho : ienv G) (x : idomain a) : ienv (a :: G) :=
  fun b v => match v in ivar G' b' return
    match G' with
    | [] => unit
    | c :: G0 => ienv G0 -> idomain c -> idomain b'
    end with
  | @iz _ _ => fun _ x0 => x0
  | @ivs _ _ _ w => fun rho0 _ => rho0 _ w
  end rho x.

Fixpoint ieval {G a} (t : itm symbol G a) : ienv G -> worlds M -> idomain a :=
  match t in itm _ G' a' return ienv G' -> worlds M -> idomain a' with
  | IVar v => fun rho _ => rho _ v
  | IConst c => fun _ _ => wlexical M _ (@constants _ c)
  | ILam t => fun rho w x => ieval t (iextend rho x) w
  | IApp f x => fun rho w => ieval f rho w (ieval x rho w)
  | IImp p q => fun rho w => bimp (ieval p rho w) (ieval q rho w)
  | IAll p => fun rho w => wforall (wquantifiers M) _ (fun x => ieval p (iextend rho x) w)
  | IUp t => fun rho _ w' => ieval t rho w'
  | IDown t => fun rho w => ieval t rho w w
  | IBox p => fun rho _ => wforall (wquantifiers M) ws (fun w' => ieval p rho w')
  end.

Theorem explicit_world_preservation (FE : FunExt) : forall G a (t : itm symbol G a)
  D (r : ivmap G D) (w : wtm target D ws) (rho : wenv M D) (sigma : ienv G),
  (forall b v, rho _ (r b v) = sigma b v) ->
  weval M (explicit_world constants t r w) rho = ieval t sigma (weval M w rho).
Proof.
  intros G a t; induction t; intros D r w rho sigma H; cbn.
  - apply H.
  - reflexivity.
  - apply FE; intro x.
    refine (eq_trans (IHt _ (ilift r) (wweaken w) (wextend rho x) (iextend sigma x) _) _).
    + apply ivar_cons_cases; cbn; [reflexivity | intros; apply H].
    + rewrite (weval_weaken FE); reflexivity.
  - exact (f_equal2 (fun f x => f x) (IHt1 _ r w rho sigma H) (IHt2 _ r w rho sigma H)).
  - exact (f_equal2 bimp (IHt1 _ r w rho sigma H) (IHt2 _ r w rho sigma H)).
  - f_equal; apply FE; intro x.
    refine (eq_trans (IHt _ (ilift r) (wweaken w) (wextend rho x) (iextend sigma x) _) _).
    + apply ivar_cons_cases; cbn; [reflexivity | intros; apply H].
    + rewrite (weval_weaken FE); reflexivity.
  - apply FE; intro w'.
    apply IHt; intros; cbn; apply H.
  - exact (f_equal (fun f => f (weval M w rho)) (IHt _ r w rho sigma H)).
  - f_equal; apply FE; intro w'.
    apply IHt; intros; cbn; apply H.
Qed.

Definition source_env {G} (rho : wenv M (map world_type G)) : ienv G :=
  fun a v => rho _ (ivar_embed v).

Theorem intension_translation_preservation (FE : FunExt) : forall G a
  (t : itm symbol G a) (rho : wenv M (map world_type G)) w,
  weval M (translate_intension constants t) rho w = ieval t (source_env rho) w.
Proof.
  intros; unfold translate_intension; cbn -[explicit_world].
  apply explicit_world_preservation; [exact FE | intros; reflexivity].
Qed.

Theorem translated_truth_iff (FE : FunExt) : forall G (p : itm symbol G it) rho w,
  weval M (translate_intension constants p) rho w = true <->
  ieval p (source_env rho) w = true.
Proof. intros; rewrite (intension_translation_preservation FE); reflexivity. Qed.

Theorem translated_counterexample_iff (FE : FunExt) : forall G (p q : itm symbol G it) rho w,
  (weval M (translate_intension constants p) rho w = true /\
   weval M (translate_intension constants q) rho w = false) <->
  (ieval p (source_env rho) w = true /\ ieval q (source_env rho) w = false).
Proof. intros; repeat rewrite (intension_translation_preservation FE); reflexivity. Qed.

(* Semantic cancellation, not a new primitive IL conversion rule. *)
Theorem down_up_cancellation : forall G a (t : itm symbol G a) rho w,
  ieval (IDown (IUp t)) rho w = ieval t rho w.
Proof. reflexivity. Qed.

Definition index_rigid {G a} (t : itm symbol G a) :=
  forall rho w w', ieval t rho w = ieval t rho w'.

Theorem variables_are_index_rigid : forall G a (v : ivar G a), index_rigid (IVar v).
Proof. intros; intros rho w w'; reflexivity. Qed.
Theorem constants_are_index_rigid : forall G a (c : symbol a), index_rigid (@IConst symbol G a c).
Proof. intros; intros rho w w'; reflexivity. Qed.
Theorem up_is_index_rigid : forall G a (t : itm symbol G a), index_rigid (IUp t).
Proof. intros; intros rho w w'; reflexivity. Qed.
Theorem box_is_index_rigid : forall G (p : itm symbol G it), index_rigid (IBox p).
Proof. intros; intros rho w w'; reflexivity. Qed.

Theorem up_down_for_rigid_intensions (FE : FunExt) : forall G a (t : itm symbol G (intens a)),
  index_rigid t -> forall rho w, ieval (IUp (IDown t)) rho w = ieval t rho w.
Proof. intros G a t R rho w; apply FE; intro w'; cbn; rewrite (R rho w' w); reflexivity. Qed.

Theorem implicit_necessity_meaning : forall G (p : itm symbol G it) rho w,
  ieval (IBox p) rho w = true <-> forall w', ieval p rho w' = true.
Proof. intros; cbn; apply wforall_spec. Qed.
End Interpretation.
Arguments ieval {symbol target} constants M {G a} _ _ _.
