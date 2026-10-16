(* A term-valued generalization of the existing compiler, for proving its
   substitution laws. Agreement with the existing translation is syntactic. *)
From Coq Require Import List.
From MontaguePTQ Require Import Syntax.
From MontagueGallin Require Import Types Target Translation Minimal Substitution SyntaxAlgebra
  Untensed ILCore.
Import ListNotations.
Set Implicit Arguments.
Local Notation C := (ctm source_symbol source_parameter).
Definition lvalues G D := forall a, var G a -> C D (translate_type a).
Definition lshift {G D b} (r : lvalues G D) : lvalues G (b :: D) := fun a v => cweaken (r a v).
Definition lbind {G D a} (r : lvalues G D) (q : C D (translate_type a)) : lvalues (a :: G) D :=
  fun b v => match v in var G' b' return
    match G' with [] => unit | c :: G0 =>
      lvalues G0 D -> C D (translate_type c) -> C D (translate_type b') end with
  | @vz _ _ => fun _ x => x | @vs _ _ _ w => fun r0 _ => r0 _ w
  end r q.
Definition llift {G D a} (r : lvalues G D) : lvalues (a :: G) (translate_type a :: D) :=
  lbind (lshift r) (CVar gz).
Definition variable_values {G D} (r : variable_map G D) : lvalues G D := fun a v => CVar (r a v).
Fixpoint lcompile {G a} (p : ltm G a) : forall D, lvalues G D -> C D gs -> C D (translate_type a) :=
  match p in ltm G' a' return forall D, lvalues G' D -> C D gs -> C D (translate_type a') with
  | LVar v => fun D r _ => r _ v
  | LFree n => fun D _ _ => CFree (SourceFree _ n)
  | LCon n => fun D _ i => CApp (CCon (IndexedConstant _ n)) i
  | LLam p => fun D r i => CLam (lcompile p (llift r) (cweaken i))
  | LApp p q => fun D r i => CApp (lcompile p r i) (lcompile q r i)
  | LEq p q => fun D r i => CEq (lcompile p r i) (lcompile q r i)
  | LUp p => fun D r _ => CLam (lcompile p (lshift r) (CVar gz))
  | LDown p => fun D r i => CApp (lcompile p r i) i
  end.

Lemma lcompile_ext G a (p : ltm G a) : forall D (r s : lvalues G D) i,
  (forall b v, r b v = s b v) -> lcompile p r i = lcompile p s i.
Proof.
  induction p; intros D r rr i H; cbn; try reflexivity; try apply H;
    try (rewrite (IHp1 D r rr i H), (IHp2 D r rr i H); reflexivity).
  - f_equal; apply IHp; apply var_cases; cbn; [reflexivity | intros; unfold lshift; rewrite H; reflexivity].
  - f_equal; apply IHp; intros; unfold lshift; rewrite H; reflexivity.
  - rewrite (IHp D r rr i H); reflexivity.
Qed.
Lemma lcompile_source_rename G a (p : ltm G a) : forall H D (r : lren G H)
  (s : lvalues H D) (u : lvalues G D) i,
  (forall b v, s b (r b v) = u b v) -> lcompile (lrename p r) s i = lcompile p u i.
Proof.
  induction p; intros H D r sub u i HE; cbn; try reflexivity; try apply HE;
    try (rewrite IHp1 with (u := u), IHp2 with (u := u); auto; fail).
  - f_equal; apply IHp; apply var_cases; cbn; [reflexivity | intros; unfold lshift; rewrite HE; reflexivity].
  - f_equal; apply IHp; intros; unfold lshift; rewrite HE; reflexivity.
  - rewrite IHp with (u := u); auto.
Qed.
Lemma lcompile_target_subst G a (p : ltm G a) : forall D E (r : lvalues G D)
  (s : csub source_symbol source_parameter D E) i,
  csubst (lcompile p r i) s = lcompile p (fun b v => csubst (r b v) s) (csubst i s).
Proof.
  induction p; intros D E r sub i; cbn; try reflexivity; try (rewrite IHp1, IHp2; reflexivity).
  - f_equal; rewrite IHp, csubst_lift_weaken.
    apply lcompile_ext; apply var_cases; cbn; [reflexivity | intros; apply csubst_lift_weaken].
  - f_equal; rewrite IHp; apply lcompile_ext; intros; apply csubst_lift_weaken.
  - rewrite IHp; reflexivity.
Qed.
Lemma lcompile_target_rename G a (p : ltm G a) D E (s : lvalues G D) (r : gren D E) i :
  crename (lcompile p s i) r =
  lcompile p (fun b v => crename (s b v) r) (crename i r).
Proof.
  rewrite <- csubst_renaming, lcompile_target_subst, csubst_renaming.
  apply lcompile_ext; intros; apply csubst_renaming.
Qed.
Lemma lcompile_weaken G D a b (p : ltm G b) (s : lvalues G D) i :
  @cweaken source_symbol source_parameter D a (translate_type b) (lcompile p s i) =
  lcompile p (lshift s) (cweaken i).
Proof. apply lcompile_target_rename. Qed.
Lemma lcompile_modal_closed G a (p : ltm G a) (H : ModallyClosed p) :
  forall D (r : lvalues G D) i j, lcompile p r i = lcompile p r j.
Proof.
  induction H; intros D r i j; cbn; try reflexivity;
    try (rewrite IHModallyClosed1 with (j := j), IHModallyClosed2 with (j := j); reflexivity).
  f_equal; apply IHModallyClosed.
Qed.
Theorem lcompile_agrees_with_existing G a (p : ltm G a) : forall D (r : variable_map G D)
  (i : gvar D gs), lcompile p (variable_values r) (CVar i) =
  eliminate (compile (embed_il (include_il p)) r (GVar i)).
Proof.
  induction p; intros D r i; cbn [lcompile include_il embed_il compile eliminate]; try reflexivity;
    try (rewrite IHp1, IHp2; reflexivity).
  - f_equal; change (lcompile p (llift (variable_values r)) (CVar (gvs i)) =
      eliminate (compile (embed_il (include_il p)) (lift_map r) (GVar (gvs i)))).
    rewrite <- IHp; apply lcompile_ext; apply var_cases; cbn; reflexivity.
  - f_equal; rewrite <- IHp; apply lcompile_ext; intros; reflexivity.
  - rewrite IHp; reflexivity.
Qed.

Lemma lcompile_true G D (r : lvalues G D) i : lcompile (@ltrue G) r i = ctrue.
Proof. reflexivity. Qed.
Lemma lcompile_false G D (r : lvalues G D) i : lcompile (@lfalse G) r i = cfalse.
Proof. reflexivity. Qed.
Lemma lcompile_source_weaken G D a b (p : ltm G b) (r : lvalues G D)
  (x : C D (translate_type a)) i : lcompile (lweaken p) (lbind r x) i = lcompile p r i.
Proof. apply lcompile_source_rename; intros; reflexivity. Qed.
Lemma lcompile_and G (p q : ltm G t) D (r : lvalues G D) i :
  lcompile (land p q) r i = cand (lcompile p r i) (lcompile q r i).
Proof.
  cbn [land lcompile cand]; unfold llift.
  rewrite !lcompile_source_weaken, <- !lcompile_weaken; reflexivity.
Qed.
Lemma lcompile_imp G (p q : ltm G t) D (r : lvalues G D) i :
  lcompile (limp p q) r i = cimp (lcompile p r i) (lcompile q r i).
Proof. cbn [limp lcompile cimp]; rewrite lcompile_and; reflexivity. Qed.
Lemma lcompile_all G a (p : ltm (a :: G) t) D (r : lvalues G D) i :
  lcompile (lall p) r i = call (lcompile p (llift r) (cweaken i)).
Proof. reflexivity. Qed.
Lemma lcompile_box G (p : ltm G t) D (r : lvalues G D) i :
  lcompile (lbox p) r i = call (lcompile p (lshift r) (CVar gz)).
Proof. reflexivity. Qed.

Lemma lcompile_beta G a b (p : ltm (a :: G) b) D (r : lvalues G D) i q :
  subst0 (lcompile p (llift r) (cweaken i)) q = lcompile p (lbind r q) i.
Proof.
  unfold subst0; rewrite lcompile_target_subst.
  change (lcompile p (fun c v => csubst (@llift G D a r c v) (csub_head q))
    (subst0 (cweaken i) q) = lcompile p (lbind r q) i).
  rewrite subst0_weaken; apply lcompile_ext; apply var_cases; cbn; [reflexivity |].
  intros; apply subst0_weaken.
Qed.
Lemma lcompile_index_beta G a (p : ltm G a) D (r : lvalues G D) i :
  subst0 (lcompile p (lshift r) (CVar gz)) i = lcompile p r i.
Proof.
  unfold subst0; rewrite lcompile_target_subst; cbn.
  apply lcompile_ext; intros; apply subst0_weaken.
Qed.
Lemma lcompile_weaken_under_binder G D a b (p : ltm G b) (r : lvalues G D) i :
  lcompile (@lweaken G a b p) (llift r) (cweaken i) = cweaken (lcompile p r i).
Proof. unfold llift; rewrite lcompile_source_weaken; symmetry; apply lcompile_weaken. Qed.
Lemma lcompile_swap_beta G D a b c (p : ltm (b :: a :: G) c) (r : lvalues G D)
  (q : C D (translate_type a)) i :
  lcompile (lrename p lswap) (lbind (@llift G D b r) (cweaken q)) (cweaken i) =
  lcompile p (llift (lbind r q)) (cweaken i).
Proof.
  apply lcompile_source_rename; apply var_cases; cbn; [reflexivity |].
  intros d v; revert d v; apply var_cases; cbn; reflexivity.
Qed.
