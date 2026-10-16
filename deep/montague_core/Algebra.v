(* Syntactic renaming/substitution algebra. All equalities are proved
   pointwise and structurally: no function extensionality or model premise. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax.
Import ListNotations.
Set Implicit Arguments.

Section Algebra.
Variable symbol : ty -> Type.

Lemma rename_ext : forall G a (t : tm symbol G a) D (r q : ren G D),
  (forall b v, r b v = q b v) -> rename t r = rename t q.
Proof.
  intros G a t; induction t; intros D r q E; cbn; f_equal; auto.
  - apply IHt; apply var_cons_cases; cbn; intros; [reflexivity | f_equal; apply E].
  - apply IHt; apply var_cons_cases; cbn; intros; [reflexivity | f_equal; apply E].
Qed.

Lemma subst_ext : forall G a (t : tm symbol G a) D (s r : sub symbol G D),
  (forall b v, s b v = r b v) -> subst t s = subst t r.
Proof.
  intros G a t; induction t; intros D theta r E; cbn; try (f_equal; auto).
  - apply IHt; apply var_cons_cases; cbn; intros; [reflexivity | f_equal; apply E].
  - apply IHt; apply var_cons_cases; cbn; intros; [reflexivity | f_equal; apply E].
Qed.

Lemma rename_id : forall G a (t : tm symbol G a),
  rename t (fun _ v => v) = t.
Proof.
  intros G a t; induction t; cbn; try (f_equal; auto).
  - transitivity (rename t (fun _ v => v)); [apply rename_ext | exact IHt].
    apply var_cons_cases; reflexivity.
  - transitivity (rename t (fun _ v => v)); [apply rename_ext | exact IHt].
    apply var_cons_cases; reflexivity.
Qed.

Lemma rename_comp : forall G a (t : tm symbol G a) D E
  (r : ren G D) (q : ren D E),
  rename (rename t r) q = rename t (fun b v => q b (r b v)).
Proof.
  intros G a t; induction t; intros D E r q; cbn; try (f_equal; auto).
  - rewrite IHt. apply rename_ext; apply var_cons_cases; reflexivity.
  - rewrite IHt. apply rename_ext; apply var_cons_cases; reflexivity.
Qed.

Lemma rename_weaken : forall G a b (t : tm symbol G b) D (r : ren G D),
  rename (@weaken symbol G a b t) (lift_ren r) = weaken (rename t r).
Proof.
  intros; unfold weaken; rewrite !rename_comp.
  apply rename_ext; intros; reflexivity.
Qed.

Lemma subst_after_rename : forall G a (t : tm symbol G a) D E
  (r : ren G D) (s : sub symbol D E),
  subst (rename t r) s = subst t (fun b v => s b (r b v)).
Proof.
  intros G a t; induction t; intros D E r theta; cbn; try (f_equal; auto).
  - rewrite IHt. apply subst_ext; apply var_cons_cases; reflexivity.
  - rewrite IHt. apply subst_ext; apply var_cons_cases; reflexivity.
Qed.

Lemma rename_after_subst : forall G a (t : tm symbol G a) D E
  (s : sub symbol G D) (r : ren D E),
  rename (subst t s) r = subst t (fun b v => rename (s b v) r).
Proof.
  intros G a t; induction t; intros D E theta r; cbn; try (f_equal; auto).
  - rewrite IHt. apply subst_ext; apply var_cons_cases; cbn; intros.
    + reflexivity.
    + apply rename_weaken.
  - rewrite IHt. apply subst_ext; apply var_cons_cases; cbn; intros.
    + reflexivity.
    + apply rename_weaken.
Qed.

Lemma subst_weaken : forall G a b (t : tm symbol G b) D (s : sub symbol G D),
  subst (@weaken symbol G a b t) (lift_sub s) = weaken (subst t s).
Proof.
  intros; unfold weaken at 1 2.
  rewrite subst_after_rename, rename_after_subst.
  apply subst_ext; intros; reflexivity.
Qed.

Lemma subst_comp : forall G a (t : tm symbol G a) D E
  (s : sub symbol G D) (r : sub symbol D E),
  subst (subst t s) r = subst t (fun b v => subst (s b v) r).
Proof.
  intros G a t; induction t; intros D E theta r; cbn; try (f_equal; auto).
  - rewrite IHt. apply subst_ext; apply var_cons_cases; cbn; intros.
    + reflexivity.
    + apply subst_weaken.
  - rewrite IHt. apply subst_ext; apply var_cons_cases; cbn; intros.
    + reflexivity.
    + apply subst_weaken.
Qed.

Lemma subst_renaming : forall G a (t : tm symbol G a) D (r : ren G D),
  subst t (fun b v => Var (r b v)) = rename t r.
Proof.
  intros G a t; induction t; intros D r; cbn; try (f_equal; auto).
  - transitivity (subst t (fun b v => Var (lift_ren r v))).
    + apply subst_ext; apply var_cons_cases; reflexivity.
    + apply IHt.
  - transitivity (subst t (fun b v => Var (lift_ren r v))).
    + apply subst_ext; apply var_cons_cases; reflexivity.
    + apply IHt.
Qed.

Lemma subst_id : forall G a (t : tm symbol G a),
  subst t (fun b v => Var v) = t.
Proof. intros; rewrite subst_renaming; apply rename_id. Qed.

Lemma instantiate_weaken : forall G a b (t : tm symbol G b) (u : tm symbol G a),
  instantiate u (weaken t) = t.
Proof.
  intros; unfold instantiate, weaken; rewrite subst_after_rename.
  apply subst_id.
Qed.

Lemma rename_instantiate : forall G a b (t : tm symbol (a :: G) b)
  (u : tm symbol G a) D (r : ren G D),
  rename (instantiate u t) r = instantiate (rename u r) (rename t (lift_ren r)).
Proof.
  intros; unfold instantiate; rewrite rename_after_subst, subst_after_rename.
  apply subst_ext; apply var_cons_cases; reflexivity.
Qed.

Lemma subst_instantiate : forall G a b (t : tm symbol (a :: G) b)
  (u : tm symbol G a) D (s : sub symbol G D),
  subst (instantiate u t) s = instantiate (subst u s) (subst t (lift_sub s)).
Proof.
  intros; unfold instantiate; rewrite !subst_comp.
  apply subst_ext; apply var_cons_cases; cbn; intros; [reflexivity |].
  symmetry; apply instantiate_weaken.
Qed.

Lemma map_rename_weaken : forall G D a (H : list (tm symbol G truth)) (r : ren G D),
  map (fun p => rename p (@lift_ren G D a r)) (map (@weaken symbol G a truth) H) =
  map (@weaken symbol D a truth) (map (fun p => rename p r) H).
Proof. intros; rewrite !map_map; apply map_ext; intro p; apply rename_weaken. Qed.

Lemma map_subst_weaken : forall G D a (H : list (tm symbol G truth)) (s : sub symbol G D),
  map (fun p => subst p (@lift_sub symbol G D a s)) (map (@weaken symbol G a truth) H) =
  map (@weaken symbol D a truth) (map (fun p => subst p s) H).
Proof. intros; rewrite !map_map; apply map_ext; intro p; apply subst_weaken. Qed.

End Algebra.
