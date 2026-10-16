(* Gallin 1975, section 8, pp. 58-60: e, t, s and functional types.
   Here s denotes a PTQ world-time index. This is the declared tense
   specialization, not an identification of worlds with times. *)
From MontaguePTQ Require Import Syntax Models.
Set Implicit Arguments.

Inductive gty := ge | gt | gs | garr (a b : gty).
Fixpoint translate_type (a : ty) : gty :=
  match a with
  | e => ge | t => gt
  | arr a b => garr (translate_type a) (translate_type b)
  | intens a => garr gs (translate_type a)
  end.
Fixpoint gdomain (F : frame) (a : gty) : Type :=
  match a with
  | ge => entity F | gt => bool | gs => index F
  | garr a b => gdomain F a -> gdomain F b
  end.

Definition arrow_eq {A A' B B' : Type} (p : A = A') (q : B = B') :
  (A -> B) = (A' -> B').
Proof. destruct p, q; reflexivity. Defined.
Definition cast {A B : Type} (p : A = B) (x : A) : B :=
  match p with eq_refl => x end.
Lemma cast_back {A B : Type} (p : A = B) x :
  cast (eq_sym p) (cast p x) = x.
Proof. destruct p; reflexivity. Qed.
Lemma cast_forward {A B : Type} (p : A = B) x :
  cast p (cast (eq_sym p) x) = x.
Proof. destruct p; reflexivity. Qed.
Lemma cast_application {A A' B B' : Type} (p : A = A') (q : B = B') f x :
  cast (arrow_eq p q) f (cast p x) = cast q (f x).
Proof. destruct p, q; reflexivity. Qed.
Lemma cast_lambda {A A' B B' : Type} (p : A = A') (q : B = B') f :
  cast (arrow_eq p q) f = fun x => cast q (f (cast (eq_sym p) x)).
Proof. destruct p, q; reflexivity. Qed.
Lemma cast_equality {A B : Type} (p : A = B) x y :
  (cast p x = cast p y) = (x = y).
Proof. destruct p; reflexivity. Qed.
Lemma cast_forall {A B : Type} (p : A = B) (P : A -> Prop) :
  (forall y, P (cast (eq_sym p) y)) = (forall x, P x).
Proof. destruct p; reflexivity. Qed.
Lemma cast_exists {A B : Type} (p : A = B) (P : A -> Prop) :
  (exists y, P (cast (eq_sym p) y)) = (exists x, P x).
Proof. destruct p; reflexivity. Qed.

Fixpoint domain_agreement F a : domain F a = gdomain F (translate_type a) :=
  match a with
  | e => eq_refl | t => eq_refl
  | arr a b => arrow_eq (domain_agreement F a) (domain_agreement F b)
  | intens a => arrow_eq eq_refl (domain_agreement F a)
  end.
Definition lift_value F a := cast (domain_agreement F a).
Definition lower_value F a := cast (eq_sym (domain_agreement F a)).
Lemma lower_lift F a x : lower_value F a (lift_value F a x) = x.
Proof. apply cast_back. Qed.
Lemma lift_lower F a x : lift_value F a (lower_value F a x) = x.
Proof. apply cast_forward. Qed.
Lemma lift_application F a b (f : domain F (arr a b)) x :
  lift_value F (arr a b) f (lift_value F a x) = lift_value F b (f x).
Proof. apply cast_application. Qed.
Lemma lift_lambda F a b (f : domain F (arr a b)) :
  lift_value F (arr a b) f = fun x => lift_value F b (f (lower_value F a x)).
Proof. apply cast_lambda. Qed.
Lemma lift_intension F a (f : domain F (intens a)) :
  lift_value F (intens a) f = fun i => lift_value F a (f i).
Proof. apply cast_lambda. Qed.
Lemma lift_equality F a (x y : domain F a) :
  (lift_value F a x = lift_value F a y) = (x = y).
Proof. apply cast_equality. Qed.
Lemma lower_forall F a (P : domain F a -> Prop) :
  (forall y, P (lower_value F a y)) = (forall x, P x).
Proof. apply cast_forall. Qed.
Lemma lower_exists F a (P : domain F a -> Prop) :
  (exists y, P (lower_value F a y)) = (exists x, P x).
Proof. apply cast_exists. Qed.

Theorem index_is_not_a_source_type : forall a, translate_type a <> gs.
Proof. destruct a; discriminate. Qed.
Theorem type_translation_injective : forall a b,
  translate_type a = translate_type b -> a = b.
Proof.
  induction a; destruct b; cbn; intro H; try discriminate; try reflexivity.
  - inversion H; f_equal; auto.
  - inversion H; exfalso; eapply index_is_not_a_source_type; eauto.
  - inversion H; exfalso; eapply index_is_not_a_source_type; symmetry; eauto.
  - inversion H; f_equal; auto.
Qed.
