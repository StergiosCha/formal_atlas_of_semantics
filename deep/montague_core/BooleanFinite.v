(* Executable full Boolean models over finite, inhabited individual domains.
   Every simple type is enumerated, including ALL functions at arrow types.
   Function extensionality proves enumeration completeness. Neither global
   excluded middle nor ClassicalDecision is used by this construction. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Syntax Models BooleanModels.
Import ListNotations.
Set Implicit Arguments.

Record finite (A : Type) : Type := {
  default_value : A;
  values : list A;
  value_eq : forall x y : A, {x = y} + {x <> y};
  values_complete : forall x, In x values
}.
Arguments default_value {A} _.
Arguments values {A} _.
Arguments value_eq {A} _ _ _.

Lemma finite_forall_spec : forall A (F : finite A) (p : A -> bool),
  forallb p (values F) = true <-> forall x, p x = true.
Proof.
  intros; rewrite forallb_forall; split.
  - intros H x; apply H; apply values_complete.
  - intros H x _; apply H.
Qed.

Definition finite_bool : finite bool.
Proof.
  refine {| default_value := false; values := [false; true]; value_eq := Bool.bool_dec |}.
  destruct x; cbn; auto.
Defined.

Definition finite_unit : finite unit.
Proof.
  refine {| default_value := tt; values := [tt] |}.
  - intros [] []; left; reflexivity.
  - intros []; cbn; auto.
Defined.

Section FunctionEnumeration.
Context {A B : Type} (FA : finite A) (FB : finite B).

Definition override (x : A) (y : B) (f : A -> B) : A -> B :=
  fun z => if value_eq FA z x then y else f z.

Fixpoint tables (xs : list A) : list (A -> B) :=
  match xs with
  | [] => [fun _ => default_value FB]
  | x :: rest => flat_map
      (fun y => map (override x y) (tables rest)) (values FB)
  end.

Lemma tables_cover_points : forall xs (f : A -> B),
  exists g, In g (tables xs) /\ forall x, In x xs -> g x = f x.
Proof.
  intro xs; induction xs as [| x rest IH]; intro f; cbn.
  - exists (fun _ => default_value FB); split; [left; reflexivity | intros; contradiction].
  - destruct (IH f) as [g [Hin Agree]].
    exists (override x (f x) g); split.
    + apply in_flat_map; exists (f x); split; [apply values_complete |].
      apply in_map_iff; exists g; split; [reflexivity | exact Hin].
    + intros z Hz; unfold override; destruct (value_eq FA z x) as [E | NE].
      * subst z; reflexivity.
      * apply Agree; destruct Hz as [E | Hz]; [symmetry in E; contradiction | exact Hz].
Qed.

Lemma tables_complete (FE : FunExt) : forall f : A -> B,
  In f (tables (values FA)).
Proof.
  intro f; destruct (tables_cover_points (values FA) f) as [g [Hin Agree]].
  assert (E : g = f).
  { apply FE; intro x; apply Agree; apply values_complete. }
  rewrite <- E; exact Hin.
Qed.

Definition function_eq (FE : FunExt) (f g : A -> B) : {f = g} + {f <> g}.
Proof.
  destruct (forallb (fun x => if value_eq FB (f x) (g x) then true else false)
    (values FA)) eqn:H.
  - left; apply FE; intro x.
    pose proof (proj1 (finite_forall_spec FA _) H x) as E.
    cbn in E; destruct (value_eq FB (f x) (g x)); [assumption | discriminate].
  - right; intro E; subst g.
    assert (K : forallb (fun x => if value_eq FB (f x) (f x) then true else false)
      (values FA) = true).
    { apply finite_forall_spec; intro x; destruct (value_eq FB (f x) (f x));
        [reflexivity | contradiction]. }
    rewrite K in H; discriminate.
Defined.

Definition finite_arrow (FE : FunExt) : finite (A -> B) :=
  {| default_value := fun _ => default_value FB;
     values := tables (values FA);
     value_eq := function_eq FE;
     values_complete := tables_complete FE |}.

End FunctionEnumeration.

Fixpoint finite_domain {E} (FE : FunExt) (F : finite E) (a : ty) : finite (bdomain E a) :=
  match a with
  | entity => F
  | truth => finite_bool
  | arrow a b => finite_arrow (finite_domain FE F a) (finite_domain FE F b) FE
  end.

Definition finite_quantifiers {E} (FE : FunExt) (F : finite E) : BooleanQuantifiers E :=
  {| bforall := fun a p => forallb p (values (finite_domain FE F a));
     bforall_spec := fun a p => finite_forall_spec (finite_domain FE F a) p |}.

Definition finite_model {symbol E} (FE : FunExt) (F : finite E)
  (lex : forall a, symbol a -> bdomain E a) : bmodel symbol :=
  {| bindividuals := E;
     bindividuals_nonempty := inhabits (default_value F);
     blexical := lex;
     bquantifiers := finite_quantifiers FE F |}.

Lemma finite_quantification_complete : forall E (FE : FunExt) (F : finite E) a p,
  bforall (finite_quantifiers FE F) a p = true <-> forall x, p x = true.
Proof. intros; apply bforall_spec. Qed.

(* Equal truth values do not assert equality of arbitrary Coq propositions. *)
Lemma booleans_are_two_valued : forall b : bool, b = true \/ b = false.
Proof. destruct b; auto. Qed.
