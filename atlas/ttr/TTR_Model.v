(* Cooper 2023: explicit models and the distinctions lost by inhabitation.
   Read: section 1.3 pp. 11-14; section 1.4.1 pp. 18-19; A2-A3
   pp. 400-401; A8-A9 pp. 404-406.  Coq is the metalanguage here:
   object-language type codes are NOT their extensions or Coq Types.

   Fragment: fixed type syntax, atomic predicate arguments, possibly
   structured witnesses.  admissible checks a monomorphic basic-type
   arity and coverage of atoms.  This does not implement A9's varying
   Type_M sets, polymorphic arities, or the stratification of A10.
   All-model theorems hold even for unrestricted assignments and hence
   also for any chosen family of admissible models. *)
Require Import List Bool.
Require ttr.TTR.
Import ListNotations.

Section Models.
Variables D Base Pred : Type.

Record model : Type := {
  basic_extension : D -> Base -> Prop;
  ptype_extension : Pred -> list D -> TTR.val D -> Prop
}.

Definition admissible (arity : Pred -> list Base) (M : model) : Prop :=
  (forall d, exists b, basic_extension M d b) /\
  (forall p ds v, ptype_extension M p ds v ->
     Forall2 (basic_extension M) ds (arity p)).

Definition typing (M : model) :=
  TTR.of_ty D Base Pred (basic_extension M) (ptype_extension M).

Definition record_typing (M : model) :=
  TTR.of_rty D Base Pred (basic_extension M) (ptype_extension M).

(* Extension in ONE assignment versus necessary inclusion across a
   specified family (A9 restrictive notions, on the fixed syntax). *)
Definition subtype_at (M : model) (A B : TTR.ty Base Pred) : Prop :=
  forall amb v, typing M amb v A -> typing M amb v B.

Definition subtype_in (family : model -> Prop) (A B : TTR.ty Base Pred) : Prop :=
  forall M, family M -> subtype_at M A B.

Definition coextensional_at (M : model) (A B : TTR.ty Base Pred) : Prop :=
  forall amb v, typing M amb v A <-> typing M amb v B.

Definition inhabited_at (M : model) (T : TTR.ty Base Pred) : Prop :=
  exists v, typing M [] v T.

Definition necessary (family : model -> Prop) (T : TTR.ty Base Pred) : Prop :=
  forall M, family M -> inhabited_at M T.

Definition possible (family : model -> Prop) (T : TTR.ty Base Pred) : Prop :=
  exists M, family M /\ inhabited_at M T.

Theorem necessary_possible : forall family T,
  (exists M, family M) -> necessary family T -> possible family T.
Proof. intros family T [M HM] H; exists M; split; [exact HM | apply H, HM]. Qed.

Theorem checked_subtype_all_models : forall be pe,
  (forall a b, reflect (a = b) (be a b)) ->
  (forall p q, reflect (p = q) (pe p q)) ->
  forall A B, TTR.subb Base Pred be pe A B = true ->
  subtype_in (fun _ => True) A B.
Proof.
  intros be pe Hb Hp A B H M _ amb v Hv.
  exact (TTR.subb_sound D Base Pred (basic_extension M) (ptype_extension M)
           be pe Hb Hp A B amb v H Hv).
Qed.

(* A8 uses the SAME witness on both sides. *)
Theorem meet_same_witness : forall M amb v A B,
  typing M amb v (TTR.TMeet A B) <-> typing M amb v A /\ typing M amb v B.
Proof. reflexivity. Qed.

End Models.

Arguments basic_extension {D Base Pred} _ _ _.
Arguments ptype_extension {D Base Pred} _ _ _ _.
Arguments typing {D Base Pred} _ _ _ _.
Arguments record_typing {D Base Pred} _ _ _.
Arguments inhabited_at {D Base Pred} _ _.
Arguments coextensional_at {D Base Pred} _ _ _.

Module Countermodels.

(* Both models agree on which ptypes are inhabited.  They disagree on
   which object witnesses p(true).  All predicate arities are empty. *)
Definition assignment (tag : bool) : model bool bool bool :=
  {| basic_extension := fun _ _ => True;
     ptype_extension := fun (p : bool) ds v =>
       ds = [] /\ v = TTR.VBase (if p then tag else false) |}.

Theorem assignments_admissible : forall tag,
  admissible bool bool bool (fun _ => []) (assignment tag).
Proof.
  intros tag; split.
  - intros d; exists true; exact I.
  - intros p ds v [-> _]; constructor.
Qed.

Theorem erased_assignments_agree : forall p ds,
  (exists v, ptype_extension (assignment true) p ds v) <->
  (exists v, ptype_extension (assignment false) p ds v).
Proof.
  intros p ds; split; intros [v [-> Hv]].
  - exists (TTR.VBase false); split; [reflexivity | destruct p; reflexivity].
  - exists (TTR.VBase (if p then true else false)); split; reflexivity.
Qed.

Theorem same_type_same_object_different_models :
  typing (assignment true) [] (TTR.VBase true) (TTR.TPty true []) /\
  ~ typing (assignment false) [] (TTR.VBase true) (TTR.TPty true []).
Proof. cbn; split; [split; reflexivity | intros [_ H]; discriminate]. Qed.

Theorem truth_does_not_type_every_object :
  inhabited_at (assignment true) (TTR.TPty true []) /\
  ~ typing (assignment true) [] (TTR.VBase false) (TTR.TPty true []).
Proof.
  split.
  - exists (TTR.VBase true); cbn; split; reflexivity.
  - cbn; intros [_ H]; discriminate.
Qed.

(* Cooper's distinct coextensional types, section 1.3 pp. 12-13. *)
Theorem coextension_does_not_identify_types :
  coextensional_at (assignment true) (TTR.TBase true) (TTR.TBase false) /\
  @TTR.TBase bool bool true <> TTR.TBase false.
Proof.
  split; [intros amb [d | r]; cbn; tauto | discriminate].
Qed.

(* Inhabited P and inhabited Q need not share a witness.  Replacing F
   by a truth predicate would destroy this counterexample. *)
Theorem inhabited_conjuncts_empty_meet :
  inhabited_at (assignment true) (TTR.TPty true []) /\
  inhabited_at (assignment true) (TTR.TPty false []) /\
  ~ inhabited_at (assignment true)
      (TTR.TMeet (TTR.TPty true []) (TTR.TPty false [])).
Proof.
  split.
  - exists (TTR.VBase true); cbn; split; reflexivity.
  - split.
    + exists (TTR.VBase false); cbn; split; reflexivity.
    + intros [v [[_ H1] [_ H2]]]; congruence.
Qed.

(* A structured witness is permitted by section 1.4.1 p. 19.  Renaming
   it in a fixed model can change its membership: equivariance is not
   a consequence of injectivity of the label map. *)
Definition structured_model : model bool bool bool :=
  {| basic_extension := fun _ _ => True;
     ptype_extension := fun _ ds v =>
       ds = [] /\ v = TTR.VRec [(0, TTR.VBase false)] |}.

Theorem structured_witness_renaming_needs_model_compatibility :
  typing structured_model [] (TTR.VRec [(0, TTR.VBase false)])
    (TTR.TPty true []) /\
  ~ typing structured_model []
    (TTR.rename_val bool S (TTR.VRec [(0, TTR.VBase false)]))
    (TTR.TPty true []).
Proof. cbn; split; [split; reflexivity | intros [_ H]; discriminate]. Qed.

End Countermodels.

Print Assumptions checked_subtype_all_models.
Print Assumptions meet_same_witness.
Print Assumptions Countermodels.assignments_admissible.
Print Assumptions Countermodels.erased_assignments_agree.
Print Assumptions Countermodels.same_type_same_object_different_models.
Print Assumptions Countermodels.truth_does_not_type_every_object.
Print Assumptions Countermodels.coextension_does_not_identify_types.
Print Assumptions Countermodels.inhabited_conjuncts_empty_meet.
Print Assumptions Countermodels.structured_witness_renaming_needs_model_compatibility.
