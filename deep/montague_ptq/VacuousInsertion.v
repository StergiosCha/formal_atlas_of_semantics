(* Why an absent first occurrence cannot silently mean no-op while keeping
   the source's truth-condition claims. This is an explicit alternative to
   the failing operation in Surface.v, not its default behavior. *)
From Coq Require Import List Bool Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Surface Catalogue.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Definition walking_constants B a n i : domain two_times a :=
  match ty_eq_dec ivty a with
  | left H => carry H (fun x => if Nat.eqb n 1 then true else sample_constants B ivty n i x)
  | right _ => sample_constants B a n i
  end.
Definition walking_model B FE : model :=
  {| carrier := two_times; boolean_truth := B; function_extensionality := FE;
     constants := walking_constants B |}.
Definition walking_assignment B FE : free_env (walking_model B FE) := fun a _ => zero_value a.

Theorem walking_model_admissible B FE : admissible (walking_model B FE).
Proof.
  constructor.
  - intro n; exists false; destruct n; reflexivity.
  - intros c O i x H; destruct c; cbn in O; try contradiction; discriminate.
  - intros v O; exists (fun _ _ => match v with walk => true | _ => false end);
      destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O; exists (fun _ _ _ => false); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O Q; exists (fun _ _ => true); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v p; exists (fun _ _ => true); destruct v; reflexivity.
  - intros v Q; exists (fun _ _ => true); destruct v; reflexivity.
  - exists (fun _ _ _ _ => false); reflexivity.
  - unfold mp9; intros; reflexivity.
Qed.

Definition no_target_noop n alpha phi := match f10 n alpha phi with
  | Some out => out | None => phi end.
Definition vacuous_unicorn := s14 some_unicorn 9 bill_walks.

Example no_target_noop_keeps_display :
  words (no_target_noop 9 [literal "a"; noun unicorn] [name bill; verb (viv walk) present]) =
  ["Bill"; "walks"] /\ surface vacuous_unicorn = None.
Proof. split; reflexivity. Qed.

Theorem vacuous_insertion_changes_truth B FE :
  let M := walking_model B FE in
  admissible M /\
  eval M (translate_closed bill_walks) (empty_env M) (walking_assignment B FE) (tt,false) = true /\
  eval M (translate_closed vacuous_unicorn) (empty_env M) (walking_assignment B FE) (tt,false) = false.
Proof.
  cbn zeta; split; [apply walking_model_admissible|].
  rewrite !closed_translation_interpretation; split; [reflexivity|].
  change (truth B (exists x : domain two_times ic, false = true) = false).
  destruct (truth B (exists x : domain two_times ic, false = true)) eqn:E; auto.
  apply truth_spec in E; destruct E as [x E]; discriminate.
Qed.
