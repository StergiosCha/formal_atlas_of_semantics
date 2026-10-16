(* Source-calculus proof trees and counterexamples to missing side conditions.
   The counterexamples diagnose encodings; the restrictions are Gallin's. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Independent Minimal MinimalCorrespondence
  Untensed UntensedTranslation UntensedModels UntensedExamples ILCore ILCalculus.
Import ListNotations.
Set Implicit Arguments.

Definition il_derive_reflexivity {G a} (p : ltm G a) : ILDerivation (LEq p p) :=
  IL_R1 (IL_R8 p (ILByAxiom (IL_AS42 p))) (ILByAxiom (IL_AS42 p)).
Definition il_derive_truth {G} : ILDerivation (@ltrue G) :=
  il_derive_reflexivity (@LLam G t t (LVar vz)).
Definition il_derive_symmetry {G a} (p q : ltm G a) (H : ILDerivation (LEq p q)) :
  ILDerivation (LEq q p) := IL_R1 (IL_R8 p H) (il_derive_reflexivity p).
Definition il_derive_transitivity {G a} (p q r : ltm G a)
  (HP : ILDerivation (LEq p q)) (HQ : ILDerivation (LEq q r)) : ILDerivation (LEq p r) :=
  IL_R1 (IL_R7 p HQ) HP.
Definition il_axiom_one_tree : ILDerivation (il_axiom1 (@LFree [] (arr t t) 0)) :=
  ILByAxiom (IL_A1 (ILNamedVariable 0)).
Definition il_axiom_two_tree : ILDerivation (il_axiom2 (@LFree [] e 0) (LFree 1) (LFree 2)) :=
  ILByAxiom (IL_A2 (ILNamedVariable 0) (ILNamedVariable 1) (ILNamedVariable 2)).
Definition il_axiom_three_tree : ILDerivation (il_axiom3 (@LFree [] (arr e t) 0) (LFree 1)) :=
  ILByAxiom (IL_A3 (ILNamedVariable 0) (ILNamedVariable 1)).
Definition il_axiom_five_tree : ILDerivation (il_axiom5 (@LFree [] (intens e) 0) (LFree 1)) :=
  ILByAxiom (IL_A5 (ILNamedVariable 0) (ILNamedVariable 1)).
Definition il_modal_beta_tree : ILDerivation
  (LEq (LApp (LLam (LUp (LVar vz))) (@LUp [] t (LCon 0)))
    (LUp (LApp (LLam (LVar vz)) (LUp (LCon 0))))) :=
  ILByAxiom (IL_AS47 (LVar vz) (MCUp (LCon 0))).
Definition il_beta_under_intension_tree G a b (p : ltm G b) (q : ltm G a) :
  ILDerivation (LEq (LUp (LApp (LLam (lweaken p)) q)) (LUp p)) :=
  IL_R5 (ILByAxiom (IL_AS41 p q)).
Definition il_intension_cancellation_tree G a (p : ltm G a) :
  ILDerivation (LEq (LDown (LUp p)) p) := ILByAxiom (IL_AS6 p).

(* Soundness can be combined with the existing semantic correspondence.
   The conclusion is target validity, explicitly NOT a target proof tree. *)
Definition included_il_theory (Gamma : ltm [] t -> Prop) (q : il_formula) : Prop :=
  exists p, Gamma p /\ q = include_il p.
Theorem il_derivation_implies_source_validity (p : ltm [] t) (H : ILDerivation p) :
  il_standard_consequence (fun _ => False) (include_il p).
Proof. intros M sigma i _; exact (il_derivations_sound sigma H (il_empty M) i). Qed.
Theorem il_derivation_implies_translated_validity (p : ltm [] t) (H : ILDerivation p) :
  ty2_standard_consequence (translated_il_theory (fun _ => False)) (il_minimal_translate (include_il p)).
Proof. apply untensed_standard_validity; apply il_derivation_implies_source_validity; exact H. Qed.
Theorem il_assumptions_imply_translated_consequence (Gamma : ltm [] t -> Prop) p
  (H : ILFrom Gamma p) :
  ty2_standard_consequence (translated_il_theory (included_il_theory Gamma))
    (il_minimal_translate (include_il p)).
Proof.
  apply untensed_standard_consequence; intros M sigma i HG.
  apply (@il_from_assumptions_sound [] Gamma p H M sigma (il_empty M) i).
  intros q HQ; apply HG; exists q; split; [exact HQ | reflexivity].
Qed.

Definition modal_test_constant (a : ty) (i : bool) : idomain bool bool a :=
  match a with
  | t => i
  | intens b => match b as b0 return bool -> idomain bool bool b0 with
      | t => fun j => xorb i j | b0 => fun _ => plain_value b0 end
  | a0 => plain_value a0
  end.
Definition modal_test_model B FE : il_model :=
  {| il_entities := bool; il_indices := bool;
     il_entities_inhabited := inhabits false; il_indices_inhabited := inhabits false;
     il_truth := B; il_extensionality := FE;
     il_constants := fun a _ i => modal_test_constant a i |}.
Definition modal_test_assignment B FE : il_free_env (modal_test_model B FE) := fun a _ => plain_value a.

Definition forbidden_modal_beta : ltm [] t :=
  LEq (LApp (LLam (LUp (LVar vz))) (@LCon [] t 0))
    (LUp (LApp (LLam (LVar vz)) (LCon 0))).
Theorem unrestricted_modal_beta_is_false B FE :
  lval (modal_test_model B FE) forbidden_modal_beta (il_empty _) (modal_test_assignment B FE) false = false.
Proof.
  change (truth B ((fun _ : bool => false) = (fun j : bool => j)) = false).
  destruct (truth B _) eqn:H; auto.
  apply (proj1 (truth_spec B _)) in H; apply (f_equal (fun f => f true)) in H; discriminate.
Qed.
Theorem forbidden_modal_beta_has_no_derivation (B : BooleanTruth) (FE : FunExt) :
  ILDerivation forbidden_modal_beta -> False.
Proof.
  intro H; pose proof (il_derivations_sound (modal_test_assignment B FE) H (il_empty _) false) as K.
  rewrite unrestricted_modal_beta_is_false in K; discriminate.
Qed.
Theorem constants_are_not_syntactically_modally_closed G a n : ~ ModallyClosed (@LCon G a n).
Proof. intro H; inversion H. Qed.

Theorem current_index_equality_cannot_be_replaced_under_up B FE :
  let M := modal_test_model B FE in let sigma := modal_test_assignment B FE in
  lval M (LEq (@LCon [] t 0) lfalse) (il_empty M) sigma false = true /\
  lval M (LEq (LUp (@LCon [] t 0)) (LUp lfalse)) (il_empty M) sigma false = false.
Proof.
  cbn zeta; split.
  - apply lval_eq_true; rewrite lval_false; reflexivity.
  - change (truth B ((fun j : bool => j) =
      (fun j => lval (modal_test_model B FE) lfalse (il_empty _) (modal_test_assignment B FE) j)) = false).
    destruct (truth B _) eqn:H; auto.
    apply (proj1 (truth_spec B _)) in H; apply (f_equal (fun f => f true)) in H.
    rewrite lval_false in H; discriminate.
Qed.

Theorem axiom_five_cannot_accept_arbitrary_intension_terms B FE :
  let M := modal_test_model B FE in
  lval M (il_axiom5 (@LCon [] (intens t) 0) (LUp lfalse))
    (il_empty M) (modal_test_assignment B FE) false = false.
Proof.
  cbn zeta.
  change (truth B (lval (modal_test_model B FE)
    (lbox (LEq (LDown (@LCon [] (intens t) 0)) (LDown (LUp lfalse))))
      (il_empty _) (modal_test_assignment B FE) false =
    lval (modal_test_model B FE) (LEq (@LCon [] (intens t) 0) (LUp lfalse))
      (il_empty _) (modal_test_assignment B FE) false) = false).
  assert (L : lval (modal_test_model B FE)
    (lbox (LEq (LDown (@LCon [] (intens t) 0)) (LDown (LUp lfalse))))
      (il_empty _) (modal_test_assignment B FE) false = true).
  { rewrite lval_box; apply (proj2 (truth_spec B _)); intro j; apply lval_eq_true.
    change (xorb j j = lval (modal_test_model B FE) lfalse (il_empty _) (modal_test_assignment B FE) j).
    rewrite lval_false; destruct j; reflexivity. }
  assert (R : lval (modal_test_model B FE) (LEq (@LCon [] (intens t) 0) (LUp lfalse))
      (il_empty _) (modal_test_assignment B FE) false = false).
  { change (truth B ((fun j : bool => j) =
      (fun j => lval (modal_test_model B FE) lfalse (il_empty _) (modal_test_assignment B FE) j)) = false).
    destruct (truth B _) eqn:H; auto.
    apply (proj1 (truth_spec B _)) in H; apply (f_equal (fun f => f true)) in H.
    rewrite lval_false in H; discriminate. }
  rewrite L, R, boolean_equality; reflexivity.
Qed.

Theorem il_no_derivation_of_false (B : BooleanTruth) (FE : FunExt) G : ILDerivation (@lfalse G) -> False.
Proof.
  intro H.
  pose (rho := fun a (_ : var G a) => plain_value a).
  pose proof (il_derivations_sound (modal_test_assignment B FE) H rho false) as K.
  rewrite lval_false in K; discriminate.
Qed.
Example beta_exchange_does_not_capture G :
  lrename (@LVar (t :: t :: G) t (vs vz)) lswap = @LVar (t :: t :: G) t vz.
Proof. reflexivity. Qed.
