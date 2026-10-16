(* Explicit derivation trees and negative semantic checks on the rule R. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Models.
From MontagueGallin Require Import Types Target Minimal Independent Substitution Calculus.
Import ListNotations.
Set Implicit Arguments.

Definition boolean_axiom_proof S P :
  Derivation (@axiom1 S P [garr gt gt] (CVar gz)) :=
  ByAxiom (A1 (ContextVariable gz)).
Definition predicate_axiom_proof S P a :
  Derivation (@axiom2 S P [a; a; garr a gt] a
    (CVar gz) (CVar (gvs gz)) (CVar (gvs (gvs gz)))) :=
  ByAxiom (A2 (ContextVariable gz) (ContextVariable (gvs gz))
    (ContextVariable (gvs (gvs gz)))).
Definition extensionality_axiom_proof S P a b :
  Derivation (@axiom3 S P [garr a b; garr a b] a b (CVar gz) (CVar (gvs gz))) :=
  ByAxiom (A3 (ContextVariable gz) (ContextVariable (gvs gz))).
Definition named_variable_axiom_proof S P G (g : P (garr gt gt)) :
  Derivation (@axiom1 S P G (CFree g)) := ByAxiom (A1 (ParameterVariable g)).

Definition beta_under_lambda_proof S P G a :
  Derivation (CEq
    (@CLam S P G a a (CApp (CLam (CVar gz)) (CVar gz)))
    (CLam (CVar gz))).
Proof.
  exact (@derive_context_congruence S P (a :: G) a G (garr a a) (LambdaBody Hole)
    (CApp (CLam (CVar gz)) (CVar gz)) (CVar gz) (ByAxiom (AS4 (CVar gz) (CVar gz)))).
Defined.

Fixpoint proof_test_value (a : gty) : value_domain bool bool a :=
  match a with
  | ge | gt | gs => false
  | garr a b => fun _ => proof_test_value b
  end.
Definition proof_test_lex (S : gty -> Type) a (_ : S a) := proof_test_value a.
Definition proof_test_env G : value_env bool bool G := fun a _ => proof_test_value a.

(* Relative consistency: requires the stated BooleanTruth and FunExt,
   rather than claiming to construct those foundations inside CIC. *)
Theorem ty2_no_derivation_of_false (B : BooleanTruth) (FE : FunExt) S P G :
  Derivation (@cfalse S P G) -> False.
Proof.
  intro H; pose proof (@ty2_derivations_sound S P bool bool B FE
    (proof_test_lex S) (proof_test_lex P) G cfalse H (@proof_test_env G)) as K.
  rewrite ceval_false in K; discriminate.
Qed.

Definition no_symbols (_ : gty) : Type := Empty_set.
Definition no_valuation a (v : no_symbols a) : value_domain bool bool a := match v with end.
Definition bool_environment (x : bool) : value_env bool bool [gt] :=
  @value_extend bool bool [] gt (value_empty bool bool) x.

Theorem pointwise_equality_cannot_justify_lambda_replacement (B : BooleanTruth) :
  ceval B no_valuation no_valuation (@CVar no_symbols no_symbols [gt] gt gz) (bool_environment true) =
  ceval B no_valuation no_valuation ctrue (bool_environment true) /\
  ceval B no_valuation no_valuation (@CLam no_symbols no_symbols [] gt gt (CVar gz))
    (value_empty bool bool) <>
  ceval B no_valuation no_valuation (@CLam no_symbols no_symbols [] gt gt ctrue)
    (value_empty bool bool).
Proof.
  split.
  - symmetry; apply ceval_true.
  - intro H; apply (f_equal (fun f => f false)) in H.
    change (false = ceval B no_valuation no_valuation ctrue (bool_environment false)) in H.
    rewrite ceval_true in H; discriminate.
Qed.
Theorem pointwise_true_equation_has_no_derivation (B : BooleanTruth) (FE : FunExt) :
  Derivation (@CEq no_symbols no_symbols [gt] gt (CVar gz) ctrue) -> False.
Proof.
  intro H; pose proof (@ty2_derivations_sound no_symbols no_symbols bool bool B FE
    no_valuation no_valuation [gt] (CEq (CVar gz) ctrue) H (bool_environment false)) as K.
  change (truth B (false = ceval B no_valuation no_valuation ctrue (bool_environment false)) = true) in K.
  apply (proj1 (truth_spec B _)) in K; rewrite ceval_true in K; discriminate.
Qed.

Theorem capture_changes_beta_prediction (B : BooleanTruth) :
  ceval B no_valuation no_valuation
    (subst0 (@CLam no_symbols no_symbols [gt; gt] gt gt (CVar (gvs gz))) (CVar gz))
    (bool_environment false) true = false /\
  ceval B no_valuation no_valuation (@CLam no_symbols no_symbols [gt] gt gt (CVar gz))
    (bool_environment false) true = true.
Proof. split; reflexivity. Qed.
