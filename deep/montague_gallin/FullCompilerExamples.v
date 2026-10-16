(* Public-interface regressions for the full proof compiler. *)
From Coq Require Import List.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Minimal Calculus Independent
  MinimalCorrespondence Untensed UntensedTranslation UntensedModels ILCore ILCalculus ILCalculusExamples
  ILProofTranslation ILFullProofTranslation ProofDischarge.
Import ListNotations.
Set Implicit Arguments.

Definition nested_scope_formula : ltm [] t :=
  LEq (@LLam [] e (intens e) (LUp (LDown (LUp (LVar vz)))))
    (LLam (LUp (LVar vz))).
Definition nested_scope_source_proof : ILDerivation nested_scope_formula :=
  IL_R4 (IL_R5 (ILByAxiom (IL_AS6 (LVar vz)))).
Definition nested_scope_target_proof : Derivation (il_at nested_scope_formula) :=
  compile_il_proof nested_scope_source_proof.

Definition exchange_formula : ltm [] t :=
  LEq (LApp (LLam (LLam (@LVar [e; e] e (vs vz)))) (LCon 0))
    (LLam (LApp (LLam (LVar vz)) (LCon 0))).
Definition exchange_source_proof : ILDerivation exchange_formula :=
  ILByAxiom (IL_AS45 (LVar (vs vz)) (LCon 0)).
Definition exchange_target_proof : Derivation (il_at exchange_formula) :=
  compile_il_proof exchange_source_proof.

Definition full_compiled_modal_beta : Derivation
  (il_at (LEq (LApp (LLam (LUp (LVar vz))) (@LUp [] t (LCon 0)))
    (LUp (LApp (LLam (LVar vz)) (LUp (LCon 0)))))) :=
  compile_il_proof il_modal_beta_tree.
Definition full_compiled_intension_extensionality : Derivation
  (il_at (il_axiom5 (@LFree [] (intens e) 0) (LFree 1))) :=
  compile_il_proof il_axiom_five_tree.

(* Discharge preserves arbitrary Gamma and the source's finite dependency
   list. The empty-list example supplies a concrete checked proof bundle. *)
Definition source_truth_from_empty : ILFrom (fun _ : ltm [] t => False) ltrue :=
  existT _ [] (Forall_nil _, il_derive_truth).
Definition target_truth_from_empty : Ty2From (compiled_premises (fun _ : ltm [] t => False)) (il_at ltrue) :=
  compile_il_from source_truth_from_empty.

(* Cross-check the explicit-index body against the existing semantic
   correspondence. This is a check on the compiler, not one of its inputs. *)
Theorem il_at_interpretation M sigma G a (p : ltm G a) (rho : il_env M G) i :
  core_standard_eval (il_target M) (il_target_assignment sigma) (il_at p)
    (@value_extend (il_entities M) (il_indices M) (map translate_type G) gs (il_canonical_env rho) i) =
  il_lift (il_entities M) (il_indices M) a (lval M p rho sigma i).
Proof. exact (@untensed_forward_preservation M sigma G a (include_il p) rho i). Qed.

Theorem target_derivation_of_il_body_is_source_valid G (p : ltm G t) (H : Derivation (il_at p))
  M sigma (rho : il_env M G) i : lval M p rho sigma i = true.
Proof.
  pose proof (standard_model_derivation_soundness (il_target M) (il_target_assignment sigma) H
    (@value_extend (il_entities M) (il_indices M) (map translate_type G) gs (il_canonical_env rho) i)) as K.
  change (core_standard_eval (il_target M) (il_target_assignment sigma) (il_at p)
    (@value_extend (il_entities M) (il_indices M) (map translate_type G) gs (il_canonical_env rho) i) = true) in K.
  rewrite il_at_interpretation in K; exact K.
Qed.
Theorem forbidden_modal_beta_has_no_target_derivation (B : BooleanTruth) (FE : FunExt) :
  Derivation (il_at forbidden_modal_beta) -> False.
Proof.
  intro H; pose proof (@target_derivation_of_il_body_is_source_valid [] forbidden_modal_beta H
    (modal_test_model B FE) (modal_test_assignment B FE) (il_empty _) false) as K.
  rewrite unrestricted_modal_beta_is_false in K; discriminate.
Qed.
