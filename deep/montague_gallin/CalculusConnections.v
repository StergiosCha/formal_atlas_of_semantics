(* Object-language Ty2 derivations imply semantic validity of the actual
   translated IL formulas. This is not an IL-to-Ty2 proof translation. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Minimal Independent MinimalCorrespondence
  Untensed UntensedTranslation UntensedModels Substitution Calculus.
Import ListNotations.
Set Implicit Arguments.

(* Apply the s -> t translation to an explicitly scoped index variable. *)
Definition il_proof_formula (p : il_formula) : ctm source_symbol source_parameter [gs] gt :=
  CApp (cweaken (il_minimal_translate p)) (CVar gz).

Lemma il_proof_formula_interpretation N theta (p : il_formula) i :
  core_standard_eval N theta (il_proof_formula p)
    (@value_extend (standard_entities N) (standard_indices N) [] gs
      (value_empty (standard_entities N) (standard_indices N)) i) =
  core_standard_eval N theta (il_minimal_translate p)
    (value_empty (standard_entities N) (standard_indices N)) i.
Proof.
  unfold core_standard_eval, il_proof_formula; cbn [ceval].
  rewrite ceval_weaken by exact (standard_extensionality N); reflexivity.
Qed.
Theorem derived_il_translation_is_valid (p : il_formula) :
  Derivation (il_proof_formula p) -> il_standard_consequence (fun _ => False) p.
Proof.
  intro H; apply (proj2 (untensed_standard_validity p)).
  intros N theta i HP.
  rewrite <- il_proof_formula_interpretation.
  apply standard_model_derivation_soundness; exact H.
Qed.

(* A concrete proof object for a translated IL formula, not just a Coq
   proof of its semantic value. Beta expansion and reflexivity are derived
   from AS4 and R, and do not add inference constructors. *)
Definition il_constant_reflexivity : il_formula := IEq (@ICon [] e 0) (ICon 0).
Definition il_constant_reflexivity_proof : Derivation (il_proof_formula il_constant_reflexivity).
Proof.
  change (@Derivation source_symbol source_parameter [gs] (CApp
    (CLam (CEq (CApp (CCon (IndexedConstant e 0)) (CVar gz))
               (CApp (CCon (IndexedConstant e 0)) (CVar gz))))
    (CVar gz))).
  apply derive_beta_expansion; apply derive_reflexivity.
Defined.
Theorem il_reflexivity_via_object_proof :
  il_standard_consequence (fun _ => False) il_constant_reflexivity.
Proof. apply derived_il_translation_is_valid; exact il_constant_reflexivity_proof. Qed.
