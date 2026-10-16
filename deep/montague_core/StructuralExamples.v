(* Regression fixtures for structural transformations and context placement.
   These are tests of our calculus, not new empirical claims about English. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax Algebra Calculus Structural Contexts Examples.
Import ListNotations.
Set Implicit Arguments.

Definition man_x : tm word [entity] truth := App man (Var vz).
Definition x_is_man : mixed word [entity] :=
  context_true (context_var entity context_empty) man_x.

Example interleaved_fresh_variable :
  mixed_derives constructive x_is_man
    (All (@App word [entity; entity] entity truth man (Var (vs vz)))).
Proof.
  apply m_all_intro; apply m_assume.
  change (lookup (context_var entity x_is_man) (weaken man_x)).
  apply lookup_var; apply lookup_here.
Qed.

Example split_fresh_variable :
  derives constructive [man_x]
    (All (@App word [entity; entity] entity truth man (Var (vs vz)))).
Proof. exact (mixed_to_split interleaved_fresh_variable). Qed.

(* The older free variable is replaced; the newer bound variable is not. *)
Example substitute_beneath_generalization :
  derives constructive [@man_john []] (All (@man_john [entity])).
Proof.
  exact (derivation_instantiation john split_fresh_variable).
Qed.

Example weaken_open_derivation :
  derives constructive [@App word [truth; entity] entity truth man (Var (vs vz))]
    (All (@App word [entity; truth; entity] entity truth man (Var (vs (vs vz))))).
Proof. exact (derivation_weakening truth split_fresh_variable). Qed.

Example substitute_conversion_derivation :
  derives constructive [@walk_john []]
    (App walk (App (Lam (Var vz)) john)).
Proof.
  assert (D : derives constructive [@App word [entity] entity truth walk (Var vz)]
    (App walk (App (Lam (Var vz)) (Var vz)))).
  { eapply d_conversion with (p := App walk (Var vz)).
    - apply d_assume; cbn; auto.
    - apply beta_app; [apply beta_refl | apply beta_sym; apply beta_step]. }
  exact (derivation_instantiation john D).
Qed.

Example classical_rule_survives_substitution :
  derives classical [neg (neg (@man_john []))] man_john.
Proof.
  assert (D : derives classical [neg (neg man_x)] man_x).
  { apply d_double_negation; [reflexivity | apply d_assume; cbn; auto]. }
  exact (derivation_instantiation john D).
Qed.

Example beta_substitution_beneath_binder :
  beta
    (@Lam word [entity] entity entity
      (App (Lam (Var (vs (vs vz)))) (Var vz)))
    (@Lam word [entity] entity entity (Var (vs vz))).
Proof.
  pose proof (beta_substitution
    (beta_lam (@beta_step word [entity; entity; entity] entity entity
      (Var (vs (vs vz))) (Var vz)))
    (@head_sub word [entity] entity (Var vz))) as B.
  exact B.
Qed.

Definition before_variable : mixed word [entity] :=
  context_var entity (context_true context_empty (@man_john [])).
Definition after_variable : mixed word [entity] :=
  context_true (context_var entity context_empty) (@man_john [entity]).

Example same_flattening : hypotheses before_variable = hypotheses after_variable.
Proof. reflexivity. Qed.

Example different_interleavings : before_variable <> after_variable.
Proof. discriminate. Qed.

Example round_trip_preserves_judgment : forall L (p : tm word [entity] truth),
  mixed_derives L before_variable p <-> mixed_derives L after_variable p.
Proof. intros; rewrite !mixed_split_equivalence; reflexivity. Qed.
