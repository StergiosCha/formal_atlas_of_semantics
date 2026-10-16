(* Actual finite Boolean models and computation/derivation regression cases.
   General proofs take FunExt explicitly. Finite quantifiers use no global
   excluded middle, ClassicalDecision or choice operator. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Syntax Models Calculus Examples
  BooleanModels BooleanFinite BooleanEquality.
Import ListNotations.
Set Implicit Arguments.

Definition bempty_env {symbol} (M : bmodel symbol) : benv M [] :=
  fun a v => match v in var G a return
    match G with [] => bdomain (bindividuals M) a | _ :: _ => unit end
    with vz => tt | vs _ => tt end.

Definition bool_no_men (FE : FunExt) : bmodel word :=
  finite_model FE finite_unit
    (fun a w => match w in word a return bdomain unit a with
     | John => tt
     | Man => fun _ => false
     | Walk => fun _ => true
     | Move => fun _ => true
     end).

Definition bool_all_men (FE : FunExt) : bmodel word :=
  finite_model FE finite_unit
    (fun a w => match w in word a return bdomain unit a with
     | John => tt
     | Man => fun _ => true
     | Walk => fun _ => true
     | Move => fun _ => true
     end).

Definition bool_two_people (FE : FunExt) : bmodel word :=
  finite_model FE finite_bool
    (fun a w => match w in word a return bdomain bool a with
     | John => true
     | Man => fun x => x
     | Walk => fun _ => true
     | Move => fun _ => true
     end).

Example boolean_no_men_countermodel (FE : FunExt) :
  beval (bool_no_men FE) (@every_man_walks []) (bempty_env _) = true /\
  beval (bool_no_men FE) (@a_man_walks []) (bempty_env _) = false.
Proof. split; reflexivity. Qed.

Example boolean_generalization_countermodel (FE : FunExt) :
  beval (bool_two_people FE) (@man_john []) (bempty_env _) = true /\
  beval (bool_two_people FE) (@All word [] entity (App man (Var vz))) (bempty_env _) = false.
Proof. split; reflexivity. Qed.

Example boolean_lexical_variation (FE : FunExt) :
  beval (bool_all_men FE) (@man_john []) (bempty_env _) = true /\
  beval (bool_no_men FE) (@man_john []) (bempty_env _) = false.
Proof. split; reflexivity. Qed.

Theorem boolean_no_existential_import (FE : FunExt) : forall L,
  ~ derives L [@every_man_walks []] a_man_walks.
Proof.
  intro L; apply (boolean_countermodel_blocks_derivation FE
    (M:=bool_no_men FE) (rho:=bempty_env _)).
  - intros p [E | E]; [subst; reflexivity | contradiction].
  - reflexivity.
Qed.

Theorem boolean_no_generalization_from_one_name (FE : FunExt) : forall L,
  ~ derives L [@man_john []] (All (App man (Var vz))).
Proof.
  intro L; apply (boolean_countermodel_blocks_derivation FE
    (M:=bool_two_people FE) (rho:=bempty_env _)).
  - intros p [E | E]; [subst; reflexivity | contradiction].
  - reflexivity.
Qed.

Theorem boolean_john_walks_consequence (FE : FunExt) :
  bconsequence [@man_john []; every_man_walks] walk_john.
Proof. apply constructive_boolean_sound; [exact FE | exact john_walks_derivation]. Qed.

Theorem boolean_syllogism_consequence (FE : FunExt) :
  bconsequence [@every_man_walks []; every_walker_moves] every_man_moves.
Proof.
  apply classical_boolean_sound; [exact FE |].
  apply constructive_in_classical; exact syllogism_derivation.
Qed.

Theorem boolean_existential_consequence (FE : FunExt) :
  bconsequence [@man_john []; walk_john] a_man_walks.
Proof. apply constructive_boolean_sound; [exact FE | exact existential_derivation]. Qed.

Theorem boolean_double_negation_consequence (FE : FunExt) :
  bconsequence [neg (neg (@man_john []))] man_john.
Proof.
  apply classical_boolean_sound; [exact FE | exact classical_double_negation_derivation].
Qed.

Example four_individual_predicates (FE : FunExt) :
  length (values (finite_domain FE finite_bool (arrow entity truth))) = 4.
Proof. reflexivity. Qed.

Example sixteen_predicates_of_predicates (FE : FunExt) :
  length (values (finite_domain FE finite_bool (arrow (arrow entity truth) truth))) = 16.
Proof. reflexivity. Qed.

Definition all_predicates_hold_of_john : tm word [] truth :=
  All (App (Var vz) john).

Example higher_order_quantification_checks_all_functions (FE : FunExt) :
  beval (bool_two_people FE) all_predicates_hold_of_john (bempty_env _) = false.
Proof. reflexivity. Qed.

Example finite_function_equality_reflects_denotation (FE : FunExt) :
  beval (bool_two_people FE) (leibniz_equal (@walk []) move) (bempty_env _) = true.
Proof.
  apply finite_leibniz_equality; reflexivity.
Qed.

Example distinct_predicates_are_not_equal (FE : FunExt) :
  beval (bool_two_people FE) (leibniz_equal (@man []) walk) (bempty_env _) = false.
Proof. reflexivity. Qed.

(* A named infinite-domain instance exists under an explicit data-valued
   decision principle. This construction is not advertised as executable. *)
Definition natural_number_model (CD : ClassicalDecision) : bmodel word :=
  decision_model CD (inhabits 0)
    (fun a w => match w in word a return bdomain nat a with
     | John => 0
     | Man => fun _ => false
     | Walk => fun _ => true
     | Move => fun _ => true
     end).

Example decision_model_quantifier_correct (CD : ClassicalDecision) (p : nat -> bool) :
  bforall (bquantifiers (natural_number_model CD)) entity p = true <->
  forall n, p n = true.
Proof. apply bforall_spec. Qed.
