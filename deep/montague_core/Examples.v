(* Source-style inference fixtures. These are object-language derivations,
   not a natural-language parser, empirical gold labels or novelty claims. *)
From Coq Require Import List.
From MontagueProof Require Import Syntax Models Calculus.
Import ListNotations.
Set Implicit Arguments.

Inductive word : ty -> Type :=
| John : word entity
| Man : word (arrow entity truth)
| Walk : word (arrow entity truth)
| Move : word (arrow entity truth).

Definition john {G} : tm word G entity := Const John.
Definition man {G} : tm word G (arrow entity truth) := Const Man.
Definition walk {G} : tm word G (arrow entity truth) := Const Walk.
Definition move {G} : tm word G (arrow entity truth) := Const Move.
Definition man_john {G} := @App word G entity truth man john.
Definition walk_john {G} := @App word G entity truth walk john.
Definition every_man_walks {G} : tm word G truth :=
  All (Imp (App man (Var vz)) (App walk (Var vz))).
Definition every_walker_moves {G} : tm word G truth :=
  All (Imp (App walk (Var vz)) (App move (Var vz))).
Definition every_man_moves {G} : tm word G truth :=
  All (Imp (App man (Var vz)) (App move (Var vz))).
Definition a_man_walks {G} : tm word G truth :=
  exists_ (conj (App man (Var vz)) (App walk (Var vz))).

Example john_walks_derivation :
  derives constructive [@man_john []; every_man_walks] walk_john.
Proof.
  eapply d_imp_elim with (p := man_john).
  - change (derives constructive [@man_john []; every_man_walks]
      (instantiate john (Imp (App man (Var vz)) (App walk (Var vz))))).
    apply d_all_elim; apply d_assume; cbn; auto.
  - apply d_assume; cbn; auto.
Qed.

Example syllogism_derivation :
  derives constructive [@every_man_walks []; every_walker_moves] every_man_moves.
Proof.
  apply d_all_intro; apply d_imp_intro.
  eapply d_imp_elim with (p := App walk (Var vz)).
  - change (derives constructive
      [@App word [entity] entity truth man (Var vz); every_man_walks; every_walker_moves]
      (instantiate (Var vz) (Imp (App walk (Var vz)) (App move (Var vz))))).
    apply d_all_elim; apply d_assume; cbn; auto.
  - eapply d_imp_elim with (p := App man (Var vz)).
    + change (derives constructive
        [@App word [entity] entity truth man (Var vz); every_man_walks; every_walker_moves]
        (instantiate (Var vz) (Imp (App man (Var vz)) (App walk (Var vz))))).
      apply d_all_elim; apply d_assume; cbn; auto.
    + apply d_assume; cbn; auto.
Qed.

Example existential_derivation :
  derives constructive [@man_john []; walk_john] a_man_walks.
Proof.
  unfold a_man_walks, exists_; apply d_all_intro; apply d_imp_intro.
  eapply d_imp_elim with (p := conj man_john walk_john).
  - change (derives constructive
      [@All word [truth] entity (Imp (conj (App man (Var vz)) (App walk (Var vz))) (Var (vs vz)));
       man_john; walk_john]
      (instantiate john (Imp (conj (App man (Var vz)) (App walk (Var vz)))
                             (Var (vs vz))))).
    apply d_all_elim; apply d_assume; cbn; auto.
  - unfold conj; apply d_all_intro; apply d_imp_intro.
    eapply d_imp_elim with (p := walk_john).
    + eapply d_imp_elim with (p := man_john).
      * apply d_assume; cbn; auto.
      * apply d_assume; cbn; auto.
    + apply d_assume; cbn; auto.
Qed.

Example classical_double_negation_derivation :
  derives classical [neg (neg (@man_john []))] man_john.
Proof.
  apply d_double_negation; [reflexivity | apply d_assume; cbn; auto].
Qed.

(* Actual syntactic conversion: (lambda x.x) John beta-converts to John. *)
Example beta_conversion_derivation :
  derives constructive [@walk_john []]
    (App walk (App (Lam (Var vz)) john)).
Proof.
  eapply d_conversion with (p := walk_john).
  - apply d_assume; cbn; auto.
  - apply beta_app; [apply beta_refl |].
    apply beta_sym; apply beta_step.
Qed.

Example substitution_avoids_capture :
  instantiate (@Var word [entity] entity vz)
    (@Lam word [entity; entity] entity entity (Var (vs vz))) =
  @Lam word [entity] entity entity (Var (vs vz)).
Proof. reflexivity. Qed.

Definition empty_env (M : model word) : env M [] :=
  fun a v => match v in var G a return
    match G with [] => domain (individuals M) a | _ :: _ => unit end
    with vz => tt | vs _ => tt end.

Definition no_men : model word :=
  {| individuals := unit;
     individuals_nonempty := inhabits tt;
     lexical := fun a w => match w in word a return domain unit a with
       | John => tt
       | Man => fun _ => False
       | Walk => fun _ => True
       | Move => fun _ => True
       end |}.

(* Nonempty entity domain, empty noun extension. Universal statements do not
   introduce a noun inhabitant. The countermodel is fully instantiated. *)
Example no_men_countermodel :
  eval no_men (@every_man_walks []) (empty_env no_men) /\
  ~ eval no_men (@a_man_walks []) (empty_env no_men).
Proof.
  split; cbn.
  - intros; exact I.
  - intro H; apply (H False). intros x HC.
    apply (HC False); intros HM _; exact HM.
Qed.

Theorem no_existential_import (FE : FunExt) :
  ~ derives constructive [@every_man_walks []] a_man_walks.
Proof.
  apply (countermodel_blocks_derivation FE (M:=no_men) (rho:=empty_env no_men)).
  - intros E; discriminate E.
  - intros p [E | E]; [subst; exact (proj1 no_men_countermodel) | contradiction].
  - exact (proj2 no_men_countermodel).
Qed.

Theorem john_walks_in_all_models (FE : FunExt) :
  consequence [@man_john []; every_man_walks] walk_john.
Proof. apply constructive_sound; [exact FE | exact john_walks_derivation]. Qed.

Theorem syllogism_in_all_models (FE : FunExt) :
  consequence [@every_man_walks []; every_walker_moves] every_man_moves.
Proof. apply constructive_sound; [exact FE | exact syllogism_derivation]. Qed.

Theorem existential_in_all_models (FE : FunExt) :
  consequence [@man_john []; walk_john] a_man_walks.
Proof. apply constructive_sound; [exact FE | exact existential_derivation]. Qed.

(* Models really vary: this is not evaluation in one frozen interpretation. *)
Definition all_men : model word :=
  {| individuals := unit;
     individuals_nonempty := inhabits tt;
     lexical := fun a w => match w in word a return domain unit a with
       | John => tt
       | Man => fun _ => True
       | Walk => fun _ => True
       | Move => fun _ => True
       end |}.

Example lexical_model_variation :
  eval all_men (@man_john []) (empty_env all_men) /\
  ~ eval no_men (@man_john []) (empty_env no_men).
Proof. cbn; auto. Qed.

Definition two_people : model word :=
  {| individuals := bool;
     individuals_nonempty := inhabits true;
     lexical := fun a w => match w in word a return domain bool a with
       | John => true
       | Man => fun x => x = true
       | Walk => fun _ => True
       | Move => fun _ => True
       end |}.

Example generalization_countermodel :
  eval two_people (@man_john []) (empty_env two_people) /\
  ~ eval two_people (@All word [] entity (App man (Var vz))) (empty_env two_people).
Proof.
  cbn; split; [reflexivity |]. intro H; specialize (H false); discriminate H.
Qed.

Theorem no_generalization_from_one_name (FE : FunExt) :
  ~ derives constructive [@man_john []] (All (App man (Var vz))).
Proof.
  apply (countermodel_blocks_derivation FE (M:=two_people) (rho:=empty_env two_people)).
  - intros E; discriminate E.
  - intros p [E | E]; [subst; exact (proj1 generalization_countermodel) | contradiction].
  - exact (proj2 generalization_countermodel).
Qed.
