(* A paired-model inference suite. These are familiar validity/countermodel
   patterns, not claims of newly discovered linguistic results. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Models Calculus BooleanModels BooleanFinite
  Ty2Syntax Ty2Models Ty2Calculus.
From MontagueLegacy Require Import IndexSyntax IndexModels ObservationBridge.
Import ListNotations.
Set Implicit Arguments.

Inductive observed_word : wty -> Type :=
| OJohn : observed_word we
| OMan : observed_word (warr we wt)
| OWalk : observed_word (warr we wt)
| OMove : observed_word (warr we wt)
| OWeather : observed_word (warr ws wt)
| OConcept : observed_word (warr ws we)
| OActual : observed_word ws
| OAlternative : observed_word ws.

Record observation_tables := {
  men : bool -> bool;
  walkers : bool -> bool;
  movers : bool -> bool;
  weather_at : bool -> bool;
  concept_at : bool -> bool
}.
Definition paired_bool_model (FE : FunExt) (F : observation_tables) : wmodel observed_word :=
  world_finite_model FE finite_bool finite_bool
    (fun a c => match c in observed_word a return wdomain bool bool a with
    | OJohn => true | OMan => men F | OWalk => walkers F | OMove => movers F
    | OWeather => weather_at F | OConcept => concept_at F
    | OActual => true | OAlternative => false
    end).

Inductive observed_target : pty -> Type :=
| ObservedConstant : forall a, observed_word a -> observed_target (observation_type a).
Definition observed_constants a (c : observed_word a) := ObservedConstant c.
Definition paired_prop_lex (F : observation_tables) a (c : observed_target a) : pdomain bool bool unit a :=
  match c in observed_target a return pdomain bool bool unit a with
  | @ObservedConstant a c =>
    match c in observed_word a return pdomain bool bool unit (observation_type a) with
    | OJohn => true | OMan => fun x => men F x = true
    | OWalk => fun x => walkers F x = true | OMove => fun x => movers F x = true
    | OWeather => fun w => weather_at F w = true | OConcept => concept_at F
    | OActual => true | OAlternative => false
    end
  end.
Definition no_time_order (_ _ : unit) : Prop := False.

Lemma paired_lexical_relation (FE : FunExt) (F : observation_tables) : forall a (c : observed_word a),
  @observation_relation bool bool unit a
    (@paired_prop_lex F _ (@observed_constants a c)) (wlexical (paired_bool_model FE F) a c).
Proof. intros a c; destruct c; cbn; try reflexivity; intros x y E; subst; reflexivity. Qed.

Definition observed_pempty : @penv bool bool unit [] :=
  fun a v => match v in pvar G a return
    match G with [] => pdomain bool bool unit a | _ :: _ => unit end
    with pz => tt | pvs _ => tt end.
Definition observed_bempty (FE : FunExt) F : wenv (paired_bool_model FE F) [] :=
  fun a v => match v in wvar G a return
    match G with [] => wdomain bool bool a | _ :: _ => unit end
    with wz => tt | wvs _ => tt end.
Lemma paired_empty_assignments (FE : FunExt) F :
  @observation_envs observed_word (paired_bool_model FE F) unit [] observed_pempty (observed_bempty FE F).
Proof. intros a v; inversion v. Qed.

Definition proposition_value F {G} (p : wtm observed_word G wt)
  (rho : @penv bool bool unit (map observation_type G)) :=
  peval (@paired_prop_lex F) no_time_order (observation_term observed_constants p) rho.
Definition boolean_value FE F {G} (p : wtm observed_word G wt) rho := weval (paired_bool_model FE F) p rho.
Definition paired_proposition F (p : wtm observed_word [] wt) := proposition_value F p observed_pempty.
Definition paired_boolean FE F (p : wtm observed_word [] wt) := @boolean_value FE F [] p (observed_bempty FE F).

Theorem paired_formula_agreement FE F (p : wtm observed_word [] wt) : observable p ->
  paired_proposition F p <-> paired_boolean FE F p = true.
Proof.
  intro H; exact (observation_truth (M:=paired_bool_model FE F) (T:=unit)
    observed_constants (@paired_prop_lex F) no_time_order
    (paired_lexical_relation FE F) H (paired_empty_assignments FE F)).
Qed.

Definition ojohn {G} : wtm observed_word G we := WConst OJohn.
Definition oman {G} : wtm observed_word G (warr we wt) := WConst OMan.
Definition owalk {G} : wtm observed_word G (warr we wt) := WConst OWalk.
Definition omove {G} : wtm observed_word G (warr we wt) := WConst OMove.
Definition oweather {G} : wtm observed_word G (warr ws wt) := WConst OWeather.
Definition oconcept {G} : wtm observed_word G (warr ws we) := WConst OConcept.
Definition oactual {G} : wtm observed_word G ws := WConst OActual.
Definition oalternative {G} : wtm observed_word G ws := WConst OAlternative.
Definition oman_john {G} : wtm observed_word G wt := WApp oman ojohn.
Definition owalk_john {G} : wtm observed_word G wt := WApp owalk ojohn.
Definition every_man_walks_o {G} : wtm observed_word G wt :=
  WAll (WImp (WApp oman (WVar wz)) (WApp owalk (WVar wz))).
Definition every_walker_moves_o {G} : wtm observed_word G wt :=
  WAll (WImp (WApp owalk (WVar wz)) (WApp omove (WVar wz))).
Definition every_man_moves_o {G} : wtm observed_word G wt :=
  WAll (WImp (WApp oman (WVar wz)) (WApp omove (WVar wz))).
Definition weather_actual_o {G} : wtm observed_word G wt := WApp oweather oactual.
Definition weather_necessary_o {G} : wtm observed_word G wt := necessarily oweather.
Definition rigid_person_o {G} : wtm observed_word G (warr ws we) := WLam ojohn.
Definition rigid_man_o {G} : wtm observed_word G (warr ws wt) :=
  WLam (WApp oman (WApp rigid_person_o (WVar wz))).
Definition flexible_man_o {G} : wtm observed_word G (warr ws wt) :=
  WLam (WApp oman (WApp oconcept (WVar wz))).

Ltac observation_certificate :=
  unfold every_man_walks_o, every_walker_moves_o, every_man_moves_o,
    oman_john, owalk_john, weather_actual_o, weather_necessary_o,
    rigid_man_o, flexible_man_o, rigid_person_o, necessarily,
    oman, owalk, omove, ojohn, oweather, oconcept, oactual, oalternative;
  cbn [wweaken wrename wlift_ren];
  repeat first [apply observe_false | apply observe_var | apply observe_const |
    apply observe_lam | apply observe_app | apply observe_imp |
    apply observe_all | apply observe_entities | apply observe_worlds].

Example inference_suite_is_certified :
  observable (@every_man_walks_o []) /\ observable (@every_walker_moves_o []) /\
  observable (@every_man_moves_o []) /\ observable (@oman_john []) /\
  observable (@owalk_john []) /\ observable (@weather_actual_o []) /\
  observable (@weather_necessary_o []) /\ observable (necessarily (@rigid_man_o [])) /\
  observable (necessarily (@flexible_man_o [])).
Proof. repeat split; observation_certificate. Qed.

Theorem observed_instantiation_derivation :
  wderives constructive [@every_man_walks_o []; oman_john] owalk_john.
Proof.
  apply wd_imp_elim with (p:=oman_john).
  - change (wderives constructive [@every_man_walks_o []; oman_john]
      (winstantiate ojohn (WImp (WApp oman (WVar wz)) (WApp owalk (WVar wz))))).
    apply wd_all_elim; apply wd_assume; cbn; auto.
  - apply wd_assume; cbn; auto.
Qed.

Theorem observed_syllogism_derivation :
  wderives constructive [@every_man_walks_o []; every_walker_moves_o] every_man_moves_o.
Proof.
  apply wd_all_intro; apply wd_imp_intro.
  apply wd_imp_elim with (p:=WApp owalk (WVar wz)).
  - lazymatch goal with |- wderives _ ?Hs _ =>
      change (wderives constructive Hs
        (winstantiate (@WVar observed_word [we] we wz)
          (WImp (WApp owalk (WVar wz)) (WApp omove (WVar wz))))) end.
    apply wd_all_elim; apply wd_assume; cbn; auto.
  - apply wd_imp_elim with (p:=WApp oman (WVar wz)).
    + lazymatch goal with |- wderives _ ?Hs _ =>
        change (wderives constructive Hs
          (winstantiate (@WVar observed_word [we] we wz)
            (WImp (WApp oman (WVar wz)) (WApp owalk (WVar wz))))) end.
      apply wd_all_elim; apply wd_assume; cbn; auto.
    + apply wd_assume; cbn; auto.
Qed.

Theorem observed_necessity_elimination_derivation :
  wderives constructive [@weather_necessary_o []] weather_actual_o.
Proof.
  change (wderives constructive [@weather_necessary_o []]
    (winstantiate oactual (WApp oweather (WVar wz)))).
  apply wd_all_elim; apply wd_assume; cbn; auto.
Qed.

Theorem paired_derivation_transfer (FE : FunExt) F (premises : list (wtm observed_word [] wt)) q L :
  Forall (@observable observed_word [] wt) premises -> observable q -> wderives L premises q ->
  (forall p, In p premises -> paired_proposition F p) -> paired_proposition F q.
Proof.
  intros Ps Q D; exact (observable_derivation_prop_sound (M:=paired_bool_model FE F) (T:=unit) observed_constants
    (@paired_prop_lex F) no_time_order (paired_lexical_relation FE F) FE
    Ps Q D (paired_empty_assignments FE F)).
Qed.

Theorem instantiation_agrees_for_all_tables FE F :
  (paired_proposition F every_man_walks_o -> paired_proposition F oman_john -> paired_proposition F owalk_john) /\
  (paired_boolean FE F every_man_walks_o = true -> paired_boolean FE F oman_john = true ->
   paired_boolean FE F owalk_john = true).
Proof.
  split; intros A B.
  - eapply (paired_derivation_transfer FE); [| |exact observed_instantiation_derivation|].
    + repeat constructor; observation_certificate.
    + observation_certificate.
    + intros p [E | [E | []]]; subst; assumption.
  - apply (world_derivation_sound FE observed_instantiation_derivation
      (M:=paired_bool_model FE F) (rho:=observed_bempty FE F)).
    intros p [E | [E | []]]; subst; assumption.
Qed.

Theorem syllogism_agrees_for_all_tables FE F :
  (paired_proposition F every_man_walks_o -> paired_proposition F every_walker_moves_o ->
    paired_proposition F every_man_moves_o) /\
  (paired_boolean FE F every_man_walks_o = true -> paired_boolean FE F every_walker_moves_o = true ->
    paired_boolean FE F every_man_moves_o = true).
Proof.
  split; intros A B.
  - eapply (paired_derivation_transfer FE); [| |exact observed_syllogism_derivation|].
    + repeat constructor; observation_certificate.
    + observation_certificate.
    + intros p [E | [E | []]]; subst; assumption.
  - apply (world_derivation_sound FE observed_syllogism_derivation
      (M:=paired_bool_model FE F) (rho:=observed_bempty FE F)).
    intros p [E | [E | []]]; subst; assumption.
Qed.

Theorem necessity_elimination_agrees_for_all_tables FE F :
  (paired_proposition F weather_necessary_o -> paired_proposition F weather_actual_o) /\
  (paired_boolean FE F weather_necessary_o = true -> paired_boolean FE F weather_actual_o = true).
Proof.
  split; intro A.
  - eapply (paired_derivation_transfer FE); [| |exact observed_necessity_elimination_derivation|].
    + repeat constructor; observation_certificate.
    + observation_certificate.
    + intros p [E | []]; subst; assumption.
  - apply (world_derivation_sound FE observed_necessity_elimination_derivation
      (M:=paired_bool_model FE F) (rho:=observed_bempty FE F)).
    intros p [E | []]; subst; assumption.
Qed.

Definition empty_people_tables : observation_tables :=
  {| men := fun _ => false; walkers := fun _ => false; movers := fun _ => false;
     weather_at := fun w => w; concept_at := fun w => w |}.
Definition varying_tables : observation_tables :=
  {| men := fun x => x; walkers := fun x => x; movers := fun _ => true;
     weather_at := fun w => w; concept_at := fun w => w |}.

Definition entity_man_body : wtm observed_word [we] wt := WApp oman (WVar wz).
Definition some_man_boolean FE F := existsb
  (fun x => weval (paired_bool_model FE F) entity_man_body
    (wextend (observed_bempty FE F) x)) (values finite_bool).
Definition some_man_proposition F := exists x,
  proposition_value F entity_man_body (pextend observed_pempty x).

Theorem paired_entity_witness_agreement FE F :
  some_man_proposition F <-> some_man_boolean FE F = true.
Proof.
  apply (observation_finite_witnesses (M:=paired_bool_model FE F) (T:=unit)
    observed_constants (@paired_prop_lex F) no_time_order
    (paired_lexical_relation FE F) finite_bool).
  - unfold entity_man_body; observation_certificate.
  - apply paired_empty_assignments.
Qed.

Example universal_has_no_existential_import FE :
  paired_boolean FE empty_people_tables every_man_walks_o = true /\
  some_man_boolean FE empty_people_tables = false /\
  paired_proposition empty_people_tables every_man_walks_o /\
  ~ some_man_proposition empty_people_tables.
Proof.
  split; [reflexivity |]; split; [reflexivity |]; split.
  - apply (proj2 (@paired_formula_agreement FE empty_people_tables every_man_walks_o
      ltac:(observation_certificate))); reflexivity.
  - rewrite (paired_entity_witness_agreement FE); discriminate.
Qed.

Example named_individual_supplies_a_witness FE F :
  (paired_proposition F oman_john -> some_man_proposition F) /\
  (paired_boolean FE F oman_john = true -> some_man_boolean FE F = true).
Proof.
  split; intro H.
  - exists true; exact H.
  - apply existsb_exists; exists true; split; [cbn; auto | exact H].
Qed.

Example actual_truth_does_not_license_necessity FE :
  paired_boolean FE varying_tables weather_actual_o = true /\
  paired_boolean FE varying_tables weather_necessary_o = false /\
  paired_proposition varying_tables weather_actual_o /\
  ~ paired_proposition varying_tables weather_necessary_o.
Proof.
  split; [reflexivity |]; split; [reflexivity |]; split.
  - apply (proj2 (@paired_formula_agreement FE varying_tables weather_actual_o
      ltac:(observation_certificate))); reflexivity.
  - rewrite (@paired_formula_agreement FE varying_tables weather_necessary_o
      ltac:(observation_certificate)); discriminate.
Qed.

Example actual_agreement_does_not_license_necessary_substitution FE :
  weval (paired_bool_model FE varying_tables) (WApp rigid_person_o oactual)
    (observed_bempty FE varying_tables) =
  weval (paired_bool_model FE varying_tables) (WApp oconcept oactual)
    (observed_bempty FE varying_tables) /\
  peval (@paired_prop_lex varying_tables) no_time_order
    (observation_term observed_constants (WApp (@rigid_person_o []) oactual)) observed_pempty =
  peval (@paired_prop_lex varying_tables) no_time_order
    (observation_term observed_constants (WApp (@oconcept []) oactual)) observed_pempty /\
  paired_boolean FE varying_tables (WApp rigid_man_o oactual) = true /\
  paired_boolean FE varying_tables (WApp flexible_man_o oactual) = true /\
  paired_boolean FE varying_tables (necessarily rigid_man_o) = true /\
  paired_boolean FE varying_tables (necessarily flexible_man_o) = false /\
  paired_proposition varying_tables (necessarily rigid_man_o) /\
  ~ paired_proposition varying_tables (necessarily flexible_man_o).
Proof.
  split; [reflexivity |]; split; [reflexivity |];
  split; [reflexivity |]; split; [reflexivity |];
    split; [reflexivity |]; split; [reflexivity |]; split.
  - apply (proj2 (@paired_formula_agreement FE varying_tables (necessarily rigid_man_o)
      ltac:(observation_certificate))); reflexivity.
  - rewrite (@paired_formula_agreement FE varying_tables (necessarily flexible_man_o)
      ltac:(observation_certificate)); discriminate.
Qed.

Example double_negation_agrees_on_reflected_observations (FE : FunExt) F :
  paired_proposition F (wneg (wneg weather_actual_o)) <-> paired_proposition F weather_actual_o.
Proof.
  rewrite (@paired_formula_agreement FE F (wneg (wneg weather_actual_o))
    ltac:(repeat apply observable_negation; observation_certificate)).
  rewrite (@paired_formula_agreement FE F weather_actual_o ltac:(observation_certificate)).
  unfold paired_boolean, boolean_value; rewrite !wneg_value, negb_involutive; reflexivity.
Qed.

Theorem mismatched_lexicons_can_change_the_answer :
  paired_proposition varying_tables oman_john /\ ~ paired_proposition empty_people_tables oman_john.
Proof. split; [reflexivity | discriminate]. Qed.
