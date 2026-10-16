(* Nonvacuity and source-directed counterexamples. The full Boolean model
   is constructed under explicit BooleanTruth and FunExt inputs; it is not
   an executable decision procedure for arbitrary higher-order truth. *)
From Coq Require Import List Bool Arith.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning Postulates.
Import ListNotations.
Set Implicit Arguments.

Definition two_times : frame.
Proof.
  refine {| entity := bool; world := unit; time := bool;
    entity_nonempty := inhabits false; world_nonempty := inhabits tt;
    time_nonempty := inhabits false;
    time_le := fun x y => x = false \/ y = true |}.
  - intros []; auto.
  - intros [] [] []; intuition discriminate.
  - intros [] []; intuition discriminate.
  - intros [] []; auto.
Defined.

Fixpoint zero_value a : domain two_times a :=
  match a with
  | e => false | t => false
  | arr a b => fun _ => zero_value b
  | intens a => fun _ => zero_value a
  end.
Definition temperature_concept (i : index two_times) : bool := snd i.
Definition carry {a b} (H : a = b) (v : domain two_times a) : domain two_times b :=
  match H with eq_refl => v end.

Definition sample_constants (B : BooleanTruth) a n (i : index two_times) : domain two_times a :=
  match ty_eq_dec t a with
  | left H => carry H (negb (snd i))
  | right _ => match ty_eq_dec ivty a with
    | left H => carry H (fun x =>
        if (Nat.eqb n 3 || Nat.eqb n 12)%bool
        then truth B (x = temperature_concept) else false)
    | right _ => match ty_eq_dec (category_type TV) a with
      | left H => carry H (fun Q x =>
          if (Nat.leb 13 n && Nat.leb n 17)%bool then Q i (fun _ _ => false) else true)
      | right _ => match ty_eq_dec (category_type (slash IAV NP)) a with
        | left H => carry H (fun Q R x => if Nat.eqb n 24 then Q i (fun _ _ => false) else true)
        | right _ => match ty_eq_dec (category_type (dslash IV IV)) a with
          | left H => carry H (fun _ _ => true)
          | right _ => match ty_eq_dec (category_type (slash IV ct)) a with
            | left H => carry H (fun _ _ => true)
            | right _ => zero_value a
            end
          end
        end
      end
    end
  end.

Definition sample_model B FE : model :=
  {| carrier := two_times; boolean_truth := B; function_extensionality := FE;
     constants := sample_constants B |}.
Definition sample_assignment B FE : free_env (sample_model B FE) := fun a _ => zero_value a.

Theorem sample_model_admissible B FE : admissible (sample_model B FE).
Proof.
  constructor.
  - intro n; exists false; destruct n; reflexivity.
  - intros c O i x H; destruct c; cbn in O; try contradiction; discriminate.
  - intros v O; exists (fun _ _ => false); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O; exists (fun _ _ _ => false); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O Q; exists (fun _ _ => true); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v p; exists (fun _ _ => true); destruct v; reflexivity.
  - intros v Q; exists (fun _ _ => true); destruct v; reflexivity.
  - exists (fun _ _ _ _ => false); reflexivity.
  - unfold mp9; intros; reflexivity.
Qed.

Corollary source_model_conditions_are_satisfiable (CD : ClassicalDecision) (FE : FunExt) :
  exists M, admissible M.
Proof. exists (sample_model (decision_truth CD) FE); apply sample_model_admissible. Qed.

Theorem necessity_now_is_not_ptq_necessity B FE :
  (forall w, eval (sample_model B FE) (@Con [] t 0)
    (empty_env _) (sample_assignment B FE) (w,false) = true) /\
  eval (sample_model B FE) (Box (@Con [] t 0))
    (empty_env _) (sample_assignment B FE) (tt,false) = false.
Proof.
  split; [reflexivity |].
  destruct (eval (sample_model B FE) (Box (@Con [] t 0))
    (empty_env _) (sample_assignment B FE) (tt,false)) eqn:H; auto.
  pose proof (proj1 (@necessity_clause (sample_model B FE) [] (@Con [] t 0)
    (empty_env _) (sample_assignment B FE) (tt,false)) H) as K.
  specialize (K tt true); discriminate.
Qed.

Theorem general_constants_need_not_be_index_rigid B FE :
  eval (sample_model B FE) (@Con [] t 0) (empty_env _) (sample_assignment B FE) (tt,false) <>
  eval (sample_model B FE) (@Con [] t 0) (empty_env _) (sample_assignment B FE) (tt,true).
Proof. discriminate. Qed.

Theorem future_keeps_direction_and_world B FE :
  eval (sample_model B FE) (Will (Neg (@Con [] t 0)))
    (empty_env _) (sample_assignment B FE) (tt,false) = true /\
  eval (sample_model B FE) (Has (Neg (@Con [] t 0)))
    (empty_env _) (sample_assignment B FE) (tt,false) = false.
Proof.
  split.
  - apply (proj2 (@future_clause (sample_model B FE) [] (Neg (@Con [] t 0))
      (empty_env _) (sample_assignment B FE) tt false)).
    exists true; cbn; intuition discriminate.
  - destruct (eval (sample_model B FE) (Has (Neg (@Con [] t 0)))
      (empty_env _) (sample_assignment B FE) (tt,false)) eqn:H; auto.
    pose proof (proj1 (@past_clause (sample_model B FE) [] (Neg (@Con [] t 0))
      (empty_env _) (sample_assignment B FE) tt false) H) as K.
    destruct K as [[] [O [N V]]]; cbn in *; intuition discriminate.
Qed.

Lemma bool_ext p q : (p = true <-> q = true) -> p = q.
Proof. destruct p, q; intuition discriminate. Qed.

Lemma singleton_description (B : BooleanTruth) (X : Type) (x0 : X) (P : X -> bool) :
  truth B (exists y, andb
    (truth B (forall x, Bool.eqb (truth B (x = x0)) (truth B (x = y)) = true)) (P y) = true)
  = P x0.
Proof.
  apply bool_ext; rewrite truth_spec; split.
  - intros [y H]; apply andb_true_iff in H; destruct H as [U V].
    apply truth_spec in U; specialize (U x0); apply Bool.eqb_prop in U.
    assert (E : truth B (x0 = x0) = true) by (apply truth_spec; reflexivity).
    rewrite E in U; symmetry in U; apply truth_spec in U; subst y; exact V.
  - intro H; exists x0; apply andb_true_iff; split; auto.
    apply truth_spec; intro x; apply Bool.eqb_reflx.
Qed.

Definition the_temperature := s2 the (s1_word (lcn temperature)).
Definition temperature_is_ninety := s4 the_temperature (s5 s1_be (s1_name ninety)).
Definition temperature_rises := s4 the_temperature (s1_word (liv rise)).
Definition ninety_rises := s4 (s1_name ninety) (s1_word (liv rise)).

Lemma the_temperature_value B FE r i :
  denote (sample_model B FE) the_temperature r i =
  (fun P => P i temperature_concept).
Proof.
  apply FE; intro P; cbn [the_temperature denote dvalue].
  change (truth B (exists y, andb
    (truth B (forall x, Bool.eqb (truth B (x = temperature_concept)) (truth B (x = y)) = true))
    (P i y) = true) = P i temperature_concept).
  apply singleton_description.
Qed.

Theorem temperature_countermodel B FE :
  let M := sample_model B FE in
  admissible M /\
  eval M (translate_closed temperature_is_ninety) (empty_env M) (sample_assignment B FE) (tt,false) = true /\
  eval M (translate_closed temperature_rises) (empty_env M) (sample_assignment B FE) (tt,false) = true /\
  eval M (translate_closed ninety_rises) (empty_env M) (sample_assignment B FE) (tt,false) = false.
Proof.
  cbn zeta; split; [apply sample_model_admissible |].
  rewrite !closed_translation_interpretation.
  cbn [temperature_is_ninety temperature_rises ninety_rises denote].
  rewrite !the_temperature_value; cbn.
  split; [apply truth_spec; reflexivity |].
  split; [apply truth_spec; reflexivity |].
  destruct (truth B ((fun _ : index two_times => false) = temperature_concept)) eqn:H; auto.
  apply truth_spec in H; pose proof (f_equal (fun f => f (tt,true)) H); discriminate.
Qed.

Theorem temperature_inference_invalid (B : BooleanTruth) (FE : FunExt) :
  ~ english_consequence [temperature_is_ninety; temperature_rises] ninety_rises.
Proof.
  intro H; destruct (temperature_countermodel B FE) as [A [P [Q N]]].
  rewrite !closed_translation_interpretation in P, Q, N.
  specialize (H _ A (fun n => sample_assignment B FE ic (2*n)) (tt,false)).
  assert (C : denote (sample_model B FE) ninety_rises
    (fun n => sample_assignment B FE ic (2*n)) (tt,false) = true).
  { apply H; intros p [E | [E | E]]; subst; auto; contradiction. }
  congruence.
Qed.

Theorem unicorn_readings_separated B FE :
  let M := sample_model B FE in
  admissible M /\
  eval M (translate_closed seeks_unicorn_dicto) (empty_env M) (sample_assignment B FE) (tt,false) = true /\
  (forall x, word_value M (lcn unicorn) (tt,false) x = false) /\
  eval M (translate_closed seeks_unicorn_re) (empty_env M) (sample_assignment B FE) (tt,false) = false.
Proof.
  cbn zeta; split; [apply sample_model_admissible |].
  rewrite !closed_translation_interpretation.
  split; [reflexivity |]. split; [reflexivity |].
  change (truth B (exists x : domain two_times ic, false = true) = false).
  destruct (truth B (exists x : domain two_times ic, false = true)) eqn:H; auto.
  apply truth_spec in H; destruct H as [x H]; discriminate.
Qed.

Definition noun_with_free_pronoun : tree CN :=
  s15 (s1_pronoun 0) 1 (s1_word (lcn man)).
Definition relative_body := s4 (s1_pronoun 0) (s1_word (liv walk)).
Definition relative_with_collision := s3 noun_with_free_pronoun 0 relative_body.
Definition wrongly_captured_relative : tm [] ivty :=
  Lam (And (App (translate noun_with_free_pronoun (bind initial_pronouns 0)) (Var vz))
    (translate relative_body (bind initial_pronouns 0))).

Theorem relative_binding_does_not_capture_the_noun :
  translate_closed relative_with_collision <> wrongly_captured_relative.
Proof. discriminate. Qed.
