(* A genuine additional reading, not a new variable spelling: sentence
   coordination can take scope outside believe. Both surface policies admit
   this tree. A model separates it from both previously registered readings. *)
From Coq Require Import List Bool Arith Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Surface Catalogue Named PostulateFormulas Reductions Scope ReadingForms SurfaceAmendment
  ReadingClassification.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Definition belief_words :=
  ["Mary";"believes";"that";"John";"finds";"a";"unicorn";"and";"he";"eats";"it"].

Definition belief_external_conjunction := s14 some_unicorn 0
  (s14 (s1_name john) 1
    (s11 conjunction
      (s4 (s1_name mary) (s7 (s1_word (latt believe_that))
        (s4 (s1_pronoun 1) (s5 (s1_word (ltv find)) (s1_pronoun 0)))))
      (s4 (s1_pronoun 1) (s5 (s1_word (ltv eat)) (s1_pronoun 0))))).

Theorem additional_belief_reading_is_generated :
  surface belief_external_conjunction = Some belief_words /\
  amended_surface belief_external_conjunction = Some belief_words.
Proof. split; reflexivity. Qed.

Definition rf_belief_external := exists_unicorn (NCj
  (rattitude believe_that (NU (rt find (rname john) ru)) (NU (rname mary)))
  (rt eat (rname john) ru)).

Lemma external_belief_body M (A : admissible M) sigma i :
  neval M (NCj
    (rattitude believe_that (NU (rt find (rname john) ru)) (NU (rname mary)))
    (rt eat (rname john) ru)) sigma i =
  andb (word_value M (latt believe_that) i
    (fun j => word_value M (ltv find) j
      (fun k P => P k (rigid M (sigma e 0)))
      (fun k => constants M e (name_code john) k))
    (fun j => constants M e (name_code mary) j))
    (word_value M (ltv eat) i (fun j P => P j (rigid M (sigma e 0)))
      (fun j => constants M e (name_code john) j)).
Proof.
  cbn [neval]; rewrite (named_tv_entity A).
  f_equal; unfold word_value; cbn [rattitude nword rname neval].
  f_equal; apply (function_extensionality M); intro j; apply (named_tv_entity A).
Qed.

Theorem additional_belief_formula M (A : admissible M) sigma i :
  eval M (translate_closed belief_external_conjunction) (empty_env M) sigma i =
  neval M rf_belief_external sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [belief_external_conjunction some_unicorn denote jvalue].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_belief_external; rewrite exists_unicorn_interpretation.
  apply truth_congr; setoid_rewrite (external_belief_body A); reflexivity.
Qed.

Corollary additional_belief_compiled_formula M (A : admissible M) sigma i :
  eval M (translate_closed belief_external_conjunction) (empty_env M) sigma i =
  eval M (embed_named rf_belief_external) (empty_env M) sigma i.
Proof. rewrite embed_named_interpretation; apply (additional_belief_formula A). Qed.

Definition belief_boundary_constants B a n i : domain two_times a :=
  match ty_eq_dec ivty a with
  | left H => carry H (fun x => if Nat.eqb n 10
      then truth B (exists u, x = (fun _ => u)) else false)
  | right _ => sample_constants B a n i
  end.
Definition belief_boundary_model B FE : model :=
  {| carrier := two_times; boolean_truth := B; function_extensionality := FE;
     constants := belief_boundary_constants B |}.
Definition belief_boundary_assignment B FE : free_env (belief_boundary_model B FE) :=
  fun a _ => zero_value a.

Theorem belief_boundary_model_admissible B FE : admissible (belief_boundary_model B FE).
Proof.
  constructor.
  - intro n; exists false; destruct n; reflexivity.
  - intros c O i x H; destruct c; cbn in O; try contradiction;
      try discriminate; apply truth_spec in H; exact H.
  - intros v O; exists (fun _ _ => false); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O; exists (fun _ _ _ => false); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O Q; exists (fun _ _ => true); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v p; exists (fun _ _ => true); destruct v; reflexivity.
  - intros v Q; exists (fun _ _ => true); destruct v; reflexivity.
  - exists (fun _ _ _ _ => false); reflexivity.
  - unfold mp9; intros; reflexivity.
Qed.

Theorem belief_boundary_values B FE r i :
  denote (belief_boundary_model B FE) belief_external_conjunction r i = false /\
  denote (belief_boundary_model B FE) belief_unicorn_dicto r i = true /\
  denote (belief_boundary_model B FE) belief_unicorn_re r i = true.
Proof.
  split.
  - change (truth B (exists x : domain two_times ic,
      andb (truth B (exists u, x = (fun _ => u))) false = true) = false).
    destruct (truth B (exists x : domain two_times ic,
      andb (truth B (exists u, x = (fun _ => u))) false = true)) eqn:E; [|reflexivity].
    apply truth_spec in E; destruct E as [x E]; rewrite andb_false_r in E; discriminate.
  - split; [reflexivity|].
    change (truth B (exists x : domain two_times ic,
      andb (truth B (exists u, x = (fun _ => u))) true = true) = true).
    apply truth_spec; exists (fun _ => false); rewrite andb_true_r.
    apply truth_spec; exists false; reflexivity.
Qed.

Theorem additional_belief_reading_is_distinct (B : BooleanTruth) (FE : FunExt) :
  ~ reading_equivalent belief_external_conjunction belief_unicorn_dicto /\
  ~ reading_equivalent belief_external_conjunction belief_unicorn_re.
Proof.
  pose proof (belief_boundary_model_admissible B FE) as A.
  pose proof (@belief_boundary_values B FE
    (fun n => belief_boundary_assignment B FE ic (2*n)) (tt,false)) as [X [D R]].
  split; intro H; specialize (H _ A (belief_boundary_assignment B FE) (tt,false));
    rewrite !closed_translation_interpretation in H; congruence.
Qed.

Theorem registered_belief_pair_not_exhaustive (B : BooleanTruth) (FE : FunExt) :
  ~ reading_exhaustive (@surface ct) belief_words [belief_unicorn_dicto; belief_unicorn_re] /\
  ~ reading_exhaustive (@amended_surface ct) belief_words [belief_unicorn_dicto; belief_unicorn_re].
Proof.
  destruct (additional_belief_reading_is_distinct B FE) as [D R].
  split; intro H; destruct (H belief_external_conjunction eq_refl) as [v [[E|[E|E]] V]];
    try contradiction; subst v; contradiction.
Qed.

Theorem original_amended_registry_not_exhaustive (B : BooleanTruth) (FE : FunExt) :
  ~ catalogue_exhaustive (@amended_surface ct) amended_catalogue.
Proof.
  intro H; unfold catalogue_exhaustive in H; rewrite Forall_forall in H.
  assert (I : In (belief_words, [belief_unicorn_dicto; belief_unicorn_re]) amended_catalogue).
  { cbn; tauto. }
  specialize (H _ I); exact (proj2 (registered_belief_pair_not_exhaustive B FE) H).
Qed.

Definition revised_belief_candidates :=
  [belief_unicorn_dicto; belief_unicorn_re; belief_external_conjunction].
Definition revised_catalogue := firstn 16 amended_catalogue ++
  [(belief_words, revised_belief_candidates)] ++ skipn 17 amended_catalogue.
Definition revised_reading_pairs := reading_pairs ++ [(belief_external_conjunction, rf_belief_external)].

Theorem revised_catalogue_counts : List.length revised_catalogue = 20 /\
  List.length (flat_map snd revised_catalogue) = 27 /\
  List.length revised_reading_pairs = 27 /\
  map fst revised_catalogue = map fst amended_catalogue.
Proof. repeat split; reflexivity. Qed.

Theorem revised_catalogue_surface_checks :
  Forall (fun entry => Forall (fun u => amended_surface u = Some (fst entry))
    (snd entry)) revised_catalogue.
Proof. repeat constructor. Qed.

Theorem revised_formula_checks M (A : admissible M) sigma i :
  Forall (fun pair => eval M (translate_closed (fst pair)) (empty_env M) sigma i =
    eval M (embed_named (snd pair)) (empty_env M) sigma i) revised_reading_pairs.
Proof.
  apply Forall_app; split; [apply (all_listed_compiled_formulas A)|].
  constructor; [apply (additional_belief_compiled_formula A)|constructor].
Qed.

Theorem revised_registry_membership u :
  In u (flat_map snd revised_catalogue) <-> In u (map fst revised_reading_pairs).
Proof.
  cbn [revised_catalogue revised_belief_candidates revised_reading_pairs amended_catalogue
    catalogue reading_pairs firstn skipn app map flat_map fst snd In]; tauto.
Qed.

Theorem revised_catalogue_source_formulas text us u :
  In (text,us) revised_catalogue -> In u us ->
  amended_surface u = Some text /\ exists p, In (u,p) revised_reading_pairs /\
    forall M, admissible M -> forall sigma i,
      eval M (translate_closed u) (empty_env M) sigma i =
      eval M (embed_named p) (empty_env M) sigma i.
Proof.
  intros I U; split.
  - pose proof revised_catalogue_surface_checks as H; rewrite Forall_forall in H.
    specialize (H (text,us) I); rewrite Forall_forall in H; exact (H u U).
  - assert (J : In u (map fst revised_reading_pairs)).
    { apply revised_registry_membership; apply in_flat_map; exists (text,us); auto. }
    apply in_map_iff in J; destruct J as [[v p] [E J]]; cbn in E; subst v.
    exists p; split; [exact J|]; intros M A sigma i.
    pose proof (revised_formula_checks A sigma i) as H; rewrite Forall_forall in H; exact (H (u,p) J).
Qed.

Theorem three_belief_readings_pairwise_distinct (B : BooleanTruth) (FE : FunExt) :
  ~ reading_equivalent belief_unicorn_dicto belief_unicorn_re /\
  ~ reading_equivalent belief_unicorn_dicto belief_external_conjunction /\
  ~ reading_equivalent belief_unicorn_re belief_external_conjunction.
Proof.
  destruct (additional_belief_reading_is_distinct B FE) as [D R].
  split.
  - intro H; specialize (H _ (sample_model_admissible B FE) (sample_assignment B FE) (tt,false)).
    rewrite !closed_translation_interpretation in H.
    assert (N : denote (sample_model B FE) belief_unicorn_re
      (fun n => sample_assignment B FE ic (2*n)) (tt,false) = false).
    { destruct (@five_nonreferential_witnesses B FE (fun n => sample_assignment B FE ic (2*n))
        (tt,false)) as [_ [_ [_ K]]].
      rewrite Forall_forall in K; apply K; cbn [re_cases In]; tauto. }
    change (true = denote (sample_model B FE) belief_unicorn_re
      (fun n => sample_assignment B FE ic (2*n)) (tt,false)) in H.
    rewrite N in H; discriminate.
  - split; intro H; [apply D|apply R]; apply reading_equivalent_sym; exact H.
Qed.

Theorem additional_belief_reading_is_referential M r i :
  denote M belief_external_conjunction r i = true ->
  exists x, word_value M (lcn unicorn) i x = true.
Proof. apply outer_indefinite_has_witness. Qed.

Fixpoint readings_irredundant (us : list (tree ct)) : Prop := match us with
  | [] => True
  | u :: rest => Forall (fun v => ~ reading_equivalent u v) rest /\ readings_irredundant rest
  end.

Lemma dicto_re_separated (B : BooleanTruth) (FE : FunExt) u v : In u dicto_cases -> In v re_cases ->
  ~ reading_equivalent u v.
Proof.
  intros U V H.
  destruct (@five_nonreferential_witnesses B FE
    (fun n => sample_assignment B FE ic (2*n)) (tt,false)) as [A [_ [D R]]].
  rewrite Forall_forall in D, R; specialize (D u U); specialize (R v V).
  specialize (H _ A (sample_assignment B FE) (tt,false)).
  rewrite !closed_translation_interpretation, D, R in H; discriminate.
Qed.

Theorem revised_candidates_pairwise_inequivalent (B : BooleanTruth) (FE : FunExt) :
  Forall (fun entry => readings_irredundant (snd entry)) revised_catalogue.
Proof.
  destruct (three_belief_readings_pairwise_distinct B FE) as [BD [BX BR]].
  assert (Q : ~ reading_equivalent woman_loves_every_man every_man_loved_by_a_woman).
  { intro H; destruct (quantifier_readings_separated B FE) as [A [S T]].
    specialize (H _ A (scope_assignment B FE) (tt,false)); congruence. }
  cbn [revised_catalogue revised_belief_candidates amended_catalogue catalogue firstn skipn app snd];
    repeat constructor; cbn [readings_irredundant]; repeat split;
    try assumption; try constructor;
    try (apply (@dicto_re_separated B FE); cbn [dicto_cases re_cases In]; tauto).
Qed.
