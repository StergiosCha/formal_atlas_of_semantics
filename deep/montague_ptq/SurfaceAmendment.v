(* An explicitly amended surface specification, not a transcription of S4.
   Present subject attachment inflects the heads of coordinated IVs. Control
   complements remain infinitival. S17 tense/sign and F10 failure are unchanged.
   The first_verb_only policy is proved identical to Surface.realize for every
   tree; the coordination policy does not modify Grammar or Translation. *)
From Coq Require Import List Bool Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Named Surface Catalogue ReadingForms SurfaceInvariant.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Inductive surface_policy := first_verb_only | coordinated_present.
Record surface_plan := {
  plain_tokens : option (list token);
  present_tokens : option (list token)
}.

Definition first_present xs := match xs with
  | Some ts => inflect_first present ts | None => None end.
Definition ordinary_plan xs : surface_plan :=
  {| plain_tokens := xs; present_tokens := first_present xs |}.
Definition coordinated_plan policy xs ys : surface_plan :=
  {| plain_tokens := xs;
     present_tokens := match policy with
       | first_verb_only => first_present xs | coordinated_present => ys end |}.

Fixpoint plan {A} policy (u : tree A) : surface_plan := match u with
  | s1_word w => ordinary_plan (Some (lex_tokens w))
  | s1_name n => ordinary_plan (Some [name n])
  | s1_pronoun n => ordinary_plan (Some [indexed n subject_case])
  | s1_be => ordinary_plan (Some [verb vbe infinitive])
  | s1_necessarily => ordinary_plan (Some [literal "necessarily"])
  | s2 d c => ordinary_plan (match plain_tokens (plan policy c) with
      | Some cs => Some (literal (match d with every => "every" | the => "the"
          | a_or_an => "a" end) :: cs) | None => None end)
  | s3 c n p => ordinary_plan (combine (fun cs ps => match first_gender cs with
      | Some g => Some (cs ++ [literal "such"; literal "that"] ++
          map (replace_pronoun n g) ps)%list | None => None end)
      (plain_tokens (plan policy c)) (plain_tokens (plan policy p)))
  | s4 p q => ordinary_plan (combine concat_tokens
      (plain_tokens (plan policy p)) (present_tokens (plan policy q)))
  | s5 p q => ordinary_plan (combine (fun x y => concat_tokens x (object_form y))
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s6 p q => ordinary_plan (combine (fun x y => concat_tokens x (object_form y))
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s7 p q => ordinary_plan (combine concat_tokens
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s8 p q => ordinary_plan (combine concat_tokens
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s9 p q => ordinary_plan (combine concat_tokens
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s10 p q => coordinated_plan policy
      (combine (fun x y => concat_tokens y x)
        (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
      (combine (fun x y => concat_tokens y x)
        (plain_tokens (plan policy p)) (present_tokens (plan policy q)))
  | s11 j p q => ordinary_plan (combine (join_tokens j)
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s12 j p q => coordinated_plan policy
      (combine (join_tokens j) (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
      (combine (join_tokens j) (present_tokens (plan policy p)) (present_tokens (plan policy q)))
  | s13 p q => ordinary_plan (combine (join_tokens disjunction)
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s14 p n q => ordinary_plan (combine (f10 n)
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s15 p n q => ordinary_plan (combine (f10 n)
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  | s16 p n q => coordinated_plan policy
      (combine (f10 n) (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
      (combine (f10 n) (plain_tokens (plan policy p)) (present_tokens (plan policy q)))
  | s17 k p q => ordinary_plan (combine (subject_verb (sign_form k))
      (plain_tokens (plan policy p)) (plain_tokens (plan policy q)))
  end.

Definition policy_surface {A} policy (u : tree A) :=
  option_map words (plain_tokens (plan policy u)).
Definition amended_tokens {A} (u : tree A) := plain_tokens (plan coordinated_present u).
Definition amended_surface {A} (u : tree A) := policy_surface coordinated_present u.

Lemma subject_first_plan alpha delta :
  combine concat_tokens alpha (first_present delta) =
  combine (subject_verb present) alpha delta.
Proof.
  destruct alpha as [xs|], delta as [ys|]; cbn [combine first_present subject_verb];
    try reflexivity; destruct (inflect_first present ys); reflexivity.
Qed.

Theorem first_policy_plan_exact A (u : tree A) :
  plain_tokens (plan first_verb_only u) = realize u /\
  present_tokens (plan first_verb_only u) = first_present (realize u).
Proof.
  induction u;
    cbn [plan ordinary_plan coordinated_plan plain_tokens present_tokens realize];
    repeat match goal with
      | H : _ /\ _ |- _ =>
          let L := fresh "Hplain" in let R := fresh "Hpresent" in destruct H as [L R]
      end;
    repeat match goal with H : ?x = ?y |- _ => rewrite H end;
    try rewrite subject_first_plan; split; reflexivity.
Qed.

Corollary first_policy_surface_exact A (u : tree A) :
  policy_surface first_verb_only u = surface u.
Proof. unfold policy_surface, surface; rewrite (proj1 (first_policy_plan_exact u)); reflexivity. Qed.

Theorem amended_subject_attachment alpha delta :
  amended_tokens (s4 alpha delta) = combine concat_tokens
    (amended_tokens alpha) (present_tokens (plan coordinated_present delta)).
Proof. reflexivity. Qed.

Theorem coordinated_present_heads j (p q : tree IV) :
  present_tokens (plan coordinated_present (s12 j p q)) =
  combine (join_tokens j) (present_tokens (plan coordinated_present p))
    (present_tokens (plan coordinated_present q)).
Proof. reflexivity. Qed.

Theorem control_complement_stays_infinitival c (u : tree IV) :
  present_tokens (plan coordinated_present (s8 (s1_word (lcontrol c)) u)) =
  option_map (fun xs => verb (vcontrol c) present :: xs) (amended_tokens u).
Proof.
  cbn [plan ordinary_plan plain_tokens present_tokens lex_tokens].
  unfold amended_tokens; destruct (plain_tokens (plan coordinated_present u)); reflexivity.
Qed.

Theorem amendment_keeps_tense_sign k p q :
  amended_tokens (s17 k p q) =
  combine (subject_verb (sign_form k)) (amended_tokens p) (amended_tokens q).
Proof. reflexivity. Qed.

Theorem amendment_keeps_quantifying_in p n q :
  amended_tokens (s14 p n q) = combine (f10 n) (amended_tokens p) (amended_tokens q).
Proof. reflexivity. Qed.

Definition amended_catalogue := catalogue ++
  [(printed_try_wish, [joint_control try_to wish_to]);
   (printed_wish_try, [joint_control wish_to try_to])].

Theorem amended_catalogue_surface_checks :
  Forall (fun entry => Forall (fun u => amended_surface u = Some (fst entry))
    (snd entry)) amended_catalogue.
Proof. repeat constructor. Qed.

Theorem amended_catalogue_has_witnesses :
  Forall (fun entry => snd entry <> []) amended_catalogue.
Proof. repeat constructor; discriminate. Qed.

Theorem amended_registry_matches :
  map fst reading_pairs = flat_map snd amended_catalogue /\
  map fst amended_catalogue = map fst catalogue ++ [printed_try_wish; printed_wish_try] /\
  List.length amended_catalogue = 20 /\ List.length reading_pairs = 26.
Proof. repeat split; reflexivity. Qed.

Theorem amended_catalogue_source_formulas text us u :
  In (text, us) amended_catalogue -> In u us ->
  amended_surface u = Some text /\
  exists p, In (u, p) reading_pairs /\
    forall M, admissible M -> forall sigma i,
      eval M (translate_closed u) (empty_env M) sigma i =
      eval M (embed_named p) (empty_env M) sigma i.
Proof.
  intros E U; split.
  - pose proof amended_catalogue_surface_checks as H.
    rewrite Forall_forall in H; specialize (H (text,us) E).
    rewrite Forall_forall in H; exact (H u U).
  - assert (I : In u (map fst reading_pairs)).
    { rewrite (proj1 amended_registry_matches).
      apply in_flat_map; exists (text,us); split; assumption. }
    apply in_map_iff in I; destruct I as [[v p] [V I]]; cbn in V; subst v.
    exists p; split; [exact I|]. intros M A sigma i.
    pose proof (all_listed_compiled_formulas A sigma i) as H.
    rewrite Forall_forall in H; exact (H (u,p) I).
Qed.

Theorem amended_printed_examples_covered text :
  In text (map fst catalogue ++ [printed_try_wish; printed_wish_try]) ->
  exists u p, amended_surface u = Some text /\ In (u,p) reading_pairs /\
    forall M, admissible M -> forall sigma i,
      eval M (translate_closed u) (empty_env M) sigma i =
      eval M (embed_named p) (empty_env M) sigma i.
Proof.
  rewrite <- (proj1 (proj2 amended_registry_matches)); intro H.
  apply in_map_iff in H; destruct H as [[s us] [E H]]; cbn in E; subst s.
  pose proof amended_catalogue_has_witnesses as N; rewrite Forall_forall in N.
  specialize (N (text,us) H); cbn in N; destruct us as [|u us]; [contradiction|].
  destruct (@amended_catalogue_source_formulas text (u::us) u H (or_introl eq_refl))
    as [S [p [I P]]].
  exists u, p; auto.
Qed.

Example amended_try_wish :
  amended_surface (joint_control try_to wish_to) = Some printed_try_wish.
Proof. reflexivity. Qed.
Example amended_wish_try :
  amended_surface (joint_control wish_to try_to) = Some printed_wish_try.
Proof. reflexivity. Qed.
Example amended_control_scope :
  amended_surface wish_unicorn_dicto =
    Some ["John";"wishes";"to";"find";"a";"unicorn";"and";"eat";"it"].
Proof. reflexivity. Qed.
Example amended_nested_coordination :
  amended_surface (s4 (s1_name john) (s12 conjunction (s1_word (liv walk))
    (s12 disjunction (s1_word (liv run)) (s1_word (liv talk))))) =
  Some ["John";"walks";"and";"runs";"or";"talks"].
Proof. reflexivity. Qed.
Example amended_adverb_scope :
  amended_surface (s4 (s1_name john) (s10 (s1_word (liav slowly))
    (s12 conjunction (s1_word (liv walk)) (s1_word (liv talk))))) =
  Some ["John";"walks";"and";"talks";"slowly"].
Proof. reflexivity. Qed.
Example amended_iv_quantifying_in :
  amended_surface (s4 (s1_name john) (s16 some_unicorn 0 find_and_eat)) =
  Some ["John";"finds";"a";"unicorn";"and";"eats";"it"].
Proof. reflexivity. Qed.
Example amendment_does_not_distribute_negation :
  amended_surface (s17 negative (s1_name john)
    (s12 conjunction (s1_word (liv walk)) (s1_word (liv talk)))) =
  Some ["John";"does";"not";"walk";"and";"talk"].
Proof. reflexivity. Qed.
Example amended_missing_target_still_fails :
  amended_surface (s14 some_unicorn 9 bill_walks) = None.
Proof. reflexivity. Qed.
Example amended_relative_derivation :
  amended_surface every_man_loves_relative = surface every_man_loves_relative.
Proof. reflexivity. Qed.

Theorem amendment_does_not_retract_literal_refutation :
  ~ section4_generation_claim /\
  amended_surface (joint_control try_to wish_to) = Some printed_try_wish /\
  amended_surface (joint_control wish_to try_to) = Some printed_wish_try.
Proof. split; [exact section4_generation_claim_refuted|]; split; reflexivity. Qed.
