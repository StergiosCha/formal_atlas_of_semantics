(* Source section 4, pp. 29-32: explicit analysis witnesses, not a theorem
   that these exhaust all analyses of the corresponding surface strings. *)
From Coq Require Import List Bool Strings.String.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Surface.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Definition some_unicorn := s2 a_or_an (s1_word (lcn unicorn)).
Definition finds_unicorn := s4 (s1_name john) (s5 (s1_word (ltv find)) some_unicorn).
Definition tries_unicorn_dicto := s4 (s1_name john)
  (s8 (s1_word (lcontrol try_to)) (s5 (s1_word (ltv find)) some_unicorn)).
Definition tries_unicorn_re := s14 some_unicorn 0 (s4 (s1_name john)
  (s8 (s1_word (lcontrol try_to)) (s5 (s1_word (ltv find)) (s1_pronoun 0)))).
Definition talks_unicorn_dicto := s4 (s1_name john)
  (s10 (s6 (s1_word (lprep about)) some_unicorn) (s1_word (liv talk))).
Definition talks_unicorn_re := s14 some_unicorn 0 (s4 (s1_name john)
  (s10 (s6 (s1_word (lprep about)) (s1_pronoun 0)) (s1_word (liv talk)))).
Definition bill_is_mary := s4 (s1_name bill) (s5 s1_be (s1_name mary)).
Definition bill_is_man := s4 (s1_name bill) (s5 s1_be (s2 a_or_an (s1_word (lcn man)))).
Definition a_price_rises := s4 (s2 a_or_an (s1_word (lcn price))) (s1_word (liv rise)).
Definition woman_loves_every_man := s4 (s2 a_or_an (s1_word (lcn woman)))
  (s5 (s1_word (ltv love)) (s2 every (s1_word (lcn man)))).
Definition every_man_loved_by_a_woman := s14 (s2 every (s1_word (lcn man))) 0
  (s4 (s2 a_or_an (s1_word (lcn woman))) (s5 (s1_word (ltv love)) (s1_pronoun 0))).

Definition find_and_eat := s12 conjunction
  (s5 (s1_word (ltv find)) (s1_pronoun 0))
  (s5 (s1_word (ltv eat)) (s1_pronoun 0)).
Definition wish_unicorn_dicto := s4 (s1_name john)
  (s8 (s1_word (lcontrol wish_to)) (s16 some_unicorn 0 find_and_eat)).
Definition wish_unicorn_re := s14 some_unicorn 0
  (s4 (s1_name john) (s8 (s1_word (lcontrol wish_to)) find_and_eat)).

Definition john_finds_and_eats := s14 (s1_name john) 1 (s11 conjunction
  (s4 (s1_pronoun 1) (s5 (s1_word (ltv find)) (s1_pronoun 0)))
  (s4 (s1_pronoun 1) (s5 (s1_word (ltv eat)) (s1_pronoun 0)))).
Definition belief_unicorn_dicto := s4 (s1_name mary)
  (s7 (s1_word (latt believe_that)) (s14 some_unicorn 0 john_finds_and_eats)).
Definition belief_unicorn_re := s14 some_unicorn 0
  (s4 (s1_name mary) (s7 (s1_word (latt believe_that)) john_finds_and_eats)).

Definition joint_seeking := s14 some_unicorn 0 (s11 conjunction
  (s4 (s1_name john) (s5 (s1_word (ltv seek)) (s1_pronoun 0)))
  (s4 (s1_name mary) (s5 (s1_word (ltv seek)) (s1_pronoun 0)))).
Definition joint_control first second := s14 some_unicorn 0 (s4 (s1_name john)
  (s12 conjunction
    (s8 (s1_word (lcontrol first)) (s5 (s1_word (ltv find)) (s1_pronoun 0)))
    (s8 (s1_word (lcontrol second)) (s5 (s1_word (ltv eat)) (s1_pronoun 0))))).

(* A catalogue entry states the printed words and supplies candidate analyses.
   The two morphology discrepancies are asserted separately below. *)
Definition catalogue : list (list string * list (tree ct)) := [
  (["Bill";"walks"], [bill_walks]);
  (["a";"man";"walks"], [a_man_walks]);
  (["every";"man";"walks"], [every_man_walks]);
  (["the";"man";"walks"], [the_man_walks]);
  (["John";"finds";"a";"unicorn"], [finds_unicorn]);
  (["John";"seeks";"a";"unicorn"], [seeks_unicorn_dicto; seeks_unicorn_re]);
  (["John";"tries";"to";"find";"a";"unicorn"], [tries_unicorn_dicto; tries_unicorn_re]);
  (["John";"talks";"about";"a";"unicorn"], [talks_unicorn_dicto; talks_unicorn_re]);
  (["Bill";"is";"Mary"], [bill_is_mary]);
  (["Bill";"is";"a";"man"], [bill_is_man]);
  (["the";"temperature";"is";"ninety"], [temperature_is_ninety]);
  (["the";"temperature";"rises"], [temperature_rises]);
  (["ninety";"rises"], [ninety_rises]);
  (["a";"price";"rises"], [a_price_rises]);
  (["a";"woman";"loves";"every";"man"], [woman_loves_every_man; every_man_loved_by_a_woman]);
  (["John";"wishes";"to";"find";"a";"unicorn";"and";"eat";"it"], [wish_unicorn_dicto; wish_unicorn_re]);
  (["Mary";"believes";"that";"John";"finds";"a";"unicorn";"and";"he";"eats";"it"],
    [belief_unicorn_dicto; belief_unicorn_re]);
  (["John";"seeks";"a";"unicorn";"and";"Mary";"seeks";"it"], [joint_seeking])
].
Example catalogue_surface_checks :
  Forall (fun entry => Forall (fun u => surface u = Some (fst entry)) (snd entry)) catalogue.
Proof. repeat constructor. Qed.
Example catalogue_size : List.length catalogue = 18 /\
  List.length (flat_map snd catalogue) = 24.
Proof. split; reflexivity. Qed.

Definition printed_try_wish :=
  ["John";"tries";"to";"find";"a";"unicorn";"and";"wishes";"to";"eat";"it"].
Definition printed_wish_try :=
  ["John";"wishes";"to";"find";"a";"unicorn";"and";"tries";"to";"eat";"it"].
Example first_verb_rule_try_wish :
  surface (joint_control try_to wish_to) =
    Some ["John";"tries";"to";"find";"a";"unicorn";"and";"wish";"to";"eat";"it"] /\
  surface (joint_control try_to wish_to) <> Some printed_try_wish.
Proof. split; [reflexivity | discriminate]. Qed.
Example first_verb_rule_wish_try :
  surface (joint_control wish_to try_to) =
    Some ["John";"wishes";"to";"find";"a";"unicorn";"and";"try";"to";"eat";"it"] /\
  surface (joint_control wish_to try_to) <> Some printed_wish_try.
Proof. split; [reflexivity | discriminate]. Qed.

(* Source p. 21 derivation, including two pronoun indices and a relative clause. *)
Definition every_man_loves_relative := s14 (s2 every (s1_word (lcn man))) 0
  (s4 (s1_pronoun 0) (s5 (s1_word (ltv love))
    (s2 a_or_an (s3 (s1_word (lcn woman)) 1
      (s4 (s1_pronoun 1) (s5 (s1_word (ltv love)) (s1_pronoun 0))))))).
Example source_relative_surface : surface every_man_loves_relative =
  Some ["every";"man";"loves";"a";"woman";"such";"that";"she";"loves";"him"].
Proof. reflexivity. Qed.

Lemma outer_indefinite_has_witness M c n (u : tree ct) r i :
  denote M (s14 (s2 a_or_an (s1_word (lcn c))) n u) r i = true ->
  exists x, word_value M (lcn c) i x = true.
Proof.
  cbn [denote dvalue]; rewrite truth_spec.
  intros [x H]; apply andb_true_iff in H; exists x; exact (proj1 H).
Qed.

Definition dicto_cases := [seeks_unicorn_dicto; tries_unicorn_dicto;
  talks_unicorn_dicto; wish_unicorn_dicto; belief_unicorn_dicto].
Definition re_cases := [seeks_unicorn_re; tries_unicorn_re;
  talks_unicorn_re; wish_unicorn_re; belief_unicorn_re;
  joint_seeking; joint_control try_to wish_to; joint_control wish_to try_to].

Theorem referential_analyses_have_witnesses M r i :
  Forall (fun u : tree ct => denote M u r i = true ->
    exists x, word_value M (lcn unicorn) i x = true) re_cases.
Proof. repeat constructor; apply outer_indefinite_has_witness. Qed.

Theorem five_nonreferential_witnesses B FE r i :
  let M := sample_model B FE in
  admissible M /\
  (forall x, word_value M (lcn unicorn) i x = false) /\
  Forall (fun u : tree ct => denote M u r i = true) dicto_cases /\
  Forall (fun u : tree ct => denote M u r i = false) re_cases.
Proof.
  cbn zeta; split; [apply sample_model_admissible |].
  split; [reflexivity |]. split.
  - repeat constructor.
  - pose proof (@referential_analyses_have_witnesses (sample_model B FE) r i) as H.
    eapply Forall_impl; [|exact H]. intros u U.
    destruct (denote (sample_model B FE) u r i) eqn:E; [|reflexivity].
    destruct (U E) as [x X]; discriminate.
Qed.
