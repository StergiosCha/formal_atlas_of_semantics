(* PTQ section-4 readings, represented as IL formulas. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Named PostulateFormulas Catalogue Reductions Scope.
Import ListNotations.
Set Implicit Arguments.

Definition ru := NV e 0.
Definition rv := NV e 1.
Definition rx := NV ic 1.
Definition ry := NV ic 3.
Definition rname n := NC e (name_code n).

Definition star_cn_term c := NL e 0 (NA (nword (lcn c)) (NU ru)).
Definition star_iv_term v := NL e 0 (NA (nword (liv v)) (NU ru)).
Definition star_tv_term v := NL e 0 (NL e 1
  (NA (NA (nword (ltv v)) (NU (NL prop_ic 0 (NA (ND nP) (NU rv))))) (NU ru))).
Definition rc c u := NA (star_cn_term c) u.
Definition ri v u := NA (star_iv_term v) u.
Definition rt v u z := NA (NA (star_tv_term v) u) z.
Definition entity_term (u : ntm e) := NL prop_ic 0 (NA (ND nP) (NU u)).
Definition rcontrol v P subject := NA (NA (nword (lcontrol v)) P) subject.
Definition rattitude v p subject := NA (NA (nword (latt v)) p) subject.
Definition unicorn_quantifier :=
  NL prop_ic 0 (NEx e 0 (NCj (rc unicorn ru) (NA (ND nP) (NU ru)))).
Definition exists_unicorn (p : ntm t) := NEx e 0 (NCj (rc unicorn ru) p).
Definition find_eat_body := NCj (rt find (ND ry) ru) (rt eat (ND ry) ru).

Definition rf_bill_walks := ri walk (rname bill).
Definition rf_a_man := NEx e 0 (NCj (rc man ru) (ri walk ru)).
Definition rf_every_man := NAll e 0 (NI (rc man ru) (ri walk ru)).
Definition rf_the_man := NEx e 0
  (NCj (NAll e 1 (NB (rc man rv) (NE rv ru))) (ri walk ru)).
Definition rf_finds := exists_unicorn (rt find (rname john) ru).
Definition rf_seek_dicto :=
  NA (NA (nword (ltv seek)) (NU unicorn_quantifier)) (NU (rname john)).
Definition rf_seek_re := exists_unicorn (rt seek (rname john) ru).

Definition rf_try_dicto := rcontrol try_to
  (NU (NL ic 3 (exists_unicorn (rt find (ND ry) ru)))) (NU (rname john)).
Definition rf_try_re := exists_unicorn
  (rcontrol try_to (NU (NL ic 3 (rt find (ND ry) ru))) (NU (rname john))).
Definition rf_about_dicto := NA (NA (NA (nword (lprep about)) (NU unicorn_quantifier))
  (NU (nword (liv talk)))) (NU (rname john)).
Definition rf_about_re := exists_unicorn
  (NA (NA (NA (nword (lprep about)) (NU (entity_term ru)))
    (NU (nword (liv talk)))) (NU (rname john))).
Definition rf_identity := NE (rname bill) (rname mary).
Definition rf_predication := rc man (rname bill).
Definition temperature_unique := NAll ic 1 (NB (NA (nword (lcn temperature)) rx) (NE rx ry)).
Definition rf_temperature_identity := NEx ic 3
  (NCj temperature_unique (NE (ND ry) (rname ninety))).
Definition rf_temperature_rises := NEx ic 3
  (NCj temperature_unique (NA (nword (liv rise)) ry)).
Definition rf_ninety_rises := NA (nword (liv rise)) (NU (rname ninety)).
Definition rf_price := NEx ic 1 (NCj (NA (nword (lcn price)) rx) (NA (nword (liv rise)) rx)).
Definition rf_surface_scope := NEx e 0 (NCj (rc woman ru)
  (NAll e 1 (NI (rc man rv) (rt love ru rv)))).
Definition rf_inverse_scope := NAll e 1 (NI (rc man rv)
  (NEx e 0 (NCj (rc woman ru) (rt love ru rv)))).

Definition rf_wish_dicto := rcontrol wish_to
  (NU (NL ic 3 (exists_unicorn find_eat_body))) (NU (rname john)).
Definition rf_wish_re := exists_unicorn
  (rcontrol wish_to (NU (NL ic 3 find_eat_body)) (NU (rname john))).
Definition john_find_eat_formula := NCj (rt find (rname john) ru) (rt eat (rname john) ru).
Definition rf_belief_dicto := rattitude believe_that
  (NU (exists_unicorn john_find_eat_formula)) (NU (rname mary)).
Definition rf_belief_re := exists_unicorn
  (rattitude believe_that (NU john_find_eat_formula) (NU (rname mary))).
Definition rf_joint_seeking := exists_unicorn
  (NCj (rt seek (rname john) ru) (rt seek (rname mary) ru)).
Definition rf_joint_control first second := exists_unicorn (NCj
  (rcontrol first (NU (NL ic 3 (rt find (ND ry) ru))) (NU (rname john)))
  (rcontrol second (NU (NL ic 3 (rt eat (ND ry) ru))) (NU (rname john)))).

Lemma star_cn_interpretation M c sigma i :
  neval M (star_cn_term c) sigma i = cn_star M c i.
Proof. reflexivity. Qed.
Lemma star_iv_interpretation M v sigma i :
  neval M (star_iv_term v) sigma i = iv_star M v i.
Proof. reflexivity. Qed.
Lemma star_tv_interpretation M v sigma i :
  neval M (star_tv_term v) sigma i = tv_star M v i.
Proof. reflexivity. Qed.

Ltac unfold_reading := cbn [rf_bill_walks rf_a_man rf_every_man rf_the_man rf_finds
  rf_identity rf_predication rf_temperature_identity rf_temperature_rises rf_ninety_rises
  rf_price rf_surface_scope rf_inverse_scope temperature_unique exists_unicorn
  star_cn_term star_iv_term star_tv_term rc ri rt ru rv rx ry rname
  nword nP prop_ic neval put ty_eq_dec].

Theorem reading_bill_walks M (A : admissible M) sigma i :
  eval M (translate_closed bill_walks) (empty_env M) sigma i = neval M rf_bill_walks sigma i.
Proof. rewrite (bill_walks_source_reduction A); reflexivity. Qed.

Theorem reading_a_man M (A : admissible M) sigma i :
  eval M (translate_closed a_man_walks) (empty_env M) sigma i = neval M rf_a_man sigma i.
Proof.
  apply bool_ext; rewrite (a_man_source_reduction A).
  unfold_reading; rewrite truth_spec; setoid_rewrite andb_true_iff; reflexivity.
Qed.

Theorem reading_every_man M (A : admissible M) sigma i :
  eval M (translate_closed every_man_walks) (empty_env M) sigma i = neval M rf_every_man sigma i.
Proof.
  apply bool_ext; rewrite (every_man_source_reduction A).
  unfold_reading; rewrite truth_spec; setoid_rewrite boolean_implication; reflexivity.
Qed.

Theorem reading_the_man M (A : admissible M) sigma i :
  eval M (translate_closed the_man_walks) (empty_env M) sigma i = neval M rf_the_man sigma i.
Proof.
  apply bool_ext; rewrite (the_man_source_reduction A).
  unfold_reading; rewrite truth_spec; setoid_rewrite andb_true_iff;
    setoid_rewrite truth_spec; setoid_rewrite eqb_truth_iff; reflexivity.
Qed.

Theorem reading_finds M (A : admissible M) sigma i :
  eval M (translate_closed finds_unicorn) (empty_env M) sigma i = neval M rf_finds sigma i.
Proof.
  apply bool_ext; rewrite (john_finds_source_reduction A).
  unfold_reading; rewrite truth_spec; setoid_rewrite andb_true_iff; reflexivity.
Qed.

Theorem reading_identity M sigma i :
  eval M (translate_closed bill_is_mary) (empty_env M) sigma i = neval M rf_identity sigma i.
Proof. rewrite closed_translation_interpretation; reflexivity. Qed.

Theorem reading_predication M (A : admissible M) sigma i :
  eval M (translate_closed bill_is_man) (empty_env M) sigma i = neval M rf_predication sigma i.
Proof. apply bool_ext; rewrite (predication_source_reduction A); reflexivity. Qed.

Theorem reading_temperature_identity M sigma i :
  eval M (translate_closed temperature_is_ninety) (empty_env M) sigma i =
  neval M rf_temperature_identity sigma i.
Proof. rewrite closed_translation_interpretation; reflexivity. Qed.

Theorem reading_temperature_rises M sigma i :
  eval M (translate_closed temperature_rises) (empty_env M) sigma i =
  neval M rf_temperature_rises sigma i.
Proof. rewrite closed_translation_interpretation; reflexivity. Qed.

Theorem reading_ninety_rises M sigma i :
  eval M (translate_closed ninety_rises) (empty_env M) sigma i = neval M rf_ninety_rises sigma i.
Proof. rewrite closed_translation_interpretation; reflexivity. Qed.

Theorem reading_price M sigma i :
  eval M (translate_closed a_price_rises) (empty_env M) sigma i = neval M rf_price sigma i.
Proof. rewrite closed_translation_interpretation; reflexivity. Qed.

Theorem reading_surface_scope M (A : admissible M) sigma i :
  eval M (translate_closed woman_loves_every_man) (empty_env M) sigma i = neval M rf_surface_scope sigma i.
Proof.
  apply bool_ext; rewrite (surface_scope_source_reduction A); unfold_reading.
  repeat (setoid_rewrite truth_spec || setoid_rewrite andb_true_iff || setoid_rewrite boolean_implication).
  reflexivity.
Qed.

Theorem reading_inverse_scope M (A : admissible M) sigma i :
  eval M (translate_closed every_man_loved_by_a_woman) (empty_env M) sigma i = neval M rf_inverse_scope sigma i.
Proof.
  apply bool_ext; rewrite (inverse_scope_source_reduction A); unfold_reading.
  repeat (setoid_rewrite truth_spec || setoid_rewrite andb_true_iff || setoid_rewrite boolean_implication).
  reflexivity.
Qed.

Lemma unicorn_quantifier_interpretation M (A : admissible M) sigma i :
  neval M unicorn_quantifier sigma i = dvalue M a_or_an (word_value M (lcn unicorn) i) i.
Proof.
  apply (function_extensionality M); intro P; apply bool_ext.
  rewrite (indefinite_reduction A unicorn I).
  cbn [unicorn_quantifier neval]; unfold_reading.
  rewrite truth_spec; setoid_rewrite andb_true_iff; reflexivity.
Qed.

Theorem reading_seek_dicto M (A : admissible M) sigma i :
  eval M (translate_closed seeks_unicorn_dicto) (empty_env M) sigma i = neval M rf_seek_dicto sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [rf_seek_dicto neval].
  assert (H : (fun j => neval M unicorn_quantifier sigma j) =
    (fun j => dvalue M a_or_an (word_value M (lcn unicorn) j) j)).
  { apply (function_extensionality M); intro j; apply (unicorn_quantifier_interpretation A). }
  rewrite H; reflexivity.
Qed.

Theorem reading_about_dicto M (A : admissible M) sigma i :
  eval M (translate_closed talks_unicorn_dicto) (empty_env M) sigma i = neval M rf_about_dicto sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [rf_about_dicto neval].
  assert (H : (fun j => neval M unicorn_quantifier sigma j) =
    (fun j => dvalue M a_or_an (word_value M (lcn unicorn) j) j)).
  { apply (function_extensionality M); intro j; apply (unicorn_quantifier_interpretation A). }
  rewrite H; reflexivity.
Qed.

Lemma name_concept_rigid M (A : admissible M) n i :
  (fun j => constants M e (name_code n) j) = rigid M (constants M e (name_code n) i).
Proof.
  apply (function_extensionality M); intro j; apply (proper_name_rigidity_is_a_condition A).
Qed.

Lemma tv_singleton_reduction M (A : admissible M) v (O : extensional_tv v) x y i :
  word_value M (ltv v) i (fun j P => P j y) x = tv_star M v i (x i) (y i).
Proof. rewrite (@tv_extensional_reduction M A v O); reflexivity. Qed.

Lemma find_unicorn_body M (A : admissible M) sigma i x :
  word_value M (ltv find) i (fun j => dvalue M a_or_an (word_value M (lcn unicorn) j) j) x =
  neval M (NL ic 3 (exists_unicorn (rt find (ND ry) ru))) sigma i x.
Proof.
  apply bool_ext; rewrite (@tv_extensional_reduction M A find I).
  rewrite (indefinite_reduction A unicorn I).
  cbn [neval]; unfold_reading; rewrite truth_spec; setoid_rewrite andb_true_iff; reflexivity.
Qed.

Theorem reading_try_dicto M (A : admissible M) sigma i :
  eval M (translate_closed tries_unicorn_dicto) (empty_env M) sigma i = neval M rf_try_dicto sigma i.
Proof.
  rewrite closed_translation_interpretation.
  change (word_value M (lcontrol try_to) i
    (fun j x => word_value M (ltv find) j
      (fun k => dvalue M a_or_an (word_value M (lcn unicorn) k) k) x)
    (fun j => constants M e (name_code john) j) = neval M rf_try_dicto sigma i).
  unfold word_value; cbn [rf_try_dicto rcontrol nword rname neval].
  f_equal; apply (function_extensionality M); intro j.
  apply (function_extensionality M); intro x; apply (find_unicorn_body A).
Qed.

Lemma outer_unicorn_value M (A : admissible M) P i :
  dvalue M a_or_an (word_value M (lcn unicorn) i) i P =
  truth (boolean_truth M) (exists u,
    andb (cn_star M unicorn i u) (P i (rigid M u)) = true).
Proof.
  apply bool_ext; rewrite (indefinite_reduction A unicorn I), truth_spec.
  setoid_rewrite andb_true_iff; reflexivity.
Qed.

Lemma exists_unicorn_interpretation M p sigma i :
  neval M (exists_unicorn p) sigma i = truth (boolean_truth M)
    (exists u, andb (cn_star M unicorn i u) (neval M p (put sigma e 0 u) i) = true).
Proof. reflexivity. Qed.

Lemma named_tv_entity M (A : admissible M) v n sigma i :
  neval M (rt v (rname n) ru) sigma i =
  word_value M (ltv v) i (fun j P => P j (rigid M (sigma e 0)))
    (fun j => constants M e (name_code n) j).
Proof. rewrite (name_concept_rigid A n i); reflexivity. Qed.

Theorem reading_seek_re M (A : admissible M) sigma i :
  eval M (translate_closed seeks_unicorn_re) (empty_env M) sigma i = neval M rf_seek_re sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [seeks_unicorn_re denote].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_seek_re.
  rewrite exists_unicorn_interpretation.
  apply truth_congr; setoid_rewrite (named_tv_entity A); reflexivity.
Qed.

Theorem reading_about_re M (A : admissible M) sigma i :
  eval M (translate_closed talks_unicorn_re) (empty_env M) sigma i = neval M rf_about_re sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [talks_unicorn_re some_unicorn denote].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_about_re.
  rewrite exists_unicorn_interpretation; reflexivity.
Qed.

Lemma tv_entity_body M (A : admissible M) v (O : extensional_tv v) sigma x i :
  neval M (rt v (ND ry) ru) (put sigma ic 3 x) i =
  word_value M (ltv v) i (fun j P => P j (rigid M (sigma e 0))) x.
Proof. rewrite (@tv_singleton_reduction M A v O); reflexivity. Qed.

Lemma control_entity_interpretation M (A : admissible M) control v (O : extensional_tv v) sigma i :
  neval M (rcontrol control (NU (NL ic 3 (rt v (ND ry) ru))) (NU (rname john))) sigma i =
  word_value M (lcontrol control) i
    (fun j x => word_value M (ltv v) j (fun k P => P k (rigid M (sigma e 0))) x)
    (fun j => constants M e (name_code john) j).
Proof.
  unfold word_value; cbn [rcontrol nword rname neval].
  f_equal; apply (function_extensionality M); intro j.
  apply (function_extensionality M); intro x; apply (tv_entity_body A v O).
Qed.

Theorem reading_try_re M (A : admissible M) sigma i :
  eval M (translate_closed tries_unicorn_re) (empty_env M) sigma i = neval M rf_try_re sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [tries_unicorn_re some_unicorn denote].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_try_re.
  rewrite exists_unicorn_interpretation.
  apply truth_congr; setoid_rewrite (control_entity_interpretation A try_to find I); reflexivity.
Qed.

Lemma wish_entity_interpretation M (A : admissible M) sigma i :
  neval M (rcontrol wish_to (NU (NL ic 3 find_eat_body)) (NU (rname john))) sigma i =
  word_value M (lcontrol wish_to) i (fun j x => andb
    (word_value M (ltv find) j (fun k P => P k (rigid M (sigma e 0))) x)
    (word_value M (ltv eat) j (fun k P => P k (rigid M (sigma e 0))) x))
    (fun j => constants M e (name_code john) j).
Proof.
  unfold word_value; cbn [rcontrol nword rname neval].
  f_equal; apply (function_extensionality M); intro j.
  apply (function_extensionality M); intro x; cbn [find_eat_body neval].
  rewrite (tv_entity_body A find I), (tv_entity_body A eat I); reflexivity.
Qed.

Theorem reading_wish_re M (A : admissible M) sigma i :
  eval M (translate_closed wish_unicorn_re) (empty_env M) sigma i = neval M rf_wish_re sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [wish_unicorn_re some_unicorn find_and_eat denote jvalue].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_wish_re; rewrite exists_unicorn_interpretation.
  apply truth_congr; setoid_rewrite (wish_entity_interpretation A); reflexivity.
Qed.

Lemma find_eat_unicorn_body M (A : admissible M) sigma i x :
  dvalue M a_or_an (word_value M (lcn unicorn) i) i (fun j y => andb
    (word_value M (ltv find) j (fun k P => P k y) x)
    (word_value M (ltv eat) j (fun k P => P k y) x)) =
  neval M (NL ic 3 (exists_unicorn find_eat_body)) sigma i x.
Proof.
  rewrite (outer_unicorn_value A); cbn [neval]; rewrite exists_unicorn_interpretation.
  apply truth_congr.
  setoid_rewrite (@tv_singleton_reduction M A find I).
  setoid_rewrite (@tv_singleton_reduction M A eat I).
  cbn [find_eat_body neval]; unfold_reading; reflexivity.
Qed.

Theorem reading_wish_dicto M (A : admissible M) sigma i :
  eval M (translate_closed wish_unicorn_dicto) (empty_env M) sigma i = neval M rf_wish_dicto sigma i.
Proof.
  rewrite closed_translation_interpretation.
  change (word_value M (lcontrol wish_to) i
    (fun j x => dvalue M a_or_an (word_value M (lcn unicorn) j) j (fun k y => andb
      (word_value M (ltv find) k (fun l P => P l y) x)
      (word_value M (ltv eat) k (fun l P => P l y) x)))
    (fun j => constants M e (name_code john) j) = neval M rf_wish_dicto sigma i).
  unfold word_value; cbn [rf_wish_dicto rcontrol nword rname neval].
  f_equal; apply (function_extensionality M); intro j.
  apply (function_extensionality M); intro x; apply (find_eat_unicorn_body A).
Qed.

Lemma john_find_eat_interpretation M (A : admissible M) sigma i :
  neval M john_find_eat_formula sigma i = andb
    (word_value M (ltv find) i (fun j P => P j (rigid M (sigma e 0)))
      (fun j => constants M e (name_code john) j))
    (word_value M (ltv eat) i (fun j P => P j (rigid M (sigma e 0)))
      (fun j => constants M e (name_code john) j)).
Proof.
  cbn [john_find_eat_formula neval]; rewrite (named_tv_entity A), (named_tv_entity A); reflexivity.
Qed.

Lemma belief_entity_interpretation M (A : admissible M) sigma i :
  neval M (rattitude believe_that (NU john_find_eat_formula) (NU (rname mary))) sigma i =
  word_value M (latt believe_that) i (fun j => andb
    (word_value M (ltv find) j (fun k P => P k (rigid M (sigma e 0)))
      (fun k => constants M e (name_code john) k))
    (word_value M (ltv eat) j (fun k P => P k (rigid M (sigma e 0)))
      (fun k => constants M e (name_code john) k)))
    (fun j => constants M e (name_code mary) j).
Proof.
  unfold word_value; cbn [rattitude nword rname neval].
  f_equal; apply (function_extensionality M); intro j; apply (john_find_eat_interpretation A).
Qed.

Theorem reading_belief_re M (A : admissible M) sigma i :
  eval M (translate_closed belief_unicorn_re) (empty_env M) sigma i = neval M rf_belief_re sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [belief_unicorn_re some_unicorn john_finds_and_eats denote jvalue].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_belief_re; rewrite exists_unicorn_interpretation.
  apply truth_congr; setoid_rewrite (belief_entity_interpretation A); reflexivity.
Qed.

Lemma john_finds_eats_unicorn M (A : admissible M) sigma i :
  dvalue M a_or_an (word_value M (lcn unicorn) i) i (fun j x => andb
    (word_value M (ltv find) j (fun k P => P k x) (fun k => constants M e (name_code john) k))
    (word_value M (ltv eat) j (fun k P => P k x) (fun k => constants M e (name_code john) k))) =
  neval M (exists_unicorn john_find_eat_formula) sigma i.
Proof.
  rewrite (outer_unicorn_value A), exists_unicorn_interpretation.
  apply truth_congr; setoid_rewrite (john_find_eat_interpretation A); reflexivity.
Qed.

Theorem reading_belief_dicto M (A : admissible M) sigma i :
  eval M (translate_closed belief_unicorn_dicto) (empty_env M) sigma i = neval M rf_belief_dicto sigma i.
Proof.
  rewrite closed_translation_interpretation.
  change (word_value M (latt believe_that) i
    (fun j => dvalue M a_or_an (word_value M (lcn unicorn) j) j (fun k x => andb
      (word_value M (ltv find) k (fun l P => P l x) (fun l => constants M e (name_code john) l))
      (word_value M (ltv eat) k (fun l P => P l x) (fun l => constants M e (name_code john) l))))
    (fun j => constants M e (name_code mary) j) = neval M rf_belief_dicto sigma i).
  unfold word_value; cbn [rf_belief_dicto rattitude nword rname neval].
  f_equal; apply (function_extensionality M); intro j; apply (john_finds_eats_unicorn A).
Qed.

Theorem reading_joint_seeking M (A : admissible M) sigma i :
  eval M (translate_closed joint_seeking) (empty_env M) sigma i = neval M rf_joint_seeking sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [joint_seeking some_unicorn denote jvalue].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_joint_seeking; rewrite exists_unicorn_interpretation; apply truth_congr.
  cbn [neval]; setoid_rewrite (named_tv_entity A); reflexivity.
Qed.

Theorem reading_joint_control M (A : admissible M) first second sigma i :
  eval M (translate_closed (joint_control first second)) (empty_env M) sigma i =
  neval M (rf_joint_control first second) sigma i.
Proof.
  rewrite closed_translation_interpretation.
  cbn [joint_control some_unicorn denote jvalue].
  pose proof (outer_unicorn_value A) as U; unfold word_value in U; rewrite U; clear U.
  unfold rf_joint_control; rewrite exists_unicorn_interpretation; apply truth_congr.
  cbn [neval]; setoid_rewrite (control_entity_interpretation A first find I).
  setoid_rewrite (control_entity_interpretation A second eat I); reflexivity.
Qed.

Definition reading_pairs : list (tree ct * ntm t) := [
  (bill_walks, rf_bill_walks); (a_man_walks, rf_a_man);
  (every_man_walks, rf_every_man); (the_man_walks, rf_the_man);
  (finds_unicorn, rf_finds);
  (seeks_unicorn_dicto, rf_seek_dicto); (seeks_unicorn_re, rf_seek_re);
  (tries_unicorn_dicto, rf_try_dicto); (tries_unicorn_re, rf_try_re);
  (talks_unicorn_dicto, rf_about_dicto); (talks_unicorn_re, rf_about_re);
  (bill_is_mary, rf_identity); (bill_is_man, rf_predication);
  (temperature_is_ninety, rf_temperature_identity); (temperature_rises, rf_temperature_rises);
  (ninety_rises, rf_ninety_rises); (a_price_rises, rf_price);
  (woman_loves_every_man, rf_surface_scope); (every_man_loved_by_a_woman, rf_inverse_scope);
  (wish_unicorn_dicto, rf_wish_dicto); (wish_unicorn_re, rf_wish_re);
  (belief_unicorn_dicto, rf_belief_dicto); (belief_unicorn_re, rf_belief_re);
  (joint_seeking, rf_joint_seeking);
  (joint_control try_to wish_to, rf_joint_control try_to wish_to);
  (joint_control wish_to try_to, rf_joint_control wish_to try_to)
].

Example reading_pairs_cover_catalogue :
  map fst reading_pairs = flat_map snd catalogue ++
    [joint_control try_to wish_to; joint_control wish_to try_to] /\
  List.length reading_pairs = 26.
Proof. split; reflexivity. Qed.

Theorem all_listed_reading_formulas M (A : admissible M) sigma i :
  Forall (fun pair => eval M (translate_closed (fst pair)) (empty_env M) sigma i =
    neval M (snd pair) sigma i) reading_pairs.
Proof.
  repeat constructor; auto using reading_bill_walks, reading_a_man, reading_every_man,
    reading_the_man, reading_finds, reading_seek_dicto, reading_seek_re,
    reading_try_dicto, reading_try_re, reading_about_dicto, reading_about_re,
    reading_identity, reading_predication, reading_temperature_identity,
    reading_temperature_rises, reading_ninety_rises, reading_price,
    reading_surface_scope, reading_inverse_scope, reading_wish_dicto, reading_wish_re,
    reading_belief_dicto, reading_belief_re, reading_joint_seeking, reading_joint_control.
  all: cbn [fst snd]; apply (reading_joint_control A).
Qed.

Corollary all_listed_compiled_formulas M (A : admissible M) sigma i :
  Forall (fun pair => eval M (translate_closed (fst pair)) (empty_env M) sigma i =
    eval M (embed_named (snd pair)) (empty_env M) sigma i) reading_pairs.
Proof.
  eapply Forall_impl; [|apply (all_listed_reading_formulas A)].
  intros pair H; rewrite embed_named_interpretation; exact H.
Qed.
