(* Rosch 1978, Principles of Categorization: bounded R2-03/R2-04 pilot.
   Source: local reformatted PDF pp.5-6 (cue validity), pp.10-16
   (typicality and its limits). Full source reading and frozen inventory:
   atlas_data/campaigns/cohort2_2026_09_13_rosch_inventory.md.

   Finite frequency data, Boolean predicates and ordinal scores are explicit
   restrictions. No cognitive processing/learning algorithm is attributed to
   Rosch. Fixed-cue monotonicity tests an encoding, NOT the source's
   category-specific attribute account. Examples below use constructed data.
   Zero-frequency cues are undefined at the public optional interface.
   No axioms/admissions; all empirical assignments remain inputs. *)
From Coq Require Import List Bool QArith Lqa Lia Field.
Import ListNotations.
Open Scope Q_scope.

Module Frequency.
Section Data.
Variable A : Type.

(* A list of observations: repetitions represent observed frequency. *)
Fixpoint count (sample : list A) (event : A -> bool) : Q :=
  match sample with
  | [] => 0
  | x :: xs => (if event x then 1 else 0) + count xs event
  end.

Definition included_on (sample : list A) (small large : A -> bool) :=
  forall x, In x sample -> small x = true -> large x = true.

Lemma count_nonnegative : forall sample event, 0 <= count sample event.
Proof.
  intros sample event; induction sample as [|x xs IH]; cbn; [lra|].
  destruct (event x); lra.
Qed.

Lemma count_monotone : forall sample small large,
  included_on sample small large -> count sample small <= count sample large.
Proof.
  intros sample small large; induction sample as [|x xs IH]; intros H; cbn.
  - lra.
  - assert (Ht : included_on xs small large).
    { intros y Hy; apply H; right; exact Hy. }
    specialize (IH Ht).
    assert (Hx : small x = true -> large x = true) by (apply H; left; reflexivity).
    destruct (small x), (large x); cbn in *; try discriminate; lra.
Qed.

Definition joint (category cue : A -> bool) :=
  fun x => category x && cue x.

Lemma joint_count_le_cue : forall sample category cue,
  count sample (joint category cue) <= count sample cue.
Proof.
  intros; apply count_monotone; intros x Hx H.
  apply andb_true_iff in H; tauto.
Qed.

(* Internal rational expression; source conditioning requires positive cue
   count. Q division's total zero convention is NOT the public semantics. *)
Definition cue_ratio sample category cue :=
  count sample (joint category cue) / count sample cue.

Definition cue_validity sample category cue : option Q :=
  if Qeq_dec (count sample cue) 0 then None
  else Some (cue_ratio sample category cue).

Theorem undefined_exactly_zero_cue : forall sample category cue,
  cue_validity sample category cue = None <-> count sample cue == 0.
Proof.
  intros; unfold cue_validity; destruct (Qeq_dec (count sample cue) 0);
    split; intros; try assumption; try reflexivity; try contradiction; discriminate.
Qed.

Theorem positive_cue_is_defined : forall sample category cue,
  0 < count sample cue ->
  cue_validity sample category cue = Some (cue_ratio sample category cue).
Proof.
  intros sample category cue H; unfold cue_validity.
  destruct (Qeq_dec (count sample cue) 0); [lra | reflexivity].
Qed.

Theorem cue_ratio_range : forall sample category cue,
  0 < count sample cue -> 0 <= cue_ratio sample category cue <= 1.
Proof.
  intros sample category cue H.
  pose proof (count_nonnegative sample (joint category cue)) as Hn.
  pose proof (joint_count_le_cue sample category cue) as Hb.
  unfold cue_ratio; split.
  - apply Qle_shift_div_l; [exact H | lra].
  - apply Qle_shift_div_r; [exact H | lra].
Qed.

Theorem cue_ratio_monotone : forall sample small large cue,
  included_on sample small large -> 0 < count sample cue ->
  cue_ratio sample small cue <= cue_ratio sample large cue.
Proof.
  intros sample small large cue Hsub Hpos; unfold cue_ratio, Qdiv.
  apply Qmult_le_compat_r.
  - apply count_monotone; intros x Hx Hj.
    unfold joint in *; apply andb_true_iff in Hj; apply andb_true_iff.
    destruct Hj as [Hs Hc]; split; [exact (Hsub x Hx Hs) | exact Hc].
  - apply Qinv_le_0_compat; lra.
Qed.

(* Weighted extension of the unweighted source sum. The SAME list is used
   for both categories in the monotonicity theorem. Source attribute lists
   may instead differ between categories. *)
Fixpoint score sample (category : A -> bool) (cues : list ((A -> bool) * Q)) : Q :=
  match cues with
  | [] => 0
  | (cue, weight) :: rest => weight * cue_ratio sample category cue +
                            score sample category rest
  end.

Definition admissible sample (cues : list ((A -> bool) * Q)) :=
  Forall (fun cw => 0 <= snd cw /\ 0 < count sample (fst cw)) cues.

Theorem fixed_cue_score_monotone : forall sample small large cues,
  included_on sample small large -> admissible sample cues ->
  score sample small cues <= score sample large cues.
Proof.
  intros sample small large cues Hsub; induction cues as [|[cue weight] rest IH];
    intros Hgood; cbn; [lra|].
  inversion Hgood as [|cw cs [Hw Hc] Hr]; subst; cbn in Hw, Hc.
  apply Qplus_le_compat; [|apply IH; exact Hr].
  pose proof (cue_ratio_monotone sample small large cue Hsub Hc) as Hm.
  setoid_rewrite Qmult_comm; apply Qmult_le_compat_r; assumption.
Qed.

(* Rules out a STRICT maximum over a containing category; ties and a weak
   maximum are not excluded. It does not use category-specific cue lists. *)
Theorem no_strict_interior_maximum_with_fixed_cues : forall sample small large cues,
  included_on sample small large -> admissible sample cues ->
  ~ score sample large cues < score sample small cues.
Proof.
  intros sample small large cues Hsub Hgood Hlt.
  pose proof (fixed_cue_score_monotone sample small large cues Hsub Hgood); lra.
Qed.

(* Same observations, alternative route: normalize event counts first,
   then condition. This is a restricted representation check, not a second
   fitted cognitive model or a general probability-space construction. *)
Definition event_probability sample event :=
  count sample event / count sample (fun _ => true).

Definition conditional_from_probabilities sample category cue :=
  event_probability sample (joint category cue) / event_probability sample cue.

Theorem normalization_cancels : forall sample category cue,
  0 < count sample (fun _ => true) -> 0 < count sample cue ->
  conditional_from_probabilities sample category cue == cue_ratio sample category cue.
Proof.
  intros sample category cue Htotal Hcue.
  unfold conditional_from_probabilities, event_probability, cue_ratio.
  field; split; lra.
Qed.
End Data.
End Frequency.

Module ConstructedCategories.
(* Assigned example inspired by the source hierarchy, NOT experimental data.
   Two distinct features may be coextensive on this small sample. *)
Inductive object := kitchen_chair | dining_chair | table | stone.
Definition sample := [kitchen_chair; dining_chair; table; stone].
Definition furniture x := match x with stone => false | _ => true end.
Definition chair x := match x with kitchen_chair | dining_chair => true | _ => false end.
Definition kitchen x := match x with kitchen_chair => true | _ => false end.
Definition seat := chair.
Definition back := chair.
Definition support := furniture.
Definition common_cues := [(seat, 1); (back, 1); (support, 1)].
Definition furniture_cues := [(support, 1)].
Definition chair_cues := [(seat, 1); (back, 1)].
Definition kitchen_cues := chair_cues.

Example hierarchy_and_positive_cues :
  Frequency.included_on object sample kitchen chair /\
  Frequency.included_on object sample chair furniture /\
  Frequency.admissible object sample common_cues.
Proof.
  repeat split.
  - intros x _ H; destruct x; cbn in *; congruence.
  - intros x _ H; destruct x; cbn in *; congruence.
  - unfold Frequency.admissible, common_cues.
    repeat (constructor; [split; vm_compute; congruence |]); constructor.
Qed.

Example fixed_cues_favor_parent :
  Frequency.score object sample chair common_cues == (8#3) /\
  Frequency.score object sample furniture common_cues == 3.
Proof. split; vm_compute; reflexivity. Qed.

(* Category-specific feature selection is supplied, NOT learned or derived.
   The comparison is a semantic sensitivity example, not encoding robustness. *)
Example assigned_category_cues_allow_interior_maximum :
  Frequency.score object sample furniture furniture_cues == 1 /\
  Frequency.score object sample chair chair_cues == 2 /\
  Frequency.score object sample kitchen kitchen_cues == 1 /\
  Frequency.score object sample furniture furniture_cues <
    Frequency.score object sample chair chair_cues /\
  Frequency.score object sample kitchen kitchen_cues <
    Frequency.score object sample chair chair_cues.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example undefined_is_not_defined_zero :
  Frequency.cue_validity object sample chair (fun _ => false) = None /\
  Frequency.cue_validity object sample (fun _ => false) seat =
    Some (Frequency.cue_ratio object sample (fun _ => false) seat) /\
  Frequency.cue_ratio object sample (fun _ => false) seat == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Example negative_weight_breaks_monotonicity :
  Frequency.score object sample furniture [(support, -1)] <
    Frequency.score object sample chair [(support, -1)].
Proof. vm_compute; reflexivity. Qed.

Example dropping_inclusion_breaks_monotonicity :
  ~ Frequency.included_on object sample furniture chair /\
  Frequency.cue_ratio object sample chair support <
    Frequency.cue_ratio object sample furniture support.
Proof.
  split.
  - intros H; assert (Hm : In table sample) by (cbn; auto).
    specialize (H table Hm eq_refl); discriminate.
  - vm_compute; reflexivity.
Qed.
End ConstructedCategories.

Module Typicality.
Section Orders.
Variable A : Type.
Definition at_least (rank : A -> nat) x y := (rank y <= rank x)%nat.
Definition best (member : A -> bool) (rel : A -> A -> Prop) x :=
  member x = true /\ forall y, member y = true -> rel x y.

Theorem score_order_is_preorder : forall rank,
  (forall x, at_least rank x x) /\
  (forall x y z, at_least rank x y -> at_least rank y z -> at_least rank x z).
Proof. unfold at_least; intros; split; intros; lia. Qed.

(* Explicit equivalence is needed only on members. No cardinal distances or
   unique maximum are introduced by this representation correspondence. *)
Theorem best_preserved_by_order : forall member r s,
  (forall x y, member x = true -> member y = true -> (r x y <-> s x y)) ->
  forall x, best member r x <-> best member s x.
Proof.
  intros member r s H x; unfold best; split; intros [Hm Hb]; split; [exact Hm| |exact Hm|].
  - intros y Hy; apply (proj1 (H x y Hm Hy)), Hb, Hy.
  - intros y Hy; apply (proj2 (H x y Hm Hy)), Hb, Hy.
Qed.

Theorem positive_affine_rescaling_preserves_order : forall rank a b,
  (0 < a)%nat -> forall x y,
  at_least rank x y <-> at_least (fun z => (a * rank z + b)%nat) x y.
Proof. unfold at_least; intros; split; intros; nia. Qed.
End Orders.

Module ConstructedBirds.
Inductive item := robin | sparrow | penguin | rock.
Definition bird x := match x with rock => false | _ => true end.
(* The source motivates qualitative typicality differences, NOT these numbers
   or this tie. Membership remains independent of the assigned scale. *)
Definition rank x : nat := match x with robin | sparrow => 2 | penguin => 1 | rock => 0 end.
Definition rank_rescaled x : nat := (3 * rank x + 7)%nat.
Definition ordinal x y : Prop :=
  match x, y with
  | robin, _ | sparrow, _ => True
  | penguin, penguin | penguin, rock | rock, rock => True
  | _, _ => False
  end.

Theorem ordinal_matches_scores : forall x y,
  ordinal x y <-> at_least item rank x y.
Proof. intros x y; destruct x, y; unfold at_least; cbn; intuition lia. Qed.

Example members_can_differ_in_typicality :
  bird robin = true /\ bird penguin = true /\ (rank penguin < rank robin)%nat.
Proof. repeat split; cbn; auto. Qed.

Example tied_best_members :
  best item bird ordinal robin /\ best item bird ordinal sparrow /\ robin <> sparrow.
Proof.
  unfold best; repeat split; try discriminate; intros y _; destruct y; exact I.
Qed.

Theorem no_unique_best_member : ~ exists! x, best item bird ordinal x.
Proof.
  intros [x [Hx Hu]].
  destruct tied_best_members as [Hr [Hs Hne]].
  pose proof (Hu robin Hr); pose proof (Hu sparrow Hs); congruence.
Qed.

Theorem rescaling_preserves_best : forall x,
  best item bird ordinal x <-> best item bird (at_least item rank_rescaled) x.
Proof.
  apply best_preserved_by_order; intros x y _ _.
  rewrite ordinal_matches_scores; unfold rank_rescaled.
  apply positive_affine_rescaling_preserves_order; lia.
Qed.

(* Same ranking, two possible memberships: the order alone supplies no
   classifier. The alternative is a countermodel, NOT a linguistic claim
   that rocks are birds. *)
Example ranking_does_not_determine_membership :
  exists m1 m2 : item -> bool,
    m1 rock <> m2 rock /\
    (forall x y, at_least item rank x y <-> at_least item rank x y).
Proof. exists bird, (fun _ => true); split; [discriminate|tauto]. Qed.
End ConstructedBirds.
End Typicality.
