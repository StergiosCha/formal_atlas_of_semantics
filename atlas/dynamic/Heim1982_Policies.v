(* Heim 1982 / 2011 pp.244-252: compare explicit policy completions.
   None is selected as a production default or attributed as a completed source
   theory. Local/global are choices at a fresh-description repair request.
   Bridge-only is a permissive structural bound, not appropriateness.
   World-safe and assignment-safe are different candidate restrictions.
   Keep-all attention below is the existing fixed test fixture. No new axioms. *)
From Coq Require Import List Arith Bool Lia.
From dynamic Require Import Heim1982 Heim1982_Examples Heim1982_Extensions
  Heim1982_Indexed Heim1982_Binding Heim1982_Integration Heim1982_EndToEnd.
Import ListNotations.
Set Implicit Arguments.

Inductive RepairSite := NoRepair | LocalRepair | GlobalRepair.

Section NegationChoices.
Context {W D : Type}.
Definition description_body i (P Q : W -> D -> Prop) := Seq (definite i P) (unary i Q).
Definition description_repair (F : @File W D) i P := update (indefinite i P) F.
Definition local_result F i P Q := negative_result F (update (description_body i P Q) (description_repair F i P)).
Definition global_result F i P Q := negative_result (description_repair F i P)
  (update (description_body i P Q) (description_repair F i P)).
Definition selected_negation site F i P Q : option (@File W D) :=
  match site with
  | NoRepair => None
  | LocalRepair => Some (local_result F i P Q)
  | GlobalRepair => Some (global_result F i P Q)
  end.
Definition at_request (F : @File W D) (p : @Formula W D) (G : @File W D) : RepairPolicy :=
  fun actual trigger repaired => actual = F /\ trigger = p /\ repaired = G.

Lemma repaired_description_licensed : forall F i P Q,
  licensed (description_body i P Q) (description_repair F i P).
Proof. intros; simpl; unfold entails; simpl; firstorder. Qed.
Lemma fresh_description_is_unlicensed : forall F i P Q,
  ~ dom F i -> ~ licensed (description_body i P Q) F.
Proof. intros F i P Q Hfresh; simpl; tauto. Qed.
Theorem no_repair_blocks_fresh_description : forall F i P Q G,
  ~ dom F i -> ~ Run (fun _ _ _ => False) (Not (description_body i P Q)) F G.
Proof.
  intros F i P Q G Hfresh Hrun; apply no_repair_is_exact in Hrun.
  destruct Hrun as [_ HL]; eapply fresh_description_is_unlicensed; eauto.
Qed.
Theorem selected_local_is_a_valid_run : forall F i P Q,
  ~ dom F i -> Run (at_request F (description_body i P Q) (description_repair F i P))
    (Not (description_body i P Q)) F (local_result F i P Q).
Proof.
  intros F i P Q Hfresh; apply local_negation_accommodation.
  - repeat split; reflexivity.
  - apply situation_bridge_adds_information.
  - apply fresh_description_is_unlicensed; exact Hfresh.
  - apply repaired_description_licensed.
Qed.
Theorem selected_global_is_a_valid_run : forall F i P Q,
  ~ dom F i -> Run (at_request F (Not (description_body i P Q)) (description_repair F i P))
    (Not (description_body i P Q)) F (global_result F i P Q).
Proof.
  intros F i P Q Hfresh; apply global_negation_accommodation.
  - repeat split; reflexivity.
  - apply situation_bridge_adds_information.
  - apply fresh_description_is_unlicensed; exact Hfresh.
  - apply repaired_description_licensed.
Qed.
Theorem local_truth_condition : forall F i P Q w g,
  condition_B F -> ~ dom F i ->
  (sat (local_result F i P Q) w g <->
   sat F w g /\ ~ exists x, P w x /\ Q w x).
Proof.
  intros F i P Q w g HB Hfresh; split.
  - intros [HF Hnone]; split; [exact HF|].
    intros [x [HP HQ]]; apply Hnone; exists (put g i x); split.
    + intros j Hj; symmetry; apply put_other; intro Eq; subst; contradiction.
    + change (((sat F w (put g i x) /\ P w (put g i x i)) /\ P w (put g i x i)) /\ Q w (put g i x i)).
      rewrite put_same; repeat split; auto.
      apply (proj2 (fresh_put F HB w g i x Hfresh)); exact HF.
  - intros [HF Hnone]; split; [exact HF|].
    intros [h [_ [[[HH HP] _] HQ]]]; apply Hnone; exists (h i); auto.
Qed.
Theorem global_truth_condition : forall F i P Q w g,
  sat (global_result F i P Q) w g <-> sat F w g /\ P w (g i) /\ ~ Q w (g i).
Proof.
  intros F i P Q w g; split.
  - intros [[HF HP] Hnone]; repeat split; auto.
    intro HQ; apply Hnone; exists g; split; [apply agree_refl|].
    change (((sat F w g /\ P w (g i)) /\ P w (g i)) /\ Q w (g i)); auto.
  - intros [HF [HP HQ]]; split; [split; assumption|].
    intros [h [Ha [[[HH HP'] _] HQ']]].
    assert (E : g i = h i) by (apply Ha; simpl; auto).
    apply HQ; rewrite E; exact HQ'.
Qed.
Theorem local_world_truth : forall F i P Q w,
  condition_B F -> ~ dom F i ->
  (world_content (local_result F i P Q) w <->
   world_content F w /\ ~ exists x, P w x /\ Q w x).
Proof.
  intros F i P Q w HB Hfresh; split.
  - intros [g H]; apply (@local_truth_condition F i P Q w g HB Hfresh) in H.
    destruct H as [HF Hnone]; split; [exists g; exact HF|exact Hnone].
  - intros [[g HF] Hnone]; exists g.
    apply (@local_truth_condition F i P Q w g HB Hfresh); auto.
Qed.
Theorem global_world_truth : forall F i P Q w,
  condition_B F -> ~ dom F i ->
  (world_content (global_result F i P Q) w <->
   world_content F w /\ exists x, P w x /\ ~ Q w x).
Proof.
  intros F i P Q w HB Hfresh.
  assert (E : world_content (global_result F i P Q) w <->
    world_content (update (indefinite i (fun v x => P v x /\ ~ Q v x)) F) w).
  { unfold world_content; setoid_rewrite global_truth_condition; simpl; firstorder. }
  rewrite E; apply fresh_indefinite_truth; assumption.
Qed.
Theorem local_global_domain_difference : forall F i P Q,
  ~ dom F i ->
  ~ dom (local_result F i P Q) i /\ dom (global_result F i P Q) i.
Proof. intros; split; [exact H|simpl; auto]. Qed.

Theorem selected_negation_has_unique_output : forall site F i P Q G H,
  selected_negation site F i P Q = Some G -> selected_negation site F i P Q = Some H -> G = H.
Proof. intros; congruence. Qed.
End NegationChoices.

Section ProxyPolicies.
Context {W D : Type}.
Definition Permit := @Event W D -> nat -> @File W D -> @File W D -> nat -> (W -> D -> Prop) -> Prop.
Definition deny_proxy : Permit := fun _ _ _ _ _ _ => False.
Definition bridge_only : Permit := fun _ _ F G i P => G = update (indefinite i P) F.
Definition world_safe : Permit := fun event j F G i P =>
  bridge_only event j F G i P /\ forall w, world_content F w -> exists x, P w x.
Definition assignment_safe : Permit := fun event j F G i P =>
  bridge_only event j F G i P /\ forall w g, sat F w g -> sat G w g.
Definition included (a b : Permit) := forall event j F G i P,
  a event j F G i P -> b event j F G i P.
Theorem assignment_safe_implies_world_safe : included assignment_safe world_safe.
Proof.
  intros event j F G i P [HG Hsat]; split; [exact HG|].
  intros w [g HF]; specialize (Hsat w g HF); unfold bridge_only in HG; subst G.
  exists (g i); exact (proj2 Hsat).
Qed.
Theorem world_safe_implies_bridge_only : included world_safe bridge_only.
Proof. intros event j F G i P [H _]; exact H. Qed.
Theorem deny_is_least_policy : forall policy, included deny_proxy policy.
Proof. intros policy event j F G i P H; contradiction. Qed.
Theorem enlarging_permission_preserves_runs : forall attention sound a b command initial final,
  included a b -> Execute attention sound a command initial final ->
  Execute attention sound b command initial final.
Proof.
  intros attention sound a b command initial final Hab Hrun; induction Hrun;
    eauto using execute_core, execute_read, execute_direct, execute_proxy, execute_then.
Qed.
Theorem world_safe_preserves_worlds : forall event j F G i P,
  condition_B F -> ~ dom F i -> world_safe event j F G i P ->
  forall w, world_content G w <-> world_content F w.
Proof.
  intros event j F G i P HB Hfresh [HG Hworld]; unfold bridge_only in HG; subst G.
  apply existentially_supported_introduction_preserves_worlds; assumption.
Qed.
Theorem assignment_safe_preserves_every_assignment : forall event j F G i P,
  assignment_safe event j F G i P -> forall w g, sat G w g <-> sat F w g.
Proof.
  intros event j F G i P [HG Hsat] w g; split; [|apply Hsat].
  unfold bridge_only in HG; subst G; apply update_contractive.
Qed.
Theorem world_safe_characterizes_world_preservation : forall event j F G i P,
  condition_B F -> ~ dom F i -> bridge_only event j F G i P ->
  (world_safe event j F G i P <-> forall w, world_content G w <-> world_content F w).
Proof.
  intros event j F G i P HB Hfresh HG; split.
  - apply world_safe_preserves_worlds; assumption.
  - intro HE; split; [exact HG|].
    intros w HF; destruct (proj2 (HE w) HF) as [g Hsat].
    unfold bridge_only in HG; subst G; exists (g i); exact (proj2 Hsat).
Qed.
Theorem factive_program_allowed_by_world_safe : forall access P Q F h,
  (forall w, access w w) -> ~ dom F 1 ->
  Execute keep_all keep_all_sound world_safe (modal_proxy_program access P Q)
    {|current := F; history := h|} (after_assertion access P Q F h).
Proof.
  intros access P Q F h Href Hfresh; apply complete_modal_proxy_core_run; [exact Hfresh|].
  split; [reflexivity|].
  intros w [g [HF HM]].
  exact (proj1 (compiled_modal_truth access P w g) HM w (Href w)).
Qed.
Theorem bridge_only_allows_modal_program : forall access P Q F h,
  ~ dom F 1 ->
  Execute keep_all keep_all_sound bridge_only (modal_proxy_program access P Q)
    {|current := F; history := h|} (after_assertion access P Q F h).
Proof. intros; apply complete_modal_proxy_core_run; auto; reflexivity. Qed.
Theorem universal_description_allowed_by_assignment_safe : forall access Q F h,
  ~ dom F 1 ->
  Execute keep_all keep_all_sound assignment_safe
    (modal_proxy_program access (fun _ _ => True) Q) {|current := F; history := h|}
    (after_assertion access (fun _ _ => True) Q F h).
Proof.
  intros; apply complete_modal_proxy_core_run; [assumption|].
  split; [reflexivity|intros w g HF; split; [exact HF|exact I]].
Qed.
Theorem deny_blocks_modal_program : forall access P Q F h final,
  ~ Execute keep_all keep_all_sound deny_proxy (modal_proxy_program access P Q)
    {|current := F; history := h|} final.
Proof.
  intros access P Q F h final H; unfold modal_proxy_program in H.
  repeat match goal with
  | HR : Execute _ _ _ (Then _ _) _ _ |- _ => inversion HR; subst; clear HR
  end.
  eapply denying_permission_blocks_proxy; eassumption.
Qed.
End ProxyPolicies.

Module NegationModels.
Definition F : @File unit bool := empty_file.
Definition absent (_ : unit) (_ : bool) := False.
Definition king (_ : unit) (x : bool) := x = true.
Definition lunch (_ : unit) (_ : bool) := True.
Definition no_lunch (_ : unit) (_ : bool) := False.
Theorem absent_king_local_true_global_false :
  world_content (local_result F 0 absent lunch) tt /\
  ~ world_content (global_result F 0 absent lunch) tt.
Proof.
  split.
  - apply local_world_truth; [apply supported_implies_B, empty_supported|simpl; tauto|].
    split; [exists (fun _ => false); exact I|intros [x [H _]]; exact H].
  - rewrite global_world_truth.
    + intros [_ [x [H _]]]; exact H.
    + apply supported_implies_B, empty_supported.
    + simpl; tauto.
Qed.
Theorem existing_king_same_truth_different_next_pronoun :
  world_content (local_result F 0 king no_lunch) tt /\
  world_content (global_result F 0 king no_lunch) tt /\
  ~ licensed (Use 0) (local_result F 0 king no_lunch) /\
  licensed (Use 0) (global_result F 0 king no_lunch).
Proof.
  split.
  - apply local_world_truth; [apply supported_implies_B, empty_supported|simpl; tauto|].
    split; [exists (fun _ => false); exact I|intros [x [_ H]]; exact H].
  - split.
    + apply global_world_truth; [apply supported_implies_B, empty_supported|simpl; tauto|].
      split; [exists (fun _ => false); exact I|exists true; split; [reflexivity|tauto]].
    + apply local_global_domain_difference; simpl; tauto.
Qed.
End NegationModels.

Module ProxyModels.
Definition F : @File bool unit := empty_file.
Definition desires (_ v : bool) := v = true.
Definition P (w : bool) (_ : unit) := w = true.
Definition Q (_ : bool) (_ : unit) := True.
Definition input := after_read desires P F [].
Theorem desired_world_case_bridge_allowed :
  Execute keep_all keep_all_sound bridge_only (modal_proxy_program desires P Q)
    {|current := F; history := []|} (after_assertion desires P Q F []).
Proof. apply bridge_only_allows_modal_program; simpl; tauto. Qed.
Theorem desired_world_case_world_safe_blocks_proxy : forall final,
  ~ Execute keep_all keep_all_sound world_safe (Proxy 1 P) input final.
Proof.
  intros final H; apply proxy_has_recorded_authorized_origin in H.
  destruct H as [event [j [_ [_ [_ [_ [_ Hworld]]]]]]].
  assert (HF : world_content (current input) false).
  { exists (fun _ => tt); split; [exact I|].
    apply compiled_modal_truth; intros v Hv; exists tt; exact Hv. }
  destruct (Hworld false HF) as [x Hx]; discriminate Hx.
Qed.
Theorem desired_world_case_world_safe_blocks_program : forall final,
  ~ Execute keep_all keep_all_sound world_safe (modal_proxy_program desires P Q)
    {|current := F; history := []|} final.
Proof.
  intros final H; unfold modal_proxy_program in H.
  repeat match goal with
  | HR : Execute _ _ _ (Then _ _) _ _ |- _ => inversion HR; subst; clear HR
  | HR : Execute _ _ _ (Read _) _ _ |- _ => inversion HR; subst; clear HR
  end.
  eapply desired_world_case_world_safe_blocks_proxy; eassumption.
Qed.
Theorem desired_world_bridge_loses_actual_world :
  world_content (current input) false /\
  ~ world_content (current (after_assertion desires P Q F [])) false.
Proof.
  split.
  - exists (fun _ => tt); split; [exact I|].
    apply compiled_modal_truth; intros v Hv; exists tt; exact Hv.
  - intros [g [[_ HP] HQ]]; discriminate HP.
Qed.

Definition F2 : @File unit bool := empty_file.
Definition all_worlds (_ _ : unit) := True.
Definition witness (_ : unit) (x : bool) := x = true.
Definition anything (_ : unit) (_ : bool) := True.
Definition known_input := after_read all_worlds witness F2 [].
Theorem already_guaranteed_witness_world_safe_allows :
  Execute keep_all keep_all_sound world_safe (modal_proxy_program all_worlds witness anything)
    {|current := F2; history := []|} (after_assertion all_worlds witness anything F2 []).
Proof.
  apply factive_program_allowed_by_world_safe.
  - intros w; exact I.
  - simpl; tauto.
Qed.
Theorem already_guaranteed_witness_assignment_safe_blocks : forall final,
  ~ Execute keep_all keep_all_sound assignment_safe (Proxy 1 witness) known_input final.
Proof.
  intros final H; apply proxy_has_recorded_authorized_origin in H.
  destruct H as [event [j [_ [_ [_ [_ [HG Hsat]]]]]]].
  assert (HF : sat (current known_input) tt (fun _ => false)).
  { split; [exact I|apply compiled_modal_truth; intros v Hv; exists true; reflexivity]. }
  specialize (Hsat tt (fun _ => false) HF); unfold bridge_only in HG; rewrite HG in Hsat.
  destruct Hsat as [_ Hbad]; discriminate Hbad.
Qed.
Theorem already_guaranteed_witness_assignment_safe_blocks_program : forall final,
  ~ Execute keep_all keep_all_sound assignment_safe (modal_proxy_program all_worlds witness anything)
    {|current := F2; history := []|} final.
Proof.
  intros final H; unfold modal_proxy_program in H.
  repeat match goal with
  | HR : Execute _ _ _ (Then _ _) _ _ |- _ => inversion HR; subst; clear HR
  | HR : Execute _ _ _ (Read _) _ _ |- _ => inversion HR; subst; clear HR
  end.
  eapply already_guaranteed_witness_assignment_safe_blocks; eassumption.
Qed.
End ProxyModels.

Theorem bridge_only_is_strictly_more_permissive :
  ~ @included bool unit bridge_only world_safe.
Proof.
  intro Hinc.
  pose proof (enlarging_permission_preserves_runs Hinc ProxyModels.desired_world_case_bridge_allowed) as HR.
  eapply ProxyModels.desired_world_case_world_safe_blocks_program; exact HR.
Qed.
Theorem world_safe_is_strictly_more_permissive :
  ~ @included unit bool world_safe assignment_safe.
Proof.
  intro Hinc.
  pose proof (enlarging_permission_preserves_runs Hinc ProxyModels.already_guaranteed_witness_world_safe_allows) as HR.
  eapply ProxyModels.already_guaranteed_witness_assignment_safe_blocks_program; exact HR.
Qed.

Print Assumptions local_truth_condition.
Print Assumptions global_world_truth.
Print Assumptions enlarging_permission_preserves_runs.
Print Assumptions factive_program_allowed_by_world_safe.
Print Assumptions ProxyModels.already_guaranteed_witness_assignment_safe_blocks.
