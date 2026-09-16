(* Integration checks, Heim 1982 / 2011 pp.90-100,118-120,247-252.
   General truth theorems are source-linked; keep-all attention below is an
   explicit test fixture, NOT a proposed theory of prominence. Proxy permission
   remains a premise. No source-level acceptability verdict is inferred. *)
From Coq Require Import List Arith Bool Lia.
From dynamic Require Import Heim1982 Heim1982_Examples Heim1982_Extensions
  Heim1982_Indexed Heim1982_Binding Heim1982_Integration.
Import ListNotations.
Set Implicit Arguments.

Section EndToEnd.
Context {W D : Type}.
Definition keep_all (_ : @History W D) (F : @File W D) := dom F.
Definition keep_all_sound : forall h F i, keep_all h F i -> dom F i :=
  fun _ _ _ H => H.
Definition kept_event source (F : @File W D) : Event :=
  {| origin := source;
     snapshot := {| remembered_file := F; remembered_prominent := dom F;
       remembered_in_domain := fun _ H => H |} |}.
Lemma keep_all_records_each_frame : forall source files F h,
  In F files -> In (kept_event source F)
    (remember_all keep_all keep_all_sound source files h).
Proof.
  intros source files; induction files as [|G rest IH]; intros F h Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Eq|Hin].
    + subst G; cbn [remember_all]; apply remember_all_preserves_history; left; reflexivity.
    + apply IH; exact Hin.
Qed.

Definition top_tree : @Construal W D := CAtom 0 tt (fun _ _ => True).
Definition modal_tree access (P : W -> D -> Prop) :=
  CMust [] access (fun _ _ => True) top_tree (indefinite_tree 0 P).
Definition modal_query access P := compile_text (modal_tree access P).
Theorem modal_compiler_has_no_free_individuals : forall access P,
  free_indices (modal_query access P) = [].
Proof. reflexivity. Qed.
Theorem compiled_modal_truth : forall access P w g,
  satisfies (modal_query access P) w g <->
  forall v, access w v -> exists x, P v x.
Proof.
  intros access P w g; unfold modal_query.
  rewrite compiled_closed_text_truth by reflexivity.
  change ((forall v h, outside [] g h ->
    best access (fun _ _ => True) (fun _ _ => True) w v h ->
    exists a, outside [0] h a /\ True /\ P v (a 0)) <->
    forall v, access w v -> exists x, P v x).
  split.
  - intros H v Ha.
    assert (Ho : outside [] g g) by (intros i Hi; reflexivity).
    assert (Hb : best access (fun _ _ => True) (fun _ _ => True) w v g).
    { unfold best; auto. }
    destruct (H v g Ho Hb) as [a [_ [_ HP]]]; exists (a 0); exact HP.
  - intros H v h Ho [Ha _]; destruct (H v Ha) as [x HP].
    exists (put h 0 x); split; [apply outside_put; simpl; auto|].
    split; [exact I|rewrite put_same; exact HP].
Qed.

Definition modal_stage (F : @File W D) (P : W -> D -> Prop) :=
  indexed_frame (iunary 0 P)
    (indexed_frame (iunary 0 (fun _ _ => True))
      (indexed_frame (iconstant (fun _ => True)) (world_reset F))).
Theorem modal_trace_contains_description : forall access P F,
  In (modal_stage F P) (indexed_trace (modal_query access P) F).
Proof. intros; simpl; right; right; left; reflexivity. Qed.
Theorem modal_stage_retains_world_argument : forall F P w,
  world_content (modal_stage F P) w <-> exists x, P w x.
Proof.
  intros F P w; split.
  - intros [g [[[_ _] _] HP]]; exists (g 0); exact HP.
  - intros [x HP]; exists (fun _ => x); repeat split; auto.
Qed.

Definition after_read access P (F : @File W D) h : State :=
  {| current := indexed_test (modal_query access P) F;
     history := remember_all keep_all keep_all_sound (Some (modal_query access P))
       (indexed_trace (modal_query access P) F) h |}.
Definition after_proxy access P F h : State :=
  {| current := update (indefinite 1 P) (current (after_read access P F h));
     history := remember keep_all keep_all_sound None
       (update (indefinite 1 P) (current (after_read access P F h)))
       (history (after_read access P F h)) |}.
Definition after_assertion access P Q F h : State :=
  {| current := update (Seq (Use 1) (unary 1 Q)) (current (after_proxy access P F h));
     history := remember_all keep_all keep_all_sound None
       (core_trace (Seq (Use 1) (unary 1 Q)) (current (after_proxy access P F h)))
       (history (after_proxy access P F h)) |}.
Definition modal_proxy_program access P Q : @Command W D :=
  Then (Read (modal_tree access P)) (Then (Proxy 1 P) (Core (Seq (Use 1) (unary 1 Q)))).

Theorem read_generates_tentative_memory_without_export : forall access P F h,
  In (kept_event (Some (modal_query access P)) (modal_stage F P))
    (history (after_read access P F h)) /\
  remembered_prominent (snapshot (kept_event (Some (modal_query access P)) (modal_stage F P))) 0 /\
  (forall i, dom (current (after_read access P F h)) i <-> dom F i).
Proof.
  intros; split.
  - apply keep_all_records_each_frame, modal_trace_contains_description.
  - split; [simpl; auto|intro i; reflexivity].
Qed.
Theorem complete_modal_proxy_core_run : forall permit access P Q F h,
  ~ dom F 1 ->
  permit (kept_event (Some (modal_query access P)) (modal_stage F P)) 0
    (current (after_read access P F h)) (current (after_proxy access P F h)) 1 P ->
  Execute keep_all keep_all_sound permit (modal_proxy_program access P Q)
    {|current := F; history := h|} (after_assertion access P Q F h).
Proof.
  intros permit access P Q F h Hfresh Hpermit; unfold modal_proxy_program.
  eapply execute_then with (intermediate := after_read access P F h).
  - apply execute_read; intros i Hi; change (In i []) in Hi; contradiction.
  - eapply execute_then with (intermediate := after_proxy access P F h).
    + apply execute_proxy with
        (event := kept_event (Some (modal_query access P)) (modal_stage F P)) (j := 0).
      * apply read_generates_tentative_memory_without_export.
      * simpl; auto.
      * discriminate.
      * exact Hfresh.
      * exact Hpermit.
    + apply execute_core; simpl; split; [right; left; reflexivity|exact I].
Qed.
Theorem proxy_core_truth : forall (F : @File W D) P Q w,
  condition_B F -> ~ dom F 1 ->
  (world_content (update (Seq (Use 1) (unary 1 Q)) (update (indefinite 1 P) F)) w <->
   world_content F w /\ exists x, P w x /\ Q w x).
Proof.
  intros F P Q w HB Hfresh.
  assert (E : world_content (update (Seq (Use 1) (unary 1 Q)) (update (indefinite 1 P) F)) w <->
    world_content (update (indefinite 1 (fun v x => P v x /\ Q v x)) F) w).
  { unfold world_content; simpl; firstorder. }
  rewrite E; apply fresh_indefinite_truth; assumption.
Qed.
Theorem complete_program_truth_conditions : forall access P Q F h w,
  condition_B F -> ~ dom F 1 ->
  (world_content (current (after_assertion access P Q F h)) w <->
   world_content F w /\ (forall v, access w v -> exists x, P v x) /\
   exists x, P w x /\ Q w x).
Proof.
  intros access P Q F h w HB Hfresh.
  change (world_content (update (Seq (Use 1) (unary 1 Q))
    (update (indefinite 1 P) (indexed_test (modal_query access P) F))) w <->
    world_content F w /\ (forall v, access w v -> exists x, P v x) /\
    exists x, P w x /\ Q w x).
  rewrite proxy_core_truth.
  - unfold world_content, indexed_test, filter; simpl.
    setoid_rewrite compiled_modal_truth; firstorder.
  - apply indexed_test_preserves_B; [exact HB|].
    intros i Hi; rewrite modal_compiler_has_no_free_individuals in Hi; contradiction.
  - exact Hfresh.
Qed.
Theorem factive_modal_proxy_preserves_world_content : forall access P F h,
  (forall w, access w w) -> condition_B F -> ~ dom F 1 ->
  forall w, world_content (current (after_proxy access P F h)) w <->
    world_content (current (after_read access P F h)) w.
Proof.
  intros access P F h Href HB Hfresh.
  apply existentially_supported_introduction_preserves_worlds.
  - apply indexed_test_preserves_B; [exact HB|].
    intros i Hi; rewrite modal_compiler_has_no_free_individuals in Hi; contradiction.
  - exact Hfresh.
  - intros w [g [HF HM]]; exact (proj1 (compiled_modal_truth access P w g) HM w (Href w)).
Qed.

Definition core_scoped : @Formula W D := Every (indefinite 0 (fun _ _ => True)) (Use 0).
Definition scoped_result : @State W D :=
  {| current := update core_scoped empty_file;
     history := remember_all keep_all keep_all_sound None (core_trace core_scoped empty_file) [] |}.
Theorem core_run_remembers_but_cannot_directly_reuse_scoped_card : forall permit,
  Execute keep_all keep_all_sound permit (Core core_scoped)
    {|current := empty_file; history := []|} scoped_result /\
  In (kept_event None (update (indefinite 0 (fun _ _ => True)) empty_file)) (history scoped_result) /\
  forall final, ~ Execute keep_all keep_all_sound permit (Direct 0) scoped_result final.
Proof.
  intro permit; split.
  - apply execute_core; simpl; auto.
  - split.
    + apply keep_all_records_each_frame; simpl; auto.
    + intros final H; apply direct_requires_accessible_index in H; exact H.
Qed.
Theorem unresolved_deictic_blocks_read : forall permit P R h final,
  ~ Execute keep_all keep_all_sound permit (Read (text_with_deictic P R))
    {|current := empty_file; history := h|} final.
Proof.
  intros permit P R h final H; apply read_requires_computed_references in H.
  unfold references_available in H; rewrite text_closure_keeps_deictic_free in H.
  apply (H 1); simpl; auto.
Qed.
End EndToEnd.

Module NonfactiveModel.
Definition F : @File bool unit := empty_file.
Definition desires (_ v : bool) := v = true.
Definition person_in_world (w : bool) (_ : unit) := w = true.
Theorem desired_witness_is_not_an_actual_witness :
  world_content (current (after_read desires person_in_world F [])) false /\
  world_content (modal_stage F person_in_world) true /\
  ~ world_content (modal_stage F person_in_world) false /\
  ~ world_content (current (after_proxy desires person_in_world F [])) false.
Proof.
  split.
  - exists (fun _ => tt); split; [exact I|].
    apply compiled_modal_truth; intros v Hv; exists tt; exact Hv.
  - split.
    + apply modal_stage_retains_world_argument; exists tt; reflexivity.
    + split.
      * rewrite modal_stage_retains_world_argument; intros [x H]; discriminate H.
      * intros [g [_ H]]; discriminate H.
Qed.
End NonfactiveModel.

Print Assumptions complete_modal_proxy_core_run.
Print Assumptions complete_program_truth_conditions.
Print Assumptions factive_modal_proxy_preserves_world_content.
Print Assumptions NonfactiveModel.desired_witness_is_not_an_actual_witness.
