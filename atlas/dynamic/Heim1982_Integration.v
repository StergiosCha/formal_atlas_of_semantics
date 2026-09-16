(* Heim 1982 / 2011 pp.105-111,118-120,234,247-254.
   Added integration layer, NOT an identification of the two source systems.
   Core commands run final FCS; Read commands test compiled indexed texts.
   Indexed traces are tagged satisfaction-calculation snapshots, not assertions
   about the actual world. Modal descent resets world information; source
   accessibility/ordering stays in the origin formula and in the truth test.
   Proxy transitions consume recorded snapshots and explicit permission.
   Attention/retention and proxy selection are supplied policies. No oracle,
   recency threshold, accommodation preference or global axiom is introduced. *)
From Coq Require Import List Arith Bool Lia.
From dynamic Require Import Heim1982 Heim1982_Examples Heim1982_Extensions
  Heim1982_Indexed Heim1982_Binding.
Import ListNotations.
Set Implicit Arguments.

Section Adapters.
Context {W D : Type}.
Definition references_available (p : @Indexed W D) (F : @File W D) :=
  forall i, In i (free_indices p) -> dom F i.
Definition indexed_test (p : @Indexed W D) (F : @File W D) := filter F (satisfies p).
Theorem indexed_test_exact : forall p F w g,
  sat (indexed_test p F) w g <-> sat F w g /\ satisfies p w g.
Proof. reflexivity. Qed.
Theorem indexed_test_does_not_export : forall p F i,
  dom (indexed_test p F) i <-> dom F i.
Proof. reflexivity. Qed.
Theorem indexed_test_preserves_B : forall p F,
  condition_B F -> references_available p F -> condition_B (indexed_test p F).
Proof.
  intros p F HB HA w i g h Hi Hd; unfold indexed_test, filter; simpl.
  assert (E : agree_indices (free_indices p) g h).
  { intros j Hj; apply Hd; intro Eq; subst; apply Hi, HA; exact Hj. }
  rewrite (HB w i g h Hi Hd), (@satisfaction_depends_only_on_free W D p w g h E); reflexivity.
Qed.
Theorem indexed_test_preserves_support : forall p F,
  supported F -> references_available p F -> supported (indexed_test p F).
Proof.
  intros p F HF HA w g h H; unfold indexed_test, filter; simpl.
  rewrite (HF w g h H).
  assert (E : agree_indices (free_indices p) g h) by (intros i Hi; apply H, HA; exact Hi).
  rewrite (@satisfaction_depends_only_on_free W D p w g h E); reflexivity.
Qed.

(* A snapshot of a stage of indexed satisfaction calculation. Adding all
   syntactically free coordinates to its domain makes its support explicit. *)
Definition indexed_frame (p : @Indexed W D) (F : @File W D) : File :=
  {| dom := fun i => dom F i \/ In i (free_indices p);
     sat := fun w g => sat F w g /\ satisfies p w g |}.
Definition world_reset (F : @File W D) : @File W D :=
  {| dom := dom F; sat := fun _ _ => True |}.
Theorem world_reset_preserves_B : forall F, condition_B (world_reset F).
Proof. intros F w i g h Hi Hd; reflexivity. Qed.
Theorem indexed_frame_preserves_B : forall p F,
  condition_B F -> condition_B (indexed_frame p F).
Proof.
  intros p F HB w i g h Hi Hd; simpl in *.
  assert (Hout : ~ dom F i) by tauto.
  assert (E : agree_indices (free_indices p) g h).
  { intros j Hj; apply Hd; intro Eq; subst; apply Hi; auto. }
  rewrite (HB w i g h Hout Hd), (@satisfaction_depends_only_on_free W D p w g h E); reflexivity.
Qed.

Fixpoint core_trace (p : @Formula W D) (F : @File W D) : list File :=
  match p with
  | Seq p q => core_trace p F ++ core_trace q (update p F)
  | Every p q => core_trace p F ++ core_trace q (update p F) ++ [update (Every p q) F]
  | Not p => core_trace p F ++ [update (Not p) F]
  | Or p q => core_trace p F ++ core_trace q F ++ [update (Or p q) F]
  | Mark _ _ p => core_trace p F
  | _ => [update p F]
  end.
Theorem core_trace_files_satisfy_B : forall p F,
  condition_B F -> Forall condition_B (core_trace p F).
Proof.
  induction p; intros F HB; simpl.
  - constructor; [exact (@update_preserves_B W D (Atom n t P) F HB)|constructor].
  - apply Forall_app; split; [apply IHp1; exact HB|apply IHp2, update_preserves_B; exact HB].
  - apply Forall_app; split; [apply IHp1; exact HB|].
    apply Forall_app; split; [apply IHp2, update_preserves_B; exact HB|].
    constructor; [exact (@update_preserves_B W D (Every p1 p2) F HB)|constructor].
  - apply Forall_app; split; [apply IHp; exact HB|].
    constructor; [exact (@update_preserves_B W D (Not p) F HB)|constructor].
  - apply Forall_app; split; [apply IHp1; exact HB|].
    apply Forall_app; split; [apply IHp2; exact HB|].
    constructor; [exact (@update_preserves_B W D (Or p1 p2) F HB)|constructor].
  - apply IHp; exact HB.
  - constructor; [exact HB|constructor].
Qed.
Theorem universal_trace_keeps_restrictor : forall p q F G,
  In G (core_trace p F) -> In G (core_trace (Every p q) F).
Proof. intros; simpl; apply in_app_iff; auto. Qed.

Fixpoint indexed_trace (p : @Indexed W D) (F : @File W D) : list File :=
  match p with
  | IAtom _ _ _ => [indexed_frame p F]
  | IAnd p q | IAll _ p q =>
      indexed_trace p F ++ indexed_trace q (indexed_frame p F)
  | IEx _ p | INeg p => indexed_trace p F
  | IMust _ _ _ p q | IMay _ _ _ p q =>
      indexed_trace p (world_reset F) ++
      indexed_trace q (indexed_frame p (world_reset F))
  end.
Theorem indexed_trace_files_satisfy_B : forall p F,
  condition_B F -> Forall condition_B (indexed_trace p F).
Proof.
  induction p; intros F HB; simpl; repeat rewrite Forall_app;
    auto using indexed_frame_preserves_B, world_reset_preserves_B.
Qed.
Theorem modal_trace_not_an_actual_world_update : forall xs access closer p q F,
  indexed_trace (IMust xs access closer p q) F =
  indexed_trace p (world_reset F) ++ indexed_trace q (indexed_frame p (world_reset F)).
Proof. reflexivity. Qed.
End Adapters.

Section Runner.
Context {W D : Type}.
Record Event := {
  origin : option (@Indexed W D);
  snapshot : @MemoryItem W D
}.
Definition History := list Event.
Record State := { current : @File W D; history : History }.

Variable attention : History -> @File W D -> nat -> Prop.
Hypothesis attention_in_domain : forall h F i, attention h F i -> dom F i.
Definition remember (source : option (@Indexed W D)) F (h : History) : History :=
  {| origin := source;
     snapshot := {| remembered_file := F; remembered_prominent := attention h F;
                    remembered_in_domain := @attention_in_domain h F |} |} :: h.
Fixpoint remember_all source (files : list (@File W D)) (h : History) : History :=
  match files with
  | [] => h
  | F :: rest => remember_all source rest (remember source F h)
  end.
Lemma remember_all_preserves_history : forall source files h event,
  In event h -> In event (remember_all source files h).
Proof.
  intros source files; induction files; intros h event Hin; simpl; auto.
  apply IHfiles; right; exact Hin.
Qed.
Lemma remembered_frame_has_event : forall source files F h,
  In F files -> exists event, In event (remember_all source files h) /\
    origin event = source /\ remembered_file (snapshot event) = F.
Proof.
  intros source files; induction files as [|G rest IH]; intros F h Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Eq|Hin].
    + subst G; exists {| origin := source; snapshot :=
        {| remembered_file := F; remembered_prominent := attention h F;
           remembered_in_domain := @attention_in_domain h F |} |}.
      split; [cbn [remember_all]; apply remember_all_preserves_history; left; reflexivity|split; reflexivity].
    + apply IH; exact Hin.
Qed.

(* Both old and repaired files are visible to the supplied policy. Merely
   being remembered is never interpreted as permission or actual-world truth. *)
Variable permit : Event -> nat -> @File W D -> @File W D -> nat -> (W -> D -> Prop) -> Prop.
Inductive Command :=
| Core : @Formula W D -> Command
| Read : @Construal W D -> Command
| Direct : nat -> Command
| Proxy : nat -> (W -> D -> Prop) -> Command
| Then : Command -> Command -> Command.
Inductive Execute : Command -> State -> State -> Prop :=
| execute_core : forall p F h,
    licensed p F ->
    Execute (Core p) {| current := F; history := h |}
      {| current := update p F; history := remember_all None (core_trace p F) h |}
| execute_read : forall p F h,
    references_available (compile_text p) F ->
    Execute (Read p) {| current := F; history := h |}
      {| current := indexed_test (compile_text p) F;
         history := remember_all (Some (compile_text p)) (indexed_trace (compile_text p) F) h |}
| execute_direct : forall i F h,
    attention h F i -> Execute (Direct i) {| current := F; history := h |}
      {| current := F; history := h |}
| execute_proxy : forall i P F h event j,
    In event h -> remembered_prominent (snapshot event) j ->
    i <> j -> ~ dom F i ->
    permit event j F (update (indefinite i P) F) i P ->
    Execute (Proxy i P) {| current := F; history := h |}
      {| current := update (indefinite i P) F;
         history := remember None (update (indefinite i P) F) h |}
| execute_then : forall p q initial intermediate final,
    Execute p initial intermediate -> Execute q intermediate final ->
    Execute (Then p q) initial final.

Theorem core_adapter_exact : forall p initial final,
  Execute (Core p) initial final ->
  current final = update p (current initial) /\ licensed p (current initial).
Proof. intros p initial final H; inversion H; subst; simpl; auto. Qed.
Theorem read_adapter_exact : forall p initial final,
  Execute (Read p) initial final -> forall w g,
  sat (current final) w g <-> sat (current initial) w g /\ satisfies (compile_text p) w g.
Proof. intros p initial final H; inversion H; subst; reflexivity. Qed.
Theorem read_requires_computed_references : forall p initial final,
  Execute (Read p) initial final -> references_available (compile_text p) (current initial).
Proof. intros p initial final H; inversion H; subst; assumption. Qed.
Theorem execute_preserves_B : forall command initial final,
  Execute command initial final -> condition_B (current initial) -> condition_B (current final).
Proof.
  intros command initial final H; induction H; cbn [current]; intro HB.
  - apply update_preserves_B; exact HB.
  - apply indexed_test_preserves_B; assumption.
  - exact HB.
  - apply update_preserves_B; exact HB.
  - apply IHExecute2, IHExecute1; exact HB.
Qed.
Theorem execute_keeps_history : forall command initial final,
  Execute command initial final -> forall event,
  In event (history initial) -> In event (history final).
Proof.
  intros command initial final H; induction H; simpl; intros ev Hin;
    eauto using remember_all_preserves_history.
Qed.
Theorem direct_requires_accessible_index : forall i initial final,
  Execute (Direct i) initial final -> dom (current initial) i.
Proof. intros i initial final H; inversion H; subst; simpl; eapply attention_in_domain; eauto. Qed.
Theorem proxy_has_recorded_authorized_origin : forall i P initial final,
  Execute (Proxy i P) initial final -> exists event j,
  In event (history initial) /\ remembered_prominent (snapshot event) j /\
  i <> j /\ ~ dom (current initial) i /\
  permit event j (current initial) (current final) i P.
Proof. intros i P initial final H; inversion H; subst; simpl; eauto 8. Qed.
Theorem proxy_establishes_description : forall i P initial final,
  Execute (Proxy i P) initial final -> licensed (definite i P) (current final).
Proof.
  intros i P initial final H; inversion H; subst; simpl; unfold entails; simpl; firstorder.
Qed.
Theorem proxy_connects_existing_licensing_interface : forall i P initial final,
  Execute (Proxy i P) initial final ->
  pronoun_with_proxy (current final) (attention (history initial) (current final))
    (map snapshot (history initial))
    (fun m j G k => exists event, In event (history initial) /\ snapshot event = m /\
      permit event j (current initial) G k P) i.
Proof.
  intros i P initial final H; inversion H; subst; simpl.
  split; [right; left; reflexivity|right].
  exists (snapshot event), j; split; [apply in_map; assumption|].
  split; [assumption|exists event; auto].
Qed.
End Runner.

Section Restrictions.
Context {W D : Type}.
Variable attention : @History W D -> @File W D -> nat -> Prop.
Variable sound : forall h F i, attention h F i -> dom F i.
Theorem denying_permission_blocks_proxy : forall i P initial final,
  ~ Execute attention sound (fun _ _ _ _ _ _ => False) (Proxy i P) initial final.
Proof. intros i P initial final H; inversion H; contradiction. Qed.
Theorem missing_memory_blocks_proxy : forall permit i P F final,
  ~ Execute attention sound permit (Proxy i P) {|current := F; history := []|} final.
Proof. intros permit i P F final H; inversion H; contradiction. Qed.
End Restrictions.

Print Assumptions indexed_test_preserves_B.
Print Assumptions execute_preserves_B.
Print Assumptions proxy_connects_existing_licensing_interface.
