(* Heim 1982 / 2011: accommodation (pp.239-246), false-context revision
   (pp.218-220), prominence/proxy (pp.247-252), and explicit requirements.

   Policy inputs are NOT claimed to solve the source's open pragmatic problems.
   Run represents finite interleavings of interpretation and supplied repairs;
   it chooses neither a bridge nor local/global preference automatically.
   The only imported logical principle used below is Classical_Prop.classic,
   for the positive arbitrary-domain membership conclusion of p.238 fn.21
   and exhaustiveness of the source's classical truth criterion C.
   All other results are constructive; Print Assumptions distinguishes them. *)
From Coq Require Import List Arith Lia Classical.
From dynamic Require Import Heim1982 Heim1982_Examples.
Import ListNotations.
Set Implicit Arguments.

Section Accommodation.
Context {W D : Type}.
Definition strengthens (F G : @File W D) :=
  (forall i, dom F i -> dom G i) /\
  (forall w g, sat G w g -> sat F w g).
Definition weakens (F G : @File W D) :=
  (forall i, dom G i -> dom F i) /\
  (forall w g, sat F w g -> sat G w g).

Definition RepairPolicy := @File W D -> @Formula W D -> @File W D -> Prop.

(* Supplied policies must additionally express the source-appropriate bridge
   and contextual licensing. strengthens alone is NOT sufficient for that.
   Its two components express only addition of cards and information. *)
Inductive Run (policy : RepairPolicy) : Formula -> File -> File -> Prop :=
| run_atom : forall n xs P F, Run policy (Atom n xs P) F (atomic n xs P F)
| run_use : forall i F, dom F i -> Run policy (Use i) F F
| run_seq : forall p q F G H,
    Run policy p F G -> Run policy q G H -> Run policy (Seq p q) F H
| run_every : forall p q F R S,
    Run policy p F R -> Run policy q R S ->
    Run policy (Every p q) F (universal_result F R S)
| run_not : forall p F G,
    Run policy p F G -> Run policy (Not p) F (negative_result F G)
| run_or : forall p q F G H,
    Run policy p F G -> Run policy q F H ->
    Run policy (Or p q) F (disjunctive_result F G H)
| run_mark : forall (b : bool) i p F G,
    (if b then dom F i /\ entails F p else ~ dom F i) ->
    Run policy p F G -> Run policy (Mark b i p) F G
| run_repair : forall p F G H,
    policy F p G -> strengthens F G -> ~ licensed p F ->
    Run policy p G H -> Run policy p F H.

Theorem raw_run : forall policy p F,
  licensed p F -> Run policy p F (update p F).
Proof.
  intros policy p; induction p; intros F H; simpl in *.
  - apply run_atom.
  - destruct H; eapply run_seq; [apply IHp1 | apply IHp2]; eauto.
  - destruct H; apply run_every; [apply IHp1 | apply IHp2]; eauto.
  - apply run_not, IHp; exact H.
  - destruct H; apply run_or; [apply IHp1 | apply IHp2]; eauto.
  - destruct H; apply run_mark; [assumption | apply IHp; assumption].
  - apply run_use; exact H.
Qed.
Theorem no_repair_is_exact : forall p F G,
  Run (fun _ _ _ => False) p F G -> G = update p F /\ licensed p F.
Proof.
  intros p F G H; induction H; simpl in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; subst;
    try solve [split; [reflexivity | tauto]]; contradiction.
Qed.
Theorem local_negation_accommodation : forall policy p F G,
  policy F p G -> strengthens F G -> ~ licensed p F -> licensed p G ->
  Run policy (Not p) F (negative_result F (update p G)).
Proof.
  intros policy p F G HP HE Hbad Hgood.
  apply run_not; eapply run_repair; eauto using raw_run.
Qed.
Theorem global_negation_accommodation : forall policy p F G,
  policy F (Not p) G -> strengthens F G -> ~ licensed p F -> licensed p G ->
  Run policy (Not p) F (negative_result G (update p G)).
Proof.
  intros policy p F G HP HE Hbad Hgood.
  eapply run_repair with (G := G).
  - exact HP.
  - exact HE.
  - exact Hbad.
  - apply raw_run; exact Hgood.
Qed.

Definition bridge (F : @File W D) new old (R : W -> D -> D -> Prop) :=
  update (binary new old R) F.
Definition situation_bridge (F : @File W D) new (R : W -> D -> Prop) :=
  update (unary new R) F.

Theorem bridge_adds_information : forall F i j R, strengthens F (bridge F i j R).
Proof. intros; split; simpl; intuition. Qed.
Theorem bridge_licenses_description : forall F i j R,
  licensed (Mark true i (binary i j R)) (bridge F i j R).
Proof. intros; simpl; unfold entails, bridge; simpl; firstorder. Qed.
Theorem bridge_has_old_anchor : forall F i j R,
  ~ dom F i -> dom F j ->
  i <> j /\ dom (bridge F i j R) i /\ dom (bridge F i j R) j.
Proof. intros; unfold bridge; simpl; intuition congruence. Qed.
Theorem situation_bridge_adds_information : forall F i R,
  strengthens F (situation_bridge F i R).
Proof. intros; split; simpl; intuition. Qed.

Lemma universal_scope_extensional : forall F R (S T : @File W D),
  (forall w g, sat S w g <-> sat T w g) ->
  file_equiv (universal_result F R S) (universal_result F R T).
Proof.
  intros F R S T H; split; [intro i; reflexivity |].
  intros w g; split; intros [HF Hall]; split; [exact HF | | exact HF |];
    intros b Hab Hb; destruct (Hall b Hab Hb) as [c [Hbc Hc]];
    exists c; split; [exact Hbc | | exact Hbc |].
  - apply (proj1 (H w c)); exact Hc.
  - apply (proj2 (H w c)); exact Hc.
Qed.

Definition father_scope (Father Hates : W -> D -> D -> Prop) :=
  Seq (Mark true 1 (binary 0 1 Father)) (binary 0 1 Hates).
Definition father_repair (R : @File W D) (Father : W -> D -> D -> Prop) :=
  bridge R 1 0 (fun w dad man => Father w man dad).

Theorem father_repair_licenses_scope : forall R Father Hates,
  licensed (father_scope Father Hates) (father_repair R Father).
Proof.
  intros; unfold father_scope, father_repair, bridge; simpl;
    unfold entails; simpl; firstorder.
Qed.

(* pp.242-243: genuinely definite syntax plus an explicit local repair,
   rather than renaming an indefinite and calling it accommodation. *)
Theorem accommodated_father_run : forall policy F Man Father Hates,
  ~ dom F 0 -> ~ dom F 1 ->
  policy (update (indefinite 0 Man) F) (father_scope Father Hates)
    (father_repair (update (indefinite 0 Man) F) Father) ->
  Run policy (Every (indefinite 0 Man) (father_scope Father Hates)) F
    (universal_result F (update (indefinite 0 Man) F)
      (update (father_scope Father Hates)
        (father_repair (update (indefinite 0 Man) F) Father))).
Proof.
  intros policy F Man Father Hates H0 H1 HP; apply run_every.
  - apply raw_run; apply indefinite_felicity; exact H0.
  - eapply run_repair; [exact HP | | |].
    + apply bridge_adds_information.
    + intros [[Hdom _] _]; simpl in Hdom; intuition discriminate.
    + apply raw_run, father_repair_licenses_scope.
Qed.

Theorem accommodated_father_truth_conditions : forall F Man Father Hates w g,
  condition_B F -> ~ dom F 0 -> ~ dom F 1 ->
  (sat (universal_result F (update (indefinite 0 Man) F)
    (update (father_scope Father Hates)
      (father_repair (update (indefinite 0 Man) F) Father))) w g <->
   sat F w g /\ forall x, Man w x -> exists y, Father w x y /\ Hates w x y).
Proof.
  intros F Man Father Hates w g HB H0 H1.
  set (R := update (indefinite 0 Man) F).
  set (T := update (Seq (indefinite 1 (fun (_ : W) (_ : D) => True))
    (binary 0 1 (fun w x y => Father w x y /\ Hates w x y))) R).
  assert (HE : forall v h,
    sat (update (father_scope Father Hates) (father_repair R Father)) v h <-> sat T v h).
  { intros; unfold father_scope, father_repair, bridge, T; simpl; tauto. }
  pose proof (universal_scope_extensional F R _ T HE) as [_ Hsat].
  rewrite (Hsat w g).
  change (sat (update (nuclear_indefinite Man (fun (_ : W) (_ : D) => True)
    (fun w x y => Father w x y /\ Hates w x y)) F) w g <->
    sat F w g /\ forall x, Man w x -> exists y, Father w x y /\ Hates w x y).
  rewrite nuclear_existential_truth_conditions by assumption; firstorder.
Qed.

(* Source C': relevance and the admissible erasures remain a policy input. *)
Definition revised_truth (relevant_repair : RepairPolicy) p F w :=
  exists G, relevant_repair F p G /\ weakens F G /\ world_content G w /\
    licensed p G /\ world_content (update p G) w.

(* p.250-251: world content, not the full assignment set, can be preserved
   by a new card for an already guaranteed existential witness. *)
Theorem existentially_supported_introduction_preserves_worlds : forall (F : @File W D) i P,
  condition_B F -> ~ dom F i ->
  (forall w, world_content F w -> exists x, P w x) ->
  forall w, world_content (update (indefinite i P) F) w <-> world_content F w.
Proof.
  intros F i P HB Hi HE w.
  rewrite (@fresh_indefinite_truth W D F i P w HB Hi); firstorder.
Qed.

Theorem nontrivial_entailment_forces_familiarity : forall (F : @File W D) i P,
  condition_B F -> entails F (unary i P) ->
  (exists w g x, sat F w g /\ ~ P w x) -> dom F i.
Proof.
  intros F i P HB HE HW; apply NNPP.
  eapply nontrivial_entailment_not_not_familiar; eauto.
Qed.
Theorem criterion_C_exhaustive_on_felicitous_true_inputs : forall p (F : @File W D) w,
  licensed p F -> world_content F w ->
  utterance_true p F w \/ utterance_false p F w.
Proof.
  intros p F w HL HF; destruct (classic (world_content (update p F) w)) as [HT | HN].
  - left; split; assumption.
  - right; repeat split; assumption.
Qed.

(* Source prominence is small/recent but no threshold or general proxy rule
   is specified. Memory retains tentative files, including cards no longer
   exported by a quantifier. This is a representation and conditional
   licensing interface, not a solved theory of pronoun acceptability. *)
Record MemoryItem := {
  remembered_file : @File W D;
  remembered_prominent : nat -> Prop;
  remembered_in_domain : forall i, remembered_prominent i -> dom remembered_file i
}.
Definition pronoun_with_proxy (current : @File W D) (prominent : nat -> Prop)
  (memory : list MemoryItem)
  (proxy : MemoryItem -> nat -> @File W D -> nat -> Prop) (i : nat) :=
  dom current i /\
  (prominent i \/ exists event j,
     In event memory /\ remembered_prominent event j /\ proxy event j current i).
Theorem proxy_needs_recorded_precedent : forall current prominent memory proxy i,
  pronoun_with_proxy current prominent memory proxy i -> ~ prominent i ->
  exists event j, In event memory /\ dom (remembered_file event) j /\
    proxy event j current i.
Proof.
  intros current prominent memory proxy i [_ [H | [ev [j [Hin [Hp Hrel]]]]]] Hnot.
  - contradiction.
  - exists ev, j; repeat split; auto; apply remembered_in_domain; exact Hp.
Qed.
Theorem proxy_policy_changes_licensing : forall current prominent memory i event j,
  dom current i -> ~ prominent i -> In event memory -> remembered_prominent event j ->
  pronoun_with_proxy current prominent memory (fun _ _ _ _ => True) i /\
  ~ pronoun_with_proxy current prominent memory (fun _ _ _ _ => False) i.
Proof.
  intros current prominent memory i event j Hi Hnp Hin Hj; split.
  - split; [exact Hi | right; exists event, j; auto].
  - intros [_ [Hp | [ev [k [_ [_ Hbad]]]]]]; contradiction.
Qed.
End Accommodation.

Module RequirementModels.
Definition F : @File unit bool := empty_file.
Definition is_true (_ : unit) (x : bool) := x = true.
Definition G : @File unit bool := update (indefinite 0 is_true) F.

Theorem world_preservation_is_not_Sat_preservation :
  (forall w, world_content F w <-> world_content G w) /\
  exists w g, sat F w g /\ ~ sat G w g.
Proof.
  split.
  - intro w; split.
    + intros H; exists (fun _ => true); split; reflexivity.
    + intros H; exists (fun _ => false); exact I.
  - exists tt, (fun _ => false); split; [exact I |].
    intros [_ H]; discriminate H.
Qed.

(* The literal B constrains one-coordinate changes, not arbitrary infinite
   changes. No strengthening of B was used in the general donkey proofs. *)
Definition tail_file : @File unit bool :=
  {| dom := fun _ => False;
     sat := fun _ g => exists N, forall n, N <= n -> g n = true |}.
Theorem B_does_not_imply_full_domain_support :
  condition_B tail_file /\ ~ supported tail_file.
Proof.
  split.
  - intros w i g h _ Hd; split; intros [N HN]; exists (Nat.max N (S i));
      intros n Hn.
    + rewrite <- (Hd n) by lia; apply HN; lia.
    + rewrite (Hd n) by lia; apply HN; lia.
  - intro H.
    assert (Ha : agree (dom tail_file) (fun _ => true) (fun _ => false)).
    { intros i Hi; contradiction. }
    assert (Ht : sat tail_file tt (fun _ => true)).
    { exists 0; intros; reflexivity. }
    destruct (proj1 (H tt _ _ Ha) Ht) as [N HN].
    specialize (HN N (Nat.le_refl N)); discriminate.
Qed.

Definition known : @File unit unit :=
  {| dom := fun _ => True; sat := fun _ _ => True |}.
Theorem total_felicity_decider_decides_arbitrary_propositions :
  (forall (p : @Formula unit unit) F, {licensed p F} + {~ licensed p F}) ->
  forall P : Prop, {P} + {~ P}.
Proof.
  intros decide P.
  destruct (decide (definite 0 (fun _ _ => P)) known) as [Hy | Hn].
  - left; apply definite_felicity in Hy; destruct Hy as [_ H].
    exact (H tt (fun _ => tt) I).
  - right; intro HP; apply Hn; apply definite_felicity; split; [exact I | auto].
Qed.

Definition no_king (_ : unit) (_ : bool) := False.
Definition lunch (_ : unit) (_ : bool) := True.
Definition king_file := situation_bridge F 0 no_king.
Definition king_body := Seq (definite 0 no_king) (unary 0 lunch).
Theorem local_global_accommodation_differ :
  licensed king_body king_file /\
  world_content (negative_result F (update king_body king_file)) tt /\
  ~ world_content (negative_result king_file (update king_body king_file)) tt.
Proof.
  split.
  - unfold king_body, king_file, situation_bridge; simpl; unfold entails; simpl; firstorder.
  - split.
    + exists (fun _ => false); split; [exact I |].
      intros [g [_ [[[_ Hfalse] _] _]]]; exact Hfalse.
    + intros [g [[_ Hfalse] _]]; exact Hfalse.
Qed.

Definition broken : @File unit bool := false_file (fun i => i = 0).
Definition tracks (b : bool) : @File unit bool :=
  {| dom := fun i => i = 0; sat := fun _ g => g 0 = b |}.
Definition assertion := Seq (Use 0) (unary 0 is_true).
Definition erase_toward (b : bool) : @RepairPolicy unit bool :=
  fun _ _ G => G = tracks b.
Theorem false_context_repair_is_not_determined_by_weakening :
  weakens broken (tracks true) /\ weakens broken (tracks false) /\
  revised_truth (erase_toward true) assertion broken tt /\
  ~ revised_truth (erase_toward false) assertion broken tt.
Proof.
  assert (HW : forall b, weakens broken (tracks b)).
  { intros b; split.
    - intros i Hi; exact Hi.
    - intros w g Hfalse; contradiction. }
  split; [apply HW |].
  split; [apply HW |].
  split.
  - exists (tracks true); split; [reflexivity |].
    split; [apply HW |].
    split; [exists (fun _ => true); reflexivity |].
    split; [simpl; auto | exists (fun _ => true); split; reflexivity].
  - intros [G [HG [_ [_ [_ [g [HF HP]]]]]]]; unfold erase_toward in HG; subst G.
    change (g 0 = false) in HF; change (g 0 = true) in HP; congruence.
Qed.
End RequirementModels.

Print Assumptions no_repair_is_exact.
Print Assumptions local_negation_accommodation.
Print Assumptions nontrivial_entailment_forces_familiarity.
Print Assumptions RequirementModels.world_preservation_is_not_Sat_preservation.
Print Assumptions RequirementModels.B_does_not_imply_full_domain_support.
Print Assumptions RequirementModels.total_felicity_decider_decides_arbitrary_propositions.
