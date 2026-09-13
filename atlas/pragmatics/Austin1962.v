(* Austin 1962, How to Do Things with Words, pp.5-11 and Lectures
   II-IV pp.12-52. P1 campaign, inventory A1-A7.
   Six PROVISIONAL NECESSARY conditions; Gamma conditions are conditional
   on the procedure. Overlapping failures are retained. Unknown is not
   success. Institutional achievement and other effects are separate.
   Added machinery: partial diagnostic observations and a finite recognizer
   for the offer/acceptance example. No algorithm decides which conventions
   are accepted, who is entitled, or whether an intention is sincere.
   Passing this checklist is NOT defined as full felicity (pp.21-23).
   No whole-book speech-act semantics, axioms or admissions. *)
Require Import List Bool.
Import ListNotations.

Inductive condition := A1 | A2 | B1 | B2 | G1 | G2.
Definition all_conditions := [A1; A2; B1; B2; G1; G2].
Definition constitutive_conditions := [A1; A2; B1; B2].
Definition observations := condition -> option bool.
Definition required attitude conduct c :=
  match c with G1 => attitude | G2 => conduct | _ => true end.

Section Diagnostics.
Variables attitude conduct : bool.
Definition passes (s : observations) c :=
  required attitude conduct c = false \/ s c = Some true.
Definition fails (s : observations) c :=
  required attitude conduct c = true /\ s c = Some false.
Definition failedb (s : observations) c :=
  required attitude conduct c &&
  match s c with Some false => true | _ => false end.
Definition report s := filter (failedb s) all_conditions.
Definition listed_pass s := forall c, passes s c.
Definition assessed (s : observations) := forall c, required attitude conduct c = true -> s c <> None.
Definition misfire s := exists c, In c constitutive_conditions /\ fails s c.
Definition abuse_of_achieved (s : observations) (achieved : Prop) :=
  achieved /\ (fails s G1 \/ fails s G2).

Lemma condition_enumeration : forall c, In c all_conditions.
Proof. destruct c; cbn; tauto. Qed.

Theorem report_exact : forall s c, In c (report s) <-> fails s c.
Proof.
  intros s c; unfold report; rewrite filter_In.
  split.
  - intros [_ H]; unfold failedb in H; apply andb_true_iff in H.
    destruct H as [Hr Hv]; unfold fails; split; [assumption |].
    destruct (s c) as [[|]|]; cbn in Hv; congruence.
  - intros [Hr Hv]; split; [apply condition_enumeration |].
    unfold failedb; rewrite Hr, Hv; reflexivity.
Qed.

Theorem passing_excludes_failure : forall s c, passes s c -> ~ fails s c.
Proof. unfold passes, fails; intros s c [H | H] [Hr Hv]; congruence. Qed.

Theorem no_report_complete_when_assessed : forall s,
  assessed s -> ((forall c, ~ In c (report s)) <-> listed_pass s).
Proof.
  intros s Hknown; split.
  - intros Hnone c; unfold passes.
    destruct (required attitude conduct c) eqn:Hr; [right | left; reflexivity].
    destruct (s c) as [[|]|] eqn:Hs; [reflexivity | |].
    + exfalso; apply (Hnone c), report_exact; split; assumption.
    + exfalso; exact (Hknown c Hr Hs).
  - intros Hall c Hfail; apply report_exact in Hfail.
    exact (passing_excludes_failure s c (Hall c) Hfail).
Qed.

Definition refines (before after : observations) :=
  forall c b, before c = Some b -> after c = Some b.

Theorem known_failures_survive_refinement : forall before after,
  refines before after -> incl (report before) (report after).
Proof.
  intros before after H c Hc; apply report_exact in Hc; apply report_exact.
  destruct Hc as [Hr Hv]; split; [exact Hr | exact (H c false Hv)].
Qed.

(* A2: achievement is not inferred by assuming the checklist sufficient. *)
Theorem misfire_blocks_intended_act : forall s (achieved : Prop),
  (achieved -> forall c, In c constitutive_conditions -> passes s c) ->
  misfire s -> ~ achieved.
Proof.
  intros s achieved Hnecess [c [Hc Hf]] Hact.
  exact (passing_excludes_failure s c (Hnecess Hact c Hc) Hf).
Qed.

Theorem failed_necessary_condition_blocks_felicity : forall s (felicitous : Prop),
  (felicitous -> listed_pass s) ->
  (exists c, In c (report s)) -> ~ felicitous.
Proof.
  intros s happy Hnec [c Hc] Hhappy; apply report_exact in Hc.
  exact (passing_excludes_failure s c (Hnec Hhappy c) Hc).
Qed.
End Diagnostics.

Module Cases.
Definition unknown : observations := fun _ => None.
Definition all_ok : observations := fun _ => Some true.
Definition insincere : observations :=
  fun c => match c with G1 => Some false | _ => Some true end.
Definition overlapping : observations :=
  fun c => match c with A2 | G1 => Some false | _ => Some true end.

Theorem unknown_is_not_success :
  report true true unknown = [] /\ ~ listed_pass true true unknown.
Proof.
  split; [reflexivity | intros H; specialize (H A1); destruct H; discriminate].
Qed.

(* A3 pp.11,16,40. Achievement is supplied as part of the source example;
   it is NOT computed from the four A/B checks. *)
Theorem insincere_promise_can_be_achieved :
  (forall c, In c constitutive_conditions -> passes true true insincere c) /\
  abuse_of_achieved true true insincere True /\
  ~ listed_pass true true insincere.
Proof.
  split.
  - intros c H; destruct c; cbn in *; try (right; reflexivity); intuition discriminate.
  - split.
    + split; [exact I | left; split; reflexivity].
    + intros H; specialize (H G1); destruct H; discriminate.
Qed.

(* A5 p.23: the list must not pick one exclusive failure class. *)
Theorem simultaneous_failures : report true true overlapping = [A2; G1].
Proof. reflexivity. Qed.

Theorem inapplicable_attitudes_not_failures : report false false insincere = [].
Proof. reflexivity. Qed.

(* A6 pp.21-22: another requirement can remain unsatisfied even when all
   six listed checks pass. This refutes completeness of the checklist,
   not any claim by Austin that his list was complete. *)
Theorem listed_conditions_are_not_sufficient :
  listed_pass true true all_ok /\
  exists additional_requirement : Prop,
    ~ (listed_pass true true all_ok /\ additional_requirement).
Proof.
  split; [intros c; right; reflexivity | exists False; tauto].
Qed.

(* A2 pp.17,23: the unauthorized naming attempt can still break a bottle. *)
Record naming_result := { ship_named : bool; bottle_broken : bool }.
Definition naming_attempt authorized :=
  {| ship_named := authorized; bottle_broken := true |}.
Theorem void_act_can_have_other_effects :
  ship_named (naming_attempt false) = false /\
  bottle_broken (naming_attempt false) = true.
Proof. split; reflexivity. Qed.

(* Subsequent conduct does not retrospectively change the observation
   that an A/B condition was met. It may add a Gamma2 failure. *)
Definition after_conduct fulfilled : observations :=
  fun c => match c with G2 => Some fulfilled | _ => Some true end.
Theorem breach_not_incomplete_execution :
  report true true (after_conduct false) = [G2] /\
  ~ misfire true true (after_conduct false).
Proof.
  split; [reflexivity | intros [c [Hc [_ Hbad]]]].
  destruct c; cbn in *; try discriminate; intuition discriminate.
Qed.

(* A7 pp.41,49: truth and sincere belief are different coordinates. *)
Theorem truth_does_not_force_sincere_belief :
  exists (content_true speaker_believes : bool),
    content_true = true /\ speaker_believes = false.
Proof. exists true, false; split; reflexivity. Qed.
End Cases.

Module Betting.
(* A4 pp.9,36-37. A strict two-step recognizer is added machinery for
   one example. It is not the full grammar of conventional procedures. *)
Inductive move := offer | accept | refuse.
Inductive phase := awaiting_offer | awaiting_acceptance | completed | broken.
Definition step state event :=
  match state, event with
  | awaiting_offer, offer => awaiting_acceptance
  | awaiting_acceptance, accept => completed
  | _, _ => broken
  end.
Fixpoint run state events :=
  match events with [] => state | e :: rest => run (step state e) rest end.

Lemma broken_absorbing : forall events, run broken events = broken.
Proof. induction events as [|e rest IH]; cbn; [reflexivity | exact IH]. Qed.

Theorem complete_trace_exact : forall events,
  run awaiting_offer events = completed <-> events = [offer; accept].
Proof.
  intros [|e [|f rest]]; cbn; try (split; discriminate).
  - destruct e; cbn; split; discriminate.
  - destruct e, f; cbn; try rewrite broken_absorbing;
      try (split; discriminate).
    destruct rest as [|g tail]; cbn; [tauto |].
    rewrite broken_absorbing; split; discriminate.
Qed.

Theorem offer_requires_uptake :
  run awaiting_offer [offer] = awaiting_acceptance /\
  run awaiting_offer [offer] <> completed.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem accepted_offer_completes : run awaiting_offer [offer; accept] = completed.
Proof. reflexivity. Qed.

Theorem refusal_and_reversed_order_fail :
  run awaiting_offer [offer; refuse] = broken /\
  run awaiting_offer [accept; offer] = broken.
Proof. split; reflexivity. Qed.
End Betting.
