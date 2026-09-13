(* Horn 1984, Toward a New Taxonomy for Pragmatic Inference.
   P2 coverage campaign; source inventory H1-H6 in
   atlas_data/campaigns/tiers_2026_09_13_inventory.md.

   SOURCE CORE: p.13 knowledge/relevance qualification on Q; pp.20-21
   (12) S entails W, Q implicates not-S, R implicates S; pp.22-23
   (16)-(18) division of pragmatic labor; pp.27-29 causatives/limits.
   Added machinery: possible-world knowledge, bool-valued context flags,
   finite candidate enumeration. Relevance, observance, competence,
   correspondence and stereotypes are inputs, not derived from words.
   No universal pragmatic parser, weighting algorithm or diachrony.
   Crucially: ignorance is not negative truth; logical compatibility does
   not establish the source's empirical ban on R-cancelling negation.
   No axioms or admissions. *)
Require Import List Bool Arith Lia.
Import ListNotations.

Section Knowledge.
Variable World : Type.
Variable accessible : World -> Prop.
Definition knows (p : World -> Prop) := forall w, accessible w -> p w.
Definition competent (p : World -> Prop) := knows p \/ knows (fun w => ~ p w).

(* H1 p.13. A speaker observed not to choose an available stronger form,
   while observing the relevant Q obligation, cannot know its content.
   Availability is an input, not inferred from a possible stronger content. *)
Theorem q_yields_ignorance : forall (strong : World -> Prop)
  (relevant available used_strong : Prop),
  relevant -> available ->
  (relevant -> available -> knows strong -> used_strong) ->
  ~ used_strong -> ~ knows strong.
Proof.
  intros strong relevant available used Hr Ha Hnorm Hnot Hknow.
  apply Hnot, Hnorm; assumption.
Qed.

(* Competence and actual-world accessibility are explicit extra premises,
   not consequences of failing to utter a stronger alternative. *)
Theorem negative_truth_needs_strengthening : forall strong actual,
  accessible actual -> competent strong -> ~ knows strong -> ~ strong actual.
Proof.
  intros strong actual Ha [Hyes | Hno] Hignorant.
  - contradiction.
  - exact (Hno actual Ha).
Qed.
End Knowledge.

Theorem ignorance_compatible_with_strong_truth :
  let k := fun _ : bool => True in
  let s := fun w : bool => w = true in
  ~ knows bool k s /\ ~ knows bool k (fun w => ~ s w) /\ s true.
Proof.
  cbn; split.
  - intros H; specialize (H false I); discriminate.
  - split; [intros H; exact (H true I eq_refl) | reflexivity].
Qed.

Section ScalarLogic.
Variables W S : Prop.
Hypothesis stronger_entails_weaker : S -> W.
Definition q_content := W /\ ~ S.
Definition r_content := W /\ S.

(* H3: the logical part of (12), not a decision rule for readings. *)
Theorem descriptive_negation_excludes_stronger : ~ W -> ~ S.
Proof. intros H Hs; apply H, stronger_entails_weaker, Hs. Qed.

Theorem stronger_forces_non_descriptive_rejection : S -> ~ (~ W).
Proof. intros Hs Hnw; apply Hnw, stronger_entails_weaker, Hs. Qed.

Theorem q_r_incompatible : q_content -> r_content -> False.
Proof. intros [_ Hnot] [_ Hs]; contradiction. Qed.

Theorem stronger_cancels_q_not_literal : S -> W /\ ~ q_content.
Proof. intros Hs; split; [apply stronger_entails_weaker; assumption | intros [_ H]; auto]. Qed.

Theorem r_cancellation_preserves_literal : W -> ~ S -> W /\ ~ r_content.
Proof. intros Hw Hs; split; [exact Hw | intros [_ H]; contradiction]. Qed.

(* Logical disjointness does not assert every hearer chooses one default. *)
Theorem reading_partition_requires_a_decision :
  (S \/ ~ S) -> W -> q_content \/ r_content.
Proof. intros [Hs | Hns] Hw; [right | left]; split; assumption. Qed.
End ScalarLogic.

(* H3 boundary: (S -> W) alone cannot rule out a state that retains W
   while rejecting the R enrichment. This does not refute Horn's
   linguistic judgment about which NEGATED UTTERANCES receive that reading. *)
Theorem logical_entailment_does_not_ban_r_rejection :
  exists W S : Prop, (S -> W) /\ W /\ ~ S /\ ~ r_content W S.
Proof. exists True, False; unfold r_content; tauto. Qed.

Module Numerals.
(* Horn pp.14,20 (2a),(10a),(10a'): literal lower bound, pragmatic upper
   bound, and cancellation by the stronger continuation. *)
Definition lower n count := n <= count.
Definition q_reading n count := lower n count /\ ~ lower (S n) count.

Theorem two_sided_is_exact : forall n count, q_reading n count <-> count = n.
Proof. unfold q_reading, lower; intros; lia. Qed.

Theorem four_cancels_three_upper_bound : lower 3 4 /\ ~ q_reading 3 4.
Proof. unfold q_reading, lower; lia. Qed.

Theorem descriptive_not_three_excludes_four : forall count,
  ~ lower 3 count -> ~ lower 4 count.
Proof. unfold lower; intros; lia. Qed.

Theorem cancellation_is_not_descriptive_negation :
  ~ q_reading 3 4 /\ ~ (~ lower 3 4).
Proof. unfold q_reading, lower; lia. Qed.
End Numerals.

Inductive expression := unmarked | marked.
Record context := {
  ordinary : bool;
  counterpart_available : bool
}.

Section Labor.
Variable World : Type.
Variables literal stereotype : World -> bool.

(* H4 (17): fix an exact common extension for the two expressions.
   Markedness/correspondence are supplied contextual judgments, NOT word
   length tests. Disabling ordinary conditions withdraws both enrichments. *)
Definition accepts (c : context) (e : expression) (w : World) : bool :=
  literal w &&
  if ordinary c then
    match e with
    | unmarked => stereotype w
    | marked => if counterpart_available c then negb (stereotype w) else true
    end
  else true.

Definition readings c e (domain : list World) := filter (accepts c e) domain.

Theorem finite_readings_exact : forall c e domain w,
  In w (readings c e domain) <-> In w domain /\ accepts c e w = true.
Proof. intros; apply filter_In. Qed.

Theorem readings_preserve_literal : forall c e domain w,
  In w (readings c e domain) -> literal w = true.
Proof.
  intros c e domain w H; apply finite_readings_exact in H.
  destruct H as [_ H]; unfold accepts in H; apply andb_true_iff in H; tauto.
Qed.

Theorem labor_disjoint_when_applicable : forall c w,
  ordinary c = true -> counterpart_available c = true ->
  accepts c unmarked w = true -> accepts c marked w <> true.
Proof.
  intros c w Ho Hc; unfold accepts; rewrite Ho, Hc.
  destruct (literal w), (stereotype w); cbn; discriminate.
Qed.

Theorem labor_covers_common_extension : forall c w,
  ordinary c = true -> counterpart_available c = true -> literal w = true ->
  accepts c unmarked w = true \/ accepts c marked w = true.
Proof.
  intros c w Ho Hc Hl; unfold accepts; rewrite Ho, Hc, Hl.
  destruct (stereotype w); cbn; auto.
Qed.

Theorem context_cancellation_restores_literal : forall c e w,
  ordinary c = false -> (accepts c e w = true <-> literal w = true).
Proof. intros c e w H; unfold accepts; rewrite H, andb_true_r; reflexivity. Qed.

Theorem no_counterpart_no_marked_exclusion : forall c w,
  counterpart_available c = false -> (accepts c marked w = true <-> literal w = true).
Proof.
  intros c w H; unfold accepts; rewrite H; destruct (ordinary c);
    rewrite andb_true_r; reflexivity.
Qed.
End Labor.

Module Causatives.
(* H5, p.27 (28): illustration with supplied direct/indirect stereotype.
   These two states do not define the general semantics of kill/cause. *)
Inductive situation := direct | indirect.
Definition domain := [direct; indirect].
Definition literal (_ : situation) := true.
Definition stereotype s := match s with direct => true | indirect => false end.
Definition normal := {| ordinary := true; counterpart_available := true |}.
Definition cancelled := {| ordinary := false; counterpart_available := true |}.
Definition no_counterpart := {| ordinary := true; counterpart_available := false |}.

Theorem killed_caused_contrast :
  readings situation literal stereotype normal unmarked domain = [direct] /\
  readings situation literal stereotype normal marked domain = [indirect].
Proof. split; reflexivity. Qed.

Theorem counterpart_and_context_matter :
  readings situation literal stereotype no_counterpart marked domain = domain /\
  readings situation literal stereotype cancelled unmarked domain = domain /\
  readings situation literal stereotype cancelled marked domain = domain.
Proof. repeat split; reflexivity. Qed.

Theorem same_extension_does_not_identify_readings :
  readings situation literal stereotype normal unmarked domain <>
  readings situation literal stereotype normal marked domain.
Proof. discriminate. Qed.

Theorem removing_counterpart_restores_direct_case :
  ~ In direct (readings situation literal stereotype normal marked domain) /\
  In direct (readings situation literal stereotype no_counterpart marked domain).
Proof. cbn; split; [intros [H | []]; discriminate | auto]. Qed.
End Causatives.
