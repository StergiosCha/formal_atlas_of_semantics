(* Derrida, Signature Event Context (1972), local English Limited Inc
   text pp.1-23. P0 campaign, inventory D1-D6.

   ILLUSTRATIVE RECONSTRUCTION, not a verification of deconstruction.
   Added: inductive frames, a tiny interpretation function, exact form
   equality, finite lists, and a two-world accessibility relation. The
   source does not give these definitions. In particular, infinitely many
   quote frames do NOT prove semantic non-saturation of all contexts.
   Distinguish repeatable form, occurrence, origin and contextual effect;
   preserve the p.12 qualification that citability is not validity outside
   a context. The signature result is conditional on identical observed
   forms with distinct origins; it is not an impossibility of authentication
   by richer evidence. No universal readability or intention-independence
   theorem about real language, and no axioms or admissions. *)
Require Import List Arith Lia.
Import ListNotations.

Module ContextualExample.
Inductive mark := sky_blue | green_is_either | signature (pattern : nat).
Inductive frame := assertion | grammar_example | citation (surround : frame).
Inductive effect := weather_claim | example_of_agrammaticality
                  | quoted_form | signature_effect.

(* D2 p.12: the same agrammatical phrase can function as an example.
   Partiality is with respect to this chosen assertion grammar only. *)
Definition reading ctx m : option effect :=
  match ctx, m with
  | assertion, sky_blue => Some weather_claim
  | assertion, green_is_either => None
  | assertion, signature _ => Some signature_effect
  | grammar_example, green_is_either => Some example_of_agrammaticality
  | grammar_example, _ => Some quoted_form
  | citation _, _ => Some quoted_form
  end.
Record occurrence := {
  form : mark;
  context : frame;
  producer_present : option nat
}.
Definition interpret o := reading (context o) (form o).
Definition graft o ctx :=
  {| form := form o; context := ctx; producer_present := producer_present o |}.

Theorem agrammaticality_example :
  reading assertion green_is_either = None /\
  reading grammar_example green_is_either = Some example_of_agrammaticality.
Proof. split; reflexivity. Qed.

Theorem graft_preserves_form : forall o ctx, form (graft o ctx) = form o.
Proof. reflexivity. Qed.

Theorem graft_changes_possible_effect :
  exists o, form (graft o grammar_example) = form o /\
    interpret o = None /\
    interpret (graft o grammar_example) = Some example_of_agrammaticality.
Proof.
  exists {| form := green_is_either; context := assertion; producer_present := None |}.
  repeat split; reflexivity.
Qed.

Theorem context_cannot_be_erased_from_this_interpreter :
  ~ exists decode : mark -> option effect, forall o, decode (form o) = interpret o.
Proof.
  intros [decode H].
  pose proof (H {| form := green_is_either; context := assertion;
                  producer_present := None |}) as Ha.
  pose proof (H {| form := green_is_either; context := grammar_example;
                  producer_present := None |}) as Hb.
  cbn in Ha, Hb; congruence.
Qed.

(* D1: origin metadata is not consulted by THIS chosen interpreter.
   This is an illustration of functioning in absence, not a source law
   that intentions are never relevant to any interpretation. *)
Theorem absent_producer_can_still_be_read :
  exists o, producer_present o = None /\ interpret o = Some weather_claim.
Proof.
  exists {| form := sky_blue; context := assertion; producer_present := None |}.
  split; reflexivity.
Qed.

Theorem producer_metadata_invariant_here : forall m ctx p q,
  interpret {| form := m; context := ctx; producer_present := p |} =
  interpret {| form := m; context := ctx; producer_present := q |}.
Proof. reflexivity. Qed.

Theorem same_form_need_not_be_same_occurrence :
  exists o p, form o = form p /\ o <> p.
Proof.
  exists {| form := green_is_either; context := assertion; producer_present := None |},
         {| form := green_is_either; context := grammar_example; producer_present := None |}.
  split; [reflexivity | discriminate].
Qed.

Fixpoint depth f := match f with citation outer => S (depth outer) | _ => 0 end.
Fixpoint quote n f := match n with 0 => f | S k => citation (quote k f) end.
Fixpoint ceiling fs :=
  match fs with [] => 0 | f :: rest => S (depth f + ceiling rest) end.

Lemma quotation_depth : forall n f, depth (quote n f) = n + depth f.
Proof. induction n; intros f; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma member_below_ceiling : forall fs f, In f fs -> depth f < ceiling fs.
Proof.
  induction fs as [|g fs IH]; intros f H; cbn in *; [contradiction |].
  destruct H as [<- | H]; [lia | specialize (IH f H); lia].
Qed.

(* D2: an actual unboundedness proof about the ADDED quotation syntax.
   Not a proof that the meaning of every mark is semantically unbounded. *)
Theorem fresh_quote_beyond_any_finite_list : forall fs m,
  exists f, ~ In f fs /\ reading f m = Some quoted_form.
Proof.
  intros fs m; exists (quote (S (ceiling fs)) assertion); split.
  - intros H; apply member_below_ceiling in H; rewrite quotation_depth in H; cbn in H; lia.
  - reflexivity.
Qed.

Theorem quotation_levels_distinct : forall n k,
  n <> k -> quote n assertion <> quote k assertion.
Proof.
  intros n k H E; apply (f_equal depth) in E.
  repeat rewrite quotation_depth in E; cbn in E; lia.
Qed.

(* D3 boundary: this model has unbounded contexts but a constant effect
   over ALL quoted instances. Counting contexts cannot prove changing
   meaning or Derrida's universal non-saturation thesis. *)
Theorem unbounded_quotation_can_keep_effect_constant :
  (forall fs, exists f, ~ In f fs /\ reading f green_is_either = Some quoted_form) /\
  (forall n, reading (citation (quote n assertion)) green_is_either = Some quoted_form).
Proof. split; [intros fs; apply fresh_quote_beyond_any_finite_list | reflexivity]. Qed.
End ContextualExample.

Section OriginRecovery.
Variables Token Form Origin : Type.
Variable visible_form : Token -> Form.
Variable origin : Token -> Origin.
Variables a b : Token.
Hypothesis identical_form : visible_form a = visible_form b.
Hypothesis different_origins : origin a <> origin b.

(* D4 pp.19-20: a conditional information-loss result. The sameness
   criterion and origin labels are supplied by the reconstruction. *)
Theorem repeatable_form_cannot_recover_both_origins :
  ~ exists decode : Form -> Origin,
      decode (visible_form a) = origin a /\ decode (visible_form b) = origin b.
Proof. intros [decode [Ha Hb]]; apply different_origins; congruence. Qed.

Theorem richer_evidence_is_not_ruled_out :
  exists decode : Token -> Origin, forall t, decode t = origin t.
Proof. exists origin; reflexivity. Qed.
End OriginRecovery.

Theorem signature_form_and_origin_can_diverge :
  exists (visible : bool -> nat) (origin : bool -> bool),
    visible true = visible false /\ origin true <> origin false /\
    ~ exists decode, decode (visible true) = origin true /\
                     decode (visible false) = origin false.
Proof.
  exists (fun _ => 0), (fun x => x); split; [reflexivity |].
  split; [discriminate |].
  apply (repeatable_form_cannot_recover_both_origins bool nat bool
    (fun _ => 0) (fun x => x) true false); [reflexivity | discriminate].
Qed.

Module Risk.
(* D5 pp.15-18. A modal COUNTERMODEL to conflating possible failure with
   failure of every actual performance. The relation is added, not Derrida's
   definition of structural possibility. true = success, false = failure. *)
Definition accessible (_ _ : bool) := True.
Definition possible_failure here := exists there, accessible here there /\ there = false.

Theorem necessary_risk_coexists_with_success :
  (forall here, possible_failure here) /\ exists actual : bool, actual = true.
Proof.
  split.
  - intros here; exists false; split; [exact I | reflexivity].
  - exists true; reflexivity.
Qed.

Theorem necessary_risk_does_not_mean_all_actual_fail :
  (forall here, possible_failure here) /\ ~ (forall actual : bool, actual = false).
Proof.
  split.
  - exact (proj1 necessary_risk_coexists_with_success).
  - intros H; specialize (H true); discriminate.
Qed.
End Risk.
