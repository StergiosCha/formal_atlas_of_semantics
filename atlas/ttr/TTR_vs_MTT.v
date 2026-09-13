(* A model-indexed, information-losing comparison, NOT a framework
   equivalence.  Cooper 2023 sections 1.3-1.4.1 and A3.2 distinguish
   type codes, assignments and witnesses.  C&L 2020 sections 1.2, 1.4.3
   and 3.2 use an MTT as the foundational semantic language itself.

   At a FIXED TTR model, turn the extension of Ind into a Coq subtype
   and erase ptype witnesses to existential propositions.  The resulting
   MTT existential agrees with INHABITATION of the man-runs record type.
   It does not identify types, models, witness objects or judgements.
   No reverse function extracting witnesses from a Prop is assumed.
   The countermodel below proves that even the subject projection of
   well-typed records is not injective. *)
Require Import List.
Require ttr.TTR ttr.TTR_Model mtt_ranta.MTT.
Import ListNotations.

Section FixedModel.
Variables D Base Pred : Type.
Variable M : TTR_Model.model D Base Pred.
Variable ind : Base.
Variables p_man p_run : Pred.

Definition individual : MTT.CN :=
  {d : D | TTR_Model.basic_extension M d ind}.

Definition man (d : individual) : Prop :=
  exists w, TTR_Model.ptype_extension M p_man [proj1_sig d] w.
Definition runs (d : individual) : Prop :=
  exists w, TTR_Model.ptype_extension M p_run [proj1_sig d] w.

Definition man_runs_type : TTR.rty Base Pred :=
  [(0, TTR.TBase ind); (1, TTR.TPty p_man [[0]]);
   (2, TTR.TPty p_run [[0]])].

Definition witness_record (d : D) (m r : TTR.val D) : TTR.rec D :=
  [(0, TTR.VBase d); (1, m); (2, r)].

Lemma ptype_at_subject : forall r v p d,
  TTR.rlookup r 0 = Some (TTR.VBase d) ->
  (TTR_Model.typing M r v (TTR.TPty p [[0]]) <->
   TTR_Model.ptype_extension M p [d] v).
Proof.
  intros r v p d H; cbn.
  unfold TTR.resolve_arg; cbn; rewrite H; reflexivity.
Qed.

Theorem record_to_mtt : forall r,
  TTR_Model.record_typing M r man_runs_type ->
  MTT.some individual (fun d => man d /\ runs d).
Proof.
  intros r H.
  destruct (TTR.of_rty_field D Base Pred _ _ r man_runs_type 0
    (TTR.TBase ind) H eq_refl) as [v [E Hv]].
  destruct v as [d | rr]; [|destruct Hv].
  exists (exist _ d Hv); split.
  - destruct (TTR.of_rty_field D Base Pred _ _ r man_runs_type 1
      (TTR.TPty p_man [[0]]) H eq_refl) as [w [_ Hw]].
    exists w; apply (proj1 (ptype_at_subject r w p_man d E)); exact Hw.
  - destruct (TTR.of_rty_field D Base Pred _ _ r man_runs_type 2
      (TTR.TPty p_run [[0]]) H eq_refl) as [w [_ Hw]].
    exists w; apply (proj1 (ptype_at_subject r w p_run d E)); exact Hw.
Qed.

Theorem mtt_to_record_inhabited :
  MTT.some individual (fun d => man d /\ runs d) ->
  exists r, TTR_Model.record_typing M r man_runs_type.
Proof.
  intros [[d Hd] [[m Hm] [r Hr]]].
  exists (witness_record d m r); cbn in *.
  repeat split; assumption.
Qed.

Theorem fixed_model_inhabitation :
  (exists r, TTR_Model.record_typing M r man_runs_type) <->
  MTT.some individual (fun d => man d /\ runs d).
Proof.
  split; [intros [r H]; exact (record_to_mtt r H) | apply mtt_to_record_inhabited].
Qed.

End FixedModel.

Module LossOfInformation.
Definition M : TTR_Model.model bool bool bool :=
  {| TTR_Model.basic_extension := fun _ _ => True;
     TTR_Model.ptype_extension := fun _ ds _ => ds = [false] |}.

Definition r1 : TTR.rec bool :=
  [(0, TTR.VBase false); (1, TTR.VBase false); (2, TTR.VBase false)].
Definition r2 : TTR.rec bool :=
  [(0, TTR.VBase false); (1, TTR.VBase false); (2, TTR.VBase true)].

Theorem subject_projection_loses_witnesses :
  TTR_Model.record_typing M r1 (man_runs_type bool bool false true false) /\
  TTR_Model.record_typing M r2 (man_runs_type bool bool false true false) /\
  TTR.rlookup r1 0 = TTR.rlookup r2 0 /\ r1 <> r2.
Proof. cbn; repeat split; try reflexivity; discriminate. Qed.

Theorem no_inverse_from_subject :
  ~ exists restore : option (TTR.val bool) -> TTR.rec bool,
      restore (TTR.rlookup r1 0) = r1 /\ restore (TTR.rlookup r2 0) = r2.
Proof.
  intros [f [H1 H2]].
  pose proof (proj2 (proj2 (proj2 subject_projection_loses_witnesses))) as Hne.
  apply Hne; cbn in H1, H2; congruence.
Qed.
End LossOfInformation.

Print Assumptions record_to_mtt.
Print Assumptions mtt_to_record_inhabited.
Print Assumptions fixed_model_inhabitation.
Print Assumptions LossOfInformation.subject_projection_loses_witnesses.
Print Assumptions LossOfInformation.no_inverse_from_subject.
