(* Two short general proofs in scratch. The argument uses the actual Atlas Box
   clause and TTR family predicate. See CMM_CONNECTION_SPEC.md. *)
Require Import CMM_Comparison_spec.
From MontaguePTQ Require Models.
Require ttr.TTR_Model.
Theorem necessity_on_the_image : modal_bridge_statement.
Proof.
  intros D Base Pred M u rho sigma i assignment T realizes.
  rewrite Models.necessity_clause. unfold TTR_Model.necessary.
  split.
  - intros all m [[w t] <-]. apply (realizes (w,t)). apply all.
  - intros all w t. apply (realizes (w,t)).
    apply (all (assignment (w,t))). exists (w,t). reflexivity.
Qed.


Require mtt_ranta.MTT_vs_DTS montague.PTQ.
Theorem every_under_the_noun_correspondence : noun_quantification_statement.
Proof.
  intros A I D Base Pred c noun vp M T image_matches ttr_matches.
  rewrite MTT_vs_DTS.universal_image. unfold PTQ.d_every.
  split; split; intros H x member; apply H.
  - apply (image_matches x); exact member.
  - apply (image_matches x); exact member.
  - apply (ttr_matches x); exact member.
  - apply (ttr_matches x); exact member.
Qed.
