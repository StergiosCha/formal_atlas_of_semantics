(* Four worked constructions, with the translations kept explicit.
   Cooper 2023 sections 1.3, 1.4.1, A3 and 7.4 p. 312 (69);
   CL20 sections 3.2.3 and 1.4.2; Ranta sections 6.1-6.2 pp.125-127;
   BM17 sections 1.4 and 3.1-3.5.

   This is a comparison harness, NOT a common semantics for the four
   frameworks. MTT/Ranta CNs below are deliberately INDUCED from a fixed
   TTR model. DTS predicates are particular chosen predicates. Negation
   in Cooper (69) uses preclusion across possibilities: we retain that
   requirement, proving only the forward implication to non-membership.
   Our existing TTR syntax lacks negative/function type constructors;
   the corresponding semantic operations are named separately below.
   No CCG derivations, full heterogeneous IS, or dialogue model claimed. *)
Require Import List.
Require ttr.TTR ttr.TTR_Model.
Require mtt_ranta.MTT mtt_ranta.Ranta mtt_ranta.DTS mtt_ranta.DTS_Resolution.
Import ListNotations.

Section NominalPredication.
Variables D Base Pred : Type.
Variable M : TTR_Model.model D Base Pred.
Variable student : Base.
Variable study : Pred.
Variable john : D.

Definition student_type : Type := {d : D | TTR_Model.basic_extension M d student}.
Definition ttr_positive := TTR_Model.basic_extension M john student.
Definition mtt_positive := MTT.in_prop student_type D (@proj1_sig D _) john.
Definition ranta_positive : Type := {s : student_type & proj1_sig s = john}.
Definition dts_positive := TTR_Model.basic_extension M john student.
Definition studies := exists w, TTR_Model.ptype_extension M study [john] w.

(* "John is a student": an assertion about the fixed interpretation;
   it is not a Coq assumption that john already has the CN type. *)
Theorem positive_image : mtt_positive <-> ttr_positive.
Proof.
  split.
  - intros [[d Hd] E]; simpl in E; subst; exact Hd.
  - intros H; exists (exist _ john H); reflexivity.
Qed.

Theorem positive_ranta : Ranta.tequiv ranta_positive dts_positive.
Proof.
  split.
  - intros [[d Hd] E]; simpl in E; subst; exact Hd.
  - intros H; exists (exist _ john H); reflexivity.
Qed.

(* "John is not a student": MTT's image proposition and the DTS
   predicate admit ordinary constructive negation without prior typing. *)
Theorem negative_image : (~ mtt_positive) <-> (~ dts_positive).
Proof. unfold dts_positive; rewrite positive_image; reflexivity. Qed.

Theorem negative_ranta : Ranta.tequiv (Ranta.rnot ranta_positive) (~ dts_positive).
Proof.
  split.
  - intros H p; destruct (H (snd positive_ranta p)).
  - intros H p; exfalso; apply H; exact (fst positive_ranta p).
Qed.

(* "If John is a student, he studies": propositional predication, NOT
   an implication with a typing judgement illicitly placed to its left. *)
Theorem conditional_image :
  (mtt_positive -> studies) <-> (dts_positive -> studies).
Proof. unfold dts_positive; rewrite positive_image; reflexivity. Qed.

Theorem conditional_ranta :
  (ranta_positive -> studies) <-> (dts_positive -> studies).
Proof.
  split; intros H p.
  - exact (H (snd positive_ranta p)).
  - exact (H (fst positive_ranta p)).
Qed.
End NominalPredication.

Section CooperNegation.
Variables D Base Pred : Type.
Variable possibilities : TTR_Model.model D Base Pred -> Prop.
Definition precludes (A B : TTR.ty Base Pred) :=
  forall M, possibilities M -> forall amb v,
    TTR_Model.typing M amb v A -> TTR_Model.typing M amb v B -> False.
Definition negative_witness (M : TTR_Model.model D Base Pred) amb v T :=
  exists other, precludes T other /\ TTR_Model.typing M amb v other.

(* Cooper (69), restricted to the existing fixed universe of type codes.
   Mere absence in ONE assignment is not substituted for preclusion. *)
Theorem negative_excludes_positive : forall M amb v T,
  possibilities M -> negative_witness M amb v T ->
  ~ TTR_Model.typing M amb v T.
Proof.
  intros M amb v T HM [other [Hpre Hother]] Hpos.
  exact (Hpre M HM amb v Hpos Hother).
Qed.
End CooperNegation.

Section MiniDiscourse.
Variables D Base Pred : Type.
Variable M : TTR_Model.model D Base Pred.
Variable man : Base.
Variables entered whistled : Pred.
Definition Man : Type := {d : D | TTR_Model.basic_extension M d man}.
Definition Enter d : Type := {w : TTR.val D | TTR_Model.ptype_extension M entered [d] w}.
Definition Whistle d : Type := {w : TTR.val D | TTR_Model.ptype_extension M whistled [d] w}.
Definition first_sentence : Type := MTT.strong_package Man (fun x => Enter (proj1_sig x)).
Definition mtt_discourse : Type := {u : first_sentence & Whistle (proj1_sig (projT1 u))}.
Definition ranta_discourse : Type :=
  {u : Ranta.some Man (fun x => Enter (proj1_sig x)) & Whistle (proj1_sig (projT1 u))}.
Definition dts_discourse : Type :=
  DTS.PredicateDTS.sequence unit D (fun d => TTR_Model.basic_extension M d man)
    Enter Whistle tt.

(* Strong Sigma in BOTH MTT and Ranta; using MTT's weak existential
   instead would be a different choice and lose the accessible package. *)
Theorem strong_discourse_agreement : Ranta.tequiv mtt_discourse ranta_discourse.
Proof. split; exact (fun x => x). Qed.

Theorem dts_discourse_translation : Ranta.tequiv dts_discourse ranta_discourse.
Proof.
  split.
  - intros [[x [Hm He]] Hw]; exists (existT _ (exist _ x Hm) He); exact Hw.
  - intros [[[x Hm] He] Hw]; exists (existT _ x (Hm, He)); exact Hw.
Qed.

Definition discourse_record_type : TTR.rty Base Pred :=
  [(0, TTR.TBase man); (1, TTR.TPty entered [[0]]);
   (2, TTR.TPty whistled [[0]])].
Definition discourse_record (u : ranta_discourse) : TTR.rec D :=
  let '(existT _ (existT _ (exist _ x _) (exist _ e _)) (exist _ w _)) := u in
  [(0, TTR.VBase x); (1, e); (2, w)].

Theorem discourse_record_sound : forall u,
  TTR_Model.record_typing M (discourse_record u) discourse_record_type.
Proof. intros [[[x Hm] [e He]] [w Hw]]; cbn; repeat split; assumption. Qed.

Theorem discourse_same_referent : forall u,
  TTR.rlookup (discourse_record u) 0 =
    Some (TTR.VBase (proj1_sig (projT1 (projT1 u)))).
Proof. intros [[[x Hm] [e He]] [w Hw]]; reflexivity. Qed.

(* The named @ slot is discharged in the source-shaped dependent context,
   using the actual search result, not an arbitrary Ctx -> Entity parameter. *)
Theorem pronoun_resolves :
  DTS_Resolution.resolution_equation
    [DTS_Resolution.evidence; DTS_Resolution.entity;
     DTS_Resolution.evidence; DTS_Resolution.evidence] [0] 0 1.
Proof. apply DTS_Resolution.search_builds_equation; simpl; auto. Qed.
End MiniDiscourse.
